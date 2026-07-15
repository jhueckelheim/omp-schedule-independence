# Extending the Schedule-Independent Program Class in ClightOMP

This document defines *where the boundary lies* for schedule-independence and *what can be
proved*, grounded in the constructs ClightOMP actually models. It refines PROOF_PLAN.md sec 1b
and the predicates in `sched_indep/ClassPredicates.v`.

All references are to real definitions:
- `pragma_label` (`OMPParallel/OMPFor/OMPSingle/OMPBarrier/OMPPriv/OMPPrivEnd/OMPRed`) —
  `compcert/cfrontend/Clight.v:151-196`
- `privatization_clause_type := PrivClause (priv_vars: list ident)` — `Clight.v:105`
- `reduction_clause_type := RedClause red_ident red_vars` — `Clight.v:138`
- `privatization`, `init_firstprivate`, `end_privatization`, `priv_idents` — `reduction.v:178-321`
- `step_parallel/step_for/step_barrier/step_priv/step_priv_end/step_red_*/step_single` —
  `HybridMachine.v:404-590`

---

## 1. What the model can and cannot express (this fixes the boundary)

Before drawing the class boundary we note two facts about the *modeled fragment*, because a
program can only violate schedule-independence through effects the semantics represents.

- **Private variables are fresh, disjoint memory — but PER THREAD, not per iteration.**
  `privatization` calls `alloc_pvs` (`reduction.v`) which `Mem.alloc`s a NEW block per
  privatized ident and rewrites the local env, so two threads' private copies never alias.
  HOWEVER, in `transform_state_for` the `Spriv` scope wraps the thread's *entire workload*
  (`transform_chunks` folds all of a thread's chunks into one sequence), so the private block is
  allocated ONCE PER THREAD and its value PERSISTS across that thread's iterations. Consequently
  a private is a safe per-iteration scratchpad ONLY when it is *written before read within each
  iteration*. A private that is *read before written* — e.g. a per-thread iteration counter `c`
  with `c := c+1; w(i) := c` — carries state across iterations and yields SCHEDULE-DEPENDENT
  output (the final `w[]` reveals each thread's load), despite disjoint `w(i)` write sets. Such
  a program has cross-iteration read/write overlap on `c` at the memory-trace level and is
  therefore (correctly) flagged as a conflict by `HardenedConfluence.schedule_independent_or_race`,
  NOT certified as schedule-independent. Soundness of the abstract source-level predicates
  (`disjoint_write_class`) requires `read_foot`/`write_foot` to include ALL accesses, including
  reads/writes of private blocks. This soundness condition is now DISCHARGED in
  `SourceToTrace.v`: the footprints are taken directly from the traces
  (`trace_write_foot`/`trace_read_foot`), `class_eq_traces_indep` proves the class predicate at
  those footprints is equivalent to trace independence (so nothing can be forgotten), and
  `private_counter_not_in_class` proves the counter program is outside the class.

- **Thread identity is NOT a value available to the loop body.** There is no
  `omp_get_thread_num` primitive in the modeled semantics. Thread number enters ONLY inside
  runtime steps (`is_leader`, `get_thread_num` in `step_red_leader`/`step_single`), never as an
  expression the body can evaluate. Consequently *thread-id branching is not expressible* in the
  modeled fragment at all; it could only appear via an unmodeled external call, which is already
  outside the trusted fragment (externals are axiomatized, `Clight_core.v:30`). This makes the
  "no thread-id branching" restriction automatic rather than something to police — but we still
  state it as a class condition for the paper, and enforce it by *excluding external calls*.

---

## 2. The class hierarchy (increasing permissiveness)

We define four nested classes. Each is a predicate over an iteration index set `iters : Z -> Prop`
and per-iteration read/write footprints. `sched_indep/ClassPredicates.v` already has C0 and C1.

### C0 — pure (already formalized: `pure_class`)
No iteration writes any shared location. Shared memory is invariant.
*Provable now, trivially* (no commutation needed).

### C1 — disjoint-write (already formalized: `disjoint_write_class`)
`write_foot i ∩ write_foot j = ∅` and `read_foot i ∩ write_foot j = ∅` for `i≠j`.
Overlapping READ-only is allowed (no condition on `read_foot i ∩ read_foot j`).
This is `out[i]=f(i)`.

### C2 — disjoint-write + well-behaved privates (the prompt's target)
C1 on the SHARED footprint, PLUS each iteration may use private variables provided every private
is **written before read** in that iteration (no dependence on its incoming value). Formally we
split each iteration's footprint into shared and private parts:
- `swrite i`, `sread i` : shared write/read footprints (C1 conditions apply to these);
- `pvars` : the set of privatized idents (from `pc` of the enclosing `OMPPriv`/`OMPParallel`);
- condition **WBR (write-before-read)**: for each private `v` and each iteration, the first
  memory access to `v`'s private block in the iteration is a write.
Because private blocks are freshly allocated and disjoint (sec 1), and WBR means the incoming
(garbage/initial) private value is never observed, private state contributes nothing to the
cross-iteration relation. *This is the intended boundary in the prompt.*

### C3 — C2 + associative-commutative reductions
Allow shared updates that go exclusively through an `OMPRed` clause whose combiner is
associative and commutative (`RedIdPlus`, `RedIdTimes`, `RedIdOr`, `RedIdXor`, `RedIdAnd`,
logical and/or; `min`/`max`). Handled by `step_red_leader` (`HybridMachine.v:550`): the leader
folds all teammates' private copies. Schedule-independence of the *reduced result* reduces to
AC-fold-over-a-Permutation, and we already have the permutation of chunks (`ChunkIndep.v`).

---

## 3. Where the boundary lies (what BREAKS schedule-independence)

These are the exclusions; each maps to a concrete modeled construct:

1. **Overlapping shared writes** (two iterations write the same location) — breaks C1.
   Detected as `¬ foot_disjoint (swrite i) (swrite j)`.
2. **Read-after-write across iterations** (`sread i ∩ swrite j ≠ ∅`, `i≠j`) — breaks C1.
3. **`firstprivate` (`pc_first`) that is then MUTATED and whose result escapes**: `firstprivate`
   itself is deterministic (each copy initialized from the same original via `init_firstprivate`,
   `reduction.v:178`), so *reading* a firstprivate is fine and schedule-independent. The hazard is
   only if combined with `lastprivate`. We therefore ALLOW `firstprivate` under WBR-for-subsequent
   writes, and note this refines the prompt's "firstprivate probably not allowed": it is allowed
   as a pure initializer; it is the *lastprivate writeback* that is the real problem.
4. **`lastprivate`**: writes the private value of the *sequentially last* iteration back to the
   shared original. NOTE: `lastprivate` is **not currently modeled** (no clause/step for it), so
   in this framework it is simply *out of the expressible fragment*. For the paper: exclude it
   syntactically; it cannot be given a schedule-independent semantics because it names a
   distinguished "last" iteration.
5. **Thread-id branching**: not expressible (sec 1); excluded by forbidding external calls and
   `omp_get_thread_num`. Enforced via a `no_external_calls` syntactic predicate on the body.
6. **Non-AC reductions / user combiners** (`RedIdIdent id` other than min/max): excluded from C3.
7. **Reductions with `min`/`max` producing an INDEX** (argmax) — value is AC but tie-breaking is
   order-sensitive; exclude or restrict to the value.

---

## 4. What we can prove, per class (theorem shapes)

Let `obs_equiv (loop_output_foot iters swrite)` be the result relation (`ObsEquiv.v`).

- **T0 (C0):** every schedule/thread-count yields *identical* shared memory. Proof: shared write
  footprint empty ⇒ `Ostep`s on the body do not change shared contents ⇒ `content_equiv`
  trivially. *No diamond.* — smallest next milestone after StepCongruence.
- **T1 (C1):** `obs_equiv` on `loop_output_foot`. Proof: L3 independent-step diamond (disjoint
  footprints ⇒ steps commute up to `mem_equiv`) + L4 confluence + L5 chunk/thread independence
  (`ChunkIndep.v`).
- **T2 (C2):** T1, with private effects quotiented out. Proof: T1 on shared footprint; a
  *private-erasure* lemma: because private blocks are fresh and WBR holds, the shared projection
  of an iteration's step is independent of private contents. Needs a lemma that `privatization`'s
  fresh blocks are disjoint from any prior footprint (from `Mem.alloc` freshness).
- **T3 (C3):** `obs_equiv` on the reduction variables, via AC-fold-over-Permutation of the
  per-thread partial results; combine with `team_workloads_is_a_division`
  (`for_construct.v:148`) already exported by `chunksplit_covers_chunks`.

---

## 5. New predicates/lemmas to add (extends ClassPredicates.v)

In `sched_indep/ClassPredicates.v` (and later files):
- `shared_disjoint_write_class` : C1 restricted to a shared footprint (split from private).
- `write_before_read` (WBR) : per private ident, first access is a write. (Stated over the body's
  event trace / access sequence; wired up when StepCongruence exposes per-step events.)
- `no_external_calls : statement -> Prop` : rules out unmodeled thread-id/externals (walk the
  `statement` AST from `Clight.v:198`, reject `Scall`/`Sbuiltin` to non-pure targets).
- `uses_lastprivate : pragma_label -> Prop := fun _ => False` with a note that it is unmodeled
  (documents the exclusion honestly).
- `ac_reduction : reduction_identifier_type -> Prop` : the associative-commutative combiners
  (`RedIdPlus/Times/Or/Xor/And/LogicalAnd/LogicalOr`, and `RedIdIdent` only for min/max).
- Lemmas: `pure_is_disjoint_write` (have it); add `disjoint_write_shared_of_pure`,
  `firstprivate_is_deterministic` (init from same original ⇒ same value), and
  `ac_reduction_fold_permutation_invariant` (fold of an AC op is Permutation-invariant) —
  the last is a pure list lemma, provable now with no machine reasoning.

---

## 6. Recommended proof order (each independently compilable)

1. `ac_reduction_fold_permutation_invariant` — pure `stdpp`/`list` lemma; provable immediately,
   no machine step needed. Establishes the C3 algebraic core early and reuses `ChunkIndep`.
2. `firstprivate_is_deterministic` — over `init_firstprivate`; small, no schedule.
3. `no_external_calls` + `ac_reduction` + `shared_disjoint_write_class` predicates.
4. StepCongruence (L2) for Clight `dry_step` restricted to a fixed shared footprint → gives T0.
5. Diamond (L3) for two disjoint `dry_step`s → T1.
6. Private-erasure lemma (fresh-alloc disjointness) → T2.
7. Assemble T3 from step 1 + `step_red_leader` + chunk permutation.

## 7. Honest limits for the paper
- `lastprivate` and `omp_get_thread_num` are OUTSIDE the modeled fragment: the results say
  nothing about programs using them, and we state that as a scope limitation, not a proof.
- `nowait`/`schedule(...)` clauses: the machine already abstracts the schedule as `seq nat`, so
  clause-level `schedule(static|dynamic|guided)` is *subsumed* — any of them is just one concrete
  `ChunkSplit`, and our theorems quantify over all `ChunkSplit`s. This is a strength worth stating.
- Externals are axiomatized (`Clight_core.v:30`); the class forbids them, so the axiom is off-path.
- The 24 `Admitted` lemmas in the dry-machine files must be audited against the T0→T2 path.
