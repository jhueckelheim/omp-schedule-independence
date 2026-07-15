# Plan: Proving Schedule-Independence for a Class of OpenMP `parallel for` Loops in ClightOMP/Coq

This plan is grounded in the *actual* ClightOMP API (read from source, not invented). File/line
references point at the real definitions the proof must be stated against.

Environment is built and verified:
`eval $(opam env --switch=ClightOMP)`, then `make concurrency/openmp_sem/HybridMachine.vo` (exit 0).

---

## Progress log (compiled, machine-checked in `ClightOMP/sched_indep/`)

Build all with `sh sched_indep/build.sh`. Status of each file:

- `ObsEquiv.v`        — result relation `obs_equiv foot` (footprint-restricted content
                        equivalence), `Equivalence`, `mem_equiv_obs_equiv`, monotonicity,
                        `range_footprint`.  *Closed under global context.*
- `ClassPredicates.v` — `disjoint_write_class`, `pure_class`, `loop_output_foot`,
                        `pure_is_disjoint_write`.  *Closed.*
- `ChunkIndep.v`      — L5 chunk-level thread-count independence:
                        `chunksplit_thread_count_independent` (two ChunkSplits of the same loop
                        with different thread counts distribute the same multiset of chunks).
                        *Closed.*
- `Reduction.v`       — C3 algebraic core: `ac_fold_permutation_invariant`,
                        `reduce_workloads_thread_count_independent`.  *Closed.*
- `StepFraming.v`     — memory-effect core of T0: a read-only event trace leaves memory
                        unchanged (`ev_elim_read_only_id`) and preserves `obs_equiv`; bridged to
                        the `ev_step` relation used inside `dry_step`.  *Closed.*
- `DryStepFraming.v`  — T0 at the THREAD-STEP layer: `dry_step_read_only_obs_equiv` — a read-only
                        `dry_step` preserves observable memory contents on every footprint.
                        *Depends only on the CompCert/VST axiom base* (classical logic, funext,
                        `inline_external_call_mem_events`), inherited via `restrPermMap`. No
                        `Admitted`, no new axioms. This is the expected axiom boundary: any lemma
                        touching the machine's permission machinery inherits these.
- `OstepFraming.v`    — T0 at the TOP-LEVEL machine step: `Ostep_read_only_obs_equiv`. By full
                        case analysis on a coarse-machine `Ostep` (all 9 machine_step cases):
                        resume/suspend/suspend_pragma/halted/schedfail leave memory unchanged
                        (reflexivity); the internal `thread_step` case is discharged by
                        DryStepFraming under a read-only-events hypothesis; start_thread / syncStep
                        / pragmaStep are the memory-mutating cases the pure class forbids and are
                        excluded by explicit negation hypotheses. Uses coarse diluteMem = id
                        implicitly. Same CompCert/VST axiom base; no `Admitted`, no new axioms.

- `OstepRun.v`        — **T0 COMPLETE (multi-step / whole run).** `pure_run_obs_equiv`: a run in
                        which every step is taken out of a `pure_state` (all `threadStep` traces
                        read-only; no start/sync/pragma step possible) leaves the observable output
                        unchanged from start to finish. Proof: `all_pure_run` threads the per-state
                        pure conditions through the raw `Ostep` closure; `pure_ostep_preserving`
                        bridges each step to a preserving step via
                        `OstepFraming.Ostep_read_only_obs_equiv`; `preserving_run_obs_equiv` chains
                        them by induction on `clos_refl_trans_1n` using transitivity of
                        `obs_equiv`. Same CompCert/VST axiom base; no `Admitted`, no new axioms.

        Because `Ostep` is driven by the schedule (head of `U`) and the theorem quantifies over
        ALL runs, this covers every schedule; via `step_parallel`'s free choice of `num_threads`
        it also covers every thread count. **The pure class is thereby proved schedule- and
        thread-count-independent at the level of observable memory.**

- `Diamond.v`         — **memory-commutation core of L3 (disjoint-write class C1).**
                        `storebytes_storebytes_comm`: two `Mem.storebytes` to location-disjoint
                        ranges (different blocks, or same block with non-overlapping offset ranges,
                        `loc_disjoint`) commute up to `mem_equiv` — either order yields
                        content/Cur/Max/nextblock-equal memories. Supporting: `setN_setN_comm`
                        (disjoint `setN` commute pointwise) and `setN_get_in_indep` (in-range
                        `setN` value is base-independent). Built from CompCert primitives
                        `storebytes_mem_contents` / `storebytes_access` / `nextblock_storebytes` +
                        `setN_outside`. **Closed under the global context — no axioms at all**
                        (pure CompCert memory reasoning; the mem_equiv record is axiom-free here).

- `EvElimFrame.v`     — L3 lifted to the event-trace layer. `ev_elim_wr_frame`: a write-only
                        event trace preserves contents outside its write-footprint (frame).
                        `ev_elim_wr_within_base_indep`: running the SAME write-only trace on two
                        different base memories gives identical contents at any WRITTEN location
                        (last-write-wins is base-independent). **Closed under global context.**
- `StepDiamond.v`     — **the C1 DIAMOND (observable level).** `ev_elim_diamond_obs`: two
                        write-only traces with DISJOINT confinement footprints, run in either
                        order, agree on the union of the footprints. Combines the frame and
                        base-independence lemmas. **Closed under global context — no axioms.**
- `Confluence.v`      — **T1 / C1 COMPLETE (schedule-independence for disjoint-write).**
                        `run_permutation_agree`: modelling a parallel-for as a list of per-iteration
                        write-only traces confined to pairwise-disjoint footprints, ANY two orders
                        (any `Permutation` of the iteration list — i.e. any schedule / thread count)
                        agree on the observable output over the union footprint. Proof: each union
                        location has a unique owning iteration (disjointness + a `pairwise_disjoint`
                        index argument); framing makes all other iterations invisible there; the
                        owner determines the value base-independently. Depends only on classical
                        logic (`classic`, for owner-uniqueness); no `Admitted`, no framework axioms.
- `HardenedConfluence.v` — **RACE-AGNOSTIC hardening.** Independence is now read off the ACTUAL
                        traces (`writes`/`reads` extracted from the events), is decidable/total
                        (`indep_or_conflict`), and is the exact hypothesis of the guarantee.
                        `schedule_independent_or_race`: for ANY write-only trace list (race-free or
                        not) and any two orders, EITHER the two runs agree everywhere OR an explicit
                        conflicting pair is produced (a race witness). Independence transports across
                        the reordering via the permutation's positional bijection
                        (`traces_indep_perm`, from `Permutation_nth`), and the content at each
                        location is characterised canonically (`raw_run_content_char`). Depends only
                        on `classic`; no `Admitted`, no framework axioms.

STATUS: C0 (pure, T0) and C1 (disjoint-write, T1) are machine-checked, and the C1 result is
additionally available in a RACE-AGNOSTIC form (`HardenedConfluence.v`) whose independence
hypothesis is derived from the traces and comes with a race witness on the negative side. C3's
algebraic core (`Reduction.v`) and thread-count independence (`ChunkIndep.v`, L5) compose with C1.

Remaining to reach a single end-to-end `Ostep`-level C1 theorem (optional hardening): connect the
`ev_elim`-level `run` model to actual `Ostep` runs by showing each iteration's `dry_step` emits a
write-only trace confined to its footprint (via `ev_step_elim` + the disjoint-write class predicate)
and that the machine's schedule/`ChunkSplit` choice realises a permutation of the iteration list.
The memory-effect core (the hard mathematics) is complete; this remaining step is bookkeeping that
threads the thread-pool/permission plumbing, reusing `disjoint_norace`/`restrPermMap_disjoint_inv`.

---

## 0. What the framework already gives us (and what it does NOT)

Building blocks that exist:
- `Ostate := (MachState * mem)`  — `HybridMachine.v:1043`
- `MachState := (schedule * event_trace * t * team_tree)` — `HybridMachineSig.v:327`
- `schedule := seq nat` (list of thread ids) — `HybridMachineSig.v:326`
- `Ostep : Ostate -> Ostate -> Prop` (one coarse-machine step) — `HybridMachine.v:1045`
- `Ostep_refl_trans_closure := clos_refl_trans_1n Ostate Ostep` — `HybridMachine.v:1047`
- Coarse scheduler: `yield = id`, `diluteMem = id`, `isCoarse = true` — `HybridMachineSig.v:719-732`
- `pragma_step` with `step_parallel` / `step_for` / `step_barrier` / `step_red_leader` … — `HybridMachine.v:404-590`
- `ChunkSplit lb incr iter_num thread_num chunks team_workloads` record; the key field
  `team_workloads_is_a_division : Permutation (concat team_workloads) chunks` — `for_construct.v:116-149`
- `mem_equiv` : proven `Equivalence` on memories (Cur/Max/content/nextblock) — `mem_equiv.v:203-210`
  with `Proper` rewrite lemmas for `Mem.perm`, `load`, `store`, `restrPermMap`.

What does NOT yet exist (this is the novel contribution):
- No determinism / confluence / diamond / schedule-independence theorem anywhere.
- `mem_equiv` is only on memories; it is **not lifted to `Ostate`/thread pools**.
- 24 `Admitted` + 3 `Axiom`s remain (externals determinism assumed in `Clight_core.v:30`).
  The proof must either avoid the `Admitted` lemmas on its path or discharge/ scope them.

Implication for the paper: the honest framing is a **determinism / schedule-independence
meta-theorem for a restricted program class**, layered on ClightOMP. The authors already argue
data-race-freedom of successful runs; we build the stronger "same result for all schedules".

---

## 1. Two things that must be defined precisely first

### 1a. "Same behavior regardless of schedule and thread count"
Define a *result equivalence* on final observable state. Options, in increasing strength:
- (R1) `mem_equiv (final memory)` — final memories agree on contents + permissions + nextblock.
- (R2) R1 restricted to a designated output footprint (e.g. the output array block/range),
  which is what an application programmer actually cares about.
Recommended: prove R2 (footprint) as the headline, derive from R1 machinery.

We must lift `mem_equiv` (memories) to a relation `Ostate_equiv` on `Ostate`, OR — simpler and
enough for the headline claim — define observation as a projection `obs : Ostate -> mem` (the
`.2`) and state results modulo `mem_equiv` on that projection over the output footprint.

### 1b. "The program class"
Formalize a syntactic/semantic predicate on the loop body. Start with the strongest, easiest
class and generalize. Candidate predicates (define as Coq `Prop`s over the `CanonicalLoopNest`
`loop_body` and the enclosing state):

- (C-pure)  loop body performs no writes to shared memory (reads-only of shared, writes only to
  thread-private / freshly-privatized locations). Trivial independence: shared state never changes.
- (C-disjoint-write)  iteration `i` writes only within a per-iteration footprint `W(i)`, with
  `W(i) ∩ W(j) = ∅` for `i≠j`, and reads are disjoint from all `W(j)` (`j≠i`). This is the
  `output_array[i] = f(i)` case in `schedule_independent_loop.c`.
- (C-reduction)  writes go through the OMP `reduction` clause with an associative-commutative
  combiner; handled by `step_red_leader` + a Permutation/AC fold argument.

Recommended target for the first full proof: **C-disjoint-write**, because it matches the running
example, exercises `step_for` + `ChunkSplit` (the schedule), and needs no AC algebra.

---

## 2. The central theorem (statement to aim for)

Informal: for a well-formed initial `Ostate` whose only pragma is one `#pragma omp parallel for`
over a canonical loop nest whose body satisfies `C-disjoint-write`, any two terminating coarse-machine
runs starting from that state under *any* two schedules `U1, U2` and *any* thread counts reach final
states whose output footprints are `mem_equiv`.

Sketch of the Coq statement (names are placeholders to be created; everything else is real):

```coq
Theorem parallel_for_schedule_independent :
  forall (ge:genv) (os0 : Ostate) (foot : footprint)
         (U1 U2 : schedule) (os1 os2 : Ostate),
    well_formed_init os0 ->
    single_parallel_for os0 ->            (* program is exactly one omp parallel for *)
    disjoint_write_body os0 ->            (* the class predicate, sec 1b *)
    with_sched U1 os0 ->                  (* os0 but with schedule U1 *)
    Ostep_refl_trans_closure (with_sched U1 os0) os1 ->
    halted os1 ->
    Ostep_refl_trans_closure (with_sched U2 os0) os2 ->
    halted os2 ->
    mem_equiv_on foot (obs os1) (obs os2).
```

Thread-count independence is subsumed: `num_threads` is chosen inside `step_parallel`
(`Hnum_threads: num_threads > 0`, `HangleSplit: permMapJoin_list perms perm`), so quantifying over
all valid runs already quantifies over thread counts and over all `ChunkSplit`s the machine may pick.

---

## 3. Proof architecture (bottom-up lemmas)

The robust route is a **confluence / strong-local-commutation** argument specialized to the race-free
class, then "all terminating runs end mem_equiv". Layered lemmas:

**L1. Lift `mem_equiv` to states.** Define `Ostate_equiv` and prove it is an `Equivalence`
(reuse `Equivalence_mem_equiv`, `mem_equiv.v:210`). Prove `obs` and the output-footprint projection
are `Proper` w.r.t. it.

**L2. Step respects state equivalence (congruence).**
`Ostep os1 os1' -> Ostate_equiv os1 os2 -> exists os2', Ostep os2 os2' /\ Ostate_equiv os1' os2'`
for steps of the class. This is the workhorse and where most effort goes; it must be proved per
`pragma_step` / `dry_step` constructor that the class can exhibit. For C-disjoint-write the relevant
constructors are: Clight `dry_step` (thread-local body execution), `step_parallel`, `step_for`,
`step_barrier`. `step_red_*`, `step_priv*`, `step_single` are excluded by the class or handled trivially.

**L3. Independent-step commutation (the diamond).**
For two enabled steps on *different* thread ids `i≠j` operating on disjoint permission footprints
(guaranteed by `invariant tp` / `permMapJoin_list` and the disjoint-write predicate), the steps
commute up to `Ostate_equiv`:
`Ostep_i then Ostep_j  ≈  Ostep_j then Ostep_i`.
Key supporting facts already present: `store_max_equiv` (`mem_equiv.v:533`), permission-disjointness
lemmas `disjoint_norace`/`no_race_racy` (`permissions.v:374,894`), and structural commutation
`vinsert_commute` (`finThreadPool.v:812`).

**L4. Schedule reordering.** Using L3 as a local diamond, prove that permuting the schedule of a
maximal run yields an `Ostate_equiv` final state (standard confluence-from-local-diamond +
strong normalization argument; termination is assumed via the `halted os1/os2` hypotheses so we only
need the "1-step diamond ⇒ confluent" direction, i.e. Newman/Hindley-style but with equivalence).

**L5. Chunk/thread-count independence.** Specialize: the machine's choice of `num_threads` and of
`team_workloads` (a `ChunkSplit`) only reorders which thread runs which `chunk`. Because
`team_workloads_is_a_division : Permutation (concat team_workloads) chunks` (`for_construct.v:148`),
two different `ChunkSplit`s cover the exact same set of iteration chunks; combined with L3/L4 the
final output footprint is `mem_equiv`. This is where "thread count doesn't matter" is discharged.

**L6. Main theorem.** Compose L4 (schedule reorder) + L5 (chunk/thread reorder) + L2 (congruence),
project to the footprint (L1), conclude `mem_equiv_on foot`.

---

## 4. Concrete file layout to add (do not modify upstream files)

Create a new subdirectory `concurrency/openmp_sem/sched_indep/`:
- `ObsEquiv.v`        — L1: `Ostate_equiv`, `mem_equiv_on foot`, Proper instances.
- `ClassPredicates.v` — sec 1b: `disjoint_write_body`, `pure_body`, `well_formed_init`,
                         `single_parallel_for`, `with_sched`, `halted`, `obs`.
- `StepCongruence.v`  — L2, per relevant `pragma_step`/`dry_step` constructor.
- `Diamond.v`         — L3 independent-step commutation.
- `Confluence.v`      — L4 schedule reordering from the diamond.
- `ChunkIndep.v`      — L5 thread-count / ChunkSplit independence via the Permutation field.
- `ScheduleIndependence.v` — L6 main theorem + the running-example corollary.
Add these targets to a *local* `Make`/`_CoqProject` extension so upstream `Makefile` is untouched.

## 5. The running example as a corollary
Instantiate the theorem for `schedule_independent_loop.c`:
- Run `clightgen` (bundled in `compcert/`) on the C file to get its Clight AST, or hand-encode the
  canonical loop nest `for(i=0;i<n;i++) out[i]=f(i)` with `f` an opaque pure `int->int`.
- Discharge `disjoint_write_body`: iteration `i` writes only `&out[i]`; `f` reads no shared state.
  `W(i)={&out[i]}` pairwise disjoint by injectivity of array indexing.
- Apply `parallel_for_schedule_independent` to get: all schedules & thread counts agree on `out`.

## 6. Risk register / where effort concentrates
- **L2 & L3 are the hard 80%.** They require reasoning through the dry-machine permission model and
  the 24 `Admitted` lemmas in `dry_machine_lemmas.v` / `dry_machine_step_lemmas.v`. Audit which of
  those 24 lie on our proof path; either (a) prove them, (b) restrict the class so they are not
  needed, or (c) state them as explicit, clearly-labeled assumptions in the paper.
- **External-call determinism** is an `Axiom` (`Clight_core.v:30`). Keep `f` internal (no externals)
  so the axiom is irrelevant to the class, or inherit it explicitly.
- **Termination** is taken as a hypothesis (`halted`), sidestepping strong-normalization proofs.
- Decide R1 vs R2 early; R2 (footprint) is both weaker to prove and more meaningful to report.

## 7. Suggested milestones (each independently compilable / reviewable)
1. `ObsEquiv.v` + `ClassPredicates.v` compile; example loop encoded and type-checks.  (small)
2. `StepCongruence.v` for Clight `dry_step` + `step_for` only.                          (medium)
3. `Diamond.v` for two disjoint `dry_step`s.                                            (large)
4. `Confluence.v` schedule reorder for the parallel-region body.                         (large)
5. `ChunkIndep.v` + `ScheduleIndependence.v` main theorem, example corollary.            (medium)
6. Paper: state assumptions (Admitted-audit result), the class predicate, the theorem, the corollary.

## 8. Fallback if full confluence proves too costly
If L3/L4 general confluence is too heavy for the paper's timeline, retreat to the **C-pure** class
first: shared memory is invariant, so *every* schedule trivially yields the identical final memory
(no diamond needed — L2 collapses because shared state never changes). This gives a complete,
machine-checked schedule-independence theorem for a nontrivial class quickly, with C-disjoint-write
and C-reduction as the paper's "extension" sections.
