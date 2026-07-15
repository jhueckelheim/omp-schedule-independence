# Machine-Checked Schedule-Independence for OpenMP `parallel for`

This repository contains Coq proofs that certain classes of OpenMP `parallel for`
loops produce the **same observable result regardless of the schedule and the
number of threads**. The proofs are stated and machine-checked against the
[ClightOMP](https://github.com/dkxb/ClightOMP) formal semantics of C-with-OpenMP
(a fork of [VST](https://github.com/PrincetonUniversity/VST) / CompCert).

The development is self-contained (12 `.v` files under [`src/`](src/)), adds
nothing to and modifies nothing in ClightOMP, and every headline theorem has been
checked with `Print Assumptions` (no `Admitted`, no new axioms).

## What is proved

Two classes of loops are proved schedule- and thread-count-independent at the
level of observable memory, plus the algebraic core of a third:

- **C0 — pure bodies** (no shared writes).
  `pure_run_obs_equiv` ([`src/OstepRun.v`](src/OstepRun.v)) — proved **end-to-end
  on the real top-level machine relation `Ostep`**, by case analysis over all
  nine `machine_step` constructors. Any run of a pure-body loop leaves observable
  memory unchanged, for every schedule (the schedule drives `Ostep`) and every
  thread count (chosen in `step_parallel`).

- **C1 — independent iterations** (often abbreviated "disjoint-write", but the
  condition is stronger). Distinct iterations must have **disjoint write sets**
  *and* **no iteration may read a location that another iteration writes**;
  overlapping *read-only* accesses are allowed. These are exactly the Bernstein
  conditions for independence, captured by `disjoint_write_class` in
  [`src/ClassPredicates.v`](src/ClassPredicates.v) via its two fields
  `dw_write_disjoint` (no cross-iteration write/write overlap) and
  `dw_read_write_disjoint` (no cross-iteration read/write overlap).
  `run_permutation_agree` ([`src/Confluence.v`](src/Confluence.v)) — modelling the
  loop as per-iteration write-only event traces confined to pairwise-disjoint
  footprints, **any two orders of the iterations (any permutation — i.e. any
  schedule / thread count) agree on the observable output**. This is the genuine
  "same result regardless of interleaving" theorem; its core is a
  commutation/diamond argument on memory writes.

  Disjoint *writes alone* would not suffice — a read-after-write across iterations
  is order-sensitive. That case is excluded twice over: by
  `dw_read_write_disjoint`, and structurally by the proof, which represents each
  iteration as a **fixed** byte-trace and relies on it computing the same bytes
  regardless of when other iterations run — valid precisely because an
  iteration's reads are never touched by another iteration's writes.

- **C3 — associative-commutative reductions** (algebraic core).
  `reduce_workloads_thread_count_independent` ([`src/Reduction.v`](src/Reduction.v))
  — an AC reduction over the loop's chunks is invariant under the thread-count and
  work split, via the `ChunkSplit` permutation invariant.

### A guarantee that holds even for possibly-racy programs

The theorems above assume independence as a hypothesis. The **hardened** result
([`src/HardenedConfluence.v`](src/HardenedConfluence.v)) removes that assumption
and applies to an *arbitrary* program:

- `schedule_independent_or_race` — for any list of per-iteration memory-event
  traces and any two orders (permutations) of it, **either** the two runs agree
  at every memory location (schedule-independent output) **or** the traces
  exhibit an explicit conflicting pair — two distinct iterations, one writing a
  location the other reads or writes (a witnessed potential data race).

Crucially, the independence condition is **read off the actual execution traces**
(their write and read sets), not assumed about the source, and it is total
(`indep_or_conflict`: any trace list is either independent or has a witnessed
conflict). So the guarantee is never *claimed* for a racy program — on such input
the independence disjunct simply does not hold and a concrete race witness is
returned. `raw_run_permutation_agree` is the independent-case guarantee; it uses a
canonical-value characterisation (`raw_run_content_char`) and transports
independence across the reordering via the permutation's positional bijection
(`traces_indep_perm`).

## Why this is faithful to OpenMP

Two properties of the ClightOMP semantics make these results meaningful (verified
against the source; see [`docs/CLASS_EXTENSION_PLAN.md`](docs/CLASS_EXTENSION_PLAN.md)):

- **The schedule is genuinely implementation-defined.** In ClightOMP's `step_for`
  rule the chunking and the assignment of chunks to threads are *universally
  quantified* `ChunkSplit` arguments: the step relation admits **any** valid
  partition and **any** permutation of chunks across threads. No `schedule(...)`
  clause is modelled, matching the standard's "unspecified schedule when no clause
  is present." Our theorems quantify over all such splits, so they cover every
  implementation-defined schedule (and any explicit `static/dynamic/guided`, which
  is just one concrete `ChunkSplit`).

- **Private variables are per-THREAD copies that persist across a thread's
  iterations.** Privatization allocates a **fresh memory block** per privatized
  identifier (`Mem.alloc`, distinct from every block ever allocated) and rewrites
  the thread's local environment. Crucially, in `transform_state_for` the `Spriv`
  scope wraps the thread's *entire workload* (`transform_chunks` folds all of a
  thread's chunks into one sequence inside a single privatization), so a private
  copy is allocated **once per thread, not once per iteration**, and its value
  survives from one iteration to the next on the same thread. `firstprivate` is a
  deterministic initializer.

### Private variables, reads-after-writes, and synchronization

Three questions come up naturally; the answers determine exactly what is and is
not covered.

- **Reads of another iteration's writes.** A loop where iteration `i` reads a
  location that iteration `j` writes *is* schedule-dependent, and is **not**
  covered by C1: `dw_read_write_disjoint` forbids it. "Disjoint writes" is a
  deliberate shorthand for the full independence (Bernstein) condition — see the
  C1 description above.

- **Private variables carry state across a thread's iterations, and this can be
  schedule-dependent.** Because privatization is per-thread (above), a private is
  *not* automatically a safe per-iteration scratchpad. It is safe only when it is
  **written before it is read within each iteration**, so that no value flows from
  one iteration to a later one through it. A private that is *read before written*
  in an iteration — e.g. a **per-thread counter** `c` incremented each iteration
  and stored as `w(i) = c` — genuinely produces schedule-dependent output: even
  though the `w(i)` write sets are disjoint across threads, the final array lets an
  observer read off each thread's iteration count, i.e. the load distribution the
  scheduler chose.

  Such a program is **correctly *not* certified** by the hardened theorem
  ([`src/HardenedConfluence.v`](src/HardenedConfluence.v)), because that theorem's
  independence hypothesis is read off the **actual memory-event traces**: the
  counter block `c` is *read* by later iterations and *written* by earlier ones,
  so distinct iterations on the same thread have a read/write (and write/write)
  overlap on `c`. That is exactly a `conflict2`, so `traces_indep` is false and
  `schedule_independent_or_race` returns its **race-witness** disjunct rather than
  claiming schedule-independence. This is the payoff of hardening the hypothesis
  to be about traces (which include every private access) instead of about
  source-level shared footprints.

  Caveat for the *abstract source-level* predicates in
  [`src/ClassPredicates.v`](src/ClassPredicates.v): `read_foot`/`write_foot` are
  soundness-relevant only if they over-approximate **all** of an iteration's
  memory accesses, *including reads and writes of private blocks*. If a private
  read is omitted from `read_foot`, the predicate can be wrongly satisfied for a
  schedule-dependent program like the counter above. A dedicated write-before-read
  predicate (class C2) and a proof connecting the source footprints to the
  trace-level accesses (so private reads are automatically counted) is future work
  (see [`docs/CLASS_EXTENSION_PLAN.md`](docs/CLASS_EXTENSION_PLAN.md)). Until then,
  the trace-level `HardenedConfluence.v` result is the one that soundly handles
  privates, precisely because it cannot "forget" a private access.

- **Atomics, locks, and other synchronization.** These are deliberately **out of
  scope**, and correctly so: synchronization is exactly what lets one build
  schedule-dependent (yet data-race-free) outcomes. In ClightOMP, locks are a
  *separate* machine step (`syncStep`/`ext_step`), not a thread-internal
  `dry_step`. The C0 theorem excludes them by an explicit hypothesis ruling out
  `syncStep` (and `start_thread`/`pragmaStep`); the C1 model excludes them
  structurally, since a lock acquire/release is a `sync_event` and an atomic
  read-modify-write is not expressible as the plain write-only memory-event trace
  that C1 quantifies over. OpenMP `atomic`/`critical`/explicit locks are not part
  of the modelled loop-body fragment at all. The *sanctioned* way to have many
  iterations update shared state is a **reduction**, handled separately (C3,
  [`src/Reduction.v`](src/Reduction.v)) via associativity/commutativity of the
  combiner — a naive shared `+=` would be a write/write overlap that C1 forbids.

Also out of scope, by design: `lastprivate` and `omp_get_thread_num` are not
modelled by ClightOMP (so thread-id branching is not expressible in the verified
fragment); the classes forbid external calls to keep the axiomatized externals off
the proof path.

## Repository layout

```
src/                    the 12 Coq proof files (build order below)
docs/
  CLASS_EXTENSION_PLAN.md   where the class boundary lies; faithfulness audit
  PROOF_PLAN.md             design notes and per-file progress log
examples/
  schedule_independent_loop.c   the motivating C example (out[i] = f(i))
build.sh                a build driver (see below)
```

### File map (build order)

| File | Result |
|------|--------|
| [`src/ObsEquiv.v`](src/ObsEquiv.v) | observation relation `obs_equiv foot` (footprint-restricted content equivalence), an `Equivalence`; `mem_equiv` ⇒ `obs_equiv` |
| [`src/ClassPredicates.v`](src/ClassPredicates.v) | `pure_class`, `disjoint_write_class`, `loop_output_foot` |
| [`src/ChunkIndep.v`](src/ChunkIndep.v) | thread-count independence at the chunk level |
| [`src/Reduction.v`](src/Reduction.v) | C3 AC-reduction core |
| [`src/StepFraming.v`](src/StepFraming.v) | read-only `ev_step`/`ev_elim` leaves memory unchanged (C0 memory core) |
| [`src/DryStepFraming.v`](src/DryStepFraming.v) | C0 at the `dry_step` layer |
| [`src/OstepFraming.v`](src/OstepFraming.v) | C0 for one `Ostep` (all nine machine cases) |
| [`src/OstepRun.v`](src/OstepRun.v) | **C0 whole-run theorem** |
| [`src/Diamond.v`](src/Diamond.v) | disjoint `storebytes` commute up to `mem_equiv` (C1 memory core) |
| [`src/EvElimFrame.v`](src/EvElimFrame.v) | write-only trace frame + base-independence |
| [`src/StepDiamond.v`](src/StepDiamond.v) | **C1 observable diamond** |
| [`src/Confluence.v`](src/Confluence.v) | **C1 permutation-invariance theorem** (independence assumed) |
| [`src/HardenedConfluence.v`](src/HardenedConfluence.v) | **race-agnostic theorem**: independence (read off the traces) ⇒ schedule-independent, else explicit race witness |

## Axiom hygiene

Every headline theorem was checked with `Print Assumptions`:

- The pure memory-mathematics (`Diamond.v`, `EvElimFrame.v`, `StepDiamond.v`,
  `ChunkIndep.v`, `Reduction.v`, `ObsEquiv.v`, `ClassPredicates.v`,
  `StepFraming.v`) is **entirely axiom-free** ("Closed under the global context").
- Lemmas touching the machine's permission machinery (`DryStepFraming.v`,
  `OstepFraming.v`, `OstepRun.v`) inherit the standard CompCert/VST base axioms
  (classical logic, functional extensionality, `inline_external_call_mem_events`)
  transitively via `restrPermMap`.
- `Confluence.v` and `HardenedConfluence.v` additionally use classical logic
  (`classic`) only — for owner-uniqueness and for the totality of the
  independent-or-conflict disjunction. `schedule_independent_or_race` and
  `raw_run_permutation_agree` depend on `classic` and nothing else.

No `Admitted`, and no axioms introduced by this development.

## Building

These proofs use ClightOMP's logical path
`VST.concurrency.openmp_sem.sched_indep`, so they must be compiled inside a
built ClightOMP checkout.

1. **Get and build ClightOMP** (see its
   [README](https://github.com/dkxb/ClightOMP)). This development was checked
   against commit
   [`d2ebf1f`](https://github.com/dkxb/ClightOMP/commit/d2ebf1f1dbba2e47c3b922fe73c7d2b15ad0b3f1).
   In brief:
   ```sh
   git clone https://github.com/dkxb/ClightOMP
   cd ClightOMP
   git checkout d2ebf1f
   opam switch create ClightOMP ocaml-variants.4.14.1+options ocaml-option-flambda
   opam repo add coq-released https://coq.inria.fr/opam/released
   opam pin add builddep/
   git submodule update --init --recursive
   make _CoqProject
   make -j concurrency/openmp_sem/HybridMachine.vo
   ```
   Requires Coq 8.19.0 and coq-compcert (pulled in by the build-dep pin).

2. **Build these proofs**, pointing the driver at your ClightOMP checkout:
   ```sh
   ./build.sh /path/to/ClightOMP
   ```
   The script copies `src/*.v` into `<ClightOMP>/sched_indep/` and compiles them
   in dependency order (it does not modify any upstream file). If you created the
   opam switch named `ClightOMP` above, it is used automatically; otherwise
   `coqc` on your `PATH` is used.

3. **Check the axioms** of a headline theorem, e.g.:
   ```sh
   cd /path/to/ClightOMP
   echo 'From VST.concurrency.openmp_sem.sched_indep Require Import Confluence.
   Print Assumptions run_permutation_agree.' > /tmp/chk.v
   opam exec --switch=ClightOMP -- coqc $(cat _CoqProject) \
     -Q sched_indep VST.concurrency.openmp_sem.sched_indep /tmp/chk.v
   ```
