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

- **C1 — disjoint-write bodies** (iteration `i` writes only within footprint
  `W(i)`; the `W(i)` are pairwise disjoint; overlapping *reads* are allowed).
  `run_permutation_agree` ([`src/Confluence.v`](src/Confluence.v)) — modelling the
  loop as per-iteration write-only event traces confined to pairwise-disjoint
  footprints, **any two orders of the iterations (any permutation — i.e. any
  schedule / thread count) agree on the observable output**. This is the genuine
  "same result regardless of interleaving" theorem; its core is a
  commutation/diamond argument on memory writes.

- **C3 — associative-commutative reductions** (algebraic core).
  `reduce_workloads_thread_count_independent` ([`src/Reduction.v`](src/Reduction.v))
  — an AC reduction over the loop's chunks is invariant under the thread-count and
  work split, via the `ChunkSplit` permutation invariant.

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

- **Private variables are real per-thread copies.** Privatization allocates a
  **fresh memory block** per privatized identifier (`Mem.alloc`) and rewrites the
  thread's local environment, restoring/freeing at construct exit. `firstprivate`
  is a deterministic initializer. This justifies the disjointness assumptions of
  the C1/C2 classes.

Out of scope, by design: `lastprivate` and `omp_get_thread_num` are not modelled
by ClightOMP (so thread-id branching is not expressible in the verified fragment);
the classes forbid external calls to keep the axiomatized externals off the proof
path.

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
| [`src/Confluence.v`](src/Confluence.v) | **C1 permutation-invariance theorem** |

## Axiom hygiene

Every headline theorem was checked with `Print Assumptions`:

- The pure memory-mathematics (`Diamond.v`, `EvElimFrame.v`, `StepDiamond.v`,
  `ChunkIndep.v`, `Reduction.v`, `ObsEquiv.v`, `ClassPredicates.v`,
  `StepFraming.v`) is **entirely axiom-free** ("Closed under the global context").
- Lemmas touching the machine's permission machinery (`DryStepFraming.v`,
  `OstepFraming.v`, `OstepRun.v`) inherit the standard CompCert/VST base axioms
  (classical logic, functional extensionality, `inline_external_call_mem_events`)
  transitively via `restrPermMap`.
- `Confluence.v` additionally uses classical logic (`classic`) only for the
  owner-uniqueness argument.

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
