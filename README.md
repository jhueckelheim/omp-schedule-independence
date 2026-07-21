# Machine-Checked Schedule-Independence for OpenMP `parallel for`

This repository contains Coq proofs that an OpenMP `parallel for` loop produces
the **same result no matter which schedule the runtime picks or how many threads
it uses**, provided the loop's iterations are independent. The proofs are
machine-checked against the [ClightOMP](https://github.com/dkxb/ClightOMP) formal
semantics of C-with-OpenMP (a fork of
[VST](https://github.com/PrincetonUniversity/VST) / CompCert), and every headline
theorem has been checked with `Print Assumptions`: there are no `Admitted`s and no
axioms beyond classical logic.

## What is proved

For a `parallel for` whose iterations are **independent** (precise conditions
below), any two executions that differ only in the schedule and thread count
leave **identical bytes in every pre-existing memory location** — in particular,
in the loop's output. Two forms of the result are proved:

- **Independence assumed** (`class_schedule_independent`,
  [`src/SourceToTrace.v`](src/SourceToTrace.v)): if the iterations satisfy the
  independence condition, all schedules agree on the observable memory.

- **Race-agnostic** (`schedule_independent_or_race`,
  [`src/HardenedConfluence.v`](src/HardenedConfluence.v)): for an *arbitrary*
  loop — independent or not — **either** all schedules agree, **or** the program
  exhibits an explicit conflicting pair of iterations (a witnessed data race).
  The independence condition is read off the actual execution, not assumed, so
  the guarantee is never claimed for a racy program.

Two further results support the general case:

- **Pure loops** (`pure_run_obs_equiv`, [`src/OstepRun.v`](src/OstepRun.v)): a
  loop whose body performs no shared writes is schedule-independent, proved
  end-to-end on the real ClightOMP machine step relation.

- **Reductions** (`reduce_workloads_thread_count_independent`,
  [`src/Reduction.v`](src/Reduction.v)): a reduction with an associative and
  commutative combiner is invariant under the thread count and work split.

The independence condition is stated over the loop's **actual memory accesses**,
so it automatically accounts for every read and write — including those of
per-thread private variables. This is what makes it sound: a program that looks
independent at the source level but secretly depends on the schedule (for
example, a private per-thread iteration counter written into the output) is
correctly rejected, not certified.

### Data-race-freedom of the 1:1 schedule as an oracle

A separate, complementary result ([`src/DRF.v`](src/DRF.v)) is about *preserving
data-race-freedom* across schedules rather than about results. Model a schedule as
an assignment of iterations to threads; two distinct iterations may race only if
they are placed on different threads and their traces conflict. The
**maximally-parallel schedule `S1`** maps iteration `i` to thread `i` (as many
threads as iterations, 1:1), so it makes *every* pair of iterations concurrent.

- `drf_S1_implies_all_drf` — if the loop is data-race-free under `S1`, it is
  data-race-free under **every** schedule and thread count. So the single 1:1
  schedule is a sound oracle for data-race-freedom.
- `drf_S1_iff_no_conflict` — `S1` is data-race-free exactly when no pair of
  iterations conflicts, and `drf_S1_iff_traces_indep` — this coincides with the
  independence condition above.

This holds in the same fragment (fixed per-iteration footprints: no
synchronization, no per-thread state carried across iterations). It is **not** a
sound oracle outside that fragment — for a program with per-thread state (a
private counter, `threadprivate`, `lastprivate`), `S1` gives each iteration its
own thread and therefore *hides* exactly the races that reusing threads would
expose. Such constructs are outside the modelled fragment.

## Preconditions a loop must satisfy

A loop is certified schedule-independent when all of the following hold. They are
the exact hypotheses of `class_schedule_independent`.

1. **Independent iterations (Bernstein condition).** For any two distinct
   iterations:
   - they do not write the same location, and
   - neither reads a location the other writes.

   Iterations may freely read shared inputs in common (overlapping *reads* are
   fine). This condition is checked against every memory access the iteration
   actually performs, private variables included.

2. **No synchronization or external calls in the body.** The loop body may read
   and write memory and call known (non-external) functions — including functions
   that allocate and free local/stack memory, and pure functions with scratch
   buffers. It may **not** use locks, atomics, `critical`/`atomic` regions, or
   calls to external functions. Such constructs are exactly what allows
   schedule-dependent-yet-race-free behaviour, so they are out of scope.

3. **A common starting memory.** The two schedules being compared start from the
   same initial memory.

4. **Observation on pre-existing memory.** The guarantee covers every location
   whose block is valid in the initial memory (e.g. the output array). Freshly
   allocated, iteration-local scratch memory is deliberately excluded from the
   comparison — its addresses may differ between runs and it is not observable
   after the loop.

Not modelled by the underlying semantics, and therefore outside every result:
`lastprivate`, `omp_get_thread_num` (thread-id–dependent behaviour), and explicit
`schedule(...)` clauses. The last is subsumed rather than lost: the semantics
treats the schedule as an arbitrary partition of iterations across threads, so
the theorems already range over every possible static, dynamic, or guided
schedule.

## Building and running the proofs

The proofs are stated against ClightOMP's logical namespace and must be compiled
inside a built ClightOMP checkout.

### 1. Build ClightOMP

Follow the [ClightOMP](https://github.com/dkxb/ClightOMP) instructions. This
development was checked against commit `d2ebf1f`. In brief:

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

This requires Coq 8.19.0 and coq-compcert (pulled in by the build-dep pin).

### 2. Build these proofs

Point the build script at your ClightOMP checkout:

```sh
./build.sh /path/to/ClightOMP
```

It copies `src/*.v` into `<ClightOMP>/sched_indep/` and compiles them in order,
without modifying any upstream file. If you named the opam switch `ClightOMP` as
above, it is used automatically; otherwise `coqc` on your `PATH` is used.

### 3. Inspect a result

To read a theorem and check its axiom footprint, from the ClightOMP root:

```sh
echo 'From VST.concurrency.openmp_sem.sched_indep Require Import SourceToTrace.
Check @class_schedule_independent.
Print Assumptions class_schedule_independent.' > /tmp/check.v
opam exec --switch=ClightOMP -- coqc $(cat _CoqProject) \
  -Q sched_indep VST.concurrency.openmp_sem.sched_indep /tmp/check.v
```

## Repository contents

```
src/           the Coq proof files
examples/      the motivating C example (out[i] = f(i))
docs/          design notes and the full class/boundary discussion
build.sh       build driver (takes a path to a built ClightOMP checkout)
```

The main theorems live in `src/SourceToTrace.v` (independence ⇒
schedule-independence) and `src/HardenedConfluence.v` (the race-agnostic form);
the remaining files provide the supporting memory-level reasoning.
