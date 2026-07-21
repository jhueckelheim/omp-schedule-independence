# Expressing the Class Prerequisites as In-Body Assertions

This note outlines how to turn the abstract preconditions of our two results —
**schedule-independence** (`class_schedule_independent` in `src/SourceToTrace.v`)
and the **1:1 data-race-freedom oracle** (`src/DRF.v`) — into concrete assertions
that can be added to the body of an OpenMP `parallel for`, using only expressions
a program can compute at runtime (observed addresses, iteration indices, and a
small amount of side state). The goal is a *dynamic checker*: run the loop with
the assertions enabled; if none fire, the loop provably satisfies the class
prerequisite for that execution, so the proved guarantees apply.

This is deliberately a *runtime* reduction. It does not attempt static inference
of footprints; it records the accesses the loop actually performs and checks the
class condition against them. That matches the proofs exactly, because both
proofs read footprints off the *actual* memory-event traces.

## What the proofs actually require

Both classes are conditions on each iteration's **read set** `R(i)` and **write
set** `W(i)` — the sets of `(block, offset)` locations iteration `i` reads and
writes. From the Coq development:

- **Schedule-independence (C1 / `disjoint_write_class` at trace footprints).**
  For all distinct iterations `i ≠ j`:
  - `W(i) ∩ W(j) = ∅`  (no two iterations write the same location), and
  - `R(i) ∩ W(j) = ∅`  (no iteration reads what another writes).

  Overlapping reads are allowed. Additional structural conditions from the proof:
  no synchronization or external calls in the body (locks/atomics/`critical` are
  out of scope), and the observed guarantee is over pre-existing memory.

- **1:1 DRF oracle (`drf_S1_*`).** The *same* pairwise condition, viewed as "no
  conflicting pair," is what makes the 1:1 schedule data-race-free and hence a
  sound oracle. `drf_S1_iff_traces_indep` proves the two conditions coincide, so
  **one instrumentation checks both.** The oracle additionally requires the
  no-per-thread-state condition (below), which the schedule-independence result
  gets for free from reading real footprints.

So the whole prerequisite reduces to: **record `R(i)` and `W(i)` per iteration,
and check the two pairwise-disjointness conditions.** Everything below is a way to
do that with computable expressions.

## Which assertions each class needs

It helps to separate the abstract **precondition** (what must be true) from the
**assertion you actually add** (what you write or enable to check it). Both classes
share the footprint-disjointness *precondition*, but they check it by different
means, and for the DRF oracle it costs no added assertion at all.

| Precondition | Schedule-independence — what you add | 1:1 DRF oracle — what you add |
|---|---|---|
| Footprint disjointness (`W(i)∩W(j)=∅`, `R(i)∩W(j)=∅`) | **Option A** shadow-map assertions | **nothing extra** — the disjointness check *is* the 1:1 race-detector run (Option B); an overlapping write shows up as a reported data race |
| No sync / no thread-id / no external calls | **#1** syntactic scan | **#1** syntactic scan |
| Write-before-read for privates | not needed (private accesses are already in `R(i)`/`W(i)`, so a hazardous private surfaces as a conflict in Option A) | **#2** per-iteration init flag (otherwise the 1:1 schedule *hides* per-thread-state races) |
| Fixed trip count | not assumed by the statement | **#3** (the 1:1 mapping `num_threads = trip_count` must be well-defined) |

The key point about the oracle: **footprint disjointness is a precondition of the
oracle, but it is not a separate assertion you write.** Running at
`num_threads = trip_count` under a data-race detector (Option B) makes every pair
of iterations concurrent, so any write/write or read/write overlap is, by
definition, a reported data race — that report *is* the disjointness check.
(Read/read overlap is not a race and is correctly not reported, matching the
Bernstein condition that overlapping reads are allowed.) Option A is the
*alternative* way to check the same disjointness precondition when you are not
using a detector — it is the route for schedule-independence, and it is also
available for the oracle if you prefer explicit assertions over a sanitizer.

So, concretely:

- **Schedule-independence:** add **Option A** assertions + the **#1** scan.
- **1:1 DRF oracle:** run under a data-race detector with `num_threads = trip
  count` (**Option B**, which needs no added disjointness assertion) + the **#1**
  scan + the **#2** write-before-read check + the **#3** fixed-trip-count check.
  (If you cannot use a detector, substitute Option A for the disjointness part.)

## The instrumentation primitives

Introduce two macros the programmer places at each shared memory access in the
loop body. They take the accessed lvalue and record its address range against the
current iteration index `i`.

```c
#define OMP_SI_READ(lval)   omp_si_note(/*is_write=*/0, i, &(lval), sizeof(lval))
#define OMP_SI_WRITE(lval)  omp_si_note(/*is_write=*/1, i, &(lval), sizeof(lval))
```

`omp_si_note(is_write, i, addr, size)` records that iteration `i` accessed the
byte range `[addr, addr+size)` for read or write. The only expressions used are
`&lval`, `sizeof lval`, and the loop index `i` — all known or trivially
computable at the access site.

A write is then written as `OMP_SI_WRITE(a[i]); a[i] = expr;` and a read as
`OMP_SI_READ(a[k]); use(a[k]);`. (A source-to-source pass, or a compiler plugin,
can insert these automatically; by hand they go at each access.)

## Checking the disjointness conditions  — *a precondition of BOTH classes*

The pairwise conditions `W(i) ∩ W(j) = ∅` and `R(i) ∩ W(j) = ∅` are exactly the
Bernstein independence conditions, and are a precondition of both classes. There
are two ways to check them; **you need only one**. For the 1:1 DRF oracle, Option
B is the natural choice and adds *no* explicit assertion (the race detector is the
check); for schedule-independence, use Option A.

### Option A — global "owner" map, explicit assertions (used for schedule-independence)

Keep two arrays indexed by byte address (conceptually; in practice a hash map):
`writer[addr]` = the iteration that last wrote `addr`, and check on every access.

```c
// on WRITE of byte range by iteration i:
for (b in range) {
  assert(writer[b] == NONE || writer[b] == i);   // no other iteration wrote b  -> W(i)∩W(j)=∅
  assert(reader[b] == NONE || reader[b] == i);    // no other iteration read b   -> R(j)∩W(i)=∅
  writer[b] = i;
}
// on READ of byte range by iteration i:
for (b in range) {
  assert(writer[b] == NONE || writer[b] == i);    // no other iteration wrote b  -> R(i)∩W(j)=∅
  reader[b] = i;   // record; multiple readers allowed
}
```

The `assert`s use only: the byte address `b` (computable from `&lval`), the
current index `i`, and the recorded owner. If every assertion holds for the run,
the loop satisfies the class prerequisite for that input. A firing assertion
prints the conflicting `(i, j, address)` — exactly the `list_conflict` witness the
race-agnostic theorem produces.

Note the checker itself must be race-free; `writer`/`reader` updates need atomic
compare-and-set, OR the loop is run **sequentially in index order** purely for
checking (which is sound: it observes the same per-iteration footprints, since the
class forbids the schedule from changing them).

### Option B — 1:1 run under a data-race detector, no added assertion (the DRF oracle)

`src/DRF.v` says the 1:1 schedule exposes every pair as concurrent, so a
thread-sanitizer-style race detector run under "one iteration per thread" reports
a race **iff** the loop is outside the class. Concretely: compile the loop so that
`num_threads == trip_count` (the 1:1 mapping), run under a data-race detector
(e.g. ThreadSanitizer / Archer), and treat "no race reported" as the certificate.
`drf_S1_implies_all_drf` is the theorem that makes this single run conclusive for
all schedules. Here the "assertion" is the sanitizer's shadow-memory check, and
the only computed expressions are, again, the accessed addresses. Option B needs
no source edits but requires the 1:1 thread count to be realisable.

## The extra conditions, as assertions

Beyond footprint disjointness, a few structural prerequisites must also hold. Each
is tagged with the class(es) that need it.

1. **No cross-iteration synchronization / no thread-id dependence.**
   *— required by BOTH classes.* Assert the loop body calls none of
   `omp_get_thread_num`, `omp_get_num_threads`, lock acquire/release,
   `#pragma omp atomic/critical/ordered/barrier`. This is a *syntactic* side
   condition, checkable by a one-pass scan of the body rather than a runtime
   assertion; include it as a documented precondition and, if desired, a
   compile-time check (`static_assert`-style or a linter rule).

2. **No per-thread state carried across iterations.**
   *— required by the 1:1 DRF oracle only; NOT needed for schedule-independence.*
   A private variable is safe only if it is *written before read* in each
   iteration. This is checkable in-body with a per-iteration "initialized" shadow
   flag:

   ```c
   // at entry to each iteration, mark all such privates uninitialized:
   int p_init = 0;
   #define P_WRITE(p)  do { (p); p_init = 1; } while (0)
   #define P_READ(p)   ( assert(p_init), (p) )   // read-before-write -> assertion fires
   ```

   If `P_READ` ever fires, the private is read before written in some iteration —
   the per-thread-counter hazard — and the loop is outside the DRF-oracle class.
   (`firstprivate` is exempt: it is initialised deterministically from the shared
   original, so treat it as pre-initialised.)

3. **Fixed trip count.**
   *— required by the 1:1 DRF oracle only; not assumed by the schedule-independence
   statement.* For the 1:1 mapping to be well-defined the iteration count must not
   depend on the schedule; assert the loop bound is evaluated once before the
   region (`const int n = ...;` with `n` not written in the body).

## Soundness of the reduction

The assertions are sound with respect to the proofs because both proofs are
stated over the *observed* per-iteration footprints:

- If a checking run (sequential-in-index for Option A, or 1:1 for Option B)
  passes all assertions, then the recorded `R(i)`, `W(i)` satisfy
  `disjoint_write_class` at the trace-derived footprints, which is exactly the
  hypothesis of `class_schedule_independent`; and equivalently no `conflict2`
  holds, which is the hypothesis of `drf_S1_implies_all_drf`.
- The reduction is *per input*: passing on one input certifies the class only for
  that input's footprints. To certify all inputs one still needs the loop's
  footprints to be input-independent (or a proof/argument covering all inputs);
  the assertions give a strong, cheap dynamic guarantee and a precise witness on
  failure.

## Caveats and limits

- **Input coverage.** Dynamic checks certify the observed run only. They are a
  testing/monitoring tool, not a static proof, unless combined with an argument
  that footprints are input-independent.
- **Checker overhead and its own races.** Option A's shadow maps must be updated
  race-free (atomics, or a dedicated sequential checking pass). Option B inherits
  the race detector's overhead and the requirement that `num_threads == trip
  count` is achievable.
- **What cannot be reduced to an in-body assertion.** The "no synchronization /
  no external calls" condition is about *absence* of constructs, so it is a
  syntactic side condition rather than a value assertion. Likewise, `lastprivate`
  and `omp_get_thread_num` are simply disallowed (they are outside the modelled
  fragment); a scan should reject them.

## Example (from `examples/schedule_independent_loop.c`)

```c
const int n = 100;                 // fixed trip count (condition 3)
int output_array[100];

#pragma omp parallel for
for (int i = 0; i < n; i++) {
    // pure_function has no shared reads/writes and no synchronization (conditions 1,2)
    OMP_SI_WRITE(output_array[i]);       // records W(i) = { &output_array[i] }
    output_array[i] = pure_function(i);
}
```

Here `W(i) = {&output_array[i]}` are pairwise disjoint and `R(i)` is empty, so the
Option-A assertions never fire and the loop is certified in-body for this run —
matching the machine-checked result that this loop is schedule-independent.
