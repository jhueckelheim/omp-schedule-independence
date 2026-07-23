# Checking the Preconditions at Runtime

The preconditions of the two guarantees — **schedule-independence**
(`class_schedule_independent`, `src/SourceToTrace.v`) and the **1:1 data-race
oracle** (`src/DRF.v`, `src/DRFExtended.v`) — are conditions on each iteration's
memory footprint. Because both proofs read footprints off the *actual*
memory-event traces, the preconditions can be checked dynamically: run the loop
with the checks enabled; if nothing fires, the loop satisfies the precondition for
that execution and the corresponding guarantee applies.

This is a runtime check, not static inference. It certifies the observed run; see
*Coverage* below.

## The condition, in terms of footprints

Let `R(i)` and `W(i)` be the sets of `(block, offset)` locations iteration `i`
reads and writes. The core condition (the Bernstein independence condition) is,
for all distinct iterations `i ≠ j`:

- `W(i) ∩ W(j) = ∅`  — no two iterations write the same location, and
- `R(i) ∩ W(j) = ∅`  — no iteration reads a location another writes.

Overlapping reads are allowed. Both guarantees rest on this condition:
`class_schedule_independent` requires it directly, and `drf_S1_iff_traces_indep`
shows it is exactly "the 1:1 schedule has no conflicting pair," which is what makes
that schedule a sound data-race oracle.

## What is proved for the 1:1 oracle

The oracle proof has two independent parts:

- `drf_S1_implies_all_drf` (`src/DRF.v`): if the maximally parallel schedule
  `S1` has no read/write or write/write race, then no schedule has such a race.
  `S1` works because every distinct pair of iterations is concurrent there.
- `oracle_1to1_safe_implies_all_schedules_safe` (`src/PrivateOracle.v`): combine
  the shared-memory DRF oracle with a private-state check. If the 1:1 run has no
  uninitialized read of a privatized value, then every schedule is safe with
  respect to those private reads. For plain `private`, this check is equivalent
  to write-before-read (`all_private_oracle_is_write_before_read`). For
  `firstprivate`, it is vacuous at entry because the copy is already initialized
  (`firstprivate_needs_no_write_before_read_check`).

Therefore, to use the 1:1 oracle, the tool must establish both: no shared-memory
race in the 1:1 run, and no read of an uninitialized private copy in that same
run. The remaining assumptions below ensure that the trace checked by the oracle
is the trace covered by the theorem.

## Which checks each guarantee needs

| Precondition | Schedule-independence | 1:1 DRF oracle |
|---|---|---|
| Footprint disjointness (`W(i)∩W(j)=∅`, `R(i)∩W(j)=∅`) | Option A (shadow-map assertions) | Option B (1:1 run under a race detector) — no added assertion |
| No synchronization / thread-id / external calls | required (syntactic scan) | required (syntactic scan) |
| Uninitialized reads of uninitialized privates | not needed | required |
| Fixed trip count | not assumed | required |

- **Schedule-independence:** Option A + the syntactic scan.
- **1:1 DRF oracle:** Option B + the syntactic scan + the uninitialized-private-read check
  + the fixed-trip-count check. (Substitute Option A for Option B if a race
  detector is unavailable.)

For the 1:1 oracle, the tool responsibilities are:

1. **Static analysis:** reject synchronization, thread-id queries, unsupported
   external calls, `threadprivate`, and `lastprivate`.
2. **Static analysis or assertion:** ensure the trip count is fixed before the
   loop and not modified by the body.
3. **1:1 race run or shadow assertions:** establish shared footprint
   disjointness by checking that the 1:1 run has no non-exempt read/write or
   write/write races.
4. **Runtime assertion or definite-assignment analysis:** reject reads of
   uninitialized plain `private` copies. Seed `firstprivate` as initialized, so it
   requires no write-before-read assertion.

The disjointness precondition is shared, but the oracle needs no separate
disjointness *assertion*: under the 1:1 schedule every pair of iterations runs
concurrently, so any write/write or read/write overlap is a genuine data race that
a detector reports. That report is the disjointness check. (Read/read overlap is
not a race and is correctly not reported.) The uninitialized-private-read and
fixed-trip-count checks are needed only by the oracle: without the former the 1:1
schedule can otherwise *hide* schedule-dependent per-thread state (e.g. a
per-thread counter); without the latter the "one iteration per thread" mapping is
not well-defined. The check is required only for variables whose private copy is
not initialized on entry. `firstprivate` copies start initialized, so reads before
an iteration-local write are allowed for them.

## Recording footprints

Place two macros at each shared memory access. They record the accessed byte range
against the current iteration index, using only `&lval`, `sizeof lval`, and `i`.

```c
#define OMP_SI_READ(lval)   omp_si_note(/*is_write=*/0, i, &(lval), sizeof(lval))
#define OMP_SI_WRITE(lval)  omp_si_note(/*is_write=*/1, i, &(lval), sizeof(lval))
```

`omp_si_note(is_write, i, addr, size)` records that iteration `i` accessed
`[addr, addr+size)`. A write becomes `OMP_SI_WRITE(a[i]); a[i] = expr;`, a read
`OMP_SI_READ(a[k]); use(a[k]);`. A source-to-source pass or compiler plugin can
insert these automatically.

## Option A — explicit disjointness assertions

Maintain, per byte address, the iteration that last wrote it (`writer`) and read
it (`reader`) — a hash map in practice — and check on every access:

```c
// on WRITE of byte range by iteration i:
for (b in range) {
  assert(writer[b] == NONE || writer[b] == i);   // W(i)∩W(j)=∅
  assert(reader[b] == NONE || reader[b] == i);    // R(j)∩W(i)=∅
  writer[b] = i;
}
// on READ of byte range by iteration i:
for (b in range) {
  assert(writer[b] == NONE || writer[b] == i);    // R(i)∩W(j)=∅
  reader[b] = i;   // multiple readers allowed
}
```

A firing assertion prints the conflicting `(i, j, address)` — the same witness the
race-agnostic theorem `schedule_independent_or_race` produces (`list_conflict`).
The checker must itself be race-free: update the shadow maps with atomic
compare-and-set, or run the loop sequentially in index order purely for checking
(sound, since the precondition forbids the schedule from changing footprints).

## Option B — 1:1 run under a data-race detector

Compile so that `num_threads == trip_count` (iteration `i` on thread `i`) and run
under a data-race detector (e.g. ThreadSanitizer / Archer). `drf_S1_implies_all_drf`
makes this single run conclusive for all schedules: "no race reported" certifies
data-race-freedom under every schedule and thread count. The detector's
shadow-memory check *is* the disjointness check; no source edits are needed, but
the 1:1 thread count must be realisable.

## The other checks

- **No synchronization / thread-id / external calls.** The body must not call
  `omp_get_thread_num`, `omp_get_num_threads`, lock acquire/release, or use
  `#pragma omp atomic/critical/ordered/barrier`, and must not call external
  functions. This is about the *absence* of constructs, so it is a syntactic scan
  of the body (or a linter/compile-time rule), not a runtime assertion.

- **Uninitialized reads of uninitialized privates** (oracle only). A `private`
  variable is safe only if each read observes either the entry initialization or
  an earlier write in the same iteration. Plain `private` has no entry
  initialization, so this degenerates to write-before-read. Check with a
  per-iteration "initialized" flag seeded from the privatization kind:

  ```c
  int p_init = IS_FIRSTPRIVATE(p);
  #define P_WRITE(p)  do { (p); p_init = 1; } while (0)
  #define P_READ(p)   ( assert(p_init), (p) )   // read-before-write -> fires
  ```

  A firing `P_READ` means a non-initialized private copy is read before being
  written in that iteration. `firstprivate` is initialized deterministically from
  the original value before the loop body, so its flag starts true and no separate
  write-before-read assertion is needed for it. In Coq this is captured by
  `PrivateOracle.v`: `all_private_oracle_is_write_before_read` shows that for
  plain `private` the oracle check is exactly write-before-read, while
  `firstprivate_needs_no_write_before_read_check` shows initialized
  `firstprivate` needs no such check.

- **Fixed trip count** (oracle only). The iteration count must not depend on the
  schedule; ensure the loop bound is evaluated once before the region
  (`const int n = ...;`, with `n` not written in the body).

## Exempt locations (extended oracle)

`src/DRFExtended.v` lets the disjointness check ignore conflicts at declared
*exempt* locations, widening the accepted class while keeping the
"1:1 ⇒ all schedules" guarantee. Two exemptions are proved sound:

- **Reduction variables.** Locations updated only through an associative-
  commutative combiner (`sum += a[i]`, `atomicAdd(&h[k], 1)`) — their overlaps are
  not races because the reduced value is order-independent (`Reduction.v`). Do not
  instrument them; the check then flags only non-reduction conflicts.
- **Per-iteration scratch memory.** Memory allocated and freed inside one
  iteration lives at a fresh, iteration-private block and can never be a
  cross-iteration conflict (`fresh_drf_ex_sound`). Instrument only pre-existing
  shared memory.

With nothing exempted this is the plain check, so enabling exemptions only for
declared reductions and known iteration-local allocations is a safe default.

## Coverage

A passing run certifies the precondition for that input's footprints only. To
cover all inputs the footprints must be input-independent (or covered by a
separate argument). The checks are a dynamic guarantee with a precise witness on
failure, not a static proof.

## Example (`examples/schedule_independent_loop.c`)

```c
const int n = 100;                 // fixed trip count
int output_array[100];

#pragma omp parallel for
for (int i = 0; i < n; i++) {
    // pure_function: no shared reads/writes, no synchronization
    OMP_SI_WRITE(output_array[i]);       // W(i) = { &output_array[i] }
    output_array[i] = pure_function(i);
}
```

`W(i) = {&output_array[i]}` are pairwise disjoint and `R(i)` is empty, so the
Option-A assertions never fire and the loop is certified for this run — matching
the machine-checked result that it is schedule-independent.
