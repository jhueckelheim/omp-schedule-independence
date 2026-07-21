# Plan: Extending the 1:1 DRF Oracle to Sequentially-Consistent Atomics

Status: **plan only** — no proof code written yet. This documents the design
agreed for extending `src/DRF.v` to allow sequentially-consistent (SC) atomic
accesses to shared locations, in a **separate file** `src/DRFAtomic.v` (to be
merged into `DRF.v` later if successful), using a **per-iteration atomic location
set** to mark which accesses are atomic.

## The claim to be proved

Same shape as the existing oracle, but with an atomics-aware notion of *data
race*: if a `parallel for` is **data-race-free under the 1:1 schedule** (iteration
`i` on thread `i`, `num_threads = trip_count`), then it is **data-race-free under
every schedule**, even when iterations perform SC atomic accesses to shared
locations.

Why the oracle argument survives atomics: the load-bearing fact is purely
combinatorial and schedule-independent — the set of accesses each iteration
performs (and which of them are atomic) is a fixed function of the iteration
index; a data race under any schedule requires two iterations on *different*
threads; and the 1:1 schedule puts every pair on different threads, so it exposes
every potentially-racing pair. Running each iteration on its own thread only adds
behaviours; it never hides a data race. Atomics change only *which* conflicting
pairs count as data races, not this concurrency structure.

## What changes vs. `DRF.v`: the definition of "race"

The current model treats every access identically: `conflict2 T1 T2` holds when
the two traces touch a common location with at least one write. Under the C/C++/
OpenMP memory model a **data race** is more specific: two conflicting accesses,
unordered by happens-before, **at least one of which is non-atomic**. Two atomic
accesses to the same location are *not* a data race — the program still has
defined (nondeterministic) SC behaviour.

So the single change is: **an overlap counts as a data race only if at least one
of the two conflicting accesses is non-atomic.** Atomic/atomic overlaps are
excluded.

## Model (per-iteration atomic location set)

`mem_event` has no atomic marker, so we add an abstraction *on top of* the trace
model rather than reading it from ClightOMP's native semantics.

- An **annotated iteration** is a pair `(T, A)` where
  - `T : list mem_event` is the iteration's memory-event trace (as today), and
  - `A : block -> Z -> Prop` marks the locations this iteration accesses
    **atomically**.
- A `parallel for` is a `list (list mem_event * (block -> Z -> Prop))`.
- Well-formedness we assume (documented, matches the instrumentation): `A` marks
  only locations the trace actually touches, and a location an iteration touches
  is accessed *either* always-atomically *or* always-non-atomically within that
  iteration (no mixing at the same location in one iteration). This keeps
  "non-atomic access to `(b,ofs)`" well-defined as `accesses ∧ ¬A`.

### Access/data-conflict definitions

Reusing `writes`, `reads`, `conflict2` from `HardenedConfluence.v`:

- `accesses T b ofs := reads T b ofs \/ writes T b ofs`.
- `data_conflict2 (T1,A1) (T2,A2)` := there exist `b, ofs` such that
  - `conflict2 T1 T2` witnessed at `(b,ofs)` (a real read/write or write/write
    overlap), **and**
  - at least one side is non-atomic there: `¬ A1 b ofs \/ ¬ A2 b ofs`.

  Concretely, the three `conflict2` disjuncts, each additionally requiring the
  non-atomic side condition on the location.
- `data_race_free sched Ts := forall i j (concurrent), ~ data_conflict2 (its i) (its j)`.

## Theorems to prove (mirror `DRF.v`, with `data_conflict2`)

1. `data_indep_or_conflict2` — totality: for any two annotated iterations, either
   no data conflict, or a witnessed one. (Classical, as `indep_or_conflict2`.)
2. `list_data_conflict` and `data_indep_or_conflict` — the list-level analogues.
3. `drf_S1_iff_no_data_conflict` — the 1:1 schedule is data-race-free iff no pair
   has a `data_conflict2` (S1 makes every pair concurrent).
4. `no_data_conflict_all_drf` — no data-conflicting pair ⇒ every schedule DRF.
5. **`drf_S1_implies_all_drf_atomic`** (headline) — DRF under S1 ⇒ DRF under every
   schedule, for annotated iterations.
6. `drf_S1_iff_all_drf_atomic` — S1 is a sound and complete oracle.

The proofs are the existing `DRF.v` proofs with `conflict2 → data_conflict2`; the
concurrency/combinatorial skeleton is unchanged, so risk is low.

## Consistency lemmas (show it is a proper generalization)

- **Subsumption:** if every iteration's atomic set is empty (`A i = ∅` for all
  `i`), then `data_conflict2` = `conflict2` and the atomic theorems reduce to the
  existing `DRF.v` theorems. This proves the new result strictly generalizes the
  old one (justifying a later merge).
- **Atomics are exempt:** if every conflicting witness location is atomic on both
  sides, `data_conflict2` is false — the concrete statement that atomic/atomic
  overlaps are not data races.

## Explicit scope and honesty notes (to go in the file header + README)

- **This is over an atomic-annotated abstraction of the trace model, not
  ClightOMP's native semantics.** `mem_event` has no atomic events, and ClightOMP
  does not model atomics in the loop body; the annotation `A` is supplied
  (e.g. by the instrumentation in `DYNAMIC_ASSERTIONS.md`), exactly as the
  read/write footprints are. State this plainly.
- **DRF preservation, not result determinism.** SC atomics are a *sanctioned* way
  to be data-race-free yet **schedule-dependent in outcome** (e.g.
  `atomic { out[k++] = i; }`). So:
  - the DRF oracle **extends** to SC atomics (this plan), but
  - the schedule-independence result (`class_schedule_independent`) does **not**
    extend to atomics and must not be claimed to. This is consistent with the
    existing README note that synchronization is outside schedule-independence.
- **Fragment unchanged otherwise:** still no per-thread state carried across
  iterations, no thread-id dependence; footprints (and now the atomic annotation)
  are fixed functions of the iteration index. Per-thread state would still let S1
  hide races and remains excluded.

## Deliverables

1. `src/DRFAtomic.v` — the model, `data_conflict2`, the six theorems, and the two
   consistency lemmas. Compiles inside the ClightOMP checkout; `Print Assumptions`
   expected to be `classic`-only (as `DRF.v`).
2. `build.sh` — add `DRFAtomic` after `DRF`.
3. Docs — a short subsection in `README.md` (DRF oracle now covers SC atomics,
   with the "not result-determinism" caveat) and a note in `DYNAMIC_ASSERTIONS.md`
   that the instrumentation records an atomic flag per access and the data-race
   check ignores atomic/atomic overlaps.

## Non-goals

- No change to `class_schedule_independent` / the schedule-independence results.
- No attempt to model weaker-than-SC atomics (relaxed/acquire-release); the
  argument here relies on SC, where "data race" is the standard
  non-atomic-conflict notion and atomic/atomic conflicts have defined behaviour.
- No claim that the atomic annotation is derived from ClightOMP; it is an
  abstraction layered on the trace model.
