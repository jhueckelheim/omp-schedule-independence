(* The program-class predicate for schedule-independence.

   A loop's iterations are modelled by per-iteration read/write footprints.
   disjoint_write_class is the independence (Bernstein) condition: distinct
   iterations write disjoint locations, and no iteration reads a location another
   iteration writes. (Overlapping reads are allowed.) It is instantiated at the
   TRACE-DERIVED footprints in SourceToTrace.v, so it counts every actual memory
   access, private ones included.

   Build (from a built ClightOMP checkout):
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/ClassPredicates.v
*)

Require Import ZArith.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import VST.concurrency.openmp_sem.sched_indep.ObsEquiv.

Section ClassPredicates.

  (* Two footprints are disjoint. *)
  Definition foot_disjoint (f g: footprint) : Prop :=
    forall b ofs, f b ofs -> g b ofs -> False.

  (* Independence: distinct iterations write disjoint locations, and no iteration
     reads any location written by another iteration. *)
  Record disjoint_write_class
    (iters: Z -> Prop)                 (* the set of iteration indices *)
    (write_foot read_foot: Z -> footprint) : Prop :=
  { dw_write_disjoint :
      forall i j, iters i -> iters j -> i <> j ->
        foot_disjoint (write_foot i) (write_foot j);
    dw_read_write_disjoint :
      forall i j, iters i -> iters j -> i <> j ->
        foot_disjoint (read_foot i) (write_foot j) }.

End ClassPredicates.
