(* Schedule-independence development: SOURCE-PREDICATE-TO-TRACE SOUNDNESS BRIDGE.

   The abstract class predicate `disjoint_write_class` (ClassPredicates.v) is
   parameterised by user-supplied per-iteration footprints `write_foot`/`read_foot`.
   That is unsound if a user under-approximates -- e.g. omits an iteration's read
   of a per-thread PRIVATE variable (a counter), which would let a genuinely
   schedule-dependent program spuriously satisfy the predicate.

   This file closes that gap. It defines the per-iteration footprints DIRECTLY
   from the actual execution traces (so nothing -- no private read or write -- can
   be forgotten), and proves:

     1. (soundness bridge) `disjoint_write_class` at the TRACE-DERIVED footprints
        is EQUIVALENT to trace-level independence `traces_indep`
        (class_eq_traces_indep). Hence the abstract predicate, when its footprints
        are the real ones, cannot be satisfied by a program with any cross-
        iteration conflict, private accesses included.

     2. (payoff) if `disjoint_write_class` holds at the trace-derived footprints
        for a write-only trace list, then ANY two schedules (permutations) agree
        on observable memory (class_schedule_independent). This connects the
        source-level class predicate to the schedule-independence guarantee, with
        private accesses automatically counted.

     3. (the counter is rejected) a trace list in which two distinct iterations
        both touch a common (private) block does NOT satisfy the trace-derived
        `disjoint_write_class` (private_counter_not_in_class).

   Build (inside a built ClightOMP checkout):
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/SourceToTrace.v
*)

Require Import ZArith.
Require Import List.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import Coq.Sorting.Permutation.
Require Import VST.concurrency.openmp_sem.event_semantics.
Require Import VST.concurrency.openmp_sem.sched_indep.ObsEquiv.
Require Import VST.concurrency.openmp_sem.sched_indep.ClassPredicates.
Require Import VST.concurrency.openmp_sem.sched_indep.EvElimFrame.
Require Import VST.concurrency.openmp_sem.sched_indep.HardenedConfluence.

Open Scope Z_scope.

Section SourceToTrace.

  Variable Ts : list (list mem_event).

  (* The iteration index set: positions of the trace list, as integers. *)
  Definition trace_iters : Z -> Prop :=
    fun z => 0 <= z < Z.of_nat (length Ts).

  (* trace at integer index z (nil outside range). *)
  Definition trace_at (z : Z) : list mem_event :=
    nth (Z.to_nat z) Ts nil.

  (* Per-iteration footprints READ OFF THE ACTUAL TRACE. Nothing is omitted:
     every Read/Write event of iteration z contributes. Private reads and writes
     are included automatically because they are events like any other. *)
  Definition trace_write_foot (z : Z) : footprint :=
    fun b ofs => writes (trace_at z) b ofs.
  Definition trace_read_foot (z : Z) : footprint :=
    fun b ofs => reads (trace_at z) b ofs.

  (* Helper: nth (Z.to_nat z) with the range hypothesis matches nth_error. *)
  Lemma trace_at_nth_error :
    forall z, trace_iters z ->
      nth_error Ts (Z.to_nat z) = Some (trace_at z).
  Proof.
    intros z [Hlo Hhi]. unfold trace_at.
    apply nth_error_nth'.
    apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia.
  Qed.

  (* Distinct integer indices in range map to distinct nat positions. *)
  Lemma trace_iters_distinct_nat :
    forall i j, trace_iters i -> trace_iters j -> i <> j ->
      Z.to_nat i <> Z.to_nat j.
  Proof.
    intros i j [Hi1 _] [Hj1 _] Hne Heq.
    apply Hne. rewrite <- (Z2Nat.id i) by lia. rewrite <- (Z2Nat.id j) by lia.
    rewrite Heq. reflexivity.
  Qed.

  (* ---- 1. SOUNDNESS BRIDGE ---------------------------------------------- *)

  (* disjoint_write_class at the trace-derived footprints IS trace independence. *)
  Theorem class_eq_traces_indep :
    disjoint_write_class trace_iters trace_write_foot trace_read_foot
    <-> traces_indep Ts.
  Proof.
    split.
    - (* class -> traces_indep *)
      intros [Hww Hrw] i j Hij Ti Tj Hi Hj.
      (* i, j are nat positions; lift to integer indices Z.of_nat *)
      set (zi := Z.of_nat i). set (zj := Z.of_nat j).
      assert (Hzi : trace_iters zi).
      { unfold trace_iters, zi. split; [ lia |].
        apply Nat2Z.inj_lt. apply nth_error_Some. rewrite Hi. discriminate. }
      assert (Hzj : trace_iters zj).
      { unfold trace_iters, zj. split; [ lia |].
        apply Nat2Z.inj_lt. apply nth_error_Some. rewrite Hj. discriminate. }
      assert (Hzne : zi <> zj) by (unfold zi, zj; lia).
      assert (HTi : trace_at zi = Ti).
      { unfold trace_at, zi. rewrite Nat2Z.id. apply nth_error_nth with (d:=nil). exact Hi. }
      assert (HTj : trace_at zj = Tj).
      { unfold trace_at, zj. rewrite Nat2Z.id. apply nth_error_nth with (d:=nil). exact Hj. }
      (* assemble traces_indep2 Ti Tj from the class fields *)
      unfold traces_indep2. repeat split.
      + (* w/w *) intros b ofs Hw1 Hw2.
        eapply (Hww zi zj Hzi Hzj Hzne b ofs);
          unfold trace_write_foot; [ rewrite HTi; exact Hw1 | rewrite HTj; exact Hw2 ].
      + (* reads Ti / writes Tj *) intros b ofs Hr1 Hw2.
        eapply (Hrw zi zj Hzi Hzj Hzne b ofs);
          [ unfold trace_read_foot; rewrite HTi; exact Hr1
          | unfold trace_write_foot; rewrite HTj; exact Hw2 ].
      + (* reads Tj / writes Ti *) intros b ofs Hr2 Hw1.
        eapply (Hrw zj zi Hzj Hzi (not_eq_sym Hzne) b ofs);
          [ unfold trace_read_foot; rewrite HTj; exact Hr2
          | unfold trace_write_foot; rewrite HTi; exact Hw1 ].
    - (* traces_indep -> class *)
      intros Hindep. constructor.
      + (* dw_write_disjoint *)
        intros i j Hi Hj Hne b ofs Hwi Hwj.
        pose proof (trace_at_nth_error i Hi) as Hei.
        pose proof (trace_at_nth_error j Hj) as Hej.
        pose proof (trace_iters_distinct_nat i j Hi Hj Hne) as Hnn.
        destruct (Hindep (Z.to_nat i) (Z.to_nat j) Hnn _ _ Hei Hej)
          as [Hww [_ _]].
        eapply Hww; [ exact Hwi | exact Hwj ].
      + (* dw_read_write_disjoint *)
        intros i j Hi Hj Hne b ofs Hri Hwj.
        pose proof (trace_at_nth_error i Hi) as Hei.
        pose proof (trace_at_nth_error j Hj) as Hej.
        pose proof (trace_iters_distinct_nat i j Hi Hj Hne) as Hnn.
        destruct (Hindep (Z.to_nat i) (Z.to_nat j) Hnn _ _ Hei Hej)
          as [_ [Hrw _]].
        eapply Hrw; [ exact Hri | exact Hwj ].
  Qed.

End SourceToTrace.

Section Payoff.

  (* ---- 2. PAYOFF: source class predicate ==> schedule-independence ------- *)

  (* If the disjoint-write class holds at the ACTUAL trace footprints (so no
     private access is forgotten) for a write-only trace list, then any two
     schedules (permutations) agree on observable memory. *)
  Theorem class_schedule_independent :
    forall Ts Ts' m m1 m2,
      disjoint_write_class (trace_iters Ts)
                           (trace_write_foot Ts) (trace_read_foot Ts) ->
      all_wr_only Ts ->
      Permutation Ts Ts' ->
      raw_run Ts m m1 ->
      raw_run Ts' m m2 ->
      forall b ofs,
        ZMap.get ofs (Mem.mem_contents m1) !! b =
        ZMap.get ofs (Mem.mem_contents m2) !! b.
  Proof.
    intros Ts Ts' m m1 m2 Hclass Hwr Hperm Hrun1 Hrun2 b ofs.
    apply (class_eq_traces_indep Ts) in Hclass.
    eapply raw_run_permutation_agree; eauto.
  Qed.

End Payoff.

Section CounterRejected.

  (* ---- 3. THE PER-THREAD COUNTER IS REJECTED ---------------------------- *)

  (* If two DISTINCT iterations both write a common block/offset -- as a per-thread
     private counter does across a thread's iterations (each iteration writes the
     counter block) -- then the trace-derived disjoint_write_class does NOT hold.
     So the counter program cannot spuriously satisfy the (sound) predicate. *)
  Theorem private_counter_not_in_class :
    forall Ts i j b ofs,
      trace_iters Ts i -> trace_iters Ts j -> i <> j ->
      trace_write_foot Ts i b ofs ->
      trace_write_foot Ts j b ofs ->
      ~ disjoint_write_class (trace_iters Ts)
                             (trace_write_foot Ts) (trace_read_foot Ts).
  Proof.
    intros Ts i j b ofs Hi Hj Hne Hwi Hwj [Hww _].
    eapply (Hww i j Hi Hj Hne b ofs Hwi Hwj).
  Qed.

  (* The same for a read/write clash: iteration i reads what iteration j writes
     (the counter is read by later iterations). Also rejected. *)
  Theorem read_after_write_not_in_class :
    forall Ts i j b ofs,
      trace_iters Ts i -> trace_iters Ts j -> i <> j ->
      trace_read_foot Ts i b ofs ->
      trace_write_foot Ts j b ofs ->
      ~ disjoint_write_class (trace_iters Ts)
                             (trace_write_foot Ts) (trace_read_foot Ts).
  Proof.
    intros Ts i j b ofs Hi Hj Hne Hri Hwj [_ Hrw].
    eapply (Hrw i j Hi Hj Hne b ofs Hri Hwj).
  Qed.

End CounterRejected.
