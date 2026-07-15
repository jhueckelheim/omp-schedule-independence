(* Schedule-independence development, step 10: dry_step frame + two-step diamond
   for the disjoint-write class C1.

   Combining:
     - DryStepFraming: dry_step output memory has the same CONTENTS as the input
       memory outside the thread's writes (contents only change where written);
     - EvElimFrame: a write-only ev_elim trace preserves contents outside its
       write-footprint;
     - Diamond: two storebytes/writes at disjoint locations commute.

   We prove the C1 DIAMOND at the observable level: if two thread steps have
   write-only traces with DISJOINT write footprints, then each step's effect is
   invisible on the other's footprint, and the observable output on the union of
   the two footprints is the same regardless of the order in which the two steps
   run. We phrase this via ev_elim (the memory-effect layer used inside dry_step).

   Build (upstream untouched), from the ClightOMP root:
     eval $(opam env --switch=ClightOMP)
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/StepDiamond.v
*)

Require Import ZArith.
Require Import List.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import VST.concurrency.openmp_sem.event_semantics.
Require Import VST.concurrency.openmp_sem.sched_indep.ObsEquiv.
Require Import VST.concurrency.openmp_sem.sched_indep.EvElimFrame.

Open Scope Z_scope.

Section StepDiamond.

  (* A footprint that a write-only trace is confined to: every Write event of the
     trace writes only within [foot]. Equivalently, any location outside [foot]
     is outside every write in the trace. *)
  Definition trace_writes_within (foot: footprint) (T: list mem_event) : Prop :=
    forall b ofs, ~ foot b ofs -> outside_trace b ofs T.

  (* If a trace writes within [foot], it preserves contents everywhere outside
     [foot]. This is the frame lemma specialised to a footprint. *)
  Lemma ev_elim_frame_footprint :
    forall (foot: footprint) T m m',
      wr_only_trace T ->
      trace_writes_within foot T ->
      ev_elim m T m' ->
      forall b ofs, ~ foot b ofs ->
        ZMap.get ofs (Mem.mem_contents m') !! b =
        ZMap.get ofs (Mem.mem_contents m) !! b.
  Proof.
    intros foot T m m' Hwr Hwithin Hev b ofs Hnot.
    eapply ev_elim_wr_frame; eauto.
  Qed.

  (* THE C1 DIAMOND (observable level).

     Two write-only traces T1, T2 with disjoint confinement footprints foot1,
     foot2. Running them in order (T1 then T2) gives m12; running them in the
     other order (T2 then T1) gives m21. Then m12 and m21 agree on the union
     foot1 ∪ foot2 -- the observable output is order-independent.

     Proof idea: on foot1, T2 is a frame (foot2 disjoint from foot1) so m12/m21
     both reflect only T1's effect on foot1, which is base-independent within the
     written range; symmetric on foot2. We reduce to per-location reasoning using
     the frame lemma and the fact that, within a trace's own footprint, its
     effect does not depend on locations the other trace touched (disjoint). *)
  Lemma ev_elim_diamond_obs :
    forall (foot1 foot2: footprint) T1 T2 m m12a m12 m21a m21,
      wr_only_trace T1 -> wr_only_trace T2 ->
      trace_writes_within foot1 T1 ->
      trace_writes_within foot2 T2 ->
      (forall b ofs, foot1 b ofs -> foot2 b ofs -> False) ->
      (* order A: T1 then T2 *)
      ev_elim m   T1 m12a -> ev_elim m12a T2 m12 ->
      (* order B: T2 then T1 *)
      ev_elim m   T2 m21a -> ev_elim m21a T1 m21 ->
      (* agreement on the union of footprints *)
      forall b ofs, (foot1 b ofs \/ foot2 b ofs) ->
        ZMap.get ofs (Mem.mem_contents m12) !! b =
        ZMap.get ofs (Mem.mem_contents m21) !! b.
  Proof.
    intros foot1 foot2 T1 T2 m m12a m12 m21a m21
           Hwr1 Hwr2 Hin1 Hin2 Hdisj HA1 HA2 HB1 HB2 b ofs Hunion.
    destruct Hunion as [Hf1 | Hf2].
    - (* (b,ofs) in foot1 (hence NOT in foot2, by disjointness) *)
      assert (Hnf2: ~ foot2 b ofs) by (intro; eapply Hdisj; eauto).
      (* order A: m -T1-> m12a -T2-> m12. On foot1, T2 is a frame, so
         m12 = m12a at (b,ofs). *)
      assert (E12: ZMap.get ofs (Mem.mem_contents m12) !! b =
                   ZMap.get ofs (Mem.mem_contents m12a) !! b)
        by (eapply ev_elim_frame_footprint; [ exact Hwr2 | exact Hin2 | exact HA2 | exact Hnf2 ]).
      (* order B: on foot1, T2 (the first step) is a frame, so m21a = m at
         (b,ofs). *)
      assert (E21a: ZMap.get ofs (Mem.mem_contents m21a) !! b =
                    ZMap.get ofs (Mem.mem_contents m) !! b)
        by (eapply ev_elim_frame_footprint; [ exact Hwr2 | exact Hin2 | exact HB1 | exact Hnf2 ]).
      (* Now both m12 and m21 at (b,ofs) reduce to T1's effect:
           m12 = m12a = (T1 on m) at (b,ofs)     [E12, then HA1]
           m21 = (T1 on m21a) at (b,ofs), and m21a = m on foot1 [E21a]
         Case on whether T1 actually writes (b,ofs). *)
      destruct (Exists_dec (written_by b ofs) T1) as [Hw1 | Hnw1].
      { intro x. destruct x as [bb oo bs | | |].
        - unfold written_by. destruct (peq b bb).
          + destruct (zle oo ofs).
            * destruct (zlt ofs (oo + Z.of_nat (length bs)));
                [ left; split; [congruence|lia] | right; intros [_ ?]; lia ].
            * right; intros [_ ?]; lia.
          + right; intros [? _]; congruence.
        - right; intros []. - right; intros []. - right; intros []. }
      + (* T1 writes (b,ofs): base-independence gives m12a = m21 at (b,ofs) *)
        rewrite E12.
        eapply (ev_elim_wr_within_base_indep T1 m m12a m21a m21 b ofs);
          [ exact Hwr1 | exact HA1 | exact HB2 | exact Hw1 ].
      + (* T1 does NOT write (b,ofs): T1 frames it in both runs *)
        assert (Hout1: outside_trace b ofs T1).
        { unfold outside_trace. apply Forall_forall. intros x Hx.
          destruct x as [bb oo bs | bb oo nn bs | | ]; simpl; auto.
          destruct (peq b bb) as [-> | Hbne]; [| left; exact Hbne].
          right.
          destruct (zlt ofs oo); [ left; lia |].
          destruct (zle (oo + Z.of_nat (length bs)) ofs); [ right; lia |].
          exfalso. apply Hnw1. apply Exists_exists. exists (Write bb oo bs).
          split; [ exact Hx |]. simpl. split; [ reflexivity | lia ]. }
        rewrite E12.
        rewrite (ev_elim_wr_frame T1 m m12a b ofs Hwr1 Hout1 HA1).
        rewrite (ev_elim_wr_frame T1 m21a m21 b ofs Hwr1 Hout1 HB2).
        symmetry. exact E21a.
    - (* symmetric: (b,ofs) in foot2, not in foot1 *)
      assert (Hnf1: ~ foot1 b ofs) by (intro; eapply Hdisj; eauto).
      assert (E21: ZMap.get ofs (Mem.mem_contents m21) !! b =
                   ZMap.get ofs (Mem.mem_contents m21a) !! b)
        by (eapply ev_elim_frame_footprint; [ exact Hwr1 | exact Hin1 | exact HB2 | exact Hnf1 ]).
      assert (E12a: ZMap.get ofs (Mem.mem_contents m12a) !! b =
                    ZMap.get ofs (Mem.mem_contents m) !! b)
        by (eapply ev_elim_frame_footprint; [ exact Hwr1 | exact Hin1 | exact HA1 | exact Hnf1 ]).
      destruct (Exists_dec (written_by b ofs) T2) as [Hw2 | Hnw2].
      { intro x. destruct x as [bb oo bs | | |].
        - unfold written_by. destruct (peq b bb).
          + destruct (zle oo ofs).
            * destruct (zlt ofs (oo + Z.of_nat (length bs)));
                [ left; split; [congruence|lia] | right; intros [_ ?]; lia ].
            * right; intros [_ ?]; lia.
          + right; intros [? _]; congruence.
        - right; intros []. - right; intros []. - right; intros []. }
      + (* T2 writes (b,ofs): base-independence, m21a = m12 at (b,ofs) *)
        rewrite E21.
        symmetry.
        eapply (ev_elim_wr_within_base_indep T2 m m21a m12a m12 b ofs);
          [ exact Hwr2 | exact HB1 | exact HA2 | exact Hw2 ].
      + (* T2 does not write (b,ofs): frame in both runs *)
        assert (Hout2: outside_trace b ofs T2).
        { unfold outside_trace. apply Forall_forall. intros x Hx.
          destruct x as [bb oo bs | bb oo nn bs | | ]; simpl; auto.
          destruct (peq b bb) as [-> | Hbne]; [| left; exact Hbne].
          right.
          destruct (zlt ofs oo); [ left; lia |].
          destruct (zle (oo + Z.of_nat (length bs)) ofs); [ right; lia |].
          exfalso. apply Hnw2. apply Exists_exists. exists (Write bb oo bs).
          split; [ exact Hx |]. simpl. split; [ reflexivity | lia ]. }
        rewrite E21.
        rewrite (ev_elim_wr_frame T2 m m21a b ofs Hwr2 Hout2 HB1).
        rewrite (ev_elim_wr_frame T2 m12a m12 b ofs Hwr2 Hout2 HA2).
        exact E12a.
  Qed.

End StepDiamond.
