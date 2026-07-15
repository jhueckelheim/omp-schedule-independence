(* Schedule-independence development, step 9: the ev_elim frame lemma.

   A write-only event trace (only Write events; each is a Mem.storebytes,
   event_semantics.v:32) changes memory ONLY at the locations it writes. At any
   location outside the trace's write-footprint the contents are preserved.

   This is the frame direction of the diamond: it lets us conclude that one
   iteration's step is invisible on another iteration's (disjoint) footprint,
   which is what confluence needs -- WITHOUT proving a full trace-trace diamond.

   Build (upstream untouched), from the ClightOMP root:
     eval $(opam env --switch=ClightOMP)
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/EvElimFrame.v
*)

Require Import ZArith.
Require Import List.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import VST.concurrency.openmp_sem.event_semantics.
Require Import VST.concurrency.openmp_sem.sched_indep.Diamond.

Open Scope Z_scope.

Section EvElimFrame.

  (* A single event writes only within its footprint. We define what it means
     for a location (b,ofs) to be OUTSIDE a Write event's footprint. *)
  Definition outside_write (b: block) (ofs: Z) (ev: mem_event) : Prop :=
    match ev with
    | Write b' ofs' bytes =>
        b <> b' \/ ofs < ofs' \/ ofs >= ofs' + Z.of_nat (length bytes)
    | Read _ _ _ _ => True
    | Alloc _ _ _ => True   (* alloc doesn't change existing contents *)
    | Free _ => True        (* free doesn't change contents at valid locs (we only
                               consider write-only traces below, so this is unused) *)
    end.

  (* A trace is write-only if it contains only Write and Read events (the events
     a race-free straight-line iteration body emits: reads of shared/inputs and
     writes of its outputs). We exclude Alloc/Free for the frame lemma to hold
     as a clean content-preservation statement. *)
  Definition wr_only_event (ev: mem_event) : Prop :=
    match ev with
    | Write _ _ _ => True
    | Read _ _ _ _ => True
    | _ => False
    end.

  Definition wr_only_trace (T: list mem_event) : Prop :=
    Forall wr_only_event T.

  (* A location is outside a whole trace's write-footprint. *)
  Definition outside_trace (b: block) (ofs: Z) (T: list mem_event) : Prop :=
    Forall (outside_write b ofs) T.

  (* Read events don't change memory: ev_elim on a Read just requires a
     successful loadbytes and continues on the SAME memory. *)

  (* A location is WRITTEN by some event of the trace (negation of outside). *)
  Definition written_by (b: block) (ofs: Z) (ev: mem_event) : Prop :=
    match ev with
    | Write b' ofs' bytes =>
        b = b' /\ ofs' <= ofs < ofs' + Z.of_nat (length bytes)
    | _ => False
    end.

  (* FRAME: a write-only/read trace preserves contents at any location outside
     its write-footprint. *)
  Lemma ev_elim_wr_frame :
    forall T m m' b ofs,
      wr_only_trace T ->
      outside_trace b ofs T ->
      ev_elim m T m' ->
      ZMap.get ofs (Mem.mem_contents m') !! b =
      ZMap.get ofs (Mem.mem_contents m) !! b.
  Proof.
    induction T as [| ev T IH]; intros m m' b ofs Hwr Hout Hev; simpl in Hev.
    - (* nil *) subst; reflexivity.
    - inversion Hwr as [| ? ? Hwr_hd Hwr_tl]; subst.
      inversion Hout as [| ? ? Hout_hd Hout_tl]; subst.
      destruct ev as [b' ofs' bytes | b' ofs' n bytes | b' lo hi | l ].
      + (* Write: ev_elim gives m'' with storebytes m b' ofs' bytes = Some m'' *)
        destruct Hev as [m'' [Hsb Hev']].
        (* contents at (b,ofs) in m'' equal those in m, since (b,ofs) is outside
           this write *)
        transitivity (ZMap.get ofs (Mem.mem_contents m'') !! b).
        * apply IH; assumption.
        * (* storebytes frame at outside location *)
          rewrite (Mem.storebytes_mem_contents _ _ _ _ _ Hsb).
          rewrite PMap.gsspec.
          destruct (peq b b') as [-> | Hbne].
          -- (* same block: ofs outside the range *)
             simpl in Hout_hd.
             destruct Hout_hd as [Hbb | Hrange]; [ congruence |].
             rewrite Mem.setN_outside by lia. reflexivity.
          -- reflexivity.
      + (* Read: memory unchanged, ev_elim continues on same m *)
        destruct Hev as [Hlb Hev'].
        apply IH; assumption.
      + (* Alloc: excluded by wr_only_trace *)
        simpl in Hwr_hd. contradiction.
      + (* Free: excluded by wr_only_trace *)
        simpl in Hwr_hd. contradiction.
  Qed.

  (* BASE-INDEPENDENCE: running the SAME write-only trace T (same events, same
     bytes) on two different base memories yields, at any location WRITTEN by
     T, identical contents. Intuition: the last Write to that location sets the
     same bytes regardless of the base.

     We prove the general per-location statement: for any (b,ofs), the final
     contents equal
       - the base contents if (b,ofs) is outside the whole trace, OR
       - a value determined solely by T (independent of the base) if written.
     It is cleanest to prove directly: if (b,ofs) is written by the head OR the
     tail, the two runs agree there. *)
  Lemma ev_elim_wr_within_base_indep :
    forall T m1 m1' m2 m2' b ofs,
      wr_only_trace T ->
      ev_elim m1 T m1' ->
      ev_elim m2 T m2' ->
      Exists (written_by b ofs) T ->
      ZMap.get ofs (Mem.mem_contents m1') !! b =
      ZMap.get ofs (Mem.mem_contents m2') !! b.
  Proof.
    induction T as [| ev T IH]; intros m1 m1' m2 m2' b ofs Hwr Hev1 Hev2 Hwritten.
    - (* nil: nothing is written, contradiction with Exists *)
      inversion Hwritten.
    - inversion Hwr as [| ? ? Hwr_hd Hwr_tl]; subst.
      destruct ev as [b' ofs' bytes | b' ofs' n bytes | b' lo hi | l ].
      + (* Write b' ofs' bytes *)
        simpl in Hev1, Hev2.
        destruct Hev1 as [m1'' [Hsb1 Hev1']].
        destruct Hev2 as [m2'' [Hsb2 Hev2']].
        (* Case: is (b,ofs) written later in T? *)
        destruct (Exists_dec (written_by b ofs) T) as [Hlater | Hnolater].
        { intro x. destruct x as [bb oo bs | | |].
          - unfold written_by. destruct (peq b bb).
            + destruct (zle oo ofs).
              * destruct (zlt ofs (oo + Z.of_nat (length bs))).
                -- left; split; [ congruence | lia ].
                -- right; intros [_ ?]; lia.
              * right; intros [_ ?]; lia.
            + right; intros [? _]; congruence.
          - right; intros [].
          - right; intros [].
          - right; intros []. }
        * (* written later: recurse on the tail *)
          eapply IH; eauto.
        * (* NOT written later: so this head Write is the last write to (b,ofs).
             By the frame lemma the tail preserves (b,ofs), and both m1''/m2''
             got the same bytes at (b,ofs) from this storebytes. *)
          assert (Hout_tail: outside_trace b ofs T).
          { unfold outside_trace. apply Forall_forall. intros x Hx.
            destruct x as [bb oo bs | bb oo nn bs | | ]; simpl; auto.
            (* Write in tail: since not Exists written_by, this x doesn't write (b,ofs) *)
            destruct (peq b bb) as [-> | Hbne]; [| left; exact Hbne].
            right.
            destruct (zlt ofs oo); [ left; lia |].
            destruct (zle (oo + Z.of_nat (length bs)) ofs); [ right; lia |].
            exfalso. apply Hnolater. apply Exists_exists. exists (Write bb oo bs).
            split; [ exact Hx |]. simpl. split; [ reflexivity | lia ]. }
          rewrite (ev_elim_wr_frame T m1'' m1' b ofs Hwr_tl Hout_tail Hev1').
          rewrite (ev_elim_wr_frame T m2'' m2' b ofs Hwr_tl Hout_tail Hev2').
          (* now compare the two storebytes at (b,ofs). Is (b,ofs) in THIS write? *)
          inversion Hwritten as [? ? Hhd | ? ? Htl]; subst.
          -- (* head writes (b,ofs) *)
             simpl in Hhd. destruct Hhd as [Hbb Hrange]. subst b'.
             rewrite (Mem.storebytes_mem_contents _ _ _ _ _ Hsb1).
             rewrite (Mem.storebytes_mem_contents _ _ _ _ _ Hsb2).
             rewrite !PMap.gss.
             (* within range: value is base-independent (setN_get_in_indep) *)
             apply setN_get_in_indep. lia.
          -- (* tail writes (b,ofs): contradicts Hnolater *)
             exfalso. apply Hnolater. exact Htl.
      + (* Read: memory unchanged; recurse *)
        simpl in Hev1, Hev2.
        destruct Hev1 as [Hlb1 Hev1'].
        destruct Hev2 as [Hlb2 Hev2'].
        eapply IH; eauto.
        (* Exists written_by holds on tail since head Read writes nothing *)
        inversion Hwritten as [? ? Hhd | ? ? Htl]; subst; [ inversion Hhd | exact Htl ].
      + (* Alloc: excluded *)
        simpl in Hwr_hd; contradiction.
      + (* Free: excluded *)
        simpl in Hwr_hd; contradiction.
  Qed.

End EvElimFrame.
