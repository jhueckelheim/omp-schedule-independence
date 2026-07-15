(* Schedule-independence development, step 9: the ev_elim frame lemma.

   An event trace built from Read/Write/Alloc/Free (i.e. everything the Clight
   event semantics can emit, INCLUDING iteration-local allocation and free from
   known-function calls with stack-allocated locals) changes memory contents ONLY
   at the locations it writes, when observed at a block VALID in the base memory:
   - Write changes contents in its range;
   - Alloc resets contents only at the FRESH block (never a valid-in-base block);
   - Free changes only permissions, never contents.
   Hence at any base-valid location outside the trace's write-footprint the
   contents are preserved.

   This is the frame direction of the diamond: it lets us conclude that one
   iteration's step is invisible on another iteration's (disjoint) footprint,
   which is what confluence needs -- WITHOUT proving a full trace-trace diamond.
   The block-validity restriction is exactly right: freshly-allocated iteration-
   local blocks are not observable (their identities legitimately differ between
   schedules), so the guarantee is about pre-existing (e.g. shared output) memory.

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
     for a location (b,ofs) to be OUTSIDE an event's content-footprint.
     - Write b' ofs' bytes touches contents in [ofs', ofs'+|bytes|) of block b'.
     - Alloc b' lo hi resets contents of the FRESH block b' (= nextblock) to
       Undef; it touches no PRE-EXISTING block, so a valid-in-base location is
       outside it as long as b <> b'. (At call sites the observed location is
       valid in the base and the alloc'd block is fresh, so b <> b' automatically;
       we nonetheless record the b<>b' condition to keep the lemma hypothesis-free
       about validity.)
     - Free l changes only permissions, never contents, so it touches nothing. *)
  Definition outside_write (b: block) (ofs: Z) (ev: mem_event) : Prop :=
    match ev with
    | Write b' ofs' bytes =>
        b <> b' \/ ofs < ofs' \/ ofs >= ofs' + Z.of_nat (length bytes)
    | Read _ _ _ _ => True
    | Alloc _ _ _ => True   (* alloc only resets the FRESH block; a valid-in-base
                               location is never that block (discharged via a
                               validity hypothesis in the frame lemma) *)
    | Free _ => True        (* free never changes contents *)
    end.

  (* Trace effect alphabet allowed by the framing lemmas: Read, Write, Alloc,
     Free -- i.e. everything the Clight event semantics can emit for a call tree
     with iteration-local allocation/deallocation. (Read/Write already covered;
     Alloc/Free now handled too.) *)
  Definition wr_only_event (ev: mem_event) : Prop := True.

  Definition wr_only_trace (T: list mem_event) : Prop :=
    Forall wr_only_event T.

  (* Every trace satisfies the (now-trivial) trace-class predicate: the framing
     lemmas below tolerate Read/Write/Alloc/Free. Kept as a named lemma so that
     downstream witnesses of `wr_only_trace` remain easy to supply. *)
  Lemma wr_only_trace_any : forall T, wr_only_trace T.
  Proof. intro T. apply Forall_forall. intros x _. exact I. Qed.

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

  (* A single free preserves all memory contents (it only changes permissions). *)
  Lemma free_contents :
    forall m b lo hi m',
      Mem.free m b lo hi = Some m' ->
      Mem.mem_contents m' = Mem.mem_contents m.
  Proof.
    intros m b lo hi m' Hf.
    rewrite (Mem.free_result _ _ _ _ _ Hf).
    reflexivity.
  Qed.

  (* alloc changes contents only at the freshly allocated block b' (= the result
     block); at any other block the contents are unchanged. *)
  Lemma alloc_contents_other :
    forall m lo hi m' b' b ofs,
      Mem.alloc m lo hi = (m', b') ->
      b <> b' ->
      ZMap.get ofs (Mem.mem_contents m') !! b =
      ZMap.get ofs (Mem.mem_contents m) !! b.
  Proof.
    intros m lo hi m' b' b ofs Hal Hbne.
    (* alloc m lo hi = (mkmem (PMap.set (nextblock m) (init Undef) (contents m)) ..., nextblock m) *)
    Transparent Mem.alloc.
    unfold Mem.alloc in Hal.
    injection Hal; intros Hb'eq Hmeq.
    Opaque Mem.alloc.
    rewrite <- Hmeq. simpl.
    rewrite PMap.gso; [ reflexivity |].
    (* goal: b <> nextblock m; have Hbne: b <> b' and Hb'eq relating b', nextblock m *)
    congruence.
  Qed.

  (* free_list preserves all memory contents. *)
  Lemma free_list_contents :
    forall l m m',
      Mem.free_list m l = Some m' ->
      Mem.mem_contents m' = Mem.mem_contents m.
  Proof.
    induction l as [| [[b lo] hi] l IH]; intros m m' Hfl; simpl in Hfl.
    - injection Hfl; intros ->; reflexivity.
    - destruct (Mem.free m b lo hi) as [m1|] eqn:Hf1; [| discriminate ].
      rewrite (IH m1 m' Hfl). apply (free_contents _ _ _ _ _ Hf1).
  Qed.

  (* free_list preserves validity of any block. *)
  Lemma valid_block_free_list_1 :
    forall l m m' b,
      Mem.free_list m l = Some m' ->
      Mem.valid_block m b ->
      Mem.valid_block m' b.
  Proof.
    induction l as [| [[bb lo] hi] l IH]; intros m m' b Hfl Hvb; simpl in Hfl.
    - injection Hfl; intros ->; exact Hvb.
    - destruct (Mem.free m bb lo hi) as [m1|] eqn:Hf1; [| discriminate ].
      eapply IH; [ exact Hfl |].
      eapply Mem.valid_block_free_1; eauto.
  Qed.

  (* FRAME: a read/write/alloc/free trace preserves contents at any location
     outside its content-footprint (outside every Write range, and not equal to
     any freshly Alloc'd block; Free never changes contents). *)
  Lemma ev_elim_wr_frame :
    forall T m m' b ofs,
      Mem.valid_block m b ->
      outside_trace b ofs T ->
      ev_elim m T m' ->
      ZMap.get ofs (Mem.mem_contents m') !! b =
      ZMap.get ofs (Mem.mem_contents m) !! b.
  Proof.
    induction T as [| ev T IH]; intros m m' b ofs Hvb Hout Hev; simpl in Hev.
    - (* nil *) subst; reflexivity.
    - inversion Hout as [| ? ? Hout_hd Hout_tl]; subst.
      destruct ev as [b' ofs' bytes | b' ofs' n bytes | b' lo hi | l ].
      + (* Write: ev_elim gives m'' with storebytes m b' ofs' bytes = Some m'' *)
        destruct Hev as [m'' [Hsb Hev']].
        transitivity (ZMap.get ofs (Mem.mem_contents m'') !! b).
        * apply IH; auto. eapply Mem.storebytes_valid_block_1; eauto.
        * rewrite (Mem.storebytes_mem_contents _ _ _ _ _ Hsb).
          rewrite PMap.gsspec.
          destruct (peq b b') as [-> | Hbne].
          -- simpl in Hout_hd.
             destruct Hout_hd as [Hbb | Hrange]; [ congruence |].
             rewrite Mem.setN_outside by lia. reflexivity.
          -- reflexivity.
      + (* Read: memory unchanged, ev_elim continues on same m *)
        destruct Hev as [Hlb Hev'].
        apply IH; assumption.
      + (* Alloc b' lo hi: alloc changes contents only at the FRESH block b';
           b is valid in m so b <> b' by freshness. *)
        destruct Hev as [m'' [Hal Hev']].
        transitivity (ZMap.get ofs (Mem.mem_contents m'') !! b).
        * apply IH; auto. eapply Mem.valid_block_alloc; eauto.
        * assert (Hbne : b <> b')
            by (intro; subst b'; eapply Mem.fresh_block_alloc; eauto).
          apply (alloc_contents_other _ _ _ _ _ _ ofs Hal Hbne).
      + (* Free l: free_list changes only permissions, not contents *)
        destruct Hev as [m'' [Hfl Hev']].
        transitivity (ZMap.get ofs (Mem.mem_contents m'') !! b).
        * apply IH; auto. eapply valid_block_free_list_1; eauto.
        * rewrite (free_list_contents _ _ _ Hfl). reflexivity.
  Qed.

  (* A whole ev_elim run preserves validity of any pre-existing block. *)
  Lemma ev_elim_valid_block :
    forall T m m' b,
      ev_elim m T m' ->
      Mem.valid_block m b ->
      Mem.valid_block m' b.
  Proof.
    induction T as [| ev T IH]; intros m m' b Hev Hvb; simpl in Hev.
    - subst; exact Hvb.
    - destruct ev as [b' ofs' bytes | b' ofs' n bytes | b' lo hi | l ].
      + destruct Hev as [m'' [Hsb Hev']].
        eapply IH; [ exact Hev' |]. eapply Mem.storebytes_valid_block_1; eauto.
      + destruct Hev as [Hlb Hev']. eapply IH; eauto.
      + destruct Hev as [m'' [Hal Hev']].
        eapply IH; [ exact Hev' |]. eapply Mem.valid_block_alloc; eauto.
      + destruct Hev as [m'' [Hfl Hev']].
        eapply IH; [ exact Hev' |]. eapply valid_block_free_list_1; eauto.
  Qed.

  (* A freshly Alloc'd block is distinct from any block valid before the alloc. *)
  Lemma alloc_fresh_neq :
    forall m lo hi m'' b' b,
      Mem.alloc m lo hi = (m'', b') ->
      Mem.valid_block m b ->
      b <> b'.
  Proof.
    intros m lo hi m'' b' b Hal Hvb Heq. subst b'.
    apply (Mem.fresh_block_alloc _ _ _ _ _ Hal). exact Hvb.
  Qed.

  (* BASE-INDEPENDENCE: running the SAME trace T (same events, same bytes) on two
     base memories yields, at any location WRITTEN by T AND at a block valid in
     both bases, identical contents. The block-validity hypothesis restricts the
     claim to PRE-EXISTING memory (e.g. the shared output footprint); it excludes
     freshly-allocated iteration-local blocks, whose identities legitimately
     differ between runs. Alloc/Free events are tolerated: they never change
     contents at a pre-existing block. *)
  Lemma ev_elim_wr_within_base_indep :
    forall T m1 m1' m2 m2' b ofs,
      Mem.valid_block m1 b ->
      Mem.valid_block m2 b ->
      ev_elim m1 T m1' ->
      ev_elim m2 T m2' ->
      Exists (written_by b ofs) T ->
      ZMap.get ofs (Mem.mem_contents m1') !! b =
      ZMap.get ofs (Mem.mem_contents m2') !! b.
  Proof.
    induction T as [| ev T IH];
      intros m1 m1' m2 m2' b ofs Hvb1 Hvb2 Hev1 Hev2 Hwritten.
    - (* nil: nothing is written, contradiction with Exists *)
      inversion Hwritten.
    - destruct ev as [b' ofs' bytes | b' ofs' n bytes | b' lo hi | l ].
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
        * (* written later: recurse on the tail, carrying validity of b *)
          assert (Hvb1'' : Mem.valid_block m1'' b)
            by (eapply Mem.storebytes_valid_block_1; eauto).
          assert (Hvb2'' : Mem.valid_block m2'' b)
            by (eapply Mem.storebytes_valid_block_1; eauto).
          eapply (IH m1'' m1' m2'' m2' b ofs Hvb1'' Hvb2'' Hev1' Hev2' Hlater).
        * (* NOT written later: so this head Write is the last write to (b,ofs).
             By the frame lemma the tail preserves (b,ofs), and both m1''/m2''
             got the same bytes at (b,ofs) from this storebytes. *)
          assert (Hout_tail: outside_trace b ofs T).
          { unfold outside_trace. apply Forall_forall. intros x Hx.
            destruct x as [bb oo bs | bb oo nn bs | bb lo hi | l ]; simpl; auto.
            (* only the Write case is nontrivial; Read/Alloc/Free are True *)
            destruct (peq b bb) as [-> | Hbne]; [| left; exact Hbne].
            right.
            destruct (zlt ofs oo); [ left; lia |].
            destruct (zle (oo + Z.of_nat (length bs)) ofs); [ right; lia |].
            exfalso. apply Hnolater. apply Exists_exists. exists (Write bb oo bs).
            split; [ exact Hx |]. simpl. split; [ reflexivity | lia ]. }
          assert (Hvb1'' : Mem.valid_block m1'' b)
            by (eapply Mem.storebytes_valid_block_1; eauto).
          assert (Hvb2'' : Mem.valid_block m2'' b)
            by (eapply Mem.storebytes_valid_block_1; eauto).
          rewrite (ev_elim_wr_frame T m1'' m1' b ofs Hvb1'' Hout_tail Hev1').
          rewrite (ev_elim_wr_frame T m2'' m2' b ofs Hvb2'' Hout_tail Hev2').
          inversion Hwritten as [? ? Hhd | ? ? Htl]; subst.
          -- (* head writes (b,ofs) *)
             simpl in Hhd. destruct Hhd as [Hbb Hrange]. subst b'.
             rewrite (Mem.storebytes_mem_contents _ _ _ _ _ Hsb1).
             rewrite (Mem.storebytes_mem_contents _ _ _ _ _ Hsb2).
             rewrite !PMap.gss.
             apply setN_get_in_indep. lia.
          -- (* tail writes (b,ofs): contradicts Hnolater *)
             exfalso. apply Hnolater. exact Htl.
      + (* Read: memory unchanged; recurse *)
        simpl in Hev1, Hev2.
        destruct Hev1 as [Hlb1 Hev1'].
        destruct Hev2 as [Hlb2 Hev2'].
        eapply IH with (m1:=m1) (m2:=m2); eauto.
        inversion Hwritten as [? ? Hhd | ? ? Htl]; subst; [ inversion Hhd | exact Htl ].
      + (* Alloc b' lo hi: contents unchanged at the valid block b (b <> b'),
           and validity preserved; recurse. *)
        simpl in Hev1, Hev2.
        destruct Hev1 as [m1'' [Hal1 Hev1']].
        destruct Hev2 as [m2'' [Hal2 Hev2']].
        (* Exists written_by holds on the tail (Alloc writes nothing) *)
        assert (Htail : Exists (written_by b ofs) T)
          by (inversion Hwritten as [? ? Hhd | ? ? Htl]; subst;
              [ inversion Hhd | exact Htl ]).
        (* b <> b'1 and b <> b'2 by freshness (b valid in m1, m2) *)
        assert (Hvb1'' : Mem.valid_block m1'' b) by (eapply Mem.valid_block_alloc; eauto).
        assert (Hvb2'' : Mem.valid_block m2'' b) by (eapply Mem.valid_block_alloc; eauto).
        eapply IH with (m1:=m1'') (m2:=m2''); eauto.
      + (* Free l: contents unchanged, validity preserved; recurse. *)
        simpl in Hev1, Hev2.
        destruct Hev1 as [m1'' [Hfl1 Hev1']].
        destruct Hev2 as [m2'' [Hfl2 Hev2']].
        assert (Htail : Exists (written_by b ofs) T)
          by (inversion Hwritten as [? ? Hhd | ? ? Htl]; subst;
              [ inversion Hhd | exact Htl ]).
        assert (Hvb1'' : Mem.valid_block m1'' b)
          by (eapply valid_block_free_list_1; eauto).
        assert (Hvb2'' : Mem.valid_block m2'' b)
          by (eapply valid_block_free_list_1; eauto).
        eapply IH with (m1:=m1'') (m2:=m2''); eauto.
  Qed.

End EvElimFrame.
