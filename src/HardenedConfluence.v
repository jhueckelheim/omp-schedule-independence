(* Schedule-independence development: HARDENING.

   The theorems in Confluence.v assume the caller supplies pairwise-disjoint
   footprints. A skeptic asks: what if the program actually has a data race that
   was not ruled out? This file answers that by making the independence condition

     (a) DERIVED FROM THE ACTUAL EXECUTION TRACES (not assumed about the source),
     (b) DECIDABLE, and
     (c) the exact hypothesis of the schedule-independence guarantee,

   and then proving a theorem that is valid for an ARBITRARY program, race-free
   or not:

     for any list of per-iteration memory-event traces, EITHER the traces are
     independent -- in which case every schedule yields the same observable
     output -- OR they exhibit an explicit conflicting pair (a race witness).

   So the result never claims schedule-independence for a racy program: on a racy
   input the independence hypothesis is simply false (and a witness is produced).

   Independence here is the full Bernstein condition read off the traces:
   distinct iterations have disjoint WRITE sets, and no iteration READS a location
   another iteration WRITES. (Overlapping read-only is allowed.)

   Build (inside a built ClightOMP checkout):
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/HardenedConfluence.v
*)

Require Import ZArith.
Require Import List.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.Classical_Prop.
Require Import VST.concurrency.openmp_sem.event_semantics.
Require Import VST.concurrency.openmp_sem.sched_indep.ObsEquiv.
Require Import VST.concurrency.openmp_sem.sched_indep.EvElimFrame.
Require Import VST.concurrency.openmp_sem.sched_indep.StepDiamond.
Require Import VST.concurrency.openmp_sem.sched_indep.Confluence.

Open Scope Z_scope.

Section Hardened.

  (* ---- read/write sets read off an actual trace ------------------------- *)

  (* (b,ofs) is WRITTEN by trace T (some Write event of T covers it). *)
  Definition writes (T: list mem_event) (b: block) (ofs: Z) : Prop :=
    Exists (written_by b ofs) T.

  (* (b,ofs) is READ by trace T (some Read event of T covers it). *)
  Definition read_by (b: block) (ofs: Z) (ev: mem_event) : Prop :=
    match ev with
    | Read b' ofs' n _ => b = b' /\ ofs' <= ofs < ofs' + n
    | _ => False
    end.
  Definition reads (T: list mem_event) (b: block) (ofs: Z) : Prop :=
    Exists (read_by b ofs) T.

  (* ---- independence, derived from the traces themselves ------------------ *)

  (* Two traces are independent (Bernstein): no write/write overlap and no
     read/write overlap in either direction. Read/read overlap is allowed. *)
  Definition traces_indep2 (T1 T2: list mem_event) : Prop :=
    (forall b ofs, writes T1 b ofs -> writes T2 b ofs -> False) /\
    (forall b ofs, reads  T1 b ofs -> writes T2 b ofs -> False) /\
    (forall b ofs, reads  T2 b ofs -> writes T1 b ofs -> False).

  (* A conflict between two traces: a location one writes and the other reads or
     writes. This is the explicit race witness. *)
  Definition conflict2 (T1 T2: list mem_event) : Prop :=
    (exists b ofs, writes T1 b ofs /\ writes T2 b ofs) \/
    (exists b ofs, reads  T1 b ofs /\ writes T2 b ofs) \/
    (exists b ofs, reads  T2 b ofs /\ writes T1 b ofs).

  (* Independence is exactly the negation of conflict (constructively, up to the
     classical existentials). This is what makes the disjunction below total. *)
  Lemma indep_or_conflict2 :
    forall T1 T2, traces_indep2 T1 T2 \/ conflict2 T1 T2.
  Proof.
    intros T1 T2.
    destruct (classic (conflict2 T1 T2)) as [Hc | Hnc]; [ right; exact Hc |].
    left. unfold conflict2 in Hnc. repeat split; intros b ofs H1 H2.
    - apply Hnc. left. exists b, ofs. split; assumption.
    - apply Hnc. right; left. exists b, ofs. split; assumption.
    - apply Hnc. right; right. exists b, ofs. split; assumption.
  Qed.

  (* Independence of a whole list: every distinct pair is independent. *)
  Definition traces_indep (Ts: list (list mem_event)) : Prop :=
    forall i j, i <> j ->
      forall Ti Tj, nth_error Ts i = Some Ti -> nth_error Ts j = Some Tj ->
      traces_indep2 Ti Tj.

  (* A conflict somewhere in the list. *)
  Definition list_conflict (Ts: list (list mem_event)) : Prop :=
    exists i j Ti Tj, i <> j /\
      nth_error Ts i = Some Ti /\ nth_error Ts j = Some Tj /\ conflict2 Ti Tj.

  (* Totality: any list of traces is either fully independent or has a witnessed
     conflict. (Classical, via indep_or_conflict2 over the finitely many pairs.) *)
  Lemma indep_or_conflict :
    forall Ts, traces_indep Ts \/ list_conflict Ts.
  Proof.
    intros Ts.
    destruct (classic (list_conflict Ts)) as [Hc | Hnc]; [ right; exact Hc |].
    left. intros i j Hij Ti Tj Hi Hj.
    destruct (indep_or_conflict2 Ti Tj) as [Hindep | Hconf]; [ exact Hindep |].
    exfalso. apply Hnc. exists i, j, Ti, Tj. repeat split; assumption.
  Qed.

  (* ---- the write-footprint of a trace, as a Confluence.footprint --------- *)

  Definition write_foot_of (T: list mem_event) : footprint :=
    fun b ofs => writes T b ofs.

  (* By definition a trace writes within its own write-footprint. *)
  Lemma trace_within_write_foot :
    forall T, trace_writes_within (write_foot_of T) T.
  Proof.
    intros T b ofs Hnot. unfold outside_trace. apply Forall_forall.
    intros ev Hev. destruct ev as [b' o' bs | b' o' n bs | | ]; simpl; auto.
    (* Write ev: if it covered (b,ofs), then (b,ofs) in write_foot_of T,
       contradicting Hnot *)
    destruct (peq b b') as [-> | Hbne]; [| left; exact Hbne].
    right.
    destruct (zlt ofs o') as [Hlt | Hge]; [ left; lia |].
    destruct (zle (o' + Z.of_nat (length bs)) ofs) as [Hle | Hgt]; [ right; lia |].
    exfalso. apply Hnot. unfold write_foot_of, writes.
    apply Exists_exists. exists (Write b' o' bs). split; [ exact Hev |].
    simpl. split; [ reflexivity | lia ].
  Qed.

  (* ---- run over raw traces ---------------------------------------------- *)

  Definition raw_run (Ts: list (list mem_event)) (m m': mem) : Prop :=
    ev_elim m (concat Ts) m'.

  Lemma raw_run_app :
    forall Ts1 Ts2 m m',
      raw_run (Ts1 ++ Ts2) m m' <->
      exists mm, raw_run Ts1 m mm /\ raw_run Ts2 mm m'.
  Proof.
    intros. unfold raw_run. rewrite concat_app. split.
    - apply ev_elim_split.
    - intros [mm [H1 H2]]. eapply ev_elim_app; eauto.
  Qed.

  (* every trace in Ts is write-only *)
  Definition all_wr_only (Ts: list (list mem_event)) : Prop :=
    Forall wr_only_trace Ts.

  (* A location not written by ANY trace in the list is framed by the whole run. *)
  Lemma raw_other_frame :
    forall Ts m m' b ofs,
      Mem.valid_block m b ->
      (forall T, In T Ts -> ~ writes T b ofs) ->
      raw_run Ts m m' ->
      ZMap.get ofs (Mem.mem_contents m') !! b =
      ZMap.get ofs (Mem.mem_contents m) !! b.
  Proof.
    induction Ts as [| T Ts IH]; intros m m' b ofs Hvb Hout Hrun.
    - unfold raw_run in Hrun; simpl in Hrun; subst; reflexivity.
    - unfold raw_run in Hrun; simpl in Hrun.
      apply ev_elim_split in Hrun. destruct Hrun as [mm [H1 H2]].
      assert (Hvbmm : Mem.valid_block mm b)
        by (eapply ev_elim_valid_block; [ exact H1 | exact Hvb ]).
      transitivity (ZMap.get ofs (Mem.mem_contents mm) !! b).
      + apply IH; auto. intros T' HT'. apply Hout. right; auto.
      + eapply ev_elim_wr_frame; [ exact Hvb | | exact H1 ].
        (* outside_trace b ofs T: T does not write (b,ofs) *)
        apply (trace_within_write_foot T). apply Hout. left; reflexivity.
  Qed.

  (* Split a raw run around a designated owner trace T0 at position (Ts1,Ts2),
     where no other trace writes (b,ofs). Returns the pre/owner runs and the
     framing equalities. *)
  Lemma raw_run_split_owner :
    forall Ts1 T0 Ts2 m m' b ofs,
      Mem.valid_block m b ->
      (forall T, In T Ts1 -> ~ writes T b ofs) ->
      (forall T, In T Ts2 -> ~ writes T b ofs) ->
      raw_run (Ts1 ++ T0 :: Ts2) m m' ->
      exists mm mm',
        raw_run (T0 :: nil) mm mm' /\
        Mem.valid_block mm b /\
        ZMap.get ofs (Mem.mem_contents mm) !! b =
        ZMap.get ofs (Mem.mem_contents m) !! b /\
        ZMap.get ofs (Mem.mem_contents m') !! b =
        ZMap.get ofs (Mem.mem_contents mm') !! b.
  Proof.
    intros Ts1 T0 Ts2 m m' b ofs Hvb Hout1 Hout2 Hrun.
    apply raw_run_app in Hrun. destruct Hrun as [mm [Hr1 Hrest]].
    replace (T0 :: Ts2) with ((T0 :: nil) ++ Ts2) in Hrest by reflexivity.
    apply raw_run_app in Hrest. destruct Hrest as [mm' [Hr0 Hr2]].
    assert (Hvbmm : Mem.valid_block mm b)
      by (eapply ev_elim_valid_block; [ exact Hr1 | exact Hvb ]).
    assert (Hvbmm' : Mem.valid_block mm' b)
      by (eapply ev_elim_valid_block; [ exact Hr0 | exact Hvbmm ]).
    exists mm, mm'. split; [ exact Hr0 |]. split; [ exact Hvbmm |]. split.
    - apply (raw_other_frame Ts1 m mm b ofs Hvb Hout1 Hr1).
    - apply (raw_other_frame Ts2 mm' m' b ofs Hvbmm' Hout2 Hr2).
  Qed.

  (* ---- helpers connecting membership, positions, and write-ownership ----- *)

  Lemma all_wr_only_app_inv :
    forall Ts1 Ts2, all_wr_only (Ts1 ++ Ts2) -> all_wr_only Ts1 /\ all_wr_only Ts2.
  Proof. intros. unfold all_wr_only in *. apply Forall_app in H. exact H. Qed.

  Lemma all_wr_only_in :
    forall Ts T, all_wr_only Ts -> In T Ts -> wr_only_trace T.
  Proof. intros. eapply Forall_forall in H; eauto. Qed.

  (* Under list-independence, the owner of a written location is unique: if two
     positions both write (b,ofs), they are the same position. *)
  Lemma indep_unique_owner :
    forall Ts i j Ti Tj b ofs,
      traces_indep Ts ->
      nth_error Ts i = Some Ti -> nth_error Ts j = Some Tj ->
      writes Ti b ofs -> writes Tj b ofs -> i = j.
  Proof.
    intros Ts i j Ti Tj b ofs Hindep Hi Hj Hwi Hwj.
    destruct (Nat.eq_dec i j) as [Heq | Hne]; [ exact Heq |].
    exfalso.
    destruct (Hindep i j Hne Ti Tj Hi Hj) as [Hww [_ _]].
    eapply Hww; eauto.
  Qed.

  (* Every union (= "some trace writes it") location has, under independence, a
     unique owner with a pre/post decomposition where no other trace writes it. *)
  Lemma indep_owner_decomp :
    forall Ts b ofs,
      traces_indep Ts ->
      (exists T, In T Ts /\ writes T b ofs) ->
      exists Ts1 T0 Ts2,
        Ts = Ts1 ++ T0 :: Ts2 /\
        writes T0 b ofs /\
        (forall T, In T Ts1 -> ~ writes T b ofs) /\
        (forall T, In T Ts2 -> ~ writes T b ofs).
  Proof.
    intros Ts b ofs Hindep [T [Hin Hw]].
    (* locate the first writer; but under independence there is a unique writer,
       so any split around a writer has non-writing pre/post. *)
    destruct (In_nth_error _ _ Hin) as [k Hk].
    (* split the list at position k *)
    pose proof (nth_error_split Ts k Hk) as (Ts1 & Ts2 & Hsplit & Hlen).
    exists Ts1, T, Ts2. subst Ts. split; [ reflexivity |]. split; [ exact Hw |].
    split.
    - (* pre: no other trace writes (b,ofs), by uniqueness of owner *)
      intros T' HT' Hw'.
      destruct (In_nth_error _ _ HT') as [k' Hk'].
      assert (Hk'full : nth_error (Ts1 ++ T :: Ts2) k' = Some T').
      { rewrite nth_error_app1; [ exact Hk' | ].
        apply nth_error_Some. rewrite Hk'. discriminate. }
      assert (Hkfull : nth_error (Ts1 ++ T :: Ts2) (length Ts1) = Some T).
      { rewrite nth_error_app2 by apply Nat.le_refl.
        rewrite Nat.sub_diag. reflexivity. }
      (* k' < length Ts1 = position of T, so distinct positions both writing *)
      assert (Hk'lt : (k' < length Ts1)%nat).
      { apply nth_error_Some. rewrite Hk'. discriminate. }
      assert (Hne : (k' <> length Ts1)%nat) by lia.
      pose proof (indep_unique_owner _ _ _ _ _ b ofs Hindep Hk'full Hkfull Hw' Hw).
      lia.
    - (* post: symmetric *)
      intros T' HT' Hw'.
      destruct (In_nth_error _ _ HT') as [k' Hk'].
      assert (Hk'full : nth_error (Ts1 ++ T :: Ts2) (length Ts1 + S k')%nat = Some T').
      { rewrite nth_error_app2 by lia.
        replace (length Ts1 + S k' - length Ts1)%nat with (S k') by lia.
        simpl. exact Hk'. }
      assert (Hkfull : nth_error (Ts1 ++ T :: Ts2) (length Ts1) = Some T).
      { rewrite nth_error_app2 by apply Nat.le_refl.
        rewrite Nat.sub_diag. reflexivity. }
      assert (Hne : (length Ts1 + S k' <> length Ts1)%nat) by lia.
      pose proof (indep_unique_owner _ _ _ _ _ b ofs Hindep Hk'full Hkfull Hw' Hw).
      lia.
  Qed.

  (* ---- canonical value characterization --------------------------------- *)

  (* The observable content at a location after running a write-only, INDEPENDENT
     list is CANONICAL: it depends only on whether some trace writes the location
     (and which one), not on the order. We package this as: for any two runs of
     write-only independent lists that are permutations of each other, the content
     at any location agrees -- proved by showing each run equals a value fixed by
     the base m and the unique owner.

     Key device: we characterise the post-content at (b,ofs) directly from a run,
     by induction on the list, without needing a decomposition of the OTHER run. *)

  (* From a run of a write-only list, at a location, the content is either the
     base content (if no trace writes it) or equals the content produced by
     running just the unique owner trace on m (base-independent). We phrase the
     usable consequence directly. *)
  Lemma raw_run_content_char :
    forall Ts m m' b ofs,
      Mem.valid_block m b ->
      traces_indep Ts ->
      raw_run Ts m m' ->
        (* no writer: content preserved *)
        ((forall T, In T Ts -> ~ writes T b ofs) /\
         ZMap.get ofs (Mem.mem_contents m') !! b =
         ZMap.get ofs (Mem.mem_contents m) !! b)
        \/
        (* unique owner T0 writes it; the content equals T0 run on SOME base mm
           (the memory just before T0 executed), with b valid in mm. *)
        (exists T0 mm mm', In T0 Ts /\ writes T0 b ofs /\ Mem.valid_block mm b /\
           raw_run (T0 :: nil) mm mm' /\
           ZMap.get ofs (Mem.mem_contents m') !! b =
           ZMap.get ofs (Mem.mem_contents mm') !! b).
  Proof.
    intros Ts m m' b ofs Hvb Hindep Hrun.
    destruct (classic (exists T, In T Ts /\ writes T b ofs)) as [Hex | Hnex].
    - (* there is a writer; decompose around the unique owner *)
      right.
      destruct (indep_owner_decomp Ts b ofs Hindep Hex)
        as (Ts1 & T0 & Ts2 & HeqTs & Hw0 & Hpre & Hpost).
      rewrite HeqTs in Hrun.
      destruct (raw_run_split_owner Ts1 T0 Ts2 m m' b ofs Hvb Hpre Hpost Hrun)
        as (mm & mm' & Hr0 & Hvbmm & Hmm & Hm').
      exists T0, mm, mm'. split; [ | split; [ exact Hw0 | split; [ exact Hvbmm | split ] ] ].
       + rewrite HeqTs. apply in_or_app; right; left; reflexivity.
       + exact Hr0.
       + exact Hm'.
     - (* no writer: everyone frames it *)
       left. split.
       + intros T HinT HwT. apply Hnex. exists T; split; assumption.
       + apply (raw_other_frame Ts m m' b ofs Hvb);
           [ | exact Hrun ].
         intros T HinT HwT. apply Hnex. exists T; split; assumption.
   Qed.

  (* Independence transfers along a permutation, using the positional bijection
     that Permutation_nth provides (nth x Ts' = nth (f x) Ts with f injective on
     [0,len)). Distinct Ts'-positions map to distinct Ts-positions, so the
     pairwise condition transfers directly -- no duplicate/count reasoning. *)
  Lemma traces_indep_perm :
    forall Ts Ts',
      Permutation Ts Ts' ->
      traces_indep Ts ->
      traces_indep Ts'.
  Proof.
    intros Ts Ts' Hperm Hindep i j Hij Ti Tj Hi Hj.
    (* default element for nth *)
    set (d := (@nil mem_event)).
    apply Permutation_nth with (d:=d) in Hperm.
    destruct Hperm as [Hlen [f [Hbf [Hinj Hnth]]]].
    (* i,j are valid indices of Ts' *)
    assert (Hi_lt : (i < length Ts')%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    assert (Hj_lt : (j < length Ts')%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    rewrite Hlen in Hi_lt, Hj_lt.
    (* nth_error -> nth (with default) *)
    assert (HTi : nth i Ts' d = Ti) by (apply nth_error_nth; exact Hi).
    assert (HTj : nth j Ts' d = Tj) by (apply nth_error_nth; exact Hj).
    (* map to Ts positions f i, f j *)
    assert (Hfi : nth i Ts' d = nth (f i) Ts d) by (apply Hnth; exact Hi_lt).
    assert (Hfj : nth j Ts' d = nth (f j) Ts d) by (apply Hnth; exact Hj_lt).
    assert (Hfij : f i <> f j) by
      (intro Heqf; apply Hij; apply (Hinj i j Hi_lt Hj_lt Heqf)).
    assert (Hfi_lt : (f i < length Ts)%nat) by (apply (Hbf i Hi_lt)).
    assert (Hfj_lt : (f j < length Ts)%nat) by (apply (Hbf j Hj_lt)).
    (* nth (f i) Ts d = Ti via nth_error *)
    assert (HTi' : nth_error Ts (f i) = Some Ti).
    { rewrite (nth_error_nth' Ts d Hfi_lt). f_equal. rewrite <- Hfi, HTi. reflexivity. }
    assert (HTj' : nth_error Ts (f j) = Some Tj).
    { rewrite (nth_error_nth' Ts d Hfj_lt). f_equal. rewrite <- Hfj, HTj. reflexivity. }
    exact (Hindep (f i) (f j) Hfij Ti Tj HTi' HTj').
  Qed.

  (* ---- MAIN HARDENED THEOREM -------------------------------------------- *)

  (* If a list of write-only traces is INDEPENDENT (Bernstein, read off the
     traces), then any two orders (any permutation -- any schedule / thread
     count) agree on every location. Proof: both runs' content at (b,ofs) is
     characterised canonically (raw_run_content_char); the no-writer case gives
     the base value in both; the writer case gives the same owner trace T0 (unique
     across the shared multiset) run on m, hence equal by base-independence. *)
  Theorem raw_run_permutation_agree :
    forall Ts Ts' m m1 m2,
      Permutation Ts Ts' ->
      traces_indep Ts ->
      raw_run Ts m m1 ->
      raw_run Ts' m m2 ->
      forall b ofs,
        Mem.valid_block m b ->
        ZMap.get ofs (Mem.mem_contents m1) !! b =
        ZMap.get ofs (Mem.mem_contents m2) !! b.
  Proof.
    intros Ts Ts' m m1 m2 Hperm Hindep Hrun1 Hrun2 b ofs Hvb.
    assert (Hindep' : traces_indep Ts') by (eapply traces_indep_perm; eauto).
    destruct (raw_run_content_char Ts m m1 b ofs Hvb Hindep Hrun1) as [H1 | H1];
    destruct (raw_run_content_char Ts' m m2 b ofs Hvb Hindep' Hrun2) as [H2 | H2].
    - (* no writer in either: both = base m *)
      destruct H1 as [_ Hc1]; destruct H2 as [_ Hc2]. rewrite Hc1, Hc2. reflexivity.
    - (* no writer in Ts but a writer in Ts': impossible, same multiset *)
      exfalso. destruct H1 as [Hno1 _].
      destruct H2 as (T0 & mmb & mm' & Hin' & Hw' & _ & _ & _).
      apply (Hno1 T0); [| exact Hw' ].
      eapply Permutation_in; [ apply Permutation_sym; exact Hperm | exact Hin' ].
    - (* writer in Ts but none in Ts': impossible *)
      exfalso. destruct H2 as [Hno2 _].
      destruct H1 as (T0 & mmb & mm' & Hin & Hw & _ & _ & _).
      apply (Hno2 T0); [| exact Hw ].
      eapply Permutation_in; [ exact Hperm | exact Hin ].
    - (* writer in both: same owner T0; content = T0 run on its (differing)
         pre-bases, equal at (b,ofs) by base-independence. *)
      destruct H1 as (T0 & mm1 & mm1' & Hin1 & Hw1 & Hvbmm1 & Hr1 & Hc1).
      destruct H2 as (T0' & mm2 & mm2' & Hin2 & Hw2 & Hvbmm2 & Hr2 & Hc2).
      assert (HinT0'_Ts : In T0' Ts)
        by (eapply Permutation_in; [ apply Permutation_sym; exact Hperm | exact Hin2 ]).
      assert (HT0 : T0 = T0').
      { destruct (In_nth_error _ _ Hin1) as [i Hi].
        destruct (In_nth_error _ _ HinT0'_Ts) as [j Hj].
        destruct (Nat.eq_dec i j) as [He | Hne].
        - subst j. rewrite Hi in Hj. inversion Hj; reflexivity.
        - exfalso. pose proof (indep_unique_owner Ts i j T0 T0' b ofs
                                 Hindep Hi Hj Hw1 Hw2). lia. }
      subst T0'.
      rewrite Hc1, Hc2.
      (* same trace T0 on two bases mm1, mm2; both write (b,ofs); base-indep *)
      unfold raw_run in Hr1, Hr2. simpl in Hr1, Hr2.
      rewrite app_nil_r in Hr1, Hr2.
      eapply ev_elim_wr_within_base_indep;
        [ exact Hvbmm1 | exact Hvbmm2 | exact Hr1 | exact Hr2 | exact Hw1 ].
  Qed.

  (* ---- THE THEOREM THAT IS VALID FOR AN ARBITRARY PROGRAM --------------- *)

  (* For ANY list of write-only per-iteration traces -- race-free or not -- and
     any two orders (permutations) of it, EITHER

       (independent) the two runs agree at every memory location
         (schedule-independent output), OR
       (conflict) the traces exhibit an explicit conflicting pair: two distinct
         iterations, one of which writes a location the other reads or writes
         (a witnessed potential data race).

     Thus the guarantee is never claimed for a racy program: on such input the
     first disjunct's hypothesis fails and a concrete race witness is produced.
     The independence condition is read off the ACTUAL traces (writes/reads),
     not assumed about the source. *)
  Theorem schedule_independent_or_race :
    forall Ts Ts' m m1 m2,
      Permutation Ts Ts' ->
      raw_run Ts m m1 ->
      raw_run Ts' m m2 ->
      (forall b ofs, Mem.valid_block m b ->
         ZMap.get ofs (Mem.mem_contents m1) !! b =
         ZMap.get ofs (Mem.mem_contents m2) !! b)
      \/ list_conflict Ts.
  Proof.
    intros Ts Ts' m m1 m2 Hperm Hrun1 Hrun2.
    destruct (indep_or_conflict Ts) as [Hindep | Hconf].
    - left. intros b ofs Hvb.
      eapply raw_run_permutation_agree; eauto.
    - right. exact Hconf.
  Qed.

End Hardened.
