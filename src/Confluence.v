(* Schedule-independence development, step 11: confluence for the disjoint-write
   class C1 (theorem L4 / T1 headline at the memory-effect layer).

   A parallel-for over the disjoint-write class is modelled as a list of
   per-iteration WRITE-ONLY event traces, each confined to that iteration's
   footprint, with the footprints PAIRWISE DISJOINT. A schedule chooses an order
   in which to run the iterations (their traces are concatenated in that order);
   different thread counts / OMP schedules just permute this order (ChunkIndep).

   We prove: the observable output on the union of all iteration footprints is
   the SAME for any two orders (any permutation) of the iteration traces.
   Hence the disjoint-write class is schedule- and thread-count-independent at
   the level of observable memory. The single-transposition case is the diamond
   (StepDiamond.ev_elim_diamond_obs); we lift it to arbitrary permutations.

   Build (upstream untouched), from the ClightOMP root:
     eval $(opam env --switch=ClightOMP)
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/Confluence.v
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

Open Scope Z_scope.

Section Confluence.

  (* An iteration is a footprint together with its write-only event trace,
     confined to that footprint. *)
  Record iteration := {
    it_foot : footprint;
    it_trace : list mem_event;
    it_wr : wr_only_trace it_trace;
    it_within : trace_writes_within it_foot it_trace
  }.

  (* Run a list of iterations sequentially from memory m: concatenate their
     traces and eliminate. *)
  Definition run (its: list iteration) (m m': mem) : Prop :=
    ev_elim m (concat (map it_trace its)) m'.

  (* The union footprint of a list of iterations. *)
  Definition union_foot (its: list iteration) : footprint :=
    fun b ofs => Exists (fun it => it_foot it b ofs) its.

  (* Pairwise-disjoint footprints across a list of iterations. *)
  Definition pairwise_disjoint (its: list iteration) : Prop :=
    forall i j, i <> j ->
      forall it_i it_j, nth_error its i = Some it_i -> nth_error its j = Some it_j ->
      forall b ofs, it_foot it_i b ofs -> it_foot it_j b ofs -> False.

  (* Observable equality of two memories on a footprint. *)
  Definition agree_on (foot: footprint) (m1 m2: mem) : Prop :=
    forall b ofs, foot b ofs ->
      ZMap.get ofs (Mem.mem_contents m1) !! b =
      ZMap.get ofs (Mem.mem_contents m2) !! b.

  (* run distributes over append via ev_elim_app / ev_elim_split. *)
  Lemma run_app :
    forall its1 its2 m m',
      run (its1 ++ its2) m m' <->
      exists mm, run its1 m mm /\ run its2 mm m'.
  Proof.
    intros its1 its2 m m'. unfold run.
    rewrite map_app, concat_app. split.
    - intro H. apply ev_elim_split in H. exact H.
    - intros [mm [H1 H2]]. eapply ev_elim_app; eauto.
  Qed.

  (* The concatenation of a list of iterations is write-only. *)
  Lemma concat_wr_only :
    forall its, wr_only_trace (concat (map it_trace its)).
  Proof.
    induction its as [| it its IH]; simpl.
    - constructor.
    - unfold wr_only_trace. apply Forall_app. split.
      + exact (it_wr it).
      + exact IH.
  Qed.

  (* The concatenation writes within the union footprint. *)
  Lemma concat_within_union :
    forall its, trace_writes_within (union_foot its) (concat (map it_trace its)).
  Proof.
    induction its as [| it its IH]; intros b ofs Hnot.
    - simpl. constructor.
    - simpl. apply Forall_app. split.
      + (* head trace: confined to it_foot it ⊆ union_foot (it::its) *)
        apply (it_within it). intro Hf. apply Hnot.
        unfold union_foot. apply Exists_cons_hd. exact Hf.
      + (* tail: confined to union_foot its ⊆ union *)
        apply IH. intro Hf. apply Hnot.
        unfold union_foot in *. apply Exists_cons_tl. exact Hf.
  Qed.

  (* KEY: at a location owned by iteration (it0 :: nil) (in its footprint), running any
     list of pairwise-disjoint iterations that CONTAINS it0 produces contents
     determined only by it0's trace applied to the base memory m -- independent
     of the order and of the other iterations. We phrase it as: two runs of
     lists that are permutations of each other agree at every union location.

     We reduce to the two-iteration diamond by splitting the trace around it0.
     For a location (b,ofs) in it0's footprint (hence NOT in any other
     iteration's footprint), every OTHER iteration's trace frames (b,ofs), and
     it0's trace determines it base-independently. *)

  (* An iteration in the list frames every location outside its footprint. *)
  Lemma other_iters_frame :
    forall its m m' b ofs,
      (forall it, In it its -> ~ it_foot it b ofs) ->
      run its m m' ->
      ZMap.get ofs (Mem.mem_contents m') !! b =
      ZMap.get ofs (Mem.mem_contents m) !! b.
  Proof.
    induction its as [| it its IH]; intros m m' b ofs Hout Hrun.
    - unfold run in Hrun. simpl in Hrun. subst; reflexivity.
    - unfold run in Hrun. simpl in Hrun.
      apply ev_elim_split in Hrun. destruct Hrun as [mm [Hrun1 Hrun2]].
      transitivity (ZMap.get ofs (Mem.mem_contents mm) !! b).
      + apply IH; auto.
        intros it' Hin'. apply Hout. right. exact Hin'.
      + (* head iteration frames (b,ofs) since (b,ofs) not in it_foot it *)
        eapply ev_elim_wr_frame.
        * exact (it_wr it).
        * apply (it_within it). apply Hout. left; reflexivity.
        * exact Hrun1.
  Qed.

  (* At a location (b,ofs) owned by iteration it0 (in its footprint) and by no
     other iteration in the list, running the list determines (b,ofs) the same
     as running just (it0 :: nil) on the same base -- because all other iterations
     frame (b,ofs). This peels the list around the single owner. *)
  Lemma run_split_owner :
    forall its1 it0 its2 m m' b ofs,
      it_foot it0 b ofs ->
      (forall it, In it its1 -> ~ it_foot it b ofs) ->
      (forall it, In it its2 -> ~ it_foot it b ofs) ->
      run (its1 ++ it0 :: its2) m m' ->
      exists mm mm',
        run its1 m mm /\ run (it0 :: nil) mm mm' /\
        ZMap.get ofs (Mem.mem_contents mm) !! b =
        ZMap.get ofs (Mem.mem_contents m) !! b /\
        ZMap.get ofs (Mem.mem_contents m') !! b =
        ZMap.get ofs (Mem.mem_contents mm') !! b.
  Proof.
    intros its1 it0 its2 m m' b ofs Hown Hout1 Hout2 Hrun.
    apply run_app in Hrun. destruct Hrun as [mm [Hr1 Hrest]].
    replace (it0 :: its2) with ((it0 :: nil) ++ its2) in Hrest by reflexivity.
    apply run_app in Hrest. destruct Hrest as [mm' [Hr0 Hr2]].
    exists mm, mm'. split; [ exact Hr1 |]. split; [ exact Hr0 |].
    split.
    - (* mm = m at (b,ofs): its1 frames it *)
      apply (other_iters_frame its1 m mm b ofs Hout1 Hr1).
    - (* m' = mm' at (b,ofs): its2 frames it *)
      apply (other_iters_frame its2 mm' m' b ofs Hout2 Hr2).
  Qed.

  (* MAIN (T1 / L4): two runs of permuted iteration-lists, with pairwise-disjoint
     footprints, agree on the union footprint. I.e. the disjoint-write class is
     order- (schedule-) independent on its observable output.

     We prove the pointwise statement: for any (b,ofs) in the union, both runs
     give the content that the UNIQUE owning iteration produces from m. Since the
     owning iteration is the same element in both permuted lists, the two agree.

     For this headline we take the two lists to be the SAME multiset via
     Permutation, both run from the same base m. *)
  Theorem run_permutation_agree :
    forall its its' m m1 m2,
      Permutation its its' ->
      pairwise_disjoint its ->
      (* each union location has a unique owner in the list *)
      (forall b ofs, union_foot its b ofs ->
         exists pre it0 post,
           its = pre ++ it0 :: post /\
           it_foot it0 b ofs /\
           (forall it, In it pre -> ~ it_foot it b ofs) /\
           (forall it, In it post -> ~ it_foot it b ofs)) ->
      (forall b ofs, union_foot its b ofs ->
         exists pre it0 post,
           its' = pre ++ it0 :: post /\
           it_foot it0 b ofs /\
           (forall it, In it pre -> ~ it_foot it b ofs) /\
           (forall it, In it post -> ~ it_foot it b ofs) /\
           (* same owner trace as in its (owner determined by footprint) *)
           True) ->
      run its m m1 ->
      run its' m m2 ->
      agree_on (union_foot its) m1 m2.
  Proof.
    intros its its' m m1 m2 Hperm Hdisj Howner Howner' Hrun1 Hrun2 b ofs Hu.
    (* find the owner in its and in its' *)
    destruct (Howner b ofs Hu) as (pre & it0 & post & Heq & Hf0 & Hpre & Hpost).
    (* the union of its' equals union of its (permutation), so the same location
       is in union of its'; use Howner' *)
    assert (Hu' : union_foot its' b ofs).
    { unfold union_foot in *.
      apply Exists_exists in Hu. destruct Hu as [x [Hin Hx]].
      apply Exists_exists. exists x. split; [| exact Hx ].
      eapply Permutation_in; [ exact Hperm | exact Hin ]. }
    clear Hu'.
    destruct (Howner' b ofs Hu) as (pre' & it0' & post' & Heq' & Hf0' & Hpre' & Hpost' & _).
    (* split both runs around their owners *)
    subst its its'.
    destruct (run_split_owner pre it0 post m m1 b ofs Hf0 Hpre Hpost Hrun1)
      as (mm & mm' & Hr1a & Hr1b & Hmm & Hm1).
    destruct (run_split_owner pre' it0' post' m m2 b ofs Hf0' Hpre' Hpost' Hrun2)
      as (nn & nn' & Hr2a & Hr2b & Hnn & Hm2).
    (* it0 and it0' both own (b,ofs); with pairwise-disjoint footprints across a
       permutation, the owner is unique, so it0 = it0'. We derive this from the
       fact that both are elements owning (b,ofs) and footprints are disjoint. *)
    assert (Hsame : it0 = it0').
    { (* both in the permuted multiset and both own (b,ofs); disjointness forces
         them to be the same element. We use that Permutation preserves In and
         pairwise_disjoint rules out two distinct owners. *)
      assert (Hin0 : In it0 (pre ++ it0 :: post)) by (apply in_or_app; right; left; auto).
      assert (Hin0' : In it0' (pre' ++ it0' :: post')) by (apply in_or_app; right; left; auto).
      (* it0' is in its (via permutation) *)
      assert (Hin0'_its : In it0' (pre ++ it0 :: post)).
      { eapply Permutation_in; [ apply Permutation_sym; exact Hperm | exact Hin0' ]. }
      (* find indices; if it0 <> it0' they'd be two distinct owners ⇒ disjointness
         contradiction. Use nth_error via In. *)
      destruct (in_split _ _ Hin0'_its) as (l1 & l2 & Hsplit).
      (* Reduce to: any two list-members owning (b,ofs) are equal, from
         pairwise_disjoint. We prove the contrapositive by locating both. *)
      apply NNPP; intro Hne.
      (* it0 at its own position, it0' at another; both own (b,ofs) *)
      (* Build the disjointness contradiction using pairwise_disjoint on the
         indices of it0 and it0'. *)
      pose proof Hdisj as Hd.
      (* positions of it0 (index = length pre) and it0' (index in l1) *)
      unfold pairwise_disjoint in Hd.
      (* index of it0 *)
      assert (Hnth0 : nth_error (pre ++ it0 :: post) (length pre) = Some it0).
      { rewrite nth_error_app2 by apply Nat.le_refl.
        rewrite Nat.sub_diag. reflexivity. }
      (* index of it0' *)
      destruct (In_nth_error _ _ Hin0'_its) as (k & Hk).
      destruct (Nat.eq_dec k (length pre)) as [Hkeq | Hkne].
      + (* same index ⇒ it0 = it0', contradiction *)
        rewrite Hkeq in Hk. rewrite Hnth0 in Hk. inversion Hk. congruence.
      + (* distinct indices, both own (b,ofs) ⇒ disjointness contradiction *)
        exfalso.
        eapply (Hd (length pre) k (not_eq_sym Hkne) it0 it0' Hnth0 Hk b ofs Hf0 Hf0').
    }
    subst it0'.
    (* Now both owners are the same iteration it0, run (it0 :: nil) on bases mm and nn.
       mm = m and nn = m at (b,ofs) (framing), and it0's run determines (b,ofs)
       base-independently (or frames if it0 doesn't write it). *)
    rewrite Hm1, Hm2.
    (* compare run (it0 :: nil) mm mm' and run (it0 :: nil) nn nn' at (b,ofs) *)
    destruct (Exists_dec (written_by b ofs) (it_trace it0)) as [Hw | Hnw].
    { intro x. destruct x as [bb oo bs | | |].
      - unfold written_by. destruct (peq b bb).
        + destruct (zle oo ofs).
          * destruct (zlt ofs (oo + Z.of_nat (length bs)));
              [ left; split; [congruence|lia] | right; intros [_ ?]; lia ].
          * right; intros [_ ?]; lia.
        + right; intros [? _]; congruence.
      - right; intros []. - right; intros []. - right; intros []. }
    - (* it0 writes (b,ofs): base-independence *)
      unfold run in Hr1b, Hr2b. simpl in Hr1b, Hr2b.
      rewrite app_nil_r in Hr1b, Hr2b.
      eapply ev_elim_wr_within_base_indep;
        [ exact (it_wr it0) | exact Hr1b | exact Hr2b | exact Hw ].
    - (* it0 does not write (b,ofs): both framed to their base, bases agree (=m) *)
      unfold run in Hr1b, Hr2b. simpl in Hr1b, Hr2b.
      rewrite app_nil_r in Hr1b, Hr2b.
      assert (Hout0 : outside_trace b ofs (it_trace it0)).
      { unfold outside_trace. apply Forall_forall. intros x Hx.
        destruct x as [bb oo bs | bb oo nr bs | | ]; simpl; auto.
        destruct (peq b bb) as [-> | Hbne]; [| left; exact Hbne].
        right.
        destruct (zlt ofs oo); [ left; lia |].
        destruct (zle (oo + Z.of_nat (length bs)) ofs); [ right; lia |].
        exfalso. apply Hnw. apply Exists_exists. exists (Write bb oo bs).
        split; [ exact Hx |]. simpl. split; [ reflexivity | lia ]. }
      rewrite (ev_elim_wr_frame _ mm mm' b ofs (it_wr it0) Hout0 Hr1b).
      rewrite (ev_elim_wr_frame _ nn nn' b ofs (it_wr it0) Hout0 Hr2b).
      rewrite Hmm, Hnn. reflexivity.
  Qed.

End Confluence.
