(* Extending the 1:1 data-race-freedom oracle with EXEMPT locations.

   Companion to DRF.v. The plain oracle (DRF.v) rejects any loop with a
   write/write or read/write overlap across iterations. Two important families of
   such overlaps are nonetheless schedule-robust and should not be treated as
   races:

     B1. Associative-commutative REDUCTIONS: many iterations update the same
         location via an AC combiner (sum, max, histogram bump). The order does
         not affect the result (Reduction.v proves the AC-fold is
         permutation-invariant), so these overlaps are not genuine races.

     B3. Per-iteration FRESH allocations: a scratch buffer malloc'd and freed
         inside one iteration lives at a freshly-allocated block, disjoint from
         every other iteration's memory by construction, so it can never be a
         cross-iteration conflict.

   We capture both by an EXEMPT predicate on locations, and generalize the oracle
   to ignore conflicts whose witness location is exempt. Instantiating [exempt]
   with the reduction locations (B1) or the per-iteration-fresh locations (B3)
   recovers the two extensions; [exempt = nothing] recovers DRF.v exactly.

   As in DRF.v this is over the trace/footprint abstraction; [exempt] is supplied
   (e.g. by the instrumentation: reduction variables are declared, fresh blocks
   are those allocated within the iteration). The oracle argument is combinatorial
   over "which pairs are concurrent", so parameterizing the conflict notion by an
   exempt-location predicate is a routine generalization.

   Build (from a built ClightOMP checkout):
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/DRFExtended.v
*)

Require Import ZArith.
Require Import List.
Require Import Coq.Logic.Classical_Prop.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import VST.concurrency.openmp_sem.event_semantics.
Require Import VST.concurrency.openmp_sem.sched_indep.HardenedConfluence.
Require Import VST.concurrency.openmp_sem.sched_indep.DRF.

Section DRFExtended.

  (* Locations whose cross-iteration conflicts are exempt (do not count as races):
     e.g. AC-reduction variables (B1) or per-iteration fresh blocks (B3). *)
  Variable exempt : block -> Z -> Prop.

  (* A conflict that survives exemption: a real read/write or write/write overlap
     at a NON-exempt location. *)
  Definition conflict2_ex (T1 T2: list mem_event) : Prop :=
    (exists b ofs, ~ exempt b ofs /\ writes T1 b ofs /\ writes T2 b ofs) \/
    (exists b ofs, ~ exempt b ofs /\ reads  T1 b ofs /\ writes T2 b ofs) \/
    (exists b ofs, ~ exempt b ofs /\ reads  T2 b ofs /\ writes T1 b ofs).

  (* Data-race-freedom w.r.t. exempt conflicts. *)
  Definition drf_ex (sched: schedule) (Ts: list (list mem_event)) : Prop :=
    forall i j Ti Tj,
      concurrent sched i j ->
      nth_error Ts i = Some Ti ->
      nth_error Ts j = Some Tj ->
      ~ conflict2_ex Ti Tj.

  (* A surviving conflict somewhere in the list. *)
  Definition list_conflict_ex (Ts: list (list mem_event)) : Prop :=
    exists i j Ti Tj, i <> j /\
      nth_error Ts i = Some Ti /\ nth_error Ts j = Some Tj /\ conflict2_ex Ti Tj.

  (* ---- the oracle chain, generalized ------------------------------------- *)

  Theorem drf_ex_S1_iff_no_conflict :
    forall Ts, drf_ex S1 Ts <-> ~ list_conflict_ex Ts.
  Proof.
    intros Ts. split.
    - intros Hdrf [i [j [Ti [Tj (Hne & Hi & Hj & Hc)]]]].
      apply (Hdrf i j Ti Tj (S1_concurrent i j Hne) Hi Hj Hc).
    - intros Hnc i j Ti Tj [Hne _] Hi Hj Hc.
      apply Hnc. exists i, j, Ti, Tj. repeat split; assumption.
  Qed.

  Theorem no_conflict_ex_all_drf :
    forall Ts, ~ list_conflict_ex Ts -> forall sched, drf_ex sched Ts.
  Proof.
    intros Ts Hnc sched i j Ti Tj [Hne _] Hi Hj Hc.
    apply Hnc. exists i, j, Ti, Tj. repeat split; assumption.
  Qed.

  (* HEADLINE (extended): data-race-freedom (modulo exempt locations) under the
     1:1 schedule implies it under every schedule. *)
  Theorem drf_ex_S1_implies_all_drf :
    forall Ts, drf_ex S1 Ts -> forall sched, drf_ex sched Ts.
  Proof.
    intros Ts Hdrf1.
    apply no_conflict_ex_all_drf.
    apply (drf_ex_S1_iff_no_conflict Ts). exact Hdrf1.
  Qed.

  Theorem drf_ex_S1_iff_all_drf :
    forall Ts, drf_ex S1 Ts <-> (forall sched, drf_ex sched Ts).
  Proof.
    intros Ts. split.
    - apply drf_ex_S1_implies_all_drf.
    - intros H. apply H.
  Qed.

End DRFExtended.

(* ---- Recovering DRF.v: empty exemption = the plain oracle ---------------- *)

Section NoExemption.

  Definition no_exempt : block -> Z -> Prop := fun _ _ => False.

  (* With nothing exempt, conflict2_ex coincides with conflict2. *)
  Lemma conflict2_ex_no_exempt :
    forall T1 T2, conflict2_ex no_exempt T1 T2 <-> conflict2 T1 T2.
  Proof.
    intros T1 T2. unfold conflict2_ex, conflict2, no_exempt. split.
    - intros [ [b [ofs (_ & H1 & H2)]]
             | [ [b [ofs (_ & H1 & H2)]]
               | [b [ofs (_ & H1 & H2)]] ] ].
      + left; exists b, ofs; auto.
      + right; left; exists b, ofs; auto.
      + right; right; exists b, ofs; auto.
    - intros [ [b [ofs (H1 & H2)]]
             | [ [b [ofs (H1 & H2)]]
               | [b [ofs (H1 & H2)]] ] ].
      + left; exists b, ofs; repeat split; auto.
      + right; left; exists b, ofs; repeat split; auto.
      + right; right; exists b, ofs; repeat split; auto.
  Qed.

  (* Hence the extended oracle with no exemption is exactly the DRF.v oracle. *)
  Theorem drf_ex_no_exempt_is_drf :
    forall sched Ts, drf_ex no_exempt sched Ts <-> drf sched Ts.
  Proof.
    intros sched Ts. unfold drf_ex, drf. split;
      intros H i j Ti Tj Hc Hi Hj Hcf; eapply H; eauto;
      apply conflict2_ex_no_exempt; assumption.
  Qed.

End NoExemption.

(* ---- B1: associative-commutative reduction locations are exempt ---------- *)

Section ReductionExempt.

  (* A caller-supplied set of REDUCTION locations: locations updated only through
     a registered associative-commutative combiner (sum, max, ...). By Reduction.v
     the final value at such a location is permutation-invariant, so cross-
     iteration overlaps there are not genuine races. We take the set of reduction
     locations as [red_locs] and exempt them. *)
  Variable red_locs : block -> Z -> Prop.

  (* The extended oracle, specialized to reduction exemption: if the loop is
     data-race-free EXCEPT on reduction variables under the 1:1 schedule, it is so
     under every schedule. Non-reduction conflicts are still caught. *)
  Theorem reduction_drf_S1_implies_all :
    forall Ts, drf_ex red_locs S1 Ts -> forall sched, drf_ex red_locs sched Ts.
  Proof. apply drf_ex_S1_implies_all_drf. Qed.

  (* Concrete soundness of the reduction exemption. Suppose every cross-iteration
     conflict happens ONLY at reduction locations -- i.e. all shared writes hit
     red_locs (the loop is a pure reduction on those variables, with the rest
     independent). Then no surviving (non-reduction) conflict exists, so the loop
     is data-race-free modulo the reductions, on every schedule. The order-
     independence of the reduced VALUE is the separate, already-proven fact
     Reduction.ac_fold_permutation_invariant; it justifies treating those write/
     write overlaps as non-races here. *)

  (* Every write of every iteration lands on a reduction location. *)
  Definition writes_only_reductions (Ts: list (list mem_event)) : Prop :=
    forall i Ti b ofs,
      nth_error Ts i = Some Ti -> writes Ti b ofs -> red_locs b ofs.

  (* Then there is no surviving conflict: every conflict witness is a write to a
     reduction location, hence exempt. *)
  Lemma reduction_no_surviving_conflict :
    forall Ts i j Ti Tj,
      writes_only_reductions Ts ->
      nth_error Ts i = Some Ti -> nth_error Ts j = Some Tj ->
      ~ conflict2_ex red_locs Ti Tj.
  Proof.
    intros Ts i j Ti Tj Hwr Hi Hj Hc.
    destruct Hc as [ [b [ofs (Hnx & H1 & H2)]]
                   | [ [b [ofs (Hnx & H1 & H2)]]
                     | [b [ofs (Hnx & H1 & H2)]] ] ].
    - (* write/write: the (b,ofs) is a reduction loc via either write *)
      apply Hnx. eapply Hwr; [ exact Hi | exact H1 ].
    - (* read Ti / write Tj: write is on Tj, a reduction loc *)
      apply Hnx. eapply Hwr; [ exact Hj | exact H2 ].
    - (* read Tj / write Ti: write is on Ti, a reduction loc *)
      apply Hnx. eapply Hwr; [ exact Hi | exact H2 ].
  Qed.

  (* Hence a pure-reduction loop is data-race-free (modulo reductions) under every
     schedule -- trivially, since there is no surviving conflict at all. *)
  Theorem reduction_pure_all_drf :
    forall Ts, writes_only_reductions Ts -> forall sched, drf_ex red_locs sched Ts.
  Proof.
    intros Ts Hwr sched i j Ti Tj Hc Hi Hj.
    eapply reduction_no_surviving_conflict; eauto.
  Qed.

End ReductionExempt.

(* ---- B3: per-iteration fresh allocations are exempt ---------------------- *)

Section FreshExempt.

  (* [preexisting b] holds for blocks that existed before the loop (the shared,
     observable memory). A per-iteration scratch buffer is allocated INSIDE the
     iteration, so its block is not preexisting; such locations can never be a
     cross-iteration conflict and are safely exempt. We exempt everything that is
     NOT preexisting. *)
  Variable preexisting : block -> Prop.

  Definition fresh_exempt : block -> Z -> Prop :=
    fun b _ => ~ preexisting b.

  (* The extended oracle, specialized to fresh-allocation exemption: checking
     data-race-freedom on PRE-EXISTING memory under the 1:1 schedule suffices for
     every schedule. Iteration-local scratch is ignored (correctly: distinct
     iterations' fresh blocks are distinct, so they never conflict). *)
  Theorem fresh_drf_S1_implies_all :
    forall Ts, drf_ex fresh_exempt S1 Ts -> forall sched, drf_ex fresh_exempt sched Ts.
  Proof. apply drf_ex_S1_implies_all_drf. Qed.

  (* Soundness of fresh exemption, made concrete. The freshness fact -- distinct
     iterations never share a non-preexisting block -- is captured by the
     hypothesis [fresh_disjoint]: whenever two distinct iterations both access a
     block b, that block is preexisting. (This is exactly what Mem.alloc's
     nextblock-freshness guarantees; see EvElimFrame.alloc_contents_other.) Under
     it, EXEMPTING non-preexisting blocks loses nothing: every real cross-
     iteration conflict is already at a preexisting (non-exempt) location, so
     conflict2_ex fresh_exempt = conflict2 on the pairs that matter. *)

  (* An iteration accesses (reads or writes) a location. *)
  Definition accesses (T: list mem_event) (b: block) (ofs: Z) : Prop :=
    reads T b ofs \/ writes T b ofs.

  (* Freshness: any block touched by two distinct iterations is preexisting
     (their fresh blocks are private, so cannot coincide). *)
  Definition fresh_disjoint (Ts: list (list mem_event)) : Prop :=
    forall i j Ti Tj b ofs ofs',
      i <> j ->
      nth_error Ts i = Some Ti -> nth_error Ts j = Some Tj ->
      accesses Ti b ofs -> accesses Tj b ofs' -> preexisting b.

  (* Under freshness, a surviving (non-exempt) conflict is exactly a plain
     conflict: fresh exemption never hides a real cross-iteration conflict. *)
  Lemma fresh_conflict_ex_iff_conflict :
    forall Ts i j Ti Tj,
      fresh_disjoint Ts ->
      i <> j ->
      nth_error Ts i = Some Ti -> nth_error Ts j = Some Tj ->
      (conflict2_ex fresh_exempt Ti Tj <-> conflict2 Ti Tj).
  Proof.
    intros Ts i j Ti Tj Hfd Hne Hi Hj. split.
    - (* conflict2_ex -> conflict2: drop the exemption side condition *)
      intros [ [b [ofs (_ & H1 & H2)]]
             | [ [b [ofs (_ & H1 & H2)]]
               | [b [ofs (_ & H1 & H2)]] ] ].
      + left; exists b, ofs; auto.
      + right; left; exists b, ofs; auto.
      + right; right; exists b, ofs; auto.
    - (* conflict2 -> conflict2_ex: the witness block is preexisting (both
         iterations access it), hence not fresh-exempt *)
      intros [ [b [ofs (H1 & H2)]]
             | [ [b [ofs (H1 & H2)]]
               | [b [ofs (H1 & H2)]] ] ].
      + left; exists b, ofs. split; [| auto].
        unfold fresh_exempt. intro Hnp. apply Hnp.
        eapply (Hfd i j Ti Tj b ofs ofs Hne Hi Hj); [ right; exact H1 | right; exact H2 ].
      + right; left; exists b, ofs. split; [| auto].
        unfold fresh_exempt. intro Hnp. apply Hnp.
        eapply (Hfd i j Ti Tj b ofs ofs Hne Hi Hj); [ left; exact H1 | right; exact H2 ].
      + right; right; exists b, ofs. split; [| auto].
        unfold fresh_exempt. intro Hnp. apply Hnp.
        (* H1 : reads Tj b ofs, H2 : writes Ti b ofs; Ti accesses b (write),
           Tj accesses b (read) *)
        eapply (Hfd i j Ti Tj b ofs ofs Hne Hi Hj); [ right; exact H2 | left; exact H1 ].
  Qed.

  (* Consequently, under freshness, checking DRF-with-fresh-exemption on the 1:1
     schedule is the same as checking plain DRF -- so the fresh exemption is
     SOUND: it certifies the genuine data-race-freedom of shared memory while
     ignoring only the provably-private scratch. *)
  Theorem fresh_drf_ex_sound :
    forall Ts,
      fresh_disjoint Ts ->
      drf_ex fresh_exempt S1 Ts <-> drf S1 Ts.
  Proof.
    intros Ts Hfd. unfold drf_ex, drf. split.
    - intros H i j Ti Tj Hc Hi Hj Hcf.
      eapply H; eauto.
      apply (fresh_conflict_ex_iff_conflict Ts i j Ti Tj Hfd (proj1 Hc) Hi Hj).
      exact Hcf.
    - intros H i j Ti Tj Hc Hi Hj Hcf.
      eapply H; eauto.
      apply (fresh_conflict_ex_iff_conflict Ts i j Ti Tj Hfd (proj1 Hc) Hi Hj).
      exact Hcf.
  Qed.

End FreshExempt.
