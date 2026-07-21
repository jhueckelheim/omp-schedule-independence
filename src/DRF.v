(* Data-race-freedom of the maximally-parallel (1:1) schedule as an oracle.

   A companion result to the schedule-independence theorems. It concerns a
   DIFFERENT property -- preservation of data-race-freedom (DRF) across schedules
   -- rather than equality of results.

   Setting. A `parallel for` is modelled (as elsewhere here) by a list `Ts` of
   per-iteration memory-event traces, one per iteration, whose read/write sets are
   read off the traces (`reads`/`writes`, `conflict2` from HardenedConfluence.v).
   In the fragment these results target -- no synchronization and no per-thread
   state carried across iterations -- an iteration's memory footprint is a fixed
   function of the iteration index alone, so the set of CONFLICTING iteration pairs
   is a schedule-independent, purely combinatorial object.

   A SCHEDULE assigns each iteration (list position) to a thread. Iterations on
   the same thread are serialized (ordered, happens-before); iterations on
   different threads may run concurrently. So two distinct iterations i,j can race
   under a schedule iff they are placed on DIFFERENT threads AND their traces
   conflict. A schedule is data-race-free (DRF) iff no two concurrent iterations
   conflict.

   The MAXIMALLY-PARALLEL schedule S1 maps iteration i to thread i (num_threads =
   num_iterations, 1:1), so EVERY pair of distinct iterations is concurrent.

   Main results:
     - drf_S1_iff_no_conflict : S1 is DRF  <->  no conflicting pair exists
       (S1 exposes every pair, so its DRF is exactly global conflict-freedom).
     - no_conflict_all_drf    : no conflicting pair -> every schedule is DRF.
     - drf_S1_implies_all_drf : DRF under S1 -> DRF under every schedule.
       (The 1:1 schedule is a sound DRF oracle for the whole class.)
     - drf_S1_iff_traces_indep: DRF under S1 <-> the trace independence predicate
       used by the schedule-independence proof.

   SCOPE. This depends on footprints being fixed per iteration. It does NOT hold
   for programs with per-thread state carried across iterations (threadprivate,
   lastprivate, a private variable read before written such as a per-thread
   counter): there, S1 gives every iteration its own thread, so per-thread state
   never aliases across iterations and S1 HIDES exactly those races. Such
   constructs are outside the modelled fragment (see README / CLASS_EXTENSION_PLAN).

   Build (from a built ClightOMP checkout):
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/DRF.v
*)

Require Import ZArith.
Require Import List.
Require Import Coq.Logic.Classical_Prop.
Require Import VST.concurrency.openmp_sem.event_semantics.
Require Import VST.concurrency.openmp_sem.sched_indep.HardenedConfluence.

Section DRF.

  (* A schedule assigns each iteration index (a nat position in Ts) to a thread. *)
  Definition schedule := nat -> nat.

  (* The maximally-parallel 1:1 schedule: iteration i -> thread i. *)
  Definition S1 : schedule := fun i => i.

  (* Two distinct iterations run concurrently under [sched] iff they are on
     different threads. *)
  Definition concurrent (sched: schedule) (i j: nat) : Prop :=
    i <> j /\ sched i <> sched j.

  (* Data-race-freedom of a schedule: no two concurrent iterations conflict. *)
  Definition drf (sched: schedule) (Ts: list (list mem_event)) : Prop :=
    forall i j Ti Tj,
      concurrent sched i j ->
      nth_error Ts i = Some Ti ->
      nth_error Ts j = Some Tj ->
      ~ conflict2 Ti Tj.

  (* Under S1, distinct iterations are always concurrent (each on its own thread). *)
  Lemma S1_concurrent :
    forall i j, i <> j -> concurrent S1 i j.
  Proof. intros i j Hne. split; [ exact Hne | exact Hne ]. Qed.

  (* ---- S1 is DRF exactly when there is no conflicting pair at all --------- *)

  Theorem drf_S1_iff_no_conflict :
    forall Ts, drf S1 Ts <-> ~ list_conflict Ts.
  Proof.
    intros Ts. split.
    - (* drf S1 -> no conflict *)
      intros Hdrf [i [j [Ti [Tj (Hne & Hi & Hj & Hc)]]]].
      apply (Hdrf i j Ti Tj (S1_concurrent i j Hne) Hi Hj Hc).
    - (* no conflict -> drf S1 *)
      intros Hnc i j Ti Tj [Hne _] Hi Hj Hc.
      apply Hnc. exists i, j, Ti, Tj. repeat split; assumption.
  Qed.

  (* ---- no conflicting pair implies every schedule is DRF ------------------ *)

  Theorem no_conflict_all_drf :
    forall Ts, ~ list_conflict Ts -> forall sched, drf sched Ts.
  Proof.
    intros Ts Hnc sched i j Ti Tj [Hne _] Hi Hj Hc.
    apply Hnc. exists i, j, Ti, Tj. repeat split; assumption.
  Qed.

  (* ---- HEADLINE: DRF under the 1:1 schedule implies DRF under EVERY schedule *)

  Theorem drf_S1_implies_all_drf :
    forall Ts, drf S1 Ts -> forall sched, drf sched Ts.
  Proof.
    intros Ts Hdrf1.
    apply no_conflict_all_drf.
    apply (drf_S1_iff_no_conflict Ts). exact Hdrf1.
  Qed.

  (* Consequently, S1 is a SOUND ORACLE: to decide DRF for all schedules it
     suffices to check the single 1:1 schedule. (The converse direction --
     every schedule DRF implies S1 DRF -- is immediate since S1 is one of them.) *)
  Theorem drf_S1_iff_all_drf :
    forall Ts, drf S1 Ts <-> (forall sched, drf sched Ts).
  Proof.
    intros Ts. split.
    - apply drf_S1_implies_all_drf.
    - intros H. apply H.
  Qed.

  (* ---- connection to the schedule-independence proof's predicate ---------- *)

  (* DRF under S1 is exactly the trace-independence condition that drives the
     schedule-independence result: same class, viewed as "no races at maximal
     parallelism" vs "iterations are Bernstein-independent". *)
  Theorem drf_S1_iff_traces_indep :
    forall Ts, drf S1 Ts <-> traces_indep Ts.
  Proof.
    intros Ts. rewrite drf_S1_iff_no_conflict. split.
    - (* ~ list_conflict -> traces_indep *)
      intros Hnc i j Hne Ti Tj Hi Hj.
      destruct (indep_or_conflict2 Ti Tj) as [Hindep | Hconf]; [ exact Hindep |].
      exfalso. apply Hnc. exists i, j, Ti, Tj. repeat split; assumption.
    - (* traces_indep -> ~ list_conflict *)
      intros Hindep [i [j [Ti [Tj (Hne & Hi & Hj & Hc)]]]].
      destruct (Hindep i j Hne Ti Tj Hi Hj) as [Hww [Hrw Hwr]].
      destruct Hc as [ [b [ofs [H1 H2]]] | [ [b [ofs [H1 H2]]] | [b [ofs [H1 H2]]] ] ].
      + eapply Hww; eauto.
      + eapply Hrw; eauto.
      + eapply Hwr; eauto.
  Qed.

End DRF.
