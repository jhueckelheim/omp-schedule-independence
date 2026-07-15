(* Schedule-independence development, step 7: multi-step lift (theorem T0 for a
   whole run).

   Ostep_refl_trans_closure (HybridMachine.v:1047) is clos_refl_trans_1n over
   Ostep. We show that a run in which every step preserves observable memory
   contents on a footprint preserves those contents end-to-end. Combined with
   OstepFraming.Ostep_read_only_obs_equiv (each pure-class Ostep preserves
   contents), this yields: a whole read-only / pure-class run -- under ANY
   schedule -- leaves the observable output unchanged.

   Because Ostep is driven by the schedule (the head of U), and the run lemma
   quantifies over ALL runs (hence all schedules and, via step_parallel's choice
   of num_threads, all thread counts), this is theorem T0: the pure class is
   schedule- and thread-count-independent at the level of observable memory.

   Build (upstream untouched), from the ClightOMP root:
     eval $(opam env --switch=ClightOMP)
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/OstepRun.v
*)

Require Import Coq.Relations.Relation_Operators.
From compcert Require Import cfrontend.Clight.
Require Import compcert.common.Memory.
Require Import VST.concurrency.openmp_sem.event_semantics.
Require Import VST.concurrency.openmp_sem.finThreadPool.
Require Import VST.concurrency.openmp_sem.HybridMachineSig.
Require Import VST.concurrency.openmp_sem.HybridMachine.
Require Import VST.concurrency.openmp_sem.sched_indep.ObsEquiv.
Require Import VST.concurrency.openmp_sem.sched_indep.StepFraming.
Require Import VST.concurrency.openmp_sem.sched_indep.OstepFraming.

Import DryHybridMachine.

Section OstepRun.

  Context {ge : genv}.
  Context {tpool : @finThreadPool.ThreadPool.ThreadPool dryResources (@Sem ge)}.

  (* A single Ostep that preserves observable contents on [foot]. This is the
     per-step guarantee established for pure-class steps by
     OstepFraming.Ostep_read_only_obs_equiv. *)
  Definition preserving_ostep (foot : footprint) (os os' : Ostate) : Prop :=
    @Ostep ge tpool os os' /\ obs_equiv foot (snd os') (snd os).

  (* The reflexive-transitive closure of preserving steps. A "pure-class run". *)
  Definition preserving_run (foot : footprint) : Ostate -> Ostate -> Prop :=
    clos_refl_trans_1n Ostate (preserving_ostep foot).

  (* Any preserving step is in particular an Ostep. *)
  Lemma preserving_ostep_is_ostep :
    forall foot os os', preserving_ostep foot os os' -> @Ostep ge tpool os os'.
  Proof. intros ??? [H _]; exact H. Qed.

  (* MAIN (T0, multi-step): a whole preserving run leaves observable contents
     unchanged from start to finish. Proof by induction on the closure, chaining
     the per-step guarantees with transitivity of obs_equiv. *)
  Theorem preserving_run_obs_equiv :
    forall (foot : footprint) (os os' : Ostate),
      preserving_run foot os os' ->
      obs_equiv foot (snd os') (snd os).
  Proof.
    intros foot os os' Hrun.
    unfold preserving_run in Hrun.
    induction Hrun as [ os | os oy oz Hstep Hrun IH ].
    - (* refl: no steps, contents trivially equal *)
      reflexivity.
    - (* trans: os --Hstep--> oy --Hrun--> oz *)
      destruct Hstep as [Hostep Hpres].
      (* IH : obs_equiv foot (snd oz) (snd oy)
         Hpres : obs_equiv foot (snd oy) (snd os)
         goal : obs_equiv foot (snd oz) (snd os) *)
      transitivity (snd oy); [ exact IH | exact Hpres ].
  Qed.

  (* Per-state pure-class side conditions: from this state's memory, every Ostep
     is a read-only internal thread step -- i.e. all threadStep traces are
     read-only, and no start/sync/pragma step is possible. This is what a pure
     loop body guarantees at each program point of the parallel region. *)
  Definition pure_state (os : Ostate) : Prop :=
    let '(U, tr, tp, ttree, m) := os in
    (forall tid Htid Hcmpt tpx mx ev,
        @threadStep ge tpool tid tp m Htid Hcmpt tpx mx ev ->
        read_only_trace ev) /\
    (forall tid (Htid : finThreadPool.ThreadPool.containsThread tp tid) tpx mx,
        ~ @HybridMachineSig.start_thread dryResources (@Sem ge) tpool
            DryHybridMachineSig m tid tp Htid tpx mx) /\
    (forall tid (Htid : finThreadPool.ThreadPool.containsThread tp tid)
        (Hc : mem_compatible tp m) tpx mx ev,
        ~ @HybridMachineSig.syncStep dryResources (@Sem ge) tpool
            DryHybridMachineSig true tid tp m Htid Hc tpx mx ev) /\
    (forall tid (Htid : finThreadPool.ThreadPool.containsThread tp tid)
        (Hc : mem_compatible tp m) tpx mx ttx trx,
        ~ @HybridMachineSig.pragmaStep dryResources (@Sem ge) tpool
            DryHybridMachineSig tid tp m ttree Htid Hc tpx mx ttx trx).

  (* BRIDGE: a single Ostep out of a pure state is a preserving step.
     This is where OstepFraming.Ostep_read_only_obs_equiv is applied. *)
  Lemma pure_ostep_preserving :
    forall (foot : footprint) (os os' : Ostate),
      pure_state os ->
      @Ostep ge tpool os os' ->
      preserving_ostep foot os os'.
  Proof.
    intros foot os os' Hpure Hstep.
    destruct os as [[[[U tr] tp] ttree] m].
    destruct os' as [[[[U' tr'] tp'] ttree'] m'].
    destruct Hpure as (Hro & Hnostart & Hnosync & Hnopragma).
    split; [ exact Hstep |].
    simpl.
    eapply (Ostep_read_only_obs_equiv foot U tr tp ttree m U' tr' tp' ttree' m');
      eauto.
  Qed.

  (* A run whose every intermediate state is pure is a preserving run.
     [all_pure_run] threads pure_state through the raw Ostep closure. *)
  Inductive all_pure_run (foot : footprint) : Ostate -> Ostate -> Prop :=
  | apr_refl : forall os, all_pure_run foot os os
  | apr_step : forall os oy oz,
      pure_state os ->
      @Ostep ge tpool os oy ->
      all_pure_run foot oy oz ->
      all_pure_run foot os oz.

  Lemma all_pure_run_is_preserving_run :
    forall foot os os',
      all_pure_run foot os os' ->
      preserving_run foot os os'.
  Proof.
    intros foot os os' Hrun.
    induction Hrun as [ os | os oy oz Hpure Hstep Hrun IH ].
    - apply rt1n_refl.
    - eapply rt1n_trans; [ | exact IH ].
      apply pure_ostep_preserving; assumption.
  Qed.

  (* HEADLINE (T0): a pure-class run -- built from raw Ostep steps, each out of a
     pure state -- leaves the observable output unchanged, for EVERY schedule
     (the schedule is the head of U, quantified over by "for all runs") and every
     thread count. The pure class is schedule- and thread-count-independent. *)
  Theorem pure_run_obs_equiv :
    forall (foot : footprint) (os os' : Ostate),
      all_pure_run foot os os' ->
      obs_equiv foot (snd os') (snd os).
  Proof.
    intros foot os os' Hrun.
    apply preserving_run_obs_equiv.
    apply all_pure_run_is_preserving_run.
    exact Hrun.
  Qed.

End OstepRun.
