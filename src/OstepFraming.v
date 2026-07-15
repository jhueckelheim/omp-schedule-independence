(* Schedule-independence development, step 6: lifting read-only framing to the
   top-level machine step Ostep.

   Ostep (HybridMachine.v:1045) is the coarse-machine step over
     Ostate = (MachState * mem),  MachState = (schedule * event_trace * t * team_tree).
   For the COARSE machine diluteMem = id and yield = id (HybridMachineSig.v:727-732),
   and threadStep = dry_step (HybridMachine.v:592).

   We prove theorem T0 at the schedule/thread-pool level by CASE ANALYSIS on an
   actual Ostep: for every way the machine can take one step, if that step does
   not perform a shared write, the observable memory contents are preserved on
   every footprint. Concretely:
     - resume / suspend / suspend_pragma / halted / schedfail steps do not change
       memory at all (obs_equiv is reflexivity);
     - the internal thread_step case is discharged by DryStepFraming when its
       emitted event trace is read-only (the pure-iteration case);
     - start_thread / sync_step / pragma_step CAN change memory and are the cases
       the pure class excludes; we require a hypothesis ruling them out.

   This gives an honest one-step preservation theorem for the pure class, stated
   directly on Ostep.

   Build (upstream untouched), from the ClightOMP root:
     eval $(opam env --switch=ClightOMP)
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/OstepFraming.v
*)

Require Import List.
From compcert Require Import cfrontend.Clight.
Require Import compcert.common.Memory.
Require Import VST.concurrency.openmp_sem.event_semantics.
Require Import VST.concurrency.openmp_sem.permissions.
Require Import VST.concurrency.openmp_sem.mem_equiv.
Require Import VST.concurrency.openmp_sem.finThreadPool.
Require Import VST.concurrency.openmp_sem.HybridMachineSig.
Require Import VST.concurrency.openmp_sem.HybridMachine.
Require Import VST.concurrency.openmp_sem.sched_indep.ObsEquiv.
Require Import VST.concurrency.openmp_sem.sched_indep.StepFraming.
Require Import VST.concurrency.openmp_sem.sched_indep.DryStepFraming.

Import DryHybridMachine.

Section OstepFraming.

  Context {ge : genv}.
  Context {tpool : @finThreadPool.ThreadPool.ThreadPool dryResources (@Sem ge)}.

  (* The internal thread step underlying the thread_step case of an Ostep is
     threadStep = dry_step; a read-only such step preserves observable contents. *)
  Lemma threadStep_read_only_obs_equiv :
    forall (foot : footprint) tid tp m
           (Htid : finThreadPool.ThreadPool.containsThread tp tid)
           (Hcmpt : mem_compatible tp m)
           tp' m' ev,
      @threadStep ge tpool tid tp m Htid Hcmpt tp' m' ev ->
      read_only_trace ev ->
      obs_equiv foot m' m.
  Proof.
    intros foot tid tp m Htid Hcmpt tp' m' ev Hts Hro.
    unfold threadStep in Hts.
    eapply dry_step_read_only_obs_equiv; eauto.
  Qed.

  (* Predicate: this Ostep is a pure-class step, i.e. NOT one of the memory-
     mutating machine cases (start_thread spawn, sync/lock, or an OMP pragma
     step). Stated as: the step is not a start/sync/pragma step. We capture it
     positively by saying every threadStep emitted trace on this step is
     read-only, and there is no start/sync/pragma effect. For a usable one-step
     result we take the concrete "internal thread step with read-only events"
     shape, which is exactly what a pure iteration body performs. *)

  (* T0, one Ostep, by case analysis. We prove that ANY Ostep whose only memory
     effect is a read-only internal thread step preserves observable contents.
     The hypothesis [Hpure] discharges the three memory-mutating cases and
     supplies read-only-ness for the thread step. *)
  Lemma Ostep_read_only_obs_equiv :
    forall (foot : footprint)
           U tr tp ttree m U' tr' tp' ttree' m',
      @Ostep ge tpool (U, tr, tp, ttree, m) (U', tr', tp', ttree', m') ->
      (* pure-class side conditions on this concrete step: *)
      (forall tid Htid Hcmpt tpx mx ev,
          @threadStep ge tpool tid tp m Htid Hcmpt tpx mx ev ->
          read_only_trace ev) ->
      (* exclude the memory-mutating machine cases the pure class forbids.
         We phrase the exclusions generically: no start_thread, syncStep, or
         pragmaStep is possible from this state. Implicit args are left to
         unification against the hypotheses inversion introduces. *)
      (forall tid (Htid : finThreadPool.ThreadPool.containsThread tp tid) tpx mx,
          ~ @HybridMachineSig.start_thread dryResources (@Sem ge) tpool
              DryHybridMachineSig m tid tp Htid tpx mx) ->
      (forall tid (Htid : finThreadPool.ThreadPool.containsThread tp tid)
          (Hc : mem_compatible tp m) tpx mx ev,
          ~ @HybridMachineSig.syncStep dryResources (@Sem ge) tpool
              DryHybridMachineSig true tid tp m Htid Hc tpx mx ev) ->
      (forall tid (Htid : finThreadPool.ThreadPool.containsThread tp tid)
          (Hc : mem_compatible tp m) tpx mx ttx trx,
          ~ @HybridMachineSig.pragmaStep dryResources (@Sem ge) tpool
              DryHybridMachineSig tid tp m ttree Htid Hc tpx mx ttx trx) ->
      obs_equiv foot m' m.
  Proof.
    intros foot U tr tp ttree m U' tr' tp' ttree' m'
           Hstep Hpure Hnostart Hnosync Hnopragma.
    unfold Ostep, HybridMachineSig.MachStep in Hstep. simpl in Hstep.
    inversion Hstep; subst.
    - (* start_step: excluded *)
      exfalso. eapply Hnostart; eauto.
    - (* resume_step: memory unchanged *)
      intros b ofs _; reflexivity.
    - (* thread_step: read-only dry_step *)
      eapply threadStep_read_only_obs_equiv; eauto.
    - (* suspend_step: memory unchanged *)
      intros b ofs _; reflexivity.
    - (* suspend_step_pragma: memory unchanged *)
      intros b ofs _; reflexivity.
    - (* sync_step: excluded *)
      exfalso. eapply Hnosync; eauto.
    - (* halted_step: memory unchanged *)
      intros b ofs _; reflexivity.
    - (* schedfail: memory unchanged *)
      intros b ofs _; reflexivity.
    - (* pragma_step: excluded *)
      exfalso. eapply Hnopragma; eauto.
  Qed.

End OstepFraming.
