(* Schedule-independence development, step 5: lifting read-only framing through
   a single thread step (dry_step).

   dry_step (HybridMachine.v:158) is the thread-local Clight execution step of
   the machine. In its only constructor step_dry we have
     Hrestrict_pmap : restrPermMap ... = m1        (m1 has the SAME CONTENTS as m)
     Hcorestep      : ev_step semSem c m1 ev c' m'  (produces the output memory m')
   We showed in StepFraming that a read-only ev_step leaves memory unchanged
   (m' = m1). restrPermMap changes only permissions, not contents, so the
   observable CONTENTS of m' equal those of m. Hence a read-only dry_step
   preserves obs_equiv on every footprint.

   This is the thread-step-level statement of the pure class (theorem T0): a
   pure iteration executed by any thread does not change the memory contents
   that other iterations observe, so interleaving order is irrelevant.

   Stated against the real DryHybridMachine.dry_step.

   Build (upstream untouched), from the ClightOMP root:
     eval $(opam env --switch=ClightOMP)
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/DryStepFraming.v
*)

Require Import List.
From compcert Require Import cfrontend.Clight.
Require Import compcert.common.Memory.
Require Import VST.concurrency.openmp_sem.event_semantics.
Require Import VST.concurrency.openmp_sem.permissions.
Require Import VST.concurrency.openmp_sem.mem_equiv.
Require Import VST.concurrency.openmp_sem.finThreadPool.
Require Import VST.concurrency.openmp_sem.HybridMachine.
Require Import VST.concurrency.openmp_sem.sched_indep.ObsEquiv.
Require Import VST.concurrency.openmp_sem.sched_indep.StepFraming.

Import DryHybridMachine.

Section DryStepFraming.

  Context {ge : genv}.
  Context {tpool : @finThreadPool.ThreadPool.ThreadPool dryResources (@Sem ge)}.

  (* A read-only dry_step preserves memory CONTENTS on every footprint.
     (Permissions may be re-restricted via restrPermMap, but the observable
      contents seen by other iterations are unchanged.) *)
  Lemma dry_step_read_only_obs_equiv :
    forall (foot : footprint) tid0 tp m
           (cnt : finThreadPool.ThreadPool.containsThread tp tid0)
           (Hcompat : mem_compatible tp m)
           tp' m' ev,
      @dry_step ge tpool tid0 tp m cnt Hcompat tp' m' ev ->
      read_only_trace ev ->
      obs_equiv foot m' m.
  Proof.
    intros foot tid0 tp m cnt Hcompat tp' m' ev Hstep Hro b ofs Hf.
    inversion Hstep; subst.
    (* Now in context:
         Hrestrict_pmap : restrPermMap (Hcompat tid0 cnt).1 = m1
         Hcorestep      : ev_step semSem c m1 ev c' m'
       read-only ev_step fixes the memory it runs on: m' = m1 *)
    match goal with
    | [ Hcs : ev_step _ ?c ?m1 ?ev ?c' ?m' |- _ ] =>
        assert (Hid : m' = m1)
          by (eapply (ev_step_read_only_id (@semSem (@Sem ge))); eauto)
    end.
    subst.
    (* Goal is now: contents of (restrPermMap Hlt) = contents of m.
       restrPermMap changes only permissions, not contents. *)
    apply restr_content_equiv.
  Qed.

End DryStepFraming.
