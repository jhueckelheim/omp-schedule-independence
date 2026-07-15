(* Schedule-independence development, step 4: the first Ostep-adjacent lemma
   (memory-level foundation of theorem T0, the pure class).

   A "pure" loop body performs no shared writes. At the level of the memory
   event trace that drives execution (event_semantics.v), purity means the trace
   consists solely of [Read] events. We prove that such a trace leaves memory
   *literally unchanged*, and hence content_equiv / obs_equiv on ANY footprint.

   This is a genuine building block: it is the reason a pure body's execution
   cannot depend on the interleaving of iterations -- it does not modify the
   memory that other iterations observe. It is stated against the real
     ev_elim  (event_semantics.v:28)
     mem_event / Read / Write / Alloc / Free  (event_semantics.v:20-26)
   and connects to obs_equiv from ObsEquiv.v.

   No confluence, no thread pool; purely the memory-effect layer.

   Build (upstream untouched), from the ClightOMP root:
     eval $(opam env --switch=ClightOMP)
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/StepFraming.v
*)

Require Import List.
Require Import compcert.lib.Maps.
Require Import compcert.common.Memory.
Require Import VST.concurrency.openmp_sem.event_semantics.
Require Import VST.concurrency.openmp_sem.sched_indep.ObsEquiv.

Section StepFraming.

  (* A memory event trace is read-only if every event in it is a Read. *)
  Definition read_only_event (ev: mem_event) : Prop :=
    match ev with
    | Read _ _ _ _ => True
    | _ => False
    end.

  Definition read_only_trace (T: list mem_event) : Prop :=
    Forall read_only_event T.

  (* 1. A read-only event trace leaves memory literally unchanged. *)
  Lemma ev_elim_read_only_id :
    forall T m m',
      read_only_trace T ->
      ev_elim m T m' ->
      m' = m.
  Proof.
    induction T as [| ev T IH]; intros m m' Hro Hev; simpl in Hev.
    - (* nil *) congruence.
    - destruct ev as [b ofs bytes | b ofs n bytes | b lo hi | l ].
      + (* Write: excluded by read_only_trace *)
        inversion Hro as [| ? ? Hhd Htl]; subst. destruct Hhd.
      + (* Read *)
        destruct Hev as [Hload Hrest].
        inversion Hro as [| ? ? Hhd Htl]; subst.
        eapply IH; eauto.
      + (* Alloc: excluded *)
        inversion Hro as [| ? ? Hhd Htl]; subst. destruct Hhd.
      + (* Free: excluded *)
        inversion Hro as [| ? ? Hhd Htl]; subst. destruct Hhd.
  Qed.

  (* 2. Hence a read-only trace yields obs_equiv on EVERY footprint: the
        observable output is identical to the starting memory. This is the
        memory-level core of T0 (pure class): a pure iteration's step does not
        change what any observer -- or any other iteration -- sees. *)


  (* 3. Bridge to the actual thread-step layer: [dry_step] runs [ev_step semSem]
        (HybridMachine.v:167). For ANY event semantics, an [ev_step] whose
        emitted trace is read-only leaves memory unchanged, hence obs_equiv on
        every footprint. This is the property the pure class relies on at the
        exact relation used inside dry_step. *)
  Context {C : Type} (sem : @EvSem C).

  Lemma ev_step_read_only_id :
    forall c m T c' m',
      ev_step sem c m T c' m' ->
      read_only_trace T ->
      m' = m.
  Proof.
    intros c m T c' m' Hstep Hro.
    apply (ev_elim_read_only_id T m m' Hro).
    eapply ev_step_elim; eauto.
  Qed.


End StepFraming.
