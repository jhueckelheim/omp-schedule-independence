Require Import List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Section PrivateOracle.

  Definition pvar := nat.

  Inductive privatization_kind : Type :=
  | Private
  | Firstprivate.

  Definition kind_env := pvar -> privatization_kind.

  Definition entry_initialized (kind: kind_env) : pvar -> Prop :=
    fun x => kind x = Firstprivate.

  Inductive priv_event : Type :=
  | PrivRead : pvar -> priv_event
  | PrivWrite : pvar -> priv_event.

  Definition pstate := pvar -> Prop.

  Definition state_le (s1 s2: pstate) : Prop :=
    forall x, s1 x -> s2 x.

  Definition empty_state : pstate := fun _ => False.

  Definition mark_written (st: pstate) (x: pvar) : pstate :=
    fun y => st y \/ y = x.

  Fixpoint priv_trace_safe (st: pstate) (T: list priv_event) : Prop :=
    match T with
    | [] => True
    | PrivRead x :: T' => st x /\ priv_trace_safe st T'
    | PrivWrite x :: T' => priv_trace_safe (mark_written st x) T'
    end.

  Definition oracle_no_uninit (kind: kind_env) (Ts: list (list priv_event)) : Prop :=
    forall i T, nth_error Ts i = Some T -> priv_trace_safe (entry_initialized kind) T.

  Definition all_admissible_states_safe (kind: kind_env) (Ts: list (list priv_event)) : Prop :=
    forall i T st,
      nth_error Ts i = Some T ->
      state_le (entry_initialized kind) st ->
      priv_trace_safe st T.

  Lemma state_le_refl :
    forall st, state_le st st.
  Proof.
    intros st x Hx. exact Hx.
  Qed.

  Lemma state_le_mark_written :
    forall st st' x,
      state_le st st' ->
      state_le (mark_written st x) (mark_written st' x).
  Proof.
    intros st st' x Hle y [Hy | Hy].
    - left. apply Hle. exact Hy.
    - right. exact Hy.
  Qed.

  Lemma priv_trace_safe_mono :
    forall T st st',
      state_le st st' ->
      priv_trace_safe st T ->
      priv_trace_safe st' T.
  Proof.
    induction T as [| ev T IH]; intros st st' Hle Hsafe; simpl in *.
    - exact I.
    - destruct ev as [x | x].
      + destruct Hsafe as [Hx HT]. split.
        * apply Hle. exact Hx.
        * apply IH with (st := st); assumption.
      + apply IH with (st := mark_written st x).
        * apply state_le_mark_written. exact Hle.
        * exact Hsafe.
  Qed.

  Theorem oracle_no_uninit_implies_all_admissible_states :
    forall kind Ts,
      oracle_no_uninit kind Ts ->
      all_admissible_states_safe kind Ts.
  Proof.
    intros kind Ts Horacle i T st Hnth Hadm.
    eapply priv_trace_safe_mono.
    - exact Hadm.
    - apply Horacle with (i := i). exact Hnth.
  Qed.

  Definition all_firstprivate (kind: kind_env) : Prop :=
    forall x, kind x = Firstprivate.

  Definition all_private (kind: kind_env) : Prop :=
    forall x, kind x = Private.

  Definition read_before_write_free (T: list priv_event) : Prop :=
    priv_trace_safe empty_state T.

  Lemma all_initialized_safe :
    forall T st,
      (forall x, st x) ->
      priv_trace_safe st T.
  Proof.
    induction T as [| ev T IH]; intros st Hall; simpl.
    - exact I.
    - destruct ev as [x | x].
      + split.
        * apply Hall.
        * apply IH. exact Hall.
      + apply IH. intros y. left. apply Hall.
  Qed.

  Theorem firstprivate_needs_no_write_before_read_check :
    forall kind T,
      all_firstprivate kind ->
      priv_trace_safe (entry_initialized kind) T.
  Proof.
    intros kind T Hall.
    apply all_initialized_safe.
    intro x. unfold entry_initialized. apply Hall.
  Qed.

  Theorem all_firstprivate_oracle_no_uninit :
    forall kind Ts,
      all_firstprivate kind ->
      oracle_no_uninit kind Ts.
  Proof.
    intros kind Ts Hall i T _.
    apply firstprivate_needs_no_write_before_read_check.
    exact Hall.
  Qed.

  Lemma all_private_entry_empty :
    forall kind,
      all_private kind ->
      state_le (entry_initialized kind) empty_state.
  Proof.
    intros kind Hall x Hx.
    unfold entry_initialized in Hx.
    rewrite Hall in Hx. discriminate.
  Qed.

  Theorem all_private_oracle_is_write_before_read :
    forall kind Ts,
      all_private kind ->
      oracle_no_uninit kind Ts <->
      forall i T, nth_error Ts i = Some T -> read_before_write_free T.
  Proof.
    intros kind Ts Hall. split.
    - intros Horacle i T Hnth.
      unfold read_before_write_free.
      eapply priv_trace_safe_mono.
      + apply all_private_entry_empty. exact Hall.
      + apply Horacle with (i := i). exact Hnth.
    - intros Hwbr i T Hnth.
      eapply priv_trace_safe_mono.
      + intros x Hx. unfold empty_state in Hx. exact (False_rect _ Hx).
      + apply Hwbr with (i := i). exact Hnth.
  Qed.

End PrivateOracle.

Section CombinedOracle.

  Variable mem_traces : Type.
  Variable schedule : Type.
  Variable S1 : schedule.
  Variable drf : schedule -> mem_traces -> Prop.
  Variable drf_S1_implies_all : forall Ts, drf S1 Ts -> forall sched, drf sched Ts.

  Definition oracle_1to1_safe
    (kind: kind_env) (shared_traces: mem_traces) (priv_traces: list (list priv_event)) : Prop :=
    drf S1 shared_traces /\ oracle_no_uninit kind priv_traces.

  Definition all_schedules_safe
    (kind: kind_env) (shared_traces: mem_traces) (priv_traces: list (list priv_event)) : Prop :=
    (forall sched, drf sched shared_traces) /\ all_admissible_states_safe kind priv_traces.

  Theorem oracle_1to1_safe_implies_all_schedules_safe :
    forall kind shared_traces priv_traces,
      oracle_1to1_safe kind shared_traces priv_traces ->
      all_schedules_safe kind shared_traces priv_traces.
  Proof.
    intros kind shared_traces priv_traces [Hdrf Huninit]. split.
    - apply drf_S1_implies_all. exact Hdrf.
    - apply oracle_no_uninit_implies_all_admissible_states. exact Huninit.
  Qed.

End CombinedOracle.
