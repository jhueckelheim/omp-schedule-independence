(* Schedule-independence development, step 2a: the observation relation.

   To state "same behavior regardless of schedule / thread count" we need a
   relation on the OBSERVABLE part of a final state. We take the observable to
   be the final memory contents restricted to a caller-chosen FOOTPRINT (a set
   of (block, offset) locations -- e.g. the output array). This is relation (R2)
   in PROOF_PLAN.md sec 1a: weaker and more meaningful than full-memory equality.

   Everything is built on the REAL mem_equiv machinery:
     - content_equiv (mem_equiv.v:186)
     - mem_equiv     (mem_equiv.v:203), a proven Equivalence (mem_equiv.v:210)

   Build (upstream untouched), from the ClightOMP root:
     eval $(opam env --switch=ClightOMP)
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/ObsEquiv.v
*)

Require Import ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Maps.
Require Import VST.concurrency.openmp_sem.mem_equiv.

Section ObsEquiv.

  (* A footprint is a decidable-ish predicate on locations. We keep it as a plain
     predicate; membership is all we use. *)
  Definition footprint := block -> Z -> Prop.

  (* Memory contents agree on the footprint. *)
  Definition content_equiv_on (foot: footprint) (m1 m2: mem) : Prop :=
    forall b ofs, foot b ofs ->
      ZMap.get ofs (Mem.mem_contents m1) !! b =
      ZMap.get ofs (Mem.mem_contents m2) !! b.

  (* This is the result relation the main theorem will conclude. *)
  Definition obs_equiv (foot: footprint) (m1 m2: mem) : Prop :=
    content_equiv_on foot m1 m2.

  (* 1. For every footprint, obs_equiv is an equivalence relation. *)
  Global Instance Equivalence_obs_equiv (foot: footprint) :
    Equivalence (obs_equiv foot).
  Proof.
    constructor.
    - intros m b ofs _. reflexivity.
    - intros m1 m2 H b ofs Hf. symmetry. apply H, Hf.
    - intros m1 m2 m3 H12 H23 b ofs Hf.
      transitivity (ZMap.get ofs (Mem.mem_contents m2) !! b).
      + apply H12, Hf.
      + apply H23, Hf.
  Qed.

  (* 2. Full mem_equiv is stronger: it implies obs_equiv on ANY footprint.
        This lets the main proof produce full mem_equiv and then project. *)
  Lemma mem_equiv_obs_equiv (foot: footprint) (m1 m2: mem) :
    mem_equiv m1 m2 -> obs_equiv foot m1 m2.
  Proof.
    intros Hme b ofs _. apply (content_eqv _ _ Hme).
  Qed.

  (* 3. Monotonicity: agreeing on a larger footprint implies agreeing on a
        smaller one. Useful for narrowing to the output array. *)
  Lemma obs_equiv_sub (foot foot': footprint) (m1 m2: mem) :
    (forall b ofs, foot' b ofs -> foot b ofs) ->
    obs_equiv foot m1 m2 ->
    obs_equiv foot' m1 m2.
  Proof.
    intros Hsub H b ofs Hf'. apply H, Hsub, Hf'.
  Qed.

  (* 4. A concrete, common footprint: a contiguous range [lo,hi) in one block,
        e.g. an output array [b, 0 .. n). *)
  Definition range_footprint (b0: block) (lo hi: Z) : footprint :=
    fun b ofs => b = b0 /\ (lo <= ofs < hi)%Z.

End ObsEquiv.
