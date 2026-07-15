(* The observation relation.

   The observable output is final memory contents restricted to a caller-chosen
   FOOTPRINT (a set of (block, offset) locations -- e.g. the output array).
   obs_equiv is the relation the headline theorems conclude. *)

Require Import ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Maps.

Section ObsEquiv.

  (* A footprint is a predicate on locations; membership is all we use. *)
  Definition footprint := block -> Z -> Prop.

  (* Memory contents agree on the footprint. *)
  Definition content_equiv_on (foot: footprint) (m1 m2: mem) : Prop :=
    forall b ofs, foot b ofs ->
      ZMap.get ofs (Mem.mem_contents m1) !! b =
      ZMap.get ofs (Mem.mem_contents m2) !! b.

  (* The result relation the main theorems conclude. *)
  Definition obs_equiv (foot: footprint) (m1 m2: mem) : Prop :=
    content_equiv_on foot m1 m2.

  (* obs_equiv is an equivalence relation for every footprint (used implicitly by
     reflexivity/transitivity tactics in the downstream proofs). *)
  Global Instance Equivalence_obs_equiv (foot: footprint) :
    Equivalence (obs_equiv foot).
  Proof.
    constructor.
    - intros m b ofs _. reflexivity.
    - intros m1 m2 H b ofs Hf. symmetry. apply H, Hf.
    - intros m1 m2 m3 H12 H23 b ofs Hf.
      transitivity (ZMap.get ofs (Mem.mem_contents m2) !! b);
        [ apply H12 | apply H23 ]; exact Hf.
  Qed.

End ObsEquiv.
