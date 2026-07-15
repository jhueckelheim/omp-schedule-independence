(* A small memory-level fact used by the framing lemmas.

   Within the range written by Mem.setN, the resulting byte depends only on the
   written bytes and the position, not on the underlying base map. *)

Require Import ZArith.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.

Open Scope Z_scope.

Lemma setN_get_in_indep :
  forall vl p c1 c2 q,
    p <= q < p + Z.of_nat (length vl) ->
    ZMap.get q (Mem.setN vl p c1) = ZMap.get q (Mem.setN vl p c2).
Proof.
  induction vl as [| a vl IH]; intros p c1 c2 q Hq.
  - simpl in Hq. lia.
  - simpl length in Hq. rewrite Nat2Z.inj_succ in Hq. simpl Mem.setN.
    destruct (zeq p q) as [Heq | Hne].
    + (* q = p: both write a at p, then setN vl (p+1) which is outside q *)
      subst q.
      rewrite (Mem.setN_other vl _ (p+1) p) by (intros; lia).
      rewrite (Mem.setN_other vl _ (p+1) p) by (intros; lia).
      rewrite !ZMap.gss. reflexivity.
    + (* q <> p: recurse on the tail with the updated bases *)
      apply IH. lia.
Qed.
