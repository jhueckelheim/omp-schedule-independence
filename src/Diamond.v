(* Schedule-independence development, step 8: the memory-commutation core of the
   diamond (theorem L3, for the disjoint-write class C1).

   Two writes (Mem.storebytes) to DISJOINT locations commute: performing them in
   either order yields memories that are mem_equiv. This is the semantic heart of
   why disjoint-write iterations are schedule-independent -- swapping the order of
   two independent iterations' writes does not change the resulting memory.

   No such lemma exists in ClightOMP or in this CompCert (only load-after-write
   "other" lemmas). We build it from the explicit-contents equations
     storebytes_mem_contents (Memory.v:1447): contents = PMap.set b (Mem.setN ...) ...
     storebytes_access       (Memory.v:1439): mem_access unchanged
     nextblock_storebytes    (Memory.v:1486): nextblock unchanged
   plus Mem.setN_outside / PMap.gso for the disjointness, and conclude mem_equiv via
   its content/Max/Cur/nextblock components.

   Build (upstream untouched), from the ClightOMP root:
     eval $(opam env --switch=ClightOMP)
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/Diamond.v
*)

Require Import ZArith.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import VST.concurrency.openmp_sem.permissions.
Require Import VST.concurrency.openmp_sem.mem_equiv.

Open Scope Z_scope.

Section StorebytesCommute.

  (* Within the written range, the value produced by setN depends only on the
     bytes and the position, not on the underlying base map. *)
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

  (* setN at disjoint ranges commutes, pointwise. *)
  Lemma setN_setN_comm :
    forall bytes1 ofs1 bytes2 ofs2 c ofs,
      ofs1 + Z.of_nat (length bytes1) <= ofs2 \/
      ofs2 + Z.of_nat (length bytes2) <= ofs1 ->
      ZMap.get ofs (Mem.setN bytes2 ofs2 (Mem.setN bytes1 ofs1 c)) =
      ZMap.get ofs (Mem.setN bytes1 ofs1 (Mem.setN bytes2 ofs2 c)).
  Proof.
    intros bytes1 ofs1 bytes2 ofs2 c ofs Hrange.
    (* Mem.setN_in / setN_outside: a location is touched by setN vl p iff
       p <= q < p + len. Two disjoint ranges: classify ofs into
       (in range1) | (in range2) | (in neither). In each case both nestings
       agree because the OUTER setN only touches its own range. *)
    (* Helper facts: whether ofs is in each range. *)
    assert (Hin1_dec : {ofs1 <= ofs < ofs1 + Z.of_nat (length bytes1)} +
                       {ofs < ofs1 \/ ofs >= ofs1 + Z.of_nat (length bytes1)}).
    { destruct (zle ofs1 ofs); [ destruct (zlt ofs (ofs1 + Z.of_nat (length bytes1))) | ];
        [ left; lia | right; lia | right; lia ]. }
    assert (Hin2_dec : {ofs2 <= ofs < ofs2 + Z.of_nat (length bytes2)} +
                       {ofs < ofs2 \/ ofs >= ofs2 + Z.of_nat (length bytes2)}).
    { destruct (zle ofs2 ofs); [ destruct (zlt ofs (ofs2 + Z.of_nat (length bytes2))) | ];
        [ left; lia | right; lia | right; lia ]. }
    destruct Hin1_dec as [Hin1 | Hout1]; destruct Hin2_dec as [Hin2 | Hout2].
    - (* in both ranges: impossible by disjointness *)
      exfalso; lia.
    - (* in range1 only.
         LHS: get ofs (setN bytes2 ofs2 (setN bytes1 ofs1 c))
              = get ofs (setN bytes1 ofs1 c)          [ofs outside range2]
         RHS: get ofs (setN bytes1 ofs1 (setN bytes2 ofs2 c))
              = get ofs (setN bytes1 ofs1 c)          [ofs in range1, base-indep] *)
      rewrite (Mem.setN_outside bytes2 (Mem.setN bytes1 ofs1 c) ofs2) by lia.
      apply setN_get_in_indep. lia.
    - (* in range2 only: symmetric *)
      rewrite (Mem.setN_outside bytes1 (Mem.setN bytes2 ofs2 c) ofs1) by lia.
      symmetry.
      apply setN_get_in_indep. lia.
    - (* in neither range: both setN are outside at ofs *)
      rewrite (Mem.setN_outside bytes2 (Mem.setN bytes1 ofs1 c) ofs2) by lia.
      rewrite (Mem.setN_outside bytes1 c ofs1) by lia.
      rewrite (Mem.setN_outside bytes1 (Mem.setN bytes2 ofs2 c) ofs1) by lia.
      rewrite (Mem.setN_outside bytes2 c ofs2) by lia. reflexivity.
  Qed.

  (* Two byte-ranges are location-disjoint: different blocks, or the same block
     with non-overlapping offset ranges. *)
  Definition loc_disjoint (b1: block) (ofs1: Z) (n1: nat)
                          (b2: block) (ofs2: Z) (n2: nat) : Prop :=
    b1 <> b2 \/ ofs1 + Z.of_nat n1 <= ofs2 \/ ofs2 + Z.of_nat n2 <= ofs1.

  (* CONTENT COMMUTATION: writing bytes1 then bytes2, vs bytes2 then bytes1, to
     disjoint locations yields identical contents everywhere. *)
  Lemma storebytes_storebytes_content_comm :
    forall m b1 ofs1 bytes1 b2 ofs2 bytes2 m12a m12 m21a m21,
      loc_disjoint b1 ofs1 (length bytes1) b2 ofs2 (length bytes2) ->
      (* order A: 1 then 2 *)
      Mem.storebytes m   b1 ofs1 bytes1 = Some m12a ->
      Mem.storebytes m12a b2 ofs2 bytes2 = Some m12 ->
      (* order B: 2 then 1 *)
      Mem.storebytes m   b2 ofs2 bytes2 = Some m21a ->
      Mem.storebytes m21a b1 ofs1 bytes1 = Some m21 ->
      forall b ofs,
        ZMap.get ofs (Mem.mem_contents m12) !! b =
        ZMap.get ofs (Mem.mem_contents m21) !! b.
  Proof.
    intros m b1 ofs1 bytes1 b2 ofs2 bytes2 m12a m12 m21a m21
           Hdisj Hs1 Hs2 Hs2' Hs1' b ofs.
    (* expand all four storebytes into setN/PMap.set on the ORIGINAL m,
       using that the non-written block/range is untouched at each step *)
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ Hs2).
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ Hs1).
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ Hs1').
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ Hs2').
    (* Now both sides are nested PMap.set over (mem_contents m). Reduce all four
       PMap.set/get using gsspec, so each collapses by block equality. *)
    rewrite !PMap.gsspec.
    destruct (Pos.eq_dec b b1) as [Hb1 | Hb1];
    destruct (Pos.eq_dec b b2) as [Hb2 | Hb2].
    - (* b = b1 = b2 : Hdisj must be the range-disjoint case *)
      subst b. subst b2.
      destruct Hdisj as [Hbb | Hrange]; [ congruence |].
      (* collapse all peq conditionals (all keys equal to b1) *)
      rewrite !peq_true.
      (* Goal is exactly setN_setN_comm *)
      apply setN_setN_comm. exact Hrange.
    - (* b = b1 <> b2 *)
      repeat match goal with
             | |- context[if peq ?x ?y then _ else _] =>
                 destruct (peq x y); try congruence
             end.
    - (* b = b2 <> b1 *)
      repeat match goal with
             | |- context[if peq ?x ?y then _ else _] =>
                 destruct (peq x y); try congruence
             end.
    - (* b <> b1, b <> b2 *)
      repeat match goal with
             | |- context[if peq ?x ?y then _ else _] =>
                 destruct (peq x y); try congruence
             end.
  Qed.

  (* Full mem_equiv commutation: the two orderings are mem_equiv. *)
  Lemma storebytes_storebytes_comm :
    forall m b1 ofs1 bytes1 b2 ofs2 bytes2 m12a m12 m21a m21,
      loc_disjoint b1 ofs1 (length bytes1) b2 ofs2 (length bytes2) ->
      Mem.storebytes m   b1 ofs1 bytes1 = Some m12a ->
      Mem.storebytes m12a b2 ofs2 bytes2 = Some m12 ->
      Mem.storebytes m   b2 ofs2 bytes2 = Some m21a ->
      Mem.storebytes m21a b1 ofs1 bytes1 = Some m21 ->
      mem_equiv m12 m21.
  Proof.
    intros m b1 ofs1 bytes1 b2 ofs2 bytes2 m12a m12 m21a m21
           Hdisj Hs1 Hs2 Hs2' Hs1'.
    constructor.
    - (* Cur_equiv: access unchanged by storebytes *)
      unfold Cur_equiv, access_map_equiv. intro b.
      unfold getCurPerm.
      rewrite (Mem.storebytes_access _ _ _ _ _ Hs2).
      rewrite (Mem.storebytes_access _ _ _ _ _ Hs1).
      rewrite (Mem.storebytes_access _ _ _ _ _ Hs1').
      rewrite (Mem.storebytes_access _ _ _ _ _ Hs2').
      reflexivity.
    - (* Max_equiv *)
      unfold Max_equiv, access_map_equiv. intro b.
      unfold getMaxPerm.
      rewrite (Mem.storebytes_access _ _ _ _ _ Hs2).
      rewrite (Mem.storebytes_access _ _ _ _ _ Hs1).
      rewrite (Mem.storebytes_access _ _ _ _ _ Hs1').
      rewrite (Mem.storebytes_access _ _ _ _ _ Hs2').
      reflexivity.
    - (* content_equiv *)
      unfold content_equiv. intros b ofs.
      apply (storebytes_storebytes_content_comm
               m b1 ofs1 bytes1 b2 ofs2 bytes2 m12a m12 m21a m21
               Hdisj Hs1 Hs2 Hs2' Hs1').
    - (* nextblock: all four storebytes preserve nextblock *)
      pose proof (Mem.nextblock_storebytes _ _ _ _ _ Hs2) as N2.
      pose proof (Mem.nextblock_storebytes _ _ _ _ _ Hs1) as N1.
      pose proof (Mem.nextblock_storebytes _ _ _ _ _ Hs1') as N1'.
      pose proof (Mem.nextblock_storebytes _ _ _ _ _ Hs2') as N2'.
      congruence.
  Qed.

End StorebytesCommute.
