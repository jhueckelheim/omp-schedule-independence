(* Schedule-independence development, step 2b: the program-class predicates.

   PROOF_PLAN.md sec 1b. We formalize the classes of loop bodies for which
   schedule-independence is expected to hold. We phrase them abstractly enough
   to be usable in the confluence layer later, while staying anchored to the
   real CanonicalLoopNest type (canonical_loop_nest.v:158) and the footprint
   notion from ObsEquiv.

   Nothing here needs the machine step relation yet; these are the hypotheses
   the main theorem will carry.

   Build (upstream untouched), from the ClightOMP root:
     eval $(opam env --switch=ClightOMP)
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/ClassPredicates.v
*)

Require Import ZArith.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import VST.concurrency.openmp_sem.canonical_loop_nest.
Require Import VST.concurrency.openmp_sem.sched_indep.ObsEquiv.

Section ClassPredicates.

  (* We model the per-iteration effect abstractly by two footprints:
       write_foot i  : locations iteration i may WRITE
       read_foot  i  : locations iteration i may READ
     A concrete instantiation (e.g. for out[i]=f(i)) supplies these together
     with the discharge that body execution respects them; that discharge is
     the job of the StepCongruence layer. Here we define the *class conditions*
     over these footprints. *)

  (* Two footprints are disjoint. *)
  Definition foot_disjoint (f g: footprint) : Prop :=
    forall b ofs, f b ofs -> g b ofs -> False.

  (* C-disjoint-write: distinct iterations write disjoint locations, and no
     iteration reads any location written by another iteration. This is exactly
     the condition that makes iteration order irrelevant to the final contents. *)
  Record disjoint_write_class
    (iters: Z -> Prop)                 (* the set of iteration indices *)
    (write_foot read_foot: Z -> footprint) : Prop :=
  { dw_write_disjoint :
      forall i j, iters i -> iters j -> i <> j ->
        foot_disjoint (write_foot i) (write_foot j);
    dw_read_write_disjoint :
      forall i j, iters i -> iters j -> i <> j ->
        foot_disjoint (read_foot i) (write_foot j) }.

  (* C-pure: no iteration writes any shared location at all. Trivially a special
     case of disjoint-write (empty write footprints), but singled out because it
     yields schedule-independence with no commutation argument: shared memory
     is invariant. *)
  Definition empty_foot : footprint := fun _ _ => False.

  Definition pure_class (iters: Z -> Prop) (write_foot: Z -> footprint) : Prop :=
    forall i, iters i -> forall b ofs, write_foot i b ofs -> False.

  (* Sanity: the pure class is a disjoint-write class (with any read footprints),
     confirming the predicates compose as intended. *)
  Lemma pure_is_disjoint_write
    (iters: Z -> Prop) (write_foot read_foot: Z -> footprint) :
    pure_class iters write_foot ->
    disjoint_write_class iters write_foot read_foot.
  Proof.
    intros Hpure. constructor.
    - intros i j Hi Hj Hne b ofs Hwi _.
      eapply Hpure; [ exact Hi | exact Hwi ].
    - intros i j Hi Hj Hne b ofs _ Hwj.
      eapply Hpure; [ exact Hj | exact Hwj ].
  Qed.

  (* The overall output footprint of the loop: the union of all iteration writes.
     This is what the main theorem's obs_equiv will range over. *)
  Definition loop_output_foot
    (iters: Z -> Prop) (write_foot: Z -> footprint) : footprint :=
    fun b ofs => exists i, iters i /\ write_foot i b ofs.

  (* Structural well-formedness we will require of the loop under analysis:
     it is a canonical loop nest (so the machine's step_for applies). We keep
     this as an opaque marker to be refined when we wire up make_canonical_loop_nest. *)
  Definition is_canonical (cln: CanonicalLoopNest) : Prop := True.

End ClassPredicates.
