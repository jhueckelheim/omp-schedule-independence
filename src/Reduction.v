(* Associative-commutative reductions: order-independence.

   The result of an associative-commutative reduction does not depend on the
   order in which per-thread / per-chunk partial results are combined. Since a
   ChunkSplit's team_workloads is a permutation of the loop's chunks
   (ChunkIndep.chunksplit_thread_count_independent), an AC reduction over the
   chunks is therefore independent of thread count and schedule. A pure
   list-algebra fact (no machine step relation).

   Build (from a built ClightOMP checkout):
     coqc $(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep \
          sched_indep/Reduction.v
*)

From VST.concurrency.openmp_sem.sched_indep Require Import ChunkIndep.
From VST.concurrency.openmp_sem Require Import for_construct.
From stdpp Require Import base list.

Section ACReduction.

  Context {A : Type}.
  Context (op : A -> A -> A) (unit : A).
  Context `{!Assoc (=) op} `{!Comm (=) op}.

  (* fold of an AC operator is invariant under permutation of the input list. *)
  Lemma ac_fold_permutation_invariant (l1 l2 : list A) :
    l1 ≡ₚ l2 ->
    foldr op unit l1 = foldr op unit l2.
  Proof.
    intro Hperm.
    apply (foldr_permutation_proper' (=) op unit).
    exact Hperm.
  Qed.

End ACReduction.

Section ChunkReduction.

  (* Combine the algebraic core with the chunk-permutation result: reducing a
     per-chunk contribution with an AC operator is independent of the thread
     count and work assignment chosen by any ChunkSplit of the same loop. *)

  Context {A : Type}.
  Context (op : A -> A -> A) (unit : A).
  Context `{!Assoc (=) op} `{!Comm (=) op}.

  (* g maps each chunk to its partial reduction result. *)
  Variable g : chunk -> A.

  (* Reduce over all chunks assigned across a team's workloads. *)
  Definition reduce_workloads (tw : list (list chunk)) : A :=
    foldr op unit (map g (concat tw)).

  Lemma reduce_workloads_thread_count_independent
    (lb incr iter_num : Z) (tn1 tn2 : nat)
    (chunks : list chunk) (tw1 tw2 : list (list chunk))
    (cs1 : ChunkSplit lb incr iter_num tn1 chunks tw1)
    (cs2 : ChunkSplit lb incr iter_num tn2 chunks tw2) :
    reduce_workloads tw1 = reduce_workloads tw2.
  Proof.
    unfold reduce_workloads.
    apply (ac_fold_permutation_invariant op unit).
    apply Permutation_map.  (* List.map respects Permutation *)
    exact (chunksplit_thread_count_independent
             lb incr iter_num tn1 tn2 chunks tw1 tw2 cs1 cs2).
  Qed.

End ChunkReduction.
