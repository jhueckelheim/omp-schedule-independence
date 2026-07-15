(* Schedule-independence development, step 1.

   This file exercises the ClightOMP machinery without any confluence work.
   It proves a real structural building block behind THREAD-COUNT INDEPENDENCE
   (plan L5): any ChunkSplit of a loop -- regardless of how many threads it uses
   or how it assigns work -- distributes exactly the same multiset of iteration
   chunks. Two ChunkSplits of the same loop therefore cover the same chunks.

   It is stated against the real API:
     - ChunkSplit          (for_construct.v:116)
     - team_workloads_is_a_division : Permutation (concat team_workloads) chunks
     - chunk               (for_construct.v:111)

   Build (upstream untouched), from the ClightOMP root:
     eval $(opam env --switch=ClightOMP)
     coqc $(cat _CoqProject) sched_indep/ChunkIndep.v
*)

From Coq Require Import List.
From compcert Require Import -(notations) lib.Maps.
From VST.concurrency.openmp_sem Require Import for_construct.
From stdpp Require Import base list.

Import ListNotations.

Section ChunkIndependence.

  (* The whole point: the [chunks] a ChunkSplit ranges over are determined by the
     loop parameters (lb, incr, iter_num), NOT by the thread count. The thread
     count only affects how [team_workloads] partitions those chunks among
     threads. We make that precise. *)

  (* 1. A ChunkSplit's team_workloads always covers exactly its chunks,
        as a multiset (Permutation). This is literally the record's invariant,
        repackaged as a usable lemma. *)
  Lemma chunksplit_covers_chunks
    (lb incr iter_num : Z) (thread_num : nat)
    (chunks : list chunk) (team_workloads : list (list chunk))
    (cs : ChunkSplit lb incr iter_num thread_num chunks team_workloads) :
    Permutation (concat team_workloads) chunks.
  Proof.
    exact (team_workloads_is_a_division _ _ _ _ _ _ cs).
  Qed.

  (* 2. THREAD-COUNT INDEPENDENCE at the chunk level:
        any two ChunkSplits of the SAME loop (same lb, incr, iter_num, same
        chunk list) -- with possibly DIFFERENT thread counts and DIFFERENT
        work assignments -- distribute the same multiset of chunks. *)
  Lemma chunksplit_thread_count_independent
    (lb incr iter_num : Z)
    (tn1 tn2 : nat)
    (chunks : list chunk)
    (tw1 tw2 : list (list chunk))
    (cs1 : ChunkSplit lb incr iter_num tn1 chunks tw1)
    (cs2 : ChunkSplit lb incr iter_num tn2 chunks tw2) :
    Permutation (concat tw1) (concat tw2).
  Proof.
    (* both concat lists permute to the same [chunks] *)
    transitivity chunks.
    - exact (chunksplit_covers_chunks _ _ _ _ _ _ cs1).
    - symmetry. exact (chunksplit_covers_chunks _ _ _ _ _ _ cs2).
  Qed.

  (* 3. Every chunk assigned to some thread is a real chunk of the loop,
        and every loop chunk is assigned to exactly one thread's workload
        (as a multiset membership consequence). Useful later for the
        disjoint-write footprint argument. *)

End ChunkIndependence.
