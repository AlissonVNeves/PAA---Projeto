Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Require Import binsertion_sort.

(* Lemas auxiliares *)
Lemma bsearch_returns_valid_position : ...
Lemma insert_at_preserves_permutation : ...
Lemma insert_at_makes_sorted_when_position_is_correct : ...

(* Prova principal *)
Theorem binsertion_sort_correct :
  forall l,
    Sorted le (binsertion_sort l) /\
    Permutation l (binsertion_sort l).
