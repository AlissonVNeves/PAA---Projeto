Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Require Import binsertion_sort.

(* Lemas auxiliares *)
Lemma insert_at_perm: forall i x l, Permutation (x::l) (insert_at i x l).
Proof.
  induction i; intros; simpl.
  - (* Caso base: i = 0 *)
    apply Permutation_refl.
  - (* Passo indutivo: i = S i *)
    destruct l as [|h tl].
    + (* Caso lista vazia *)
      simpl. apply Permutation_refl.
    + (* Caso lista h::tl *)
      (* O alvo é mostrar Permutation (x :: h :: tl) (h :: insert_at i x tl) *)
      (* Sabemos que x :: h :: tl é permutação de h :: x :: tl (perm_swap) *)
      apply perm_trans with (h :: x :: tl).
      * apply perm_swap.
      * apply perm_skip. apply IHi.
Qed.

Lemma binsert_perm: forall x l, Permutation (x::l) (binsert x l).
Proof.
  intros.
  unfold binsert.
  apply insert_at_perm.
Qed.

Theorem binsertion_sort_correct: forall l, Sorted le (binsertion_sort l) /\ Permutation l (binsertion_sort l).
Proof.
  induction l as [|a l' IH].
  - (* Caso base: lista vazia *)
    simpl. split.
    + apply Sorted_nil.
    + apply Permutation_refl.
  - (* Passo indutivo: a::l' *)
    simpl.
    destruct IH as [HSorted HPerm]. (* Hipóteses de indução *)
    split.
    + (* Parte 1: Provar Sorted *)
      (* Aplicamos binsert_correct, que requer que a cauda já esteja ordenada (HSorted) *)
      apply binsert_correct.
      assumption.
    + (* Parte 2: Provar Permutation *)
      (* Queremos provar: Permutation (a :: l') (binsert a (binsertion_sort l')) *)
      (* Sabemos por HPerm que: Permutation l' (binsertion_sort l') *)
      
      (* Passo 1: Adicionar 'a' na cabeça da permutação conhecida *)
      apply perm_trans with (a :: binsertion_sort l').
      * apply perm_skip. assumption.
      
      (* Passo 2: Usar o lema de permutação do binsert *)
      * apply binsert_perm.
Qed.
