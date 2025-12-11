Require Import List.
Require Import Arith.
Require Import Lia.
Require Import Permutation.
Import ListNotations.

(**
   A função [bsearch x l] retorna a posição [i] ($0 \leq i \leq |l|-1$) onde [x] deve ser inserido na lista ordenada [l]:
 *)

Require Import Recdef.

Function bsearch x l {measure length l} :=
  match l with
  | [] => 0
  | [y] => if (x <=? y)
           then 0
           else 1
  | h1::h2::tl =>
      let len := length l in
      let mid := len / 2 in
      let l1 := firstn mid l in
      let l2 := skipn mid l in
      match l2 with
      | [] => 0
      | h2'::l2' => if (x <? h2')
                    then bsearch x l1
                    else
                      if x =? h2'
                      then mid
                      else mid + (bsearch x l2)
      end
  end.
Proof.
  - intros. rewrite firstn_length_le.
    + simpl length. apply Nat.div_lt.
      * lia.
      * auto.
    + simpl length. apply Nat.lt_le_incl. apply Nat.div_lt.
      * lia.
      * auto.
  - intros. rewrite <- teq1. rewrite length_skipn. simpl length. apply Nat.sub_lt.
    + apply Nat.lt_le_incl. apply Nat.div_lt.
      * lia.
      * auto.
    + apply Nat.div_str_pos. lia.
Defined.

(**
   Podemos fazer alguns testes com esta função:
 *)

Lemma test0: bsearch 1 [] = 0.
Proof.
  rewrite bsearch_equation. reflexivity.
Qed.

Lemma test1: bsearch 1 [0;2;3] = 1.
Proof.
  rewrite bsearch_equation. simpl. rewrite bsearch_equation. destruct (1 <=? 0) eqn: H.
  - inversion H.
  - reflexivity.
Qed.

Lemma test2: bsearch 2 [0;2;3] = 1.
Proof.
  rewrite bsearch_equation. simpl. reflexivity.
Qed.
  
Lemma test3: bsearch 2 [0;2;3;4] = 1.
Proof.
  rewrite bsearch_equation. simpl. rewrite bsearch_equation. simpl. reflexivity.
Qed.

Lemma test4: bsearch 3 [0;1;2;3;4;5] = 3.
Proof.
  rewrite bsearch_equation. simpl. reflexivity.
Qed.  

(**
Também podemos verificar que [bsearch x l] sempre retorna uma posição válida da lista [l]:
 *)

Lemma bsearch_valid_pos: forall l x, 0 <= bsearch x l < length l.
Proof.
  Admitted.

  
(**
A seguir, definiremos a função [insert_at i x l] que insere o elemento [x] na posição [i] da lista [l]:
 *)

Fixpoint insert_at i (x:nat) l :=
  match i with
  | 0 => x::l
  | S k => match l with
           | nil => [x]
           | h::tl => h::(insert_at k x tl)
           end
  end.

Eval compute in (insert_at 2 3 [1;2;3]).

(**
A função [binsert x l] a seguir insere o elemento x na posição retornada por [bsearch x l] de [l]:
 *)

Definition binsert x l :=
  let pos := bsearch x l in
  insert_at pos x l.

(**
 Agora podemos enunciar o teorema que caracteriza a correção da função [binsert], a saber, que [binsert x l] retorna uma lista ordenada, se [l] estiver ordenada: 
*)
(* begin hide *)
Require Import Sorted.
(* end hide *)

 (* LEMA AUXILIAR *)
Lemma insert_at_app: forall l i x,
  i <= length l ->
  insert_at i x l = firstn i l ++ x :: skipn i l.
Proof.
  induction l.
  - intros i x H. destruct i; simpl in *; try lia. reflexivity.
  - intros i0 x H. destruct i0.
    + simpl. reflexivity.
    + simpl. f_equal. apply IHl. simpl in H. lia.
Qed.

(* LEMA AUXILIAR *)
Lemma sorted_split_merge: forall l1 l2 x,
  Sorted le l1 -> Sorted le l2 ->
  Forall (fun y => y <= x) l1 ->
  Forall (fun y => x <= y) l2 ->
  Sorted le (l1 ++ x :: l2).
Proof.
  intros l1 l2 x Sl1 Sl2 Fl1 Fl2.
  induction Sl1.
  (* Caso Base *)
  - simpl. apply Sorted_cons.
    + assumption.
    + destruct l2.
      * constructor.
      * constructor. inversion Fl2. assumption.
  (* Passo Indutivo *)
  - simpl. apply Sorted_cons.
    + apply IHSl1. inversion Fl1. assumption.
    + destruct l.
      * simpl. constructor. inversion Fl1. assumption.
      * simpl. constructor. inversion H. assumption.
Qed.

(* LEMA AUXILIAR *)
Lemma bsearch_split_prop: forall l x,
  Sorted le l ->
  Forall (fun y => y <= x) (firstn (bsearch x l) l) /\
  Forall (fun y => x <= y) (skipn (bsearch x l) l).
Proof.
  Admitted.

(* LEMA AUXILIAR *)
Lemma Sorted_firstn : forall (l : list nat) (n : nat),
  Sorted le l -> Sorted le (firstn n l).
Proof.
  intros l n H.
  revert n.
  induction H as [| head tail H_sorted IH H_rel].
  - (* Caso Base: Lista vazia *)
    intros n. simpl. destruct n; constructor.
  - (* Caso Indutivo *)
    intros n. destruct n.
    + (* n = 0 *)
      simpl. constructor.
    + (* n > 0 *)
      simpl. constructor.
      * apply IH. (* A cauda também é ordenada *)
      * (* Precisamos mostrar que a relação 'HdRel' se mantém para a lista truncada *)
        destruct n.
        -- simpl. constructor.
        -- simpl. inversion H_rel. subst.
  (* Caso 1: A lista cortada ficou vazia (firstn n tail = []) *)
            constructor.

            (* Caso 2: A lista cortada não é vazia (firstn n tail = b :: ...) *)
            apply HdRel_cons.
            (* Precisamos provar head <= b using H_rel e a igualdade *)
            rewrite <- H0 in H_rel. inversion H_rel. assumption.
Qed.

Lemma Sorted_skipn : forall (l : list nat) (n : nat),
  Sorted le l -> Sorted le (skipn n l).
Proof.
  intros l n.
  revert l. 
  induction n as [| n IH].
  - (* Caso n = 0: não pule nada *)
    intros l H. simpl. assumption.
  - (* Caso n = S n: pule um, depois pule n *)
    intros l H. destruct l.
    + (* Lista vazia *)
      simpl. constructor.
    + (* Lista com cabeça e cauda *)
      simpl. apply IH.
      (* Se (a :: l) é ordenada, então l é ordenada *)
      inversion H. assumption.
Qed.

(* --- TEOREMA PRINCIPAL: Correção do binsert --- *)
Theorem binsert_correct: forall l x, Sorted le l -> Sorted le (binsert x l).
Proof.
  intros l x HSort.
  unfold binsert.
  
  (* Passo 1: Transformar a inserção em concatenação de listas *)
  rewrite insert_at_app.
  2: { 
    pose proof (bsearch_valid_pos l x). (* Traz '0 <= bsearch <= length' para o contexto *)
    lia. 
  }
  
  (* Passo 2: Usar as propriedades da busca binária *)
  pose proof (bsearch_split_prop l x HSort) as [HLeft HRight].
  
  (* Passo 3: Provar que colar tudo mantém a ordem *)
  apply sorted_split_merge.
  - apply Sorted_firstn; assumption. (* A parte esquerda já era ordenada *)
  - apply Sorted_skipn; assumption.  (* A parte direita já era ordenada *)
  - assumption. (* A esquerda é <= x *)
  - assumption. (* A direita é >= x *)
Qed.   

(**
   Alternativamente, podemos construir uma única função que combina a execução de [bsearch] e [insert_at]. A função [binsert x l] a seguir, recebe o elemento [x] e a lista ordenada [l] como argumentos e retorna uma permutação ordenada da lista [x::l]: 
 *)

Function binsert' x l {measure length l} :=
  match l with
  | [] => [x]
  | [y] => if (x <=? y)
           then [x; y]
           else [y; x]
  | h1::h2::tl =>
      let len := length l in
      let mid := len / 2 in
      let l1 := firstn mid l in
      let l2 := skipn mid l in
      match l2 with
      | [] => l
      | h2'::l2' => if x =? h2'
                    then l1 ++ (x ::l2)
                    else
                      if x <? h2'
                      then binsert' x l1
                      else binsert' x l2
      end
  end.
Proof.
  - intros. rewrite firstn_length_le.
    + simpl length. apply Nat.div_lt; lia.
    + simpl length. apply Nat.lt_le_incl. apply Nat.div_lt; lia.
  - intros. rewrite <- teq1. rewrite length_skipn. apply Nat.sub_lt.
    + simpl length. apply Nat.lt_le_incl. apply Nat.div_lt; lia.
    + simpl length. apply Nat.div_str_pos. lia.
Defined.

Lemma teste0: (binsert' 2 [1;2;3]) = [1;2;2;3].
Proof.
  rewrite binsert'_equation. simpl. reflexivity.
Qed.

(**
As funções [binsert] e [binsert'] representam o mesmo algoritmo:
 *)

Lemma binsert_equiv_binsert': forall l x, binsert x l = binsert' x l.
Proof.
Admitted.

(**
 E portanto a correção de [binsert'] é imediata:
*)

Corollary binsert'_correct: forall l x, Sorted le l -> Sorted le (binsert' x l).
Proof.
  intros l x H. rewrite <- binsert_equiv_binsert'. apply binsert_correct. assumption.
Qed.

(**
O algoritmo principal é dado a seguir:
 *)

Fixpoint binsertion_sort (l: list nat) :=
  match l with
  | [] => []
  | h::tl => binsert h (binsertion_sort tl)
  end.

(* begin hide *)
Require Import Permutation.
(* end hide *)

(* Teste com lista desordenada simples *)
Compute (binsertion_sort [4; 3; 2; 1]).
(* Esperado: [1; 2; 3; 4] *)

(* Teste com elementos repetidos *)
Compute (binsertion_sort [5; 1; 3; 1; 5]).
(* Esperado: [1; 1; 3; 5; 5] *)

(* Teste com lista vazia *)
Compute (binsertion_sort []).
(* Esperado: [] *)

Example teste_sort_1: binsertion_sort [4; 1; 3; 2] = [1; 2; 3; 4].
Proof.
  vm_compute. 
  reflexivity.
Qed.

Example teste_sort_2: binsertion_sort [10; 0; 5] = [0; 5; 10].
Proof.
  vm_compute.
  reflexivity.
Qed.

Example teste_teorema_instancia: 
  Sorted le (binsertion_sort [3; 1; 2]) /\ Permutation [3; 1; 2] (binsertion_sort [3; 1; 2]).
Proof.
   (* Teorema geral para provar este caso específico *)
  apply binsertion_sort_correct.
Qed.
