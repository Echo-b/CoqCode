Require Import Arith.

Require Import List. 
Import ListNotations.


Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | nil => i::nil
  | h::t => if i <=? h
    then i::h::t else h::insert i t
  end.

Fixpoint sort (l : list nat) :=
  match l with
  | nil => nil
  | h::t => insert h (sort t)
  end.

Inductive sort_op : list nat -> list nat-> Prop := 
  | empty : sort_op [] []
  | Step a::l: sort_op l (insert a l).

Inductive sort_ops : list nat -> list nat -> Prop :=
  | Empty : sort_ops [] []
  | kStep l l' l'': sort_ops l l'' -> sort_op l'' l' -> sort_ops l l'.
  
Inductive sorted : list nat -> Prop :=
  | sorted_nil : sorted nil
  | sorted_one : forall x, sorted (x::nil)
  | sorted_cons : forall x y l,
    x <= y -> sorted (y::l) -> sorted (x::y::l).
  

Lemma lebtop : forall x y, (x <=? y) = true -> x <= y.
Proof.
  induction x; destruct y; auto using le_0_n, le_n_S.
  intros H. inversion H.
Qed.

Lemma nlebtop : forall x y, (x <=? y) = false -> y <= x.
Proof.
  induction x; destruct y; auto using le_0_n, le_n_S.
  intros H. inversion H.
Qed.

Lemma sorted_inv :
  forall a b l, sorted (a::b::l) -> sorted (b::l) /\ a <= b.
Proof.
  intros a b l H.
  split.
  - inversion H. apply H4.
  - inversion H. apply H2.
Qed.

Lemma insert_sorted: 
  forall a l, sorted l -> sorted (insert a l).
Proof.
  intros a l H.
  induction l as [| a' l'].
  -
    simpl. apply sorted_one.
  - destruct (a <=? a') eqn:H'.
    + simpl. rewrite H'. constructor.
      * apply lebtop. assumption.
      * apply H.
    + simpl. rewrite H'. destruct l' as [| a'' l''].
      * simpl. apply nlebtop in H'. constructor. apply H'. constructor.
      * apply sorted_inv in H. destruct H. apply IHl' in H.
        destruct (a <=? a'') eqn: H''.
          ** simpl in  H. rewrite H'' in H.
             simpl. rewrite H''. constructor.
             apply nlebtop in H'. apply H'. apply H.
          ** simpl in H. rewrite H'' in H.
             simpl. rewrite H''. constructor. 
             apply H0. apply H.
Qed.

Lemma sort_sorted: forall l, sorted (sort l).
Proof.
  intros l.
  induction l.
  - 
    simpl. apply sorted_nil.
  - 
    simpl. apply insert_sorted. apply IHl.
Qed.


Lemma sort_sorted' :
  forall l l', sort_ops l l' -> sorted  l'.
Proof.
  introv H.
  induction H.
  - simpl. apply sorted_nil.
  - induction H0.
    + apply IHsort_ops.
    + destruct l'. 
Qed.

Inductive Permutation : list nat -> list nat -> Prop :=
  | perm_nil : Permutation [] []
  | perm_self l: Permutation l l
  | perm_skip x l l': Permutation l l' -> Permutation(x::l)(x::l')
  | perm_swap x y l : Permutation (y::x::l)(x::y::l)
  | perm_trans l l' l'' : Permutation l l'' -> Permutation l'' l' -> Permutation l l'.

Lemma insert_perm:
  forall x l, Permutation(x::l)(insert x l).
Proof.
  intros.
  induction l as [|x' l'].
  - simpl. apply perm_self.
  - destruct (x <=? x') eqn:Hx.
    + simpl. rewrite Hx. apply perm_self.
    + simpl. rewrite Hx. 
      assert (H' : Permutation (x::x'::l') (x'::x::l')).
      apply perm_swap. apply perm_trans with (x'::x::l').
      -- apply H'.
      -- apply perm_skip. apply IHl'.
Qed.


Require Import Classical_Prop.

Lemma  sort_perm': 
  forall l l', sort' l l' -> Permutation l l'.
Proof.
  intros.
  induction H.
  - apply perm_self.
  - induction l.
    ++ simpl 
  
Qed.


Lemma sort_perm :
  forall l, Permutation l (sort l).
Proof.
  intros l.
  induction l.
  - simpl. apply perm_nil.
  - simpl. apply (@perm_skip a _ _) in IHl.
    apply perm_trans with (a::sort l).
    + simpl. auto.
    + apply insert_perm.
Qed. 


Definition sorting_algorithm (f : list nat -> list nat) :=
  forall l, Permutation l (f l)  /\ sorted (f l).


Theorem insertion_sort_correct: sorting_algorithm sort.
Proof.
  split. 
  - apply sort_perm.
  - apply sort_sorted.
Qed.

