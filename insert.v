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

Inductive sort_op : nat -> list nat -> list nat-> Prop := 
  Step a l : sort_op a l (insert a l).

Inductive sort_ops : nat -> list nat -> list nat -> Prop :=
  | Empty a: sort_ops a [] [a]
  | kStep a l l' l'': sort_ops a l l'' -> sort_op a l'' l' -> sort_ops a l l'.
  
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

Theorem sort_sorted:
  forall a l l', sort_ops a l l' -> sorted  l'.
Proof.
  introv H.
  induction H.
  - simpl. apply sorted_one.
  - induction H0.
  simpl. apply insert_sorted. apply IHsort_ops.
Qed.
