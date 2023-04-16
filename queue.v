Require Import Arith.

Require Import LibTactics. 

Require Import List. 

Open Scope type_scope.

Import ListNotations. 

Definition element := nat. 
Definition logic_time := nat.

Definition que_entry := element * logic_time.

Inductive op_label :=
  EnQ (t: logic_time) | DeQ (e: que_entry).  

Inductive que_op : list que_entry -> list que_entry -> op_label -> Prop :=
  OpEn ens m t: que_op ens (ens++[(m, t)]) (EnQ t) |
  OpDe ens e: que_op (e :: ens) ens (DeQ e). 

Inductive que_ops : list que_entry -> list que_entry -> list op_label -> nat -> Prop :=
  Empty: que_ops [] [] [] 0 |
  EnStep ens ens' ens'' lbs k:
    que_ops ens ens'' lbs k -> 
    que_op ens'' ens' (EnQ (S k)) ->
    que_ops ens ens' lbs (S k) |
  DeStep ens ens' ens'' e lbs k:
    que_ops ens ens'' lbs k ->
    que_op ens'' ens' (DeQ e) ->
    que_ops ens ens' (lbs ++ [(DeQ e)]) k.

(* lbs = [DeQ (m1, t1); DeQ (m2, t2); ...; DeQ (m', t')] *)
(* lbs++[DeQ (m, t)] = [DeQ (m1, t1); DeQ (m2, t2); ...; DeQ (m', t')] ++ [DeQ (m, t)]  *)

Definition FIFO lbs :=
  forall ens k i1 i2 m1 m2 t1 t2, 
    que_ops [] ens lbs k  ->
    nth_error lbs i1 = Some (DeQ (m1, t1)) ->
    nth_error lbs i2 = Some (DeQ (m2, t2)) ->    
    i1 < i2 -> 
    t1 < t2. 

Definition INC (ens: list que_entry) :=
  forall i1 i2 m1 m2 t1 t2,
    nth_error ens i1 = Some (m1, t1) ->
    nth_error ens i2 = Some (m2, t2) ->
    i1 < i2 -> 
    t1 < t2. 
           
Definition FIFO_ext lbs ens :=
  FIFO lbs /\ INC ens /\
  (forall i j m m' t t', nth_error lbs i = Some (DeQ (m, t)) -> nth_error ens j = Some (m', t') -> t < t'). 

Lemma list_eq_decomp: 
  forall (ens1 ens2: list que_entry) e1 e2,
    ens1 ++ [e1] = ens2 ++ [e2] ->
    ens1 = ens2 /\ e1 = e2.
Proof.
  induction ens1.
  intros.
  destruct ens2.
  simpl in H. inverts H. split; auto.
  simpl in H.
  inverts H.
  destruct ens2; inverts H2.
  introv Heq.
  destruct ens2.
  simpl in Heq.
  inverts Heq.
  destruct ens1. simpl in H1. inverts H1. simpl in H1. inverts H1.
  simpl in Heq.
  inverts Heq.
  apply IHens1 in H1.
  destruct H1. subst.
  split; auto. 
Qed.   

Lemma lbs_eq_decomp: 
  forall (lbs1 lbs2: list op_label) lb1 lb2,
    lbs1 ++ [lb1] = lbs2 ++ [lb2] -> 
    lbs1 = lbs2 /\ lb1 = lb2. 
Proof.
  induction lbs1.
  intros.
  destruct lbs2.
  simpl in H. inverts H. split; auto.
  simpl in H.
  inverts H.
  destruct lbs2; inverts H2.
  introv Heq.
  destruct lbs2.
  simpl in Heq.
  inverts Heq.
  destruct lbs1. simpl in H1. inverts H1. simpl in H1. inverts H1.
  simpl in Heq.
  inverts Heq.
  apply IHlbs1 in H1.
  destruct H1. subst.
  split; auto. 
Qed.   

Lemma fifo_weakening: 
  forall lbs ens, FIFO_ext lbs ens -> FIFO lbs.
Proof.
  introv Hfe.
  unfolds in Hfe.
  inverts Hfe.
  auto. 
Qed.   

Lemma fifo_empty:
  FIFO [].
  unfolds.
  introv H0 Hnth1 Hnth2.
  destruct i1.
  simpl in Hnth1. inverts Hnth1.
  simpl in Hnth1. inverts Hnth1.
Qed.

Lemma inc_empty:
  INC [].
  unfolds.
  introv Hnth1 Hnth2.
  destruct i1.
  simpl in Hnth1. inverts Hnth1.
  simpl in Hnth1. inverts Hnth1.
Qed.

Lemma inc_suffix:
  forall e ens', INC (e :: ens') -> INC ens'. 
Proof.
  introv Hinc Hlt.
  unfold INC in *.
  introv Hnth1 Hnth2.
  (*???*)
  eapply Hinc with (i1:=S i1) (i2:=S i2); eauto.
  auto with arith.
Qed.   

Require Import Classical_Prop.

Lemma lbs_ub:
  forall ens ens' lbs k,
    que_ops ens ens' lbs k ->
    ((forall i m t, nth_error lbs i = Some (DeQ (m, t)) -> t <= k) /\
     (forall j m t, nth_error ens' j = Some (m, t) -> t <= k)).     
Proof.
  introv H.
  induction H.
  split; intros.
  destruct i; simpl in H; inverts H.
  destruct j; simpl in H; inverts H. 

  destruct IHque_ops.
  split.
  introv Hd. eapply H1 in Hd. auto with arith.
  inverts H0.
  introv Hnth.
  assert (Hor: j < length ens'' \/ ~ (j < length ens'')) by tauto.
  destruct Hor.
  rewrite nth_error_app1 in Hnth; auto.
  eapply H2 in Hnth. auto with arith.
  apply not_lt in H0.
  rewrite nth_error_app2 in Hnth.
  2: { auto with arith. }
  destruct (j - length ens''). simpl in Hnth. inverts Hnth. auto with arith.
  simpl in Hnth.
  destruct n; simpl in Hnth; inverts Hnth.

  (* 3rd case in inductive def of que_ops *)  
  destruct IHque_ops.
  split.
  introv Hd. 
  assert (Hor: i < length lbs \/ ~ (i < length lbs)) by tauto.  
  destruct Hor.
  rewrite nth_error_app1 in Hd; auto.
  eapply H1; eauto.
  apply not_lt in H3.
  rewrite nth_error_app2 in Hd.
  2: { auto with arith. }
  destruct (i - length lbs). simpl in Hd. inverts Hd. 
  inverts H0.
  specialize (H2 0 m t).
  simpl in H2.
  apply H2; auto.
  simpl in Hd. destruct n; simpl in Hd; inverts Hd.

  inverts H0.
  introv H_.
  specialize (H2 (S j) m t).
  simpl in H2.
  apply H2; auto.
Qed.

Lemma inc_extend_preserve:
  forall ens k m,
    INC ens ->
    (forall j m t, nth_error ens j = Some (m, t) -> t <= k) ->
    INC (ens ++ [(m, S k)]).
Proof.
  introv Hinc Hle.
  unfold INC in *.
  introv Hnth1 Hnth2 Hlt.
  assert (Hcs1: i1 < length ens \/ ~ (i1 < length ens)) by tauto.
  destruct Hcs1.
  -
    rewrite nth_error_app1 in Hnth1; auto.
    assert (Hcs2: i2 < length ens \/ ~ (i2 < length ens)) by tauto.
    destruct Hcs2.
    + 
      rewrite nth_error_app1 in Hnth2; auto. 
      eapply Hinc; eauto.
    +
      apply not_lt in H0.
      rewrite nth_error_app2 in Hnth2; auto.
      destruct (i2 - length ens).
      simpl in Hnth2. inverts Hnth2.
      apply Hle in Hnth1.
      auto with arith.
      simpl in Hnth2.
      destruct n; simpl in Hnth2; tryfalse.
  -
    apply not_lt in H.
    assert (Hi2: i2 < length (ens ++ [(m, S k)])).
    { apply nth_error_Some. rewrite Hnth2. introv Hf; inverts Hf. }
    rewrite last_length in Hi2. 
    lets H00: Nat.le_lt_trans H Hlt. 
    assert (S (length ens) <= i2) by auto with arith.
    apply lt_not_le in Hi2. apply Hi2 in H0. inverts H0.
Qed.

Lemma que_ops_prefix:
  forall ens lbs k e,
    que_ops [] ens (lbs ++ [DeQ e]) k ->
    exists ens0 k0, que_ops [] ens0 lbs k0.
Proof.
  introv Hqo.
  inductions Hqo.
  destruct lbs; tryfalse.
  eapply IHHqo; eauto. 
  apply lbs_eq_decomp in x.
  destruct x.
  subst.
  do 2 eexists; eauto. 
Qed. 

Lemma fifo_ext_holds: 
  forall ens ens' lbs k, 
    que_ops ens ens' lbs k -> FIFO_ext lbs ens'. 
Proof.
  introv H.
  induction H.
  - 
    unfolds.
    split. apply fifo_empty. split. apply inc_empty.
    introv Hnth1 Hnth2.
    destruct i.
    simpl in Hnth1. inverts Hnth1.
    simpl in Hnth1. inverts Hnth1.

  -
    unfold FIFO_ext in *.
    destruct IHque_ops.
    split; auto.
    inverts H0.
    destruct H2.
    split.
    assert (Hle:=H). 
    apply lbs_ub in Hle.
    destruct Hle as [Hle1 Hle2].
    eapply inc_extend_preserve; eauto.

    introv Hnth1 Hnth2.
    assert (Hj: j < length ens'' \/ ~(j < length ens'')) by tauto. 
    destruct Hj.
    +
      rewrite nth_error_app1 in Hnth2; auto.
      eapply H2; eauto.
    +
      apply not_lt in H3. 
      rewrite nth_error_app2 in Hnth2; auto.
      destruct (j - length ens'').
      simpl in Hnth2. inverts Hnth2.
      apply lbs_ub in H. destruct H. apply H in Hnth1. 
      clear -Hnth1. auto with arith.
      simpl in Hnth2. 
      destruct n; simpl in Hnth2; tryfalse.
      
  -
    unfold FIFO_ext in *.
    inverts H0.
    destruct IHque_ops as (Hfifo & Hinc & Hcross).
    split.
    +
      unfold FIFO in *. 
      introv Hops Hnth1 Hnth2 Hlt.
      lets Hp: que_ops_prefix Hops.
      destruct Hp as (ens0_ & k0_ & Hqo').
      assert (Hi1: i1 < length lbs \/ ~(i1 < length lbs)) by tauto. 
      destruct Hi1.
      *
        rewrite nth_error_app1 in Hnth1; auto.
        assert (Hi2: i2 < length lbs \/ ~(i2 < length lbs)) by tauto.
        destruct Hi2.
        rewrite nth_error_app1 in Hnth2; auto.
        clear Hops. eapply Hfifo; eauto. 

        apply not_lt in H1.  
        rewrite nth_error_app2 in Hnth2; auto.

        destruct (i2 - length lbs).
        simpl in Hnth2.  inverts Hnth2. 
        specialize (Hcross i1 0 m1 m2 t1 t2 Hnth1).
        simpl in Hcross.
        eapply Hcross; eauto.

        simpl in Hnth2. 
        destruct n; simpl in Hnth2; tryfalse.
      *
        apply not_lt in H0.
        assert (i2 > length lbs) by (eapply Nat.le_lt_trans; eauto).
        assert (Hi2lt: i2 < length (lbs++[DeQ e])).
        { eapply nth_error_Some. rewrite Hnth2.
          introv Hf; inverts Hf. }
        rewrite last_length in Hi2lt.
        clear -H1 Hi2lt.
        rewrite Nat.lt_succ_r in Hi2lt.
        apply gt_not_le in H1.
        tryfalse. 
    +
      split.
      eapply inc_suffix; eauto.
      introv Hnth1 Hnth2.
      assert (Hi: i < length lbs \/ ~(i < length lbs)) by tauto.
      destruct Hi.
      * 
        rewrite nth_error_app1 in Hnth1; auto. 
        eapply Hcross; eauto.
        instantiate (2:=S j).
        simpl. eauto.
      *
        apply not_lt in H0.
        rewrite nth_error_app2 in Hnth1; auto.
        destruct (i - length lbs).
        simpl in Hnth1.
        inverts Hnth1.
        unfold INC in Hinc.
        specialize (Hinc 0 (S j) m m' t t').
        eapply Hinc; eauto.
        auto with arith.

        simpl in Hnth1. destruct n; simpl in Hnth1; tryfalse.
Qed.         

Theorem fifo_queue: 
  forall ens ens' lbs k, 
    que_ops ens ens' lbs k -> FIFO lbs.
Proof.
  intros.
  eapply fifo_ext_holds; eauto. 
Qed. 
