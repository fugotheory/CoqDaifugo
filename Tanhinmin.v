Require Import Coq.Init.Nat.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.


(*******************)
(* 帰納的な単貧民定義 *)
(*******************)

Inductive sorted : list nat -> Prop :=
  | sorted_nil  : sorted []
  | sorted_cons : forall l a,
      sorted l -> a <= hd a l ->
      sorted (a :: l).

Fixpoint list_remove (a : nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | x :: l' => if (x =? a) then l' else x :: (list_remove a l')
  end.

Definition hand := list nat.
Definition counth (h : hand) := length h.
Definition removeh := list_remove.
Definition containsh (a : nat) (h : hand) := In a h.

Inductive inductive_result_is : bool -> hand -> hand -> nat -> Prop :=
  | InductiveTerm
      (h0 h1 : hand) (r : nat)
      (Hc0 : 0 < counth h0) (Hc1 : counth h1 = 0) :
      inductive_result_is false h0 h1 r
  | InductivePutWin
      (h0 h1 : hand) (r a : nat)
      (Hp : containsh a h0) (Hr : r < a)
      (Hn : inductive_result_is false h1 (removeh a h0) a) :
      inductive_result_is true h0 h1 r
  | InductivePassWin
      (h0 h1 : hand) (r : nat)
      (Hn : inductive_result_is false h1 h0 0) :
      inductive_result_is true h0 h1 r
  | InductiveLose
      (h0 h1 : hand) (r : nat)
      (Hput : forall a : nat,
              containsh a h0 -> r < a ->
              inductive_result_is true h1 (removeh a h0) a)
      (Hpass : inductive_result_is true h1 h0 0) :
      inductive_result_is false h0 h1 r.

Example inductive_result_test1 : inductive_result_is false [2] [] 1.
Proof.
  apply InductiveTerm.
  - simpl. auto.
  - simpl. reflexivity.
Qed.

Example inductive_result_test2 : inductive_result_is true [1] [2] 0.
Proof.
  apply InductivePutWin with (a:=1).
  - simpl. auto.
  - auto.
  - apply inductive_result_test1.
Qed.

Example inductive_result_test3 : inductive_result_is false [2] [1;2] 2.
Proof.
  apply InductiveLose.
  - intros a Hp Hr.
    simpl in Hp.
    destruct Hp.
    + rewrite H in Hr.
      apply Nat.lt_irrefl in Hr.
      contradiction Hr.
    + contradiction H.
  - apply InductivePutWin with (a:=2).
    + simpl. auto.
    + auto.
    + simpl.
      apply InductiveLose.
      * intros a Hp Hr.
        simpl in Hp.
        destruct Hp.
        -- rewrite H in Hr.
           apply Nat.lt_irrefl in Hr.
           contradiction Hr.
        -- contradiction H.
      * apply inductive_result_test2.
Qed.


(*****************)
(* 証明のための定義 *)
(*****************)

Fixpoint sorted_list_insert (a : nat) (l : list nat) : list nat :=
  match l with
  | nil => a :: nil
  | x :: l' => if (a <=? x) then a :: x :: l' else x :: (sorted_list_insert a l')
  end.

Fixpoint list_min (l : list nat) : nat :=
  match l with
  | nil => 0
  | x :: nil => x
  | x :: l' => min x (list_min l')
  end.

Fixpoint list_nth_min (n : nat) (l : list nat) : nat :=
  match n with
  | 0 => list_min l
  | S n' => list_nth_min n' (list_remove (list_min l) l)
  end.

Fixpoint list_mingt (l : list nat) (r : nat) : nat :=
  match l with
  | nil => 0
  | x :: l' => (fun b => if (r <? x)
                         then (if (r <? b) then min x b else x)
                         else b) (list_mingt l' r)
  end.

Fixpoint mu_sorted_up (l1 l2 : list nat) : nat :=
  match l1, l2 with
  | nil, _ => 0
  | _, nil => 0
  | x1 :: l1', x2 :: l2' =>
      if x2 <? x1 then S (mu_sorted_up l1' l2') else mu_sorted_up l1' l2
  end.

Definition ap_sorted (l : list nat) : Prop :=
  sorted l /\ 0 < length l /\ 0 < list_min l.

Definition addh := sorted_list_insert.
Definition minh := list_min.
Definition maxh := list_max.
Definition mingth := list_mingt.
Definition removeminh (h : hand) := removeh (minh h) h.
Definition secondh (h : hand) := list_nth_min 1 h.

Definition mu := mu_sorted_up.

Example mu_test1 : mu [1;2;3] [1;2] = 2.
Proof. reflexivity. Qed.

Example mu_test2 : mu [0] [0] = 0.
Proof. reflexivity. Qed.

Example mul_test3 : mu [0;1;2] [] = 0.
Proof. reflexivity. Qed.

Definition mu0 (h0 h1 : hand) (r : nat) :=
  mu h0 (addh r (removeminh h1)).

Definition mu1 (h0 h1 : hand) :=
  mu h1 (removeminh h0).

Example test_mu0_1 : mu0 [2] [1] 0 = 1.
Proof. reflexivity. Qed.
Example test_mu0_2 : mu0 [1] [] 2 = 0.
Proof. reflexivity. Qed.
Example test_mu0_3 : mu0 [1;2;2] [1;1;1;2;2;2;2] 1 = 2.
Proof. reflexivity. Qed.
Example test_mu1_1 : mu1 [1;1] [2] = 1.
Proof. reflexivity. Qed.
Example test_mu1_2 : mu1 [1;2;2] [1;1;1;2;2;2;2] = 0.
Proof. reflexivity. Qed.

Definition mu_lose_cond (h0 h1 : hand) (r : nat) : Prop :=
  mu0 h0 h1 r <= mu1 h0 h1 ->
  inductive_result_is false h0 h1 r.

Definition mu_win_cond (h0 h1 : hand) (r : nat) : Prop :=
  mu0 h0 h1 r > mu1 h0 h1 ->
  inductive_result_is true h0 h1 r.


(******************)
(* 数式に関する補題 *)
(******************)

(* 補題 : min p q < p -> min p q = q *)
Lemma min_lt_l : forall p q : nat, min p q < p -> min p q = q.
Proof.
  intros p q H.
  assert (q <= p \/ p < q).
  { apply Nat.le_gt_cases. }
  destruct H0.
  - apply min_r in H0.
    apply H0.
  - apply Nat.lt_le_incl in H0.
    apply min_l in H0.
    rewrite H0 in H.
    apply Nat.lt_irrefl in H.
    contradiction H.
Qed.

(* 補題 : p < max p q -> max p q = q *)
Lemma max_lt_l : forall p q : nat, p < max p q -> max p q = q.
Proof.
  intros p q H.
  assert (p <= q \/ q < p).
  { apply Nat.le_gt_cases. }
  destruct H0.
  - apply max_r in H0.
    apply H0.
  - apply Nat.lt_le_incl in H0.
    apply max_l in H0.
    rewrite H0 in H.
    apply Nat.lt_irrefl in H.
    contradiction H.
Qed.


(********************)
(* リストに関する補題 *)
(********************)

(* 補題 : 最小の値は必ずリスト内にある *)
Lemma min_in : forall l : list nat,
  0 < length l -> In (list_min l) l.
Proof.
  intros l H.
  induction l as [| x1 l].
  - simpl in H.
    inversion H.
  - simpl.
    destruct l as [| x2 l]. 
    + simpl.
      left.
      reflexivity.
    + assert (x1 <= list_min (x2 :: l) \/ list_min (x2 :: l) < x1).
      { apply Nat.le_gt_cases. }
      destruct H0.
      * left.
        apply min_l in H0.
        symmetry.
        apply H0.
      * right.
        apply Nat.lt_le_incl in H0.
        apply min_r in H0.
        rewrite H0.
        apply IHl.
        simpl.
        apply Nat.lt_0_succ.
Qed.

(* 補題 : 最大の値は必ずリスト内にある *)
Lemma max_in : forall l : list nat,
  0 < length l -> In (list_max l) l.
Proof.
  intros l H.
  induction l as [| x1 l].
  - simpl in H.
    inversion H.
  - simpl.
    assert (x1 < (list_max l) \/ (list_max l) <= x1).
    { apply Nat.lt_ge_cases. }
    destruct H0.
    + right.
      apply Nat.lt_le_incl in H0 as H1.
      apply max_r in H1.
      rewrite H1.
      apply IHl.
      destruct l.
      * simpl in H0.
        inversion H0.
      * simpl.
        apply Nat.lt_0_succ.
    + left.
      apply max_l in H0.
      symmetry.
      apply H0.
Qed.

(* 補題 : 最小値 <= 最大値 *)
Lemma min_le_max : forall l : list nat,
  list_min l <= list_max l.
Proof.
  destruct l as [| x1 l].
  - simpl.
    reflexivity.
  - simpl.
    destruct l as [| x2 l].
    + simpl.
      rewrite max_0_r.
      reflexivity.
    + apply le_trans with (m:=x1).
      * apply Nat.le_min_l.
      * apply Nat.le_max_l.
Qed.

(* 補題 : 要素一つのとき最大値と最小値は同じ *)
Lemma min_eq_max_one : forall l : list nat,
  length l = 1 -> list_min l = list_max l.
Proof.
  intros l H.
  destruct l.
  - discriminate H.
  - destruct l.
    + simpl.
      symmetry.
      apply max_0_r.
    + simpl in H.
      apply eq_add_S in H.
      discriminate H.
Qed.

(* 補題 : insertした値は結果のリストに含まれている *)
Lemma insert_in : forall (l : list nat) (a : nat),
  In a (sorted_list_insert a l).
Proof.
  induction l as [| x l].
  - simpl.
    auto.
  - intros.
    simpl.
    destruct (a <=? x).
    + simpl.
      auto.
    + simpl.
      right.
      apply IHl.
Qed.

(* 補題 : insert後のリスト長 *)
Lemma insert_length : forall (l : list nat) (a : nat),
  length (sorted_list_insert a l) = S (length l).
Proof.
  intros.
  induction l as [| x1 l].
  - simpl.
    reflexivity.
  - simpl.
    destruct (a <=? x1).
    + simpl.
      reflexivity.
    + simpl.
      rewrite IHl.
      reflexivity.
Qed.

(* 補題 : remove後のリスト長 *)
Lemma remove_length : forall (l : list nat) (a : nat),
  length l <= S (length (list_remove a l)) /\ length (list_remove a l) <= length l.
Proof.
  intros.
  split.
  - induction l as [| x1 l].
    + simpl.
      auto.
    + simpl.
      destruct (x1 =? a).
      * reflexivity.
      * simpl.
        destruct l.
        -- simpl.
           auto.
        -- simpl.
           simpl in IHl.
           apply le_n_S.
           apply IHl.
  - induction l as [| x1 l].
    + simpl.
      reflexivity.
    + simpl.
      destruct (x1 =? a).
      * apply Nat.le_succ_diag_r.
      * simpl.
        apply le_n_S.
        apply IHl.
Qed.

(* 補題 : 含まれている値のremove後のリスト長 *)
Lemma remove_length_in : forall (l : list nat) (a : nat),
  In a l -> S (length (list_remove a l)) = length l.
Proof.
  intros.
  induction l as [| x1 l].
  - simpl in H.
    contradiction H.
  - simpl.
    destruct (x1 =? a) eqn:E.
    + reflexivity.
    + simpl.
      destruct H.
      * apply Nat.eqb_eq in H.
        rewrite H in E.
        discriminate E.
      * destruct l.
        -- simpl in H.
           contradiction H.
        -- rewrite IHl.
           ++ simpl.
              reflexivity.
           ++ apply H.
Qed.

(* 補題 : 値をinsertすると元のリストを分割する2つのリストに挟まれる *)
Fixpoint inserted_list_left (a : nat) (l : list nat) :=
  match l with
  | nil => nil
  | x :: l' => if a <=? x then nil else x :: (inserted_list_left a l')
  end.
Fixpoint inserted_list_right (a : nat) (l : list nat) :=
  match l with
  | nil => nil
  | x :: l' => if a <=? x then l else inserted_list_right a l'
  end.

Lemma insert_split : forall (l : list nat) (a : nat),
  exists l1 l2 : list nat,
  l = l1 ++ l2 /\ sorted_list_insert a l = l1 ++ a :: l2.
Proof.
  intros.
  exists (inserted_list_left a l).
  exists (inserted_list_right a l).
  induction l as [| x1 l].
  - simpl.
    auto.
  - simpl.
    destruct (a <=? x1).
    + simpl.
      auto.
    + simpl.
      destruct IHl as [IHl1 IHl2].
      split.
      * rewrite <- IHl1.
        reflexivity.
      * rewrite <- IHl2.
        reflexivity.
Qed.

(* 補題 : 値をremoveする際値を挟んで元のリストを構成する2つのリストに分けられる *)
Fixpoint removed_list_left (a : nat) (l : list nat) :=
  match l with
  | nil => nil
  | x :: l' => if a =? x then nil else x :: (removed_list_left a l')
  end.
Fixpoint removed_list_right (a : nat) (l : list nat) :=
  match l with
  | nil => nil
  | x :: l' => if a =? x then l' else removed_list_right a l'
  end.

Lemma remove_split : forall (l : list nat) (a : nat),
  In a l ->
  exists l1 l2 : list nat,
  l = l1 ++ a :: l2 /\ list_remove a l = l1 ++ l2.
Proof.
  intros.
  exists (removed_list_left a l).
  exists (removed_list_right a l).
  induction l as [| x1 l].
  - simpl in H.
    contradiction H.
  - simpl.
    destruct (a =? x1) eqn:E.
    + apply Nat.eqb_eq in E.
      symmetry in E.
      rewrite E.
      rewrite Nat.eqb_refl.
      simpl.
      auto.
    + simpl.
      apply beq_nat_false in E.
      destruct (x1 =? a) eqn:Ec.
      * apply Nat.eqb_eq in Ec.
        symmetry in Ec.
        apply E in Ec.
        contradiction Ec.
      * destruct H.
        -- symmetry in H.
           apply E in H.
           contradiction H.
        -- apply IHl in H.
           destruct H as [H1 H2].
           split.
           ++ rewrite <- H1.
              reflexivity.
           ++ rewrite <- H2.
              reflexivity.
Qed.

(* 補題 : 第n最小値は必ずリスト内にある *)
Lemma nth_min_in : forall (n : nat) (l : list nat),
  n < length l -> In (list_nth_min n l) l.
Proof.
  induction n.
  - simpl.
    apply min_in.
  - intros l H.
    simpl.
    assert (0 < length l) as Hl0.
    { apply lt_trans with (m:=S n).
      - apply Nat.lt_0_succ.
      - apply H. }
    assert (exists l1 l2 : list nat,
            l = l1 ++ (list_min l) :: l2 /\
            list_remove (list_min l) l = l1 ++ l2) as H0.
    { apply remove_split.
      apply min_in.
      apply Hl0. }
    destruct H0 as [l1 [l2 [H1 H2]]].
    rewrite H2.
    assert (In (list_nth_min n (l1 ++ l2)) (l1 ++ l2)) as H0.
    { apply IHn.
      rewrite <- H2.
      apply lt_S_n.
      rewrite remove_length_in.
      - apply H.
      - apply min_in.
        apply Hl0. }
    rewrite H1.
    apply in_app_or in H0.
    destruct H0 as [H0 | H0].
    + apply in_or_app.
      left.
      apply H0.
    + apply in_or_app.
      right.
      apply in_or_app with (l:=[list_min l]).
      right.
      apply H0.
Qed.

(* 補題 : 最小値は先頭とそれ以外の最小値の小さい方 *)
Lemma min_cons : forall (a : nat) (l : list nat),
  0 < length l -> list_min (a :: l) = min a (list_min l).
Proof.
  intros.
  destruct l as [| x l].
  - simpl in H.
    inversion H.
  - simpl.
    reflexivity.
Qed.

(* 補題 : 値をremoveすると最小値は元の最小値以上 *)
Lemma min_le_remove_min : forall (a : nat) (l : list nat),
  1 < length l -> list_min l <= list_min (list_remove a l).
Proof.
  intros.
  induction l as [| x1 l].
  - simpl in H.
    inversion H.
  - simpl in H.
    apply lt_S_n in H.
    assert (list_min (x1 :: l) = min x1 (list_min l)).
    { apply min_cons. apply H. }
    rewrite H0. clear H0.
    simpl.
    destruct (x1 =? a).
    + apply le_min_r.
    + assert (length l <= 1 \/ 1 < length l).
      { apply Nat.le_gt_cases. }
      destruct H0.
      * destruct l as [| x2 l].
        -- simpl in H.
           inversion H.
        -- simpl in H0.
           apply le_S_n in H0.
           apply le_n_0_eq in H0.
           symmetry in H0.
           apply length_zero_iff_nil in H0.
           subst.
           simpl.
           destruct (x2 =? a).
           ++ apply le_min_l.
           ++ simpl.
              reflexivity.
      * assert (list_min (x1 :: list_remove a l)
                = min x1 (list_min (list_remove a l))).
        { apply min_cons.
          apply lt_S_n. 
          apply lt_le_trans with (m:=length l).
          - apply H0.
          - apply remove_length. }
        rewrite H1. clear H1.
        apply Nat.min_le_compat_l.
        apply IHl.
        apply H0.
Qed.

(* 補題 : リストに含まれる値はリストの最小値〜最大値の範囲にある *)
Lemma in_range_min_max : forall (l : list nat) (a : nat),
  In a l ->
  list_min l <= a <= list_max l.
Proof.
  intros.
  split.
  - induction l as [| x1 l].
    + simpl in H.
      contradiction H.
    + destruct l as [| x2 l].
      * simpl.
        simpl in H.
        destruct H as [H | H].
        -- rewrite H.
           reflexivity.
        -- contradiction H.
      * remember (x2 :: l) as ll.
        simpl. 
        rewrite Heqll.
        rewrite Heqll in IHl.
        rewrite Heqll in H.
        apply Nat.min_le_iff.
        destruct H.
        -- left.
           rewrite H.
           reflexivity.
        -- right.
           apply IHl.
           apply H.
  - induction l as [| x1 l].
    + simpl in H.
      contradiction H.
    + simpl.
      apply Nat.max_le_iff.
      destruct H.
      * left.
        rewrite H.
        reflexivity.
      * right.
        apply IHl.
        apply H.
Qed.

(* 補題 : リストの最大値が閾値を越えれば、閾値を超える最小値も閾値を超えている *)
Lemma mingt_gt_if_max_gt : forall (l : list nat) (r : nat),
  r < list_max l ->
  r < list_mingt l r.
Proof.
  intros.
  induction l as [| x1 l].
  - simpl in H.
    inversion H.
  - simpl.
    destruct (r <? x1) eqn:E1.
    + apply Nat.ltb_lt in E1.
      destruct (x1 <? list_mingt l r) eqn:E2.
      * apply Nat.ltb_lt in E2.
        assert (r < list_mingt l r) as E3.
        { apply lt_trans with (m:=x1).
          apply E1. apply E2. }
        apply Nat.ltb_lt in E3.
        rewrite E3.
        apply Nat.lt_le_incl in E2.
        apply min_l in E2.
        rewrite E2.
        apply E1.
      * apply Nat.ltb_ge in E2.
        apply min_r in E2.
        rewrite E2.
        destruct (r <? list_mingt l r) eqn:E3.
        -- apply Nat.ltb_lt in E3.
           apply E3.
        -- apply E1.
    + apply IHl.
      simpl in H.
      apply Nat.ltb_ge in E1.
      assert (x1 < Init.Nat.max x1 (list_max l)) as E2.
      { apply le_lt_trans with (m:=r).
        apply E1. apply H. }
SearchPattern(_ < max _ _ -> _).
      apply max_lt_l in E2.
      rewrite E2 in H.
      apply H.
Qed.

(* 補題 : 閾値を超える最小値が閾値を超えていれば、リストに含まれる *)
Lemma mingt_in_if_gt : forall (l : list nat) (r : nat),
  r < list_mingt l r ->
  In (list_mingt l r) l.
Proof.
  intros.
  induction l as [| x1].
  - simpl in H.
    inversion H.
  - simpl.
    destruct (r <? x1) eqn:E1.
    + apply Nat.ltb_lt in E1.
      destruct (x1 <? list_mingt l r) eqn:E2.
      * apply Nat.ltb_lt in E2.
        assert (r < list_mingt l r) as E3.
        { apply lt_trans with (m:=x1).
          apply E1. apply E2. }
        apply Nat.ltb_lt in E3.
        rewrite E3.
        apply Nat.lt_le_incl in E2.
        apply min_l in E2.
        rewrite E2.
        left.
        reflexivity.
      * apply Nat.ltb_ge in E2.
        apply min_r in E2.
        rewrite E2.
        destruct (r <? list_mingt l r) eqn:E3.
        -- right.
           apply IHl.
           apply Nat.ltb_lt in E3.
           apply E3.
        -- left.
           reflexivity.
    + simpl in H.
      rewrite E1 in H.
      right.
      apply IHl.
      apply H.
Qed.


(***************************)
(* ソート済みリストに関する補題 *)
(***************************)

(* 補題 : 要素一つのリストはソート済み *)
Lemma sorted_one : forall a : nat,
  sorted [a].
Proof.
  intros.
  apply sorted_cons.
  - constructor.
  - simpl. reflexivity.
Qed.

(* 補題 : ソート済みリストは分割してもソート済み(前) *)
Lemma sorted_split_left : forall (l1 l2 : list nat),
  sorted (l1 ++ l2) -> sorted l1.
Proof.
  induction l1.
  - constructor.
  - destruct l1.
    + intros.
      apply sorted_one.
    + intros.
      inversion H.
      apply sorted_cons.
      * apply IHl1 with l2.
        apply H2.
      * simpl.
        simpl in H3.
        apply H3.
Qed.

(* 補題 : ソート済みリストは分割してもソート済み(後) *)
Lemma sorted_split_right : forall (l1 l2 : list nat),
  sorted (l1 ++ l2) -> sorted l2.
Proof.
  induction l1.
  - trivial.
  - intros.
    inversion H.
    apply IHl1.
    apply H2.
Qed.

(* 補題 : ソート済みリストから間を抜いてもソート済み(先頭1つ) *)
Lemma sorted_remove_middle_hd : forall (l1 l2 : list nat) (a : nat),
  sorted (a :: l1 ++ l2) -> sorted (a :: l2).
Proof.
  intros.
  induction l1.
  - apply H.
  - apply IHl1.
    inversion H.
    inversion H2.
    constructor.
    + apply H6.
    + simpl in H3.
      destruct (l1 ++ l2).
      * reflexivity.
      * apply le_trans with (m:=a0).
        -- apply H3.
        -- apply H7.
Qed.

(* 補題 : ソート済みリストから間を抜いてもソート済み *)
Lemma sorted_remove_middle : forall (l1 l2 l3 : list nat),
  sorted (l1 ++ l2 ++ l3) -> sorted (l1 ++ l3).
Proof.
  intros.
  induction l1.
  - simpl.
    induction l2.
    + apply H.
    + simpl in H.
      simpl in IHl2.
      inversion H. 
      apply IHl2.
      apply H2.
  - simpl.
    inversion H.
    constructor.
    + apply IHl1.
      apply H2.
    + destruct l1.
      * simpl.
        simpl in H.
        apply sorted_remove_middle_hd in H.
        inversion H.
        apply H7.
      * apply H3.
Qed.

(* 補題 : ソート済みリスト内の任意の値の比較 *)
Lemma sorted_all_le : forall (l1 l2 l3 : list nat) (x1 x2 : nat),
  sorted (l1 ++ x1 :: l2 ++ x2 :: l3) -> x1 <= x2.
Proof.
  intros.
  induction l1 as [| y1 l1].
  - induction l2 as [| z1 l2].
    + simpl in H.
      inversion H.
      simpl in H3.
      apply H3.
    + simpl in H.
      inversion H.
      simpl in H3.
      apply IHl2.
      simpl.
      inversion H2.
      apply sorted_cons.
      * apply H6.
      * simpl in H7.
        simpl.
        apply le_trans with (m:=z1).
        -- apply H3.
        -- destruct l2 as [| z2 l2].
           ++ simpl.
              simpl in H7.
              apply H7.
           ++ simpl.
              simpl in H7.
              apply H7.
  - apply IHl1.
    simpl.
    simpl in H.
    inversion H.
    apply H2.
Qed.

(* 補題 : insertの挙動 先頭の値以下なら先頭に付けるのと同じ *)
Lemma sorted_insert_cons : forall (l : list nat) (a : nat),
  sorted l -> a <= hd a l -> sorted_list_insert a l = a :: l.
Proof.
  intros.
  induction l as [| x l].
  - reflexivity.
  - simpl.
    destruct (a <=? x) eqn:E.
    + simpl.
      reflexivity.
    + simpl in H0.
      apply Nat.leb_le in H0.
      rewrite H0 in E.
      discriminate E.
Qed.

(* 補題 : insertの挙動 値を挿入してもソート済みが保たれる *)
Lemma sorted_insert_sorted : forall (l : list nat) (a : nat),
  sorted l -> sorted (sorted_list_insert a l).
Proof.
  intros l a H.
  induction l as [| x1 l].
  - simpl.
    apply sorted_one.
  - simpl.
    destruct (a <=? x1) eqn:E1.
    + constructor.
      * apply H.
      * simpl. apply Nat.leb_le in E1. apply E1.
    + apply leb_complete_conv in E1.
      destruct l as [| x2 l].
      * simpl.
        constructor.
        -- apply sorted_one.
        -- simpl. apply Nat.lt_le_incl in E1. apply E1.
      * simpl.
        simpl in IHl.
        destruct (a <=? x2) eqn:E2.
        -- constructor.
           ++ constructor.
              ** inversion H. apply H2.
              ** simpl. apply Nat.leb_le in E2. apply E2.
           ++ simpl. apply Nat.lt_le_incl in E1. apply E1.
        -- constructor.
           ++ apply IHl.
              inversion H. apply H2.
           ++ simpl.
              inversion H. simpl in H3. apply H3.
Qed.

(* 補題 : removeの 値を除いてもソート済みが保たれる *)
Lemma sorted_remove_sorted : forall (l : list nat) (a : nat),
  sorted l -> sorted (list_remove a l).
Proof.
  intros l a H.
  induction l as [| x1 l].
  - simpl.
    constructor.
  - simpl.
    destruct (x1 =? a) eqn:E1.
    + inversion H.
      apply H2.
    + inversion H.
      constructor.
      * apply IHl.
        apply H2.
      * destruct l as [| x2 l].
        -- simpl.
           reflexivity.
        -- simpl.
           simpl in H3.
           destruct (x2 =? a) eqn:E2.
           ++ simpl.
              destruct l as [| x3 l].
              ** simpl.
                 reflexivity.
              ** simpl.
                 simpl in H3.
                 inversion H2.
                 simpl in H7.
                 apply le_trans with (m:=x2).
                 --- apply H3.
                 --- apply H7.
           ++ simpl.
              apply H3.
Qed.

(* 補題 : ソート済みリストの先頭は最小値 *)
Lemma sorted_min_is_hd : forall l : list nat,
  sorted l -> list_min l = hd 0 l.
Proof.
  induction l.
  - reflexivity.
  - intros.
    simpl.
    destruct l.
    + reflexivity.
    + inversion H.
      simpl in H3.
      rewrite IHl.
      * simpl.
        rewrite min_l.
        -- reflexivity.
        -- apply H3.
     * apply H2.
Qed.

(* 補題 : ソート済みリストの最後尾は最大値 *)
Lemma sorted_max_is_last : forall l : list nat,
  sorted l -> list_max l = last l 0.
Proof.
  induction l.
  - reflexivity.
  - intros.
    simpl.
    destruct l.
    + apply max_0_r.
    + simpl.
      inversion H.
      simpl in H3.
      rewrite max_assoc.
      rewrite max_r with (n:=a).
      * simpl in IHl.
        apply IHl.
        apply H2.
      * apply H3.
Qed.

(* 補題 : ソート済みリストのn番目は第n最小値 *)
Lemma sorted_nth_min_is_nth : forall (n : nat) (l : list nat),
  sorted l -> list_nth_min n l = nth n l 0.
Proof.
  induction n.
  - intros.
    simpl.
    destruct l as [| x1 l].
    + simpl.
      reflexivity.
    + rewrite sorted_min_is_hd.
      * simpl.
        reflexivity.
      * apply H.
  - intros.
    simpl.
    destruct l as [| x1 l].
    + simpl.
      rewrite IHn.
      simpl.
      destruct n.
      * reflexivity.
      * reflexivity.
      * apply H.
    + rewrite sorted_min_is_hd.
      * simpl.
        rewrite Nat.eqb_refl.
        apply IHn.
        inversion H.
        apply H2.
      * apply H.
Qed.

(* 補題 : ソート済みリストからremoveしてinsertすれば元のリストに戻る *)
Lemma sorted_remove_insert : forall (l : list nat) (a : nat),
  sorted l -> In a l -> sorted_list_insert a (list_remove a l) = l.
Proof.
  intros l a H1 H2.
  induction l as [| x1 l].
  - simpl in H2.
    contradiction H2.
  - simpl.
    assert (a <= x1 \/ x1 < a).
    { apply Nat.le_gt_cases. }
    destruct H.
    + destruct (x1 =? a) eqn:E.
      * apply Nat.eqb_eq in E.
        rewrite <- E.
        inversion H1.
        rewrite sorted_insert_cons.
        -- reflexivity.
        -- apply H4.
        -- apply H5.
      * apply in_range_min_max in H2.
        destruct H2 as [H2 _].
        apply sorted_min_is_hd in H1.
        rewrite H1 in H2.
        simpl in H2.
        assert (x1 = a) as Ec.
        { apply Nat.le_antisymm.
          - apply H2.
          - apply H. }
        apply Nat.eqb_eq in Ec.
        rewrite E in Ec.
        discriminate Ec.
    + destruct (x1 =? a) eqn:E.
      * apply Nat.eqb_eq in E.
        rewrite E in H.
        apply Nat.lt_irrefl in H.
        contradiction H.
      * simpl.
        apply leb_correct_conv in H.
        rewrite H.
        rewrite IHl.
        -- reflexivity.
        -- inversion H1.
           apply H4.
        -- simpl in H2.
           destruct H2 as [H2 | H2].
           ++ apply Nat.eqb_eq in H2.
              rewrite E in H2.
              discriminate H2.
           ++ apply H2.
Qed.

(* 補題 : ソート済みリストの先頭と最後尾が同じなら組み替え可能 *)
Lemma sorted_unif_swap : forall (l : list nat) (a : nat),
  sorted (a :: l ++ [a]) -> a :: l = l ++ [a].
Proof.
  intros.
  induction l as [| x1 l].
  - simpl.
    reflexivity.
  - simpl.
    assert (x1 = a) as E.
    { apply Nat.le_antisymm.
      - simpl in H.
        apply sorted_all_le with (l1:=[a]) in H.
        apply H.
      - inversion H.
        simpl in H3.
        apply H3. }
    rewrite E.
    rewrite IHl.
    + reflexivity.
    + inversion H.
      rewrite E in H2.
      apply H2.
Qed.

(* 補題 : ソート済みリストからすでに見つけた値をremoveすれば見つけた値の両側を合わせたリストになる *)
Lemma sorted_remove_inv : forall (l1 l2 : list nat) (a : nat),
  sorted (l1 ++ a :: l2) ->
  list_remove a (l1 ++ a :: l2) = l1 ++ l2.
Proof.
  intros.
  induction l1 as [| x1 l1].
  - simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - simpl.
    destruct (x1 =? a) eqn:E.
    + apply Nat.eqb_eq in E.
      rewrite E.
      replace (a :: l1 ++ l2) with ((a :: l1) ++ l2).
      * rewrite sorted_unif_swap with (l:=l1).
        -- rewrite <- app_assoc.
           simpl.
           reflexivity.
        -- simpl in H.
           rewrite E in H.
           replace (a :: l1 ++ a :: l2) with ((a :: l1 ++ [a]) ++ l2) in H.
           ++ apply sorted_split_left with (l1:=a :: l1 ++ [a]) in H.
              apply H.
           ++ simpl.
              rewrite <- app_assoc.
              reflexivity.
      * simpl.
        reflexivity.
    + rewrite IHl1.
      * reflexivity.
      * inversion H.
        apply H2.
Qed.

(* 補題 : ソート済みリストで基準値より大きい最小の値があればリストを分割できる *)
Lemma sorted_mingt_split : forall (l : list nat) (y : nat),
  sorted l ->
  y < (list_mingt l y) ->
  exists l1 l2, l = l1 ++ (list_mingt l y) :: l2 /\ list_max l1 <= y.
Proof.
  intros l y Hs Hp.
  exists (inserted_list_left (S y) l).
  exists (tl (inserted_list_right (S y) l)).
  remember (S y) as y'.
  split.
  - induction l as [| x1 l].
    + simpl in Hp.
      apply Nat.nlt_0_r in Hp.
      contradiction Hp.
    + simpl.
      destruct (y' <=? x1) eqn:E1.
      * assert (y < x1) as E2.
        { apply Nat.leb_le in E1.
          rewrite Heqy' in E1.
          apply Nat.le_succ_l.
          apply E1. }
        apply Nat.ltb_lt in E2.
        rewrite E2.
        simpl.
        destruct (y <? list_mingt l y) eqn:E3.
        -- rewrite Nat.ltb_lt in E3.
           destruct l as [| x2 l].
           ++ simpl in E3.
              apply Nat.nlt_0_r in E3.
              contradiction E3.
           ++ apply mingt_in_if_gt in E3 as E4.
              apply in_range_min_max in E4.
              destruct E4 as [E4 _].
              rewrite sorted_min_is_hd in E4.
              ** unfold hd in E4.
                 assert (x1 <= list_mingt (x2 :: l) y) as E5.
                 { apply le_trans with (m:=x2).
                   - inversion Hs. simpl in H2. apply H2.
                   - apply E4. }
                 apply min_l in E5.
                 rewrite E5.
                 reflexivity.
              ** inversion Hs.
                 apply H1.
        -- reflexivity.
      * apply leb_complete_conv in E1.
        rewrite Heqy' in E1.
        apply lt_n_Sm_le in E1.
        destruct (y <? x1) eqn:E2.
        -- apply Nat.ltb_lt in E2.
           apply lt_not_le in E2.
           apply E2 in E1.
           contradiction E1.
        -- simpl.
           rewrite <- IHl.
           ++ reflexivity.
           ++ inversion Hs. apply H1.
           ++ simpl in Hp.
              rewrite E2 in Hp.
              apply Hp.
  - induction l as [| x1 l].
    + simpl in Hp.
      apply Nat.nlt_0_r in Hp.
      contradiction Hp.
    + simpl.
      destruct (y' <=? x1) eqn:E.
      * simpl.
        apply Nat.le_0_l.
      * simpl.
        apply leb_complete_conv in E.
        rewrite Heqy' in E.
        apply lt_n_Sm_le in E.
        apply max_lub.
        -- apply E.
        -- apply IHl.
           ++ inversion Hs. apply H1.
           ++ simpl in Hp.
              destruct (y <? x1) eqn:E2.
              ** apply Nat.ltb_lt in E2.
                 apply lt_not_le in E2.
                 apply E2 in E.
                 contradiction E.
              ** apply Hp.
Qed.



(************************)
(* マッチング数に関する補題 *)
(************************)

(* 補題 : μ ([], l) = 0 *)
Lemma mu_nil_0_l : forall l : list nat,
  mu [] l = 0.
Proof.
  simpl.
  reflexivity.
Qed.

(* 補題 : μ (l, []) = 0 *)
Lemma mu_nil_0_r : forall l : list nat,
  mu l [] = 0.
Proof.
  destruct l.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

(* 補題 : μ (l1, l2) <= |l1| *)
Lemma mu_le_length1 : forall l1 l2 : list nat,
  mu l1 l2 <= length l1.
Proof.
  induction l1 as [| x1 l1].
  - simpl.
    reflexivity.
  - destruct l2 as [| x2 l2].
    + simpl.
      apply Nat.lt_le_incl.
      apply Nat.lt_0_succ.
    + simpl.
      destruct (x2 <? x1).
      * apply le_n_S.
        apply IHl1.
      * apply le_S.
        apply IHl1.
Qed.

(* 補題 : μ (l1, l2) <= |l2| *)
Lemma mu_le_length2 : forall l1 l2 : list nat,
  mu l1 l2 <= length l2.
Proof.
  induction l1 as [| x1 l1].
  - induction l2.
    + simpl.
      reflexivity.
    + simpl.
      apply Nat.lt_le_incl.
      apply Nat.lt_0_succ.
  - induction l2 as [| x2 l2].
    + simpl.
      reflexivity.
    + simpl.
      destruct (x2 <? x1).
      * apply le_n_S.
        apply IHl1.
      * apply IHl1.
Qed.

(* 補題 : μ(l1, l2) <= μ (x::l1, l2) <= S (μ(l1, l2)) *)
(* 補題 : μ(l1, l2) <= μ (l1, y::l2) <= S (μ(l1, l2)) *)

Lemma mu_le_mu_cons2 : forall (l1 l2 : list nat) (y : nat),
  sorted l1 /\ sorted (y :: l2) ->
  mu l1 l2 <= mu l1 (y :: l2).
Proof.
  induction l1 as [| x1 l1].
  - simpl.
    reflexivity.
  - intros.
    simpl.
    destruct l2 as [| y1 l2].
    + destruct (y <? x1).
      * rewrite mu_nil_0_r.
        auto.
      * apply Nat.le_0_l.
    + destruct H as [Hs1 Hs2].
      inversion Hs1.
      inversion Hs2.
      destruct (y1 <? x1) eqn:E1.
      * destruct (y <? x1) eqn:E2.
        -- apply le_n_S.
           apply IHl1.
           split. apply H1. apply H5.
        -- simpl in H6.
           apply Nat.ltb_lt in E1.
           assert (y < x1).
           { apply le_lt_trans with (m:=y1).
             apply H6. apply E1. }
           apply Nat.ltb_lt in H7.
           rewrite H7 in E2.
           discriminate E2.
      * destruct (y <? x1) eqn:E.
        -- apply Nat.le_succ_diag_r.
        -- apply IHl1.
           split. apply H1. apply Hs2.
Qed.

Lemma mu_cons2_le_S_mu : forall (l1 l2 : list nat) (y : nat),
  sorted l1 /\ sorted (y :: l2) ->
  mu l1 (y :: l2) <= S (mu l1 l2).
Proof.
  induction l1 as [| x1 l1].
  - simpl.
    auto.
  - intros.
    simpl.
    destruct l2 as [| y1 l2].
    + destruct (y <? x1).
      * rewrite mu_nil_0_r.
        reflexivity.
      * apply mu_le_length2.
    + destruct H as [Hs1 Hs2].
      inversion Hs1.
      inversion Hs2.
      destruct (y <? x1).
      * destruct (y1 <? x1).
        -- apply le_n_S.
           apply IHl1.
           split. apply H1. apply H5.
        -- reflexivity.
      * destruct (y1 <? x1).
        -- apply le_trans with (m:=S (mu l1 (y1 :: l2))).
           ++ apply IHl1.
              split. apply H1. apply Hs2.
           ++ apply le_n_S.
              apply IHl1.
              split. apply H1. apply H5.
        -- apply IHl1.
           split. apply H1. apply Hs2.
Qed.

Lemma mu_le_mu_cons1 : forall (l1 l2 : list nat) (x : nat),
  sorted (x :: l1) /\ sorted l2 ->
  mu l1 l2 <= mu (x :: l1) l2.
Proof.
  destruct l2 as [| y1 l2].
  - simpl.
    rewrite mu_nil_0_r.
    reflexivity.
  - intros.
    simpl.
    destruct H as [Hs1 Hs2].
    inversion Hs1.
    inversion Hs2.
    + destruct (y1 <? x).
      * apply mu_cons2_le_S_mu.
        split. apply H1. apply Hs2.
      * reflexivity.
Qed.

Lemma mu_cons1_le_S_mu : forall (l1 l2 : list nat) (x : nat),
  sorted (x :: l1) /\ sorted l2 ->
  mu (x :: l1) l2 <= S (mu l1 l2).
Proof.
  destruct l2 as [| y1 l2].
  - simpl.
    rewrite mu_nil_0_r.
    auto.
  - intros.
    simpl.
    destruct H as [Hs1 Hs2].
    inversion Hs1.
    inversion Hs2.
    + destruct (y1 <? x).
      * apply le_n_S.
        apply mu_le_mu_cons2.
        split. apply H1. apply Hs2.
      * apply Nat.le_succ_diag_r.
Qed.

(* 補題 : μ(l1++l3, l2) <= μ (l1++x::l3, l2) <= S (μ(l1++l3, l2)) *)
(* 補題 : μ(l1, l2++l3) <= μ (l1, l2++y::l3) <= S (μ(l1, l2++l3)) *)

Lemma mu_le_mu_ins1 : forall (l1 l2 l3 : list nat) (x : nat),
  sorted (l1 ++ x :: l2) /\ sorted l3 ->
  mu (l1 ++ l2) l3 <= mu (l1 ++ x :: l2) l3.
Proof.
  intros l1 l2 l3 x [Hs1 Hs2].
  generalize dependent l3.
  induction l1 as [| x1 l1].
  - intros.
    apply mu_le_mu_cons1.
    split. apply Hs1. apply Hs2.
  - intros.
    destruct l3 as [| y1 l3].
    + rewrite !mu_nil_0_r.
      reflexivity.
    + simpl.
      destruct (y1 <? x1).
      * apply le_n_S.
        apply IHl1.
        -- inversion Hs1. apply H1.
        -- inversion Hs2. apply H1.
      * apply IHl1 with (l3:=y1 :: l3).
        -- inversion Hs1. apply H1.
        -- apply Hs2.
Qed.

Lemma mu_le_mu_ins2 : forall (l1 l2 l3 : list nat) (y : nat),
  sorted l1 /\ sorted (l2 ++ y :: l3) ->
  mu l1 (l2 ++ l3) <= mu l1 (l2 ++ y :: l3).
Proof.
  intros l1 l2 l3 y [Hs1 Hs2].
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - intros.
    simpl.
    reflexivity.
  - intros.
    destruct l2 as [| y1 l2].
    + apply mu_le_mu_cons2.
      split. apply Hs1. apply Hs2.
    + simpl.
      destruct (y1 <? x1).
      * apply le_n_S.
        apply IHl1.
        -- inversion Hs1. apply H1.
        -- inversion Hs2. apply H1.
      * apply IHl1 with (l2:=y1 :: l2).
        -- inversion Hs1. apply H1.
        -- apply Hs2.
Qed.

Lemma mu_ins1_le_S_mu : forall (l1 l2 l3 : list nat) (x : nat),
  sorted (l1 ++ x :: l3) /\ sorted l2 ->
  mu (l1 ++ x :: l3) l2 <= S (mu (l1 ++ l3) l2).
Proof.
  intros l1 l2 l3 x [Hs1 Hs2].
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - intros.
    apply mu_cons1_le_S_mu.
    split. apply Hs1. apply Hs2.
  - intros.
    destruct l2 as [| y1 l2].
    + rewrite !mu_nil_0_r.
      auto.
    + simpl.
      destruct (y1 <? x1).
      * apply le_n_S.
        apply IHl1.
        -- inversion Hs1. apply H1.
        -- inversion Hs2. apply H1.
      * apply IHl1 with (l2:=y1 :: l2).
        -- inversion Hs1. apply H1.
        -- apply Hs2.
Qed.

Lemma mu_ins2_le_S_mu : forall (l1 l2 l3 : list nat) (y : nat),
  sorted l1 /\ sorted (l2 ++ y :: l3) ->
  mu l1 (l2 ++ y :: l3) <= S (mu l1 (l2 ++ l3)).
Proof.
  intros l1 l2 l3 y [Hs1 Hs2].
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - intros.
    simpl.
    auto.
  - intros.
    destruct l2 as [| y1 l2].
    + destruct l3 as [| z1 l3].
      * simpl.
        destruct (y <? x1).
        -- apply le_n_S.
           rewrite mu_nil_0_r.
           reflexivity.
        -- apply mu_le_length2.
      * simpl.
        destruct (z1 <? x1) eqn:E1.
        -- assert (y < x1) as E2.
           { apply le_lt_trans with (m:=z1).
             - inversion Hs2.
               simpl in H2. apply H2.
             - apply Nat.ltb_lt in E1.
               apply E1. }
           apply Nat.ltb_lt in E2.
           rewrite E2.
           apply le_n_S.
           apply mu_cons2_le_S_mu.
           split.
           ++ inversion Hs1. apply H1.
           ++ inversion Hs2. apply H1.
        -- destruct (y <? x1).
           ++ reflexivity.
           ++ apply IHl1 with (l2:=[]).
              ** inversion Hs1. apply H1.
              ** apply Hs2.
    + simpl.
      destruct (y1 <? x1).
      * apply le_n_S.
        apply IHl1.
        -- inversion Hs1. apply H1.
        -- inversion Hs2. apply H1.
      * apply IHl1 with (l2:=y1 :: l2).
        -- inversion Hs1. apply H1.
        -- apply Hs2.
Qed.

(* 補題: 左側の先頭の値の比較 *)
Lemma mu_compare_hd1 : forall (l1 l2 : list nat) (x y : nat),
  sorted (y :: l1) /\ sorted l2 ->
  x <= y ->
  mu (x :: l1) l2 <= mu (y :: l1) l2.
Proof.
  intros l1 l2 x y [Hs1 Hs2] Hr.
  induction l2 as [| y1 l2].
  - simpl.
    reflexivity.
  - simpl.
    destruct (y1 <? x) eqn:E1.
    + assert (y1 < y) as E2.
      { apply lt_le_trans with (m:=x).
        - apply Nat.ltb_lt in E1. apply E1.
        - apply Hr. }
      apply Nat.ltb_lt in E2.
      rewrite E2.
      reflexivity.
    + destruct (y1 <? y).
      * apply mu_cons2_le_S_mu.
        inversion Hs1.
        split.
        apply H1. apply Hs2.
      * reflexivity.
Qed.

(* 補題: 右側の先頭の値の比較 *)
Lemma mu_compare_hd2 : forall (l1 l2 : list nat) (x y : nat),
  sorted l1 /\ sorted (x :: l2) ->
  y <= x ->
  mu l1 (x :: l2) <= mu l1 (y :: l2).
Proof.
  intros l1 l2 x y [Hs1 Hs2] Hr.
  induction l1 as [| x1 l1].
  - simpl.
    reflexivity.
  - simpl.
    destruct (x <? x1) eqn:E1.
    + assert (y < x1) as E2.
      { apply le_lt_trans with (m:=x).
        - apply Hr.
        - apply Nat.ltb_lt in E1. apply E1. }
      apply Nat.ltb_lt in E2.
      rewrite E2.
      reflexivity.
    + destruct (y <? x1).
      * apply mu_cons2_le_S_mu.
        inversion Hs1.
        split.
        apply H1. apply Hs2.
      * apply IHl1.
        inversion Hs1.
        apply H1.
Qed.

(* 補題 : 左の最弱以降の札は強くてもμに影響しない(一枚) *)
Lemma mu_eq_change_too_low : forall (l1 l2 : list nat) (x y y' : nat),
  sorted (x :: l1) /\ sorted (y' :: y :: l2) ->
  y < x ->
  mu l1 (y' :: l2) = mu l1 (y :: l2).
Proof.
  intros l1 l2 x y y' [Hs1 Hs2] Hr.
  destruct l1 as [| x1 l1].
  - simpl.
    reflexivity.
  - simpl.
    assert (y < x1) as E1.
    { apply lt_le_trans with (m:=x).
      - apply Hr.
      - inversion Hs1.
        simpl in H2. apply H2. }
    assert (y' < x1) as E2.
    { apply le_lt_trans with (m:=y).
      - inversion Hs2.
        simpl in H2.
        apply H2.
      - apply E1. }
    apply Nat.ltb_lt in E1.
    apply Nat.ltb_lt in E2.
    rewrite E1.
    rewrite E2.
    reflexivity.
Qed.

(* 補題 : 左の最弱以降の札は強くてもμに影響しない *)
Lemma mu_eq_change_too_low_list : forall (l1 l2 l3 : list nat) (x y y' : nat),
  sorted (x :: l1) /\ sorted (y' :: l2 ++ y :: l3) ->
  y < x ->
  mu l1 (y' :: l2 ++ l3) = mu l1 (l2 ++ y :: l3).
Proof.
  intros l1 l2 l3 x y y' [Hs1 Hs2] Hr.
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - simpl.
    reflexivity.
  - simpl.
    intros.
    assert (y < x1) as E1.
    { apply lt_le_trans with (m:=x).
      - apply Hr.
      - inversion Hs1.
        simpl in H2.
        apply H2. }
    assert (y' < x1) as E2.
    { apply le_lt_trans with (m:=y).
      - apply sorted_all_le with (l1:=[]) in Hs2.
        apply Hs2.
      - apply E1. }
    apply Nat.ltb_lt in E1.
    apply Nat.ltb_lt in E2.
    destruct l2 as [| y1 l2].
    + simpl.
      rewrite E1.
      rewrite E2.
      reflexivity.
    + simpl.
      assert (y1 < x1) as E3.
      { apply le_lt_trans with (m:=y).
        - apply sorted_all_le with (l1:=[y']) in Hs2.
          apply Hs2.
        - apply Nat.ltb_lt in E1.
          apply E1. }
      apply Nat.ltb_lt in E3.
      rewrite E2.
      rewrite E3.
      apply eq_S.
      assert (mu l1 (y' :: l2 ++ l3) = mu l1 (y1 :: l2 ++ l3)) as E4.
      { apply mu_eq_change_too_low with (l1:=l1) (x:=x1).
        - inversion Hs1.
          split. apply H1.
          apply sorted_remove_middle with (l1:=y'::y1::l2) (l2:=[y]) in Hs2.
          simpl in Hs2.
          apply Hs2.
        - apply Nat.ltb_lt in E3.
          apply E3. }
      rewrite <- E4.
      apply IHl1.
      * apply sorted_remove_middle with (l1:=[x]) (l2:=[x1]) in Hs1.
        simpl in Hs1.
        apply Hs1.
      * simpl in Hs2.
        apply sorted_remove_middle with (l1:=[y']) (l2:=[y1]) in Hs2.
        simpl in Hs2.
        apply Hs2.
Qed.

(* 補題 : 任意の1組のペアの取り出し *)
Lemma mu_squeeze_one : forall (l1 l2 l3 l4 : list nat) (x y : nat),
  sorted (l1 ++ x :: l3) /\ sorted (l2 ++ y :: l4) ->
  y < x ->
  1 <= mu (l1 ++ x :: l3) (l2 ++ y :: l4).
Proof.
  intros l1 l2 l3 l4 x y [H1 H2] E1.
  induction l1 as [| x1 l1].
  - destruct l2 as [| y1 l2].
    + simpl.
      apply Nat.ltb_lt in E1.
      rewrite E1.
      apply le_n_S.
      apply Nat.le_0_l.
    + simpl.
      assert (y1 < x) as E2.
      { apply le_lt_trans with (m:=y).
        - apply sorted_all_le with (l1:=[]) in H2.
          apply H2.
        - apply E1. }
      apply Nat.ltb_lt in E2.
      rewrite E2.
      apply le_n_S.
      apply Nat.le_0_l.
  - destruct l2 as [| y1 l2].
    + simpl.
      destruct (y <? x1) eqn:E2.
      * apply le_n_S.
        apply Nat.le_0_l.
      * apply IHl1.
        inversion H1. apply H3.
    + simpl.
      destruct (y1 <? x1) eqn:E2.
      * apply le_n_S.
        apply Nat.le_0_l.
      * apply IHl1.
        inversion H1. apply H3.
Qed.

(* 補題 : 任意の1組のペアの追加 (左先頭) *)
Lemma mu_ins_eq_S_mu_hd1 : forall (l1 l2 l3 : list nat) (x y : nat),
  sorted (x :: l1) /\ sorted (l2 ++ y :: l3) ->
  y < x ->
  mu (x :: l1) (l2 ++ y :: l3) = S (mu l1 (l2 ++ l3)).
Proof.
  intros l1 l2 l3 x y [Hs1 Hs2] Hr.
  generalize dependent x.
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - intros.
    simpl.
    destruct l2 as [| y1 l2].
    * simpl.
      apply Nat.ltb_lt in Hr.
      rewrite Hr.
      reflexivity.
    * simpl.
      assert (y1 < x) as E.
      { apply le_lt_trans with (m:=y).
        - apply sorted_all_le with (l1:=[]) in Hs2.
          apply Hs2.
        - apply Hr. }
      apply Nat.ltb_lt in E.
      rewrite E.
      reflexivity.
  - intros.
    destruct l2 as [| y1 l2].
    + simpl.
      apply Nat.ltb_lt in Hr.
      rewrite Hr.
      reflexivity.
    + assert (y1 < x) as E1.
      { apply le_lt_trans with (m:=y).
        - apply sorted_all_le with (l1:=[]) in Hs2.
          apply Hs2.
        - apply Hr. }
      assert (y1 < x1) as E2.
      { apply lt_le_trans with (m:=x).
        - apply E1. 
        - inversion Hs1.
          simpl in H2.
          apply H2. }
      remember (x1 :: l1) as ll1.
      rewrite <- app_assoc with (l:=[y1]) (m:=l2).
      remember (l2 ++ y :: l3) as ll2.
      simpl.
      apply Nat.ltb_lt in E1.
      rewrite E1.
      apply eq_S.
      rewrite Heqll1.
      rewrite Heqll1 in Hs1.
      clear Heqll1.
      remember (mu (x1 :: l1) ll2) as ls.
      simpl.
      apply Nat.ltb_lt in E2.
      rewrite E2.
      rewrite Heqls.
      subst.
      apply IHl1 with (x:=x1).
      * inversion Hs2.
        apply H1.
      * inversion Hs1.
        apply H1.
      * apply lt_le_trans with (m:=x).
        -- apply Hr.
        -- inversion Hs1.
           simpl in H2.
           apply H2.
Qed.

(* 補題 : 任意の1組の値の追加下界 (右先頭) *)
Lemma mu_lt_mu_ins_prod_hd2 : forall (l1 l2 l3 : list nat) (x y : nat),
  sorted (l1 ++ x :: l3) /\ sorted (y :: l2) ->
  y < x ->
  mu (l1 ++ l3) l2 < mu (l1 ++ x :: l3) (y :: l2).
Proof.
  intros l1 l2 l3 x y [Hs1 Hs2] Hr.
  generalize dependent y.
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - intros.
    simpl.
    apply Nat.ltb_lt in Hr.
    rewrite Hr.
    apply Nat.lt_succ_diag_r.
  - intros.
    simpl.
    destruct l2 as [| y1 l2].
    + rewrite mu_nil_0_r.
      destruct (y <? x1).
      * auto.
      * replace 0 with (mu (l1 ++ l3) []).
        -- apply IHl1 with (l2:=[]).
           ++ inversion Hs1. apply H1.
           ++ apply Hs2.
           ++ apply Hr.
        -- rewrite mu_nil_0_r.
           reflexivity.
    + destruct (y1 <? x1) eqn:E1.
      * assert (y < x1) as E2.
        { apply le_lt_trans with (m:=y1).
          - inversion Hs2.
            simpl in H2.
            apply H2.
          - apply Nat.ltb_lt in E1.
            apply E1. }
        apply Nat.ltb_lt in E2.
        rewrite E2.
        apply lt_n_S.
        apply IHl1 with (y:=y1).
        -- inversion Hs1.
           apply H1.
        -- inversion Hs2.
           apply H1.
        -- apply lt_le_trans with (m:=x1).
           ++ apply Nat.ltb_lt in E1.
              apply E1.
           ++ simpl in Hs1.
              apply sorted_all_le with (l1:=[]) in Hs1.
              apply Hs1.
      * destruct (y <? x1).
        -- apply le_lt_n_Sm.
           apply mu_le_mu_ins1.
           split.
           ++ inversion Hs1. apply H1.
           ++ inversion Hs2. apply H1.
        -- apply IHl1 with (l2:=y1 :: l2).
           ++ inversion Hs1. apply H1.
           ++ apply Hs2.
           ++ apply Hr.
Qed.

(* 補題 : 任意の1組の値の追加下界 *)
Lemma mu_lt_mu_ins_prod : forall (l1 l2 l3 l4 : list nat) (x y : nat),
  sorted (l1 ++ x :: l3) /\ sorted (l2 ++ y :: l4) ->
  y < x ->
  mu (l1 ++ l3) (l2 ++ l4) < mu (l1 ++ x :: l3) (l2 ++ y :: l4).
Proof.
  intros l1 l2 l3 l4 x y [Hs1 Hs2] Hr.
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - intros.
    apply Nat.le_succ_l.
    apply Nat.eq_le_incl.
    symmetry.
    apply mu_ins_eq_S_mu_hd1.
    + split. apply Hs1. apply Hs2.
    + apply Hr.
  - destruct l2 as [| y1 l2].
    + intros.
      apply mu_lt_mu_ins_prod_hd2.
      * split. apply Hs1. apply Hs2.
      * apply Hr.
    + intros.
      simpl.
      destruct (y1 <? x1).
      * apply lt_n_S.
        apply IHl1.
        -- inversion Hs1. apply H1.
        -- inversion Hs2. apply H1.
      * apply IHl1 with (l2:=y1 :: l2).
        -- inversion Hs1. apply H1.
        -- apply Hs2.
Qed.

(* 補題 : 任意の1組のペアでない値の追加上界（左先頭） *)
Lemma mu_nonp_ins_le_S_mu_hd1 : forall (l1 l2 l3 : list nat) (x y : nat),
  sorted (x :: l1) /\ sorted (l2 ++ y :: l3) ->
  x <= y ->
  mu (x :: l1) (l2 ++ y :: l3) <= S (mu l1 (l2 ++ l3)).
Proof.
  intros l1 l2 l3 x y [Hs1 Hs2] Hr.
  generalize dependent x.
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - intros.
    rewrite mu_nil_0_l.
    apply mu_le_length1.
  - intros.
    destruct l2 as [| y1 l2].
    + remember (x1 :: l1) as ll1.
      simpl.
      apply Nat.ltb_ge in Hr.
      rewrite Hr.
      subst.
      apply mu_cons2_le_S_mu.
      split.
      * inversion Hs1. apply H1.
      * apply Hs2.
    + remember (x1 :: l1) as ll1.
      simpl.
      subst.
      destruct (y1 <? x) eqn:E1.
      * apply le_n_S.
        rewrite mu_ins_eq_S_mu_hd1 with (l2:=[]) (y:=y1) (l3:=l2 ++ l3).
        -- assert (x1 <= y \/ y < x1) as E2.
           { apply Nat.le_gt_cases. }
           destruct E2 as [E2 | E2].
           ++ apply IHl1 with (l2:=l2) (x:=x1).
              ** inversion Hs2. apply H1.
              ** inversion Hs1. apply H1.
              ** apply E2.
           ++ rewrite mu_ins_eq_S_mu_hd1.
              ** reflexivity.
              ** split.
                 --- inversion Hs1. apply H1.
                 --- inversion Hs2. apply H1.
              ** apply E2.
        -- split.
           ++ inversion Hs1. apply H1.
           ++ apply sorted_remove_middle with (l2:=[y]) in Hs2.
              apply Hs2.
        -- apply lt_le_trans with (m:=x).
           ++ apply Nat.ltb_lt in E1.
              apply E1.
           ++ inversion Hs1. simpl in H2. apply H2.
      * apply mu_ins2_le_S_mu with (l2:=y1 :: l2).
        split.
        -- inversion Hs1. apply H1.
        -- apply Hs2.
Qed.

(* 補題 : 任意の1組のペアでない値の追加上界（右先頭） *)
Lemma mu_nonp_ins_le_S_mu_hd2 : forall (l1 l2 l3 : list nat) (x y : nat),
  sorted (l1 ++ x :: l3) /\ sorted (y :: l2) ->
  x <= y ->
  mu (l1 ++ x :: l3) (y :: l2) <= S (mu (l1 ++ l3) l2).
Proof.
  intros l1 l2 l3 x y [Hs1 Hs2] Hr.
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - intros.
    simpl.
    apply Nat.ltb_ge in Hr.
    rewrite Hr.
    apply mu_cons2_le_S_mu.
    split.
    + inversion Hs1. apply H1.
    + apply Hs2.
  - intros.
    destruct l2 as [| y1 l2].
    + rewrite mu_nil_0_r.
      apply mu_le_length2.
    + simpl.
      assert (x1 <= y) as E1.
      { apply le_trans with (m:=x).
        - apply sorted_all_le with (l1:=[]) in Hs1.
          apply Hs1.
        - apply Hr. }
      assert (x1 <= y1) as E2.
      { apply le_trans with (m:=y).
        - apply E1.
        - inversion Hs2. simpl in H2. apply H2. }
      apply Nat.ltb_ge in E1.
      apply Nat.ltb_ge in E2.
      rewrite E1.
      rewrite E2.
      apply IHl1 with (l2:=y1 :: l2).
      * inversion Hs1. apply H1.
      * apply Hs2.
Qed.

(* 補題 : 任意の1組のペアでない値の追加上界 *)
Lemma mu_nonp_ins_le_S_mu : forall (l1 l2 l3 l4 : list nat) (x y : nat),
  sorted (l1 ++ x :: l3) /\ sorted (l2 ++ y :: l4) ->
  x <= y ->
  mu (l1 ++ x :: l3) (l2 ++ y :: l4) <= S (mu (l1 ++ l3) (l2 ++ l4)).
Proof.
  intros l1 l2 l3 l4 x y [Hs1 Hs2] Hr.
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - intros.
    apply mu_nonp_ins_le_S_mu_hd1.
    + split.
      * apply Hs1.
      * apply Hs2.
    + apply Hr.
  - intros.
    destruct l2 as [| y1 l2].
    + apply mu_nonp_ins_le_S_mu_hd2.
      * split.
        -- apply Hs1.
        -- apply Hs2.
      * apply Hr.
    + simpl.
      destruct (y1 <? x1).
      * apply le_n_S.
        apply IHl1 with (l2:=l2).
        -- inversion Hs1. apply H1.
        -- inversion Hs2. apply H1.
      * apply IHl1 with (l2:=y1 :: l2).
        -- inversion Hs1. apply H1.
        -- apply Hs2.
Qed.

(* 補題 : 任意の1組の値の追加上界 *)
Lemma mu_ins_le_S_S_mu : forall (l1 l2 l3 l4 : list nat) (x y : nat),
  sorted (l1 ++ x :: l3) /\ sorted (l2 ++ y :: l4) ->
  mu (l1 ++ x :: l3) (l2 ++ y :: l4) <= S (S (mu (l1 ++ l3) (l2 ++ l4))).
Proof.
  intros.
  apply le_trans with (m:=S (mu (l1 ++ x :: l3) (l2 ++ l4))).
  - apply mu_ins2_le_S_mu.
    apply H.
  - apply le_n_S.
    apply mu_ins1_le_S_mu.
    destruct H as [H1 H2].
    split.
    + apply H1.
    + apply sorted_remove_middle with (l2:=[y]).
      apply H2.
Qed.

(* 補題 : 出せる最小の組の追加（左先頭1つ） *)
Lemma mu_ins_mingt_eq_S_mu_hd1_one : forall (l1 l2 l3 : list nat) (x1 x2 y : nat),
  sorted (x1 :: x2 :: l1) /\ sorted (l2 ++ y :: l3) ->
  x1 <= y ->
  y < x2 ->
  mu (x1 :: x2 :: l1) (l2 ++ y :: l3) = S (mu (x1 :: l1) (l2 ++ l3)).
Proof.
  intros l1 l2 l3 x1 x2 y [Hs1 Hs2] Hr1 Hr2.
  destruct l2 as [| y1 l2].
  - simpl.
    apply Nat.ltb_ge in Hr1.
    rewrite Hr1.
    apply Nat.ltb_lt in Hr2.
    rewrite Hr2.
    apply eq_S.
    destruct l3 as [| z1 l3].
    + apply mu_nil_0_r.
    + assert (x1 <= z1) as E.
      { apply le_trans with (m:=y).
        - apply Nat.ltb_ge in Hr1.
          apply Hr1.
        - inversion Hs2.
          simpl in H2.
          apply H2. }
      apply Nat.ltb_ge in E.
      rewrite E.
      reflexivity.
  - simpl.
    destruct (y1 <? x1).
    + destruct l2 as [| y2 l2].
      * simpl.
        apply Nat.ltb_lt in Hr2.
        rewrite Hr2.
        reflexivity.
      * simpl.
        apply eq_S.
        assert (y2 < x2) as E.
        { apply le_lt_trans with (m:=y).
          - simpl in Hs2.
            apply sorted_all_le with (l1:=[y1]) in Hs2.
            apply Hs2.
         - apply Hr2. }
        apply Nat.ltb_lt in E.
        rewrite E.
        apply eq_S.
        symmetry.
        apply mu_eq_change_too_low_list with (x:=x2).
        -- split.
           ++ inversion Hs1. apply H1.
           ++ inversion Hs2. apply H1.
        -- apply Hr2.
    + assert (y1 < x2) as E.
      { apply le_lt_trans with (m:=y).
        - simpl in Hs2.
          apply sorted_all_le with (l1:=[]) in Hs2.
          apply Hs2.
        - apply Hr2. }
      apply Nat.ltb_lt in E.
      rewrite E.
      apply eq_S.
      symmetry.
      apply mu_eq_change_too_low_list with (x:=x2).
      * split.
        ** inversion Hs1. apply H1.
        ** apply Hs2.
      * apply Hr2.
Qed.

(* 補題 : 出せる最小の組の追加（右先頭） *)
Lemma mu_ins_mingt_eq_S_mu_hd2_one : forall (l1 l2 l3 : list nat) (x1 x2 y : nat),
  sorted (l1 ++ x1 :: x2 :: l3) /\ sorted (y :: l2) ->
  x1 <= y ->
  y < x2 ->
  mu (l1 ++ x1 :: x2 :: l3) (y :: l2) = S (mu (l1 ++ x1 :: l3) l2).
Proof.
  intros l1 l2 l3 x1 x2 y [Hs1 Hs2] Hr1 Hr2.
  generalize dependent l2.
  induction l1 as [| z1 l1].
  - intros.
    apply mu_ins_mingt_eq_S_mu_hd1_one with (l2:=[]).
    + split.
      * apply Hs1.
      * apply Hs2.
    + apply Hr1.
    + apply Hr2.
  - intros.
    simpl.
    simpl in Hs1.
    assert (z1 <= y) as E1.
    { apply le_trans with (m:=x1).
      - apply sorted_all_le with (l1:=[]) (x2:=x1) in Hs1.
        apply Hs1.
      - apply Hr1. }
    apply Nat.ltb_ge in E1.
    rewrite E1.
    destruct l2 as [| y1 l2].
    + replace 1 with (S (mu (l1 ++ x1 :: l3) [])).
      * apply IHl1 with (l2:=[]).
        -- inversion Hs1. apply H1.
        -- apply sorted_one.
      * apply eq_S.
        apply mu_nil_0_r.
    + assert (z1 <= y1) as E2.
      { apply le_trans with (m:=y).
        - apply Nat.ltb_ge in E1.
          apply E1.
        - inversion Hs2.
          simpl in H2.
          apply H2. }
      apply Nat.ltb_ge in E2.
      rewrite E2.
      apply IHl1 with (l2:=y1 :: l2).
      * inversion Hs1. apply H1.
      * apply Hs2.
Qed.

(* 補題 : 出せる最小の組の追加 *)
Lemma mu_ins_mingt_eq_S_mu : forall (l1 l2 l3 l4 : list nat) (x1 x2 y : nat),
  sorted (l1 ++ x1 :: x2 :: l3) /\ sorted (l2 ++ y :: l4) ->
  x1 <= y ->
  y < x2 ->
  mu (l1 ++ x1 :: x2 :: l3) (l2 ++ y :: l4) = S (mu (l1 ++ x1 :: l3) (l2 ++ l4)).
Proof.
  intros l1 l2 l3 l4 x1 x2 y [Hs1 Hs2] Hr1 Hr2.
  generalize dependent l2.
  induction l1 as [| z1 l1].
  - intros.
    apply mu_ins_mingt_eq_S_mu_hd1_one.
    + split. apply Hs1. apply Hs2.
    + apply Hr1.
    + apply Hr2.
  - intros.
    destruct l2 as [| y1 l2].
    + apply mu_ins_mingt_eq_S_mu_hd2_one.
      * split. apply Hs1. apply Hs2.
      * apply Hr1.
      * apply Hr2.
    + simpl.
      destruct (y1 <? z1).
      * apply eq_S.
        apply IHl1.
        -- inversion Hs1. apply H1.
        -- inversion Hs2. apply H1.
      * apply IHl1 with (l2:=y1 :: l2).
        -- inversion Hs1. apply H1.
        -- apply Hs2.
Qed.

(* 補題 : 左の最大以上の札を右から抜いてもマッチング数が変化しない *)
Lemma mu_remove_ge_right_eq_mu : forall (l1 l2 l3 : list nat) (y : nat),
  sorted l1 /\ sorted (l2 ++ y :: l3) ->
  list_max l1 <= y ->
  mu l1 (l2 ++ l3) = mu l1 (l2 ++ y :: l3).
Proof.
  intros l1 l2 l3 y [Hs1 Hs2] Hr.
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - intros.
    simpl.
    reflexivity.
  - intros.
    simpl in Hr.
    destruct l2 as [| y1 l2].
    + remember (x1 :: l1) as ll1.
      simpl.
      subst.
      remember (mu (x1 :: l1) l3) as mut.
      simpl.
      subst.
      assert (x1 <= y) as E1.
      { apply max_lub_l in Hr.
        apply Hr. }
      apply Nat.ltb_ge in E1.
      rewrite E1.
      destruct l3 as [| y2 l3].
      * rewrite mu_nil_0_r.
        rewrite <- mu_nil_0_r with (l:=l1).
        apply IHl1 with (l2:=[]).
        -- inversion Hs1. apply H1.
        -- apply max_lub_r in Hr.
           apply Hr.
        -- apply Hs2.
      * simpl.
        assert (x1 <= y2) as E2.
        { apply le_trans with (m:=y).
          - apply Nat.ltb_ge in E1. apply E1.
          - inversion Hs2. simpl in H2. apply H2. }
        apply Nat.ltb_ge in E2.
        rewrite E2.
        apply IHl1 with (l2:=[]).
        -- inversion Hs1. apply H1.
        -- apply max_lub_r in Hr.
           apply Hr.
        -- apply Hs2.
    + simpl.
      destruct (y1 <? x1).
      * apply eq_S.
        apply IHl1.
        -- inversion Hs1. apply H1.
        -- apply max_lub_r in Hr.
           apply Hr.
        -- inversion Hs2. apply H1.
      * apply IHl1 with (l2:=y1 :: l2).
        -- inversion Hs1. apply H1.
        -- apply max_lub_r in Hr.
           apply Hr.
        -- apply Hs2.
Qed.

(* 補題 : 右の最小以下の札を左から抜いてもマッチング数が変化しない *)
Lemma mu_remove_le_left_eq_mu : forall (l1 l2 l3 : list nat) (x : nat),
  sorted (l1 ++ x :: l3) /\ sorted l2 ->
  x <= list_min l2 ->
  mu (l1 ++ l3) l2 = mu (l1 ++ x :: l3) l2.
Proof.
  intros l1 l2 l3 x [Hs1 Hs2] Hr.
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - intros.
    destruct l2 as [| y1 l2].
    + rewrite !mu_nil_0_r.
      reflexivity.
    + simpl.
      rewrite sorted_min_is_hd in Hr.
      * simpl in Hr.
        apply Nat.ltb_ge in Hr.
        rewrite Hr.
        reflexivity.
      * apply Hs2.
  - intros.
    destruct l2 as [| y1 l2].
    + rewrite !mu_nil_0_r.
      reflexivity.
    + simpl.
      assert (x1 <= y1) as E.
      { apply le_trans with (m:=x).
        - apply sorted_all_le with (l1:=[]) in Hs1.
          apply Hs1.
        - rewrite sorted_min_is_hd in Hr.
          + apply Hr.
          + apply Hs2. }
      apply Nat.ltb_ge in E.
      rewrite E.
      apply IHl1 with (l2:=y1 :: l2).
      * inversion Hs1.
        apply H1.
      * apply Hs2.
      * apply Hr.
Qed.

(* 補題 : フルマッチングでないとき、左最弱のさらに下の札が来ればマッチング数は1増える *)
Lemma mu_cons2_w_eq_S_mu_if_ne : forall (l1 l2 l3 : list nat) (y : nat),
  sorted l1 /\ sorted (l2 ++ y :: l3) ->
  y < list_min l1 ->
  mu l1 (l2 ++ l3) < length l1 ->
  mu l1 (l2 ++ y :: l3) = S (mu l1 (l2 ++ l3)).
Proof.
  intros l1 l2 l3 y [Hs0 Hs1] Hr Hmu.
  generalize dependent y.
  generalize dependent l3.
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - intros.
    simpl in Hmu.
    inversion Hmu.
  - intros.
    assert (y < x1) as Hr2.
    { rewrite sorted_min_is_hd with (l:=x1 :: l1) in Hr.
      - simpl in Hr. apply Hr.
      - apply Hs0. }
    destruct l2 as [| y1 l2].
    + destruct l3 as [| z1 l3].
      * simpl.
        apply Nat.ltb_lt in Hr2.
        rewrite Hr2.
        rewrite mu_nil_0_r.
        reflexivity.
      * simpl.
        apply Nat.ltb_lt in Hr2.
        rewrite Hr2.
        destruct (z1 <? x1) eqn:E.
        -- apply eq_S.
           apply IHl1 with (l2:=[]) (y:=z1).
           ++ inversion Hs0. apply H1.
           ++ simpl in Hmu.
              rewrite E in Hmu.
              apply lt_S_n in Hmu.
              apply Hmu.
           ++ inversion Hs1.
              apply H1.
           ++ destruct l1 as [| x2 l1]. 
              ** simpl in Hmu.
                 rewrite E in Hmu.
                 apply Nat.lt_irrefl in Hmu.
                 contradiction Hmu.
              ** rewrite sorted_min_is_hd.
                 --- simpl.
                     apply lt_le_trans with (m:=x1).
                     +++ apply Nat.ltb_lt in E.
                         apply E.
                     +++ inversion Hs0.
                         simpl in H2. apply H2.
                 --- inversion Hs0. apply H1.
        -- reflexivity.
    + simpl.
      assert (y1 < x1) as E.
      { apply le_lt_trans with (m:=y).
        - simpl in Hs1.
          apply sorted_all_le with (l1:=[]) in Hs1.
          apply Hs1.
        - apply Hr2. }
      apply Nat.ltb_lt in E.
      rewrite E.
      apply eq_S.
      apply IHl1.
      * inversion Hs0. apply H1.
      * simpl in Hmu.
        rewrite E in Hmu.
        apply lt_S_n in Hmu.
        apply Hmu.
      * inversion Hs1. apply H1.
      * destruct l1 as [| x2 l1]. 
        -- simpl in Hmu.
           rewrite E in Hmu.
           apply Nat.lt_irrefl in Hmu.
           contradiction Hmu.
        -- simpl in Hr.
           apply Nat.min_glb_lt_iff in Hr.
           destruct Hr as [Hrm1 Hrm2].
           simpl.
           apply Hrm2.
Qed.

(* 補題 : 左交換によりマッチング数が減る場合は後方の全てがマッチしている *)
Lemma mu_fm_if_mu_swap21_eq_S_mu : forall (l1 l2 : list nat) (x1 x2 : nat),
  sorted (x1 :: x2 :: l1) /\ sorted l2 ->
  mu (x2 :: l1) l2 = S (mu (x1 :: l1) l2) ->
  mu (x2 :: l1) l2 = S (length l1).
Proof.
  intros l1 l2 x1 x2 [Hs1 Hs2] Hmu.
  generalize dependent x2.
  generalize dependent l2.
  induction l1 as [| x3 l1].
  - intros.
    assert (mu [x1] l2 = 0).
    { apply Nat.le_antisymm.
      - apply le_S_n.
        rewrite <- Hmu.
        apply mu_le_length1.
      - apply Nat.le_0_l. }
    rewrite H in Hmu. clear H.
    rewrite Hmu.
    simpl.
    reflexivity.
  - intros.
    destruct l2 as [| y1 l2].
    + rewrite !mu_nil_0_r in Hmu.
      discriminate Hmu.
    + remember (x3 :: l1) as ll1.
      simpl.
      simpl in Hmu.
      destruct (y1 <? x2) eqn:E1.
      * apply eq_S.
        simpl in Hmu.
        assert (y1 < x3) as E2.
        { apply Nat.ltb_lt in E1.
          apply lt_le_trans with (m:=x2).
          - apply E1.
          - inversion Hs1.
            inversion H1.
            subst.
            simpl in H6.
            apply H6. }
        apply Nat.ltb_lt in E2.
        -- destruct (y1 <? x1) eqn:E3.
           ++ apply Nat.neq_succ_diag_r in Hmu.
               contradiction Hmu.
           ++ apply eq_add_S in Hmu.
              subst.
              remember (mu (x3 :: l1) l2) as mut.
              simpl in Hmu.
              rewrite E2 in Hmu.
              subst.
              apply IHl1 with (x2:=x3).
              ** inversion Hs2.
                 apply H1.
              ** apply sorted_remove_middle with (l1:=[x1]) (l2:=[x2]) in Hs1.
                 apply Hs1.
              ** rewrite Hmu.
                 apply eq_S.
                 destruct l2 as [| y2 l2].
                 --- rewrite !mu_nil_0_r.
                     reflexivity.
                 --- apply mu_remove_le_left_eq_mu with (l1:=[]) (l2:=y2 :: l2).
                     +++ split.
                         *** apply sorted_remove_middle with (l1:=[x1]) (l2:=[x2;x3]) in Hs1.
                             apply Hs1.
                         *** inversion Hs2.
                              apply H1.
                     +++ rewrite sorted_min_is_hd.
                         *** simpl.
                             apply le_trans with (m:=y1).
                             ---- apply Nat.ltb_ge in E3.
                                  apply E3.
                             ---- inversion Hs2.
                                  simpl in H2.
                                  apply H2.
                         *** inversion Hs2.
                             apply H1.
      * assert (x1 <= y1) as E2.
        { apply le_trans with (m:=x2).
          - inversion Hs1.
            simpl in H2.
            apply H2.
          - apply Nat.ltb_ge in E1.
            apply E1. }
        apply Nat.ltb_ge in E2.
        rewrite E2 in Hmu.
        apply Nat.neq_succ_diag_r in Hmu.
        contradiction Hmu.
Qed.

(* 補題 : 左の二番目+右抜きによりマッチング数が2減る場合は全ての札がマッチしている *)
Lemma mu_fm_if_SS_mu_remove21_eq_mu : forall (l1 l2 l3 : list nat) (x1 x2 y : nat),
  sorted (x1 :: x2 :: l1) /\ sorted (l2 ++ y :: l3) ->
  mu (x1 :: x2 :: l1) (l2 ++ y :: l3) = S (S (mu (x1 :: l1) (l2 ++ l3))) ->
  mu (x1 :: x2 :: l1) (l2 ++ y :: l3) = S (S (length l1)).
Proof.
  intros l1 l2 l3 x1 x2 y [Hs1 Hs2] Hmu.
  destruct (y <? x1) eqn:E1.
  - assert (mu (x1 :: x2 :: l1) (l2 ++ y :: l3) = S (mu (x2 :: l1) (l2 ++ l3))) as H.
    { apply mu_ins_eq_S_mu_hd1 with (x:=x1) (y:=y).
      - split.
        + apply Hs1.
        + apply Hs2.
      - apply Nat.ltb_lt in E1.
        apply E1. }
    rewrite H.
    rewrite H in Hmu.
    apply eq_S.
    apply eq_add_S in Hmu.
    apply mu_fm_if_mu_swap21_eq_S_mu with (x1:=x1).
    + split.
      * apply Hs1.
      * apply sorted_remove_middle with (l2:=[y]) in Hs2.
        apply Hs2.
    + apply Hmu.
  - destruct (y <? x2) eqn:E2.
    + assert (mu (x1 :: x2 :: l1) (l2 ++ y :: l3) = S (mu (x1 :: l1) (l2 ++ l3))) as H.
      { apply mu_ins_mingt_eq_S_mu_hd1_one.
        - split.
          + apply Hs1.
          + apply Hs2.
        - apply Nat.ltb_ge in E1.
          apply E1.
        - apply Nat.ltb_lt in E2.
          apply E2. }
      rewrite H in Hmu.
      apply Nat.neq_succ_diag_r in Hmu.
      contradiction Hmu.
    + apply Nat.ltb_ge in E2.
      assert (mu (x1 :: x2 :: l1) (l2 ++ y :: l3) <= S (mu (x1 :: l1) (l2 ++ l3))) as H.
      { apply mu_nonp_ins_le_S_mu with (l1:=[x1]).
        - split.
          + apply Hs1.
          + apply Hs2.
        - apply E2. }
      rewrite Hmu in H.
      apply Nat.nle_succ_diag_l in H.
      contradiction H.
Qed.

(* 補題 : 右先頭の交換でマッチングが増えた場合のマッチング数の上限 *)
Lemma mu_le_len2_if_mu_swap_eq_S_mu : forall (l1 l2 : list nat) (y1 y2 : nat),
  sorted l1 /\ sorted (y1 :: y2 :: l2) ->
  mu l1 (y1 :: l2) = S (mu l1 (y2 :: l2)) ->
  mu l1 (y2 :: l2) <= length l2.
Proof.
  intros l1 l2 y1 y2 [Hs1 Hs2] Hmu.
  generalize dependent l2.
  induction l1 as [| x1 l1].
  - intros.
    simpl in Hmu.
    discriminate Hmu.
  - intros.
    simpl.
    simpl in Hmu.
    destruct (y2 <? x1) eqn:E1.
    + assert (y1 < x1) as E2.
      { apply le_lt_trans with (m:=y2).
        - inversion Hs2.
          simpl in H2.
          apply H2.
        - apply Nat.ltb_lt in E1.
          apply E1. }
      apply Nat.ltb_lt in E2.
      rewrite E2 in Hmu.
      apply Nat.neq_succ_diag_r in Hmu.
      contradiction Hmu.
    + destruct (y1 <? x1) eqn:E2.
      * apply eq_add_S in Hmu.
        rewrite <- Hmu.
        apply mu_le_length2.
      * apply IHl1.
        -- inversion Hs1.
           apply H1.
        -- apply Hs2.
        -- apply Hmu.
Qed.


(**********************)
(* 手札の性質に関する補題 *)
(**********************)

(* 補題 : 最大の札が出せなければ出せる札がない *)
Lemma forced_pass_cond : forall (h : hand) (r : nat),
  maxh h <= r -> (forall a : nat, ~(containsh a h /\ r < a)).
Proof.
  intros h r Hm a [Hp Hr].
  apply in_range_min_max in Hp.
  assert (a <= r) as H.
  { apply le_trans with (m:=maxh h).
    - apply Hp.
    - apply Hm. }
  - apply le_not_lt in H.
    apply H.
    apply Hr.
Qed.

(* 補題 : removeminhの展開を短縮 *)
Lemma unfold_removeminh : forall (h : hand) (a : nat),
  sorted (a :: h) -> removeminh (a :: h) = h.
Proof.
  intros.
  unfold removeminh.
  rewrite sorted_min_is_hd.
  - simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - apply H.
Qed.

(* removeの挙動 2枚以上なら値を除いてもAPソート済みが保たれる *)
Lemma ap_sorted_remove_ap_sorted : forall (h : hand) (a : nat),
  ap_sorted h -> 1 < counth h -> ap_sorted (removeh a h).
Proof.
  intros.
  split.
  - apply sorted_remove_sorted.
    apply H.
  - split.
    + apply lt_S_n.
      apply le_trans with (m:=counth h).
      * apply H0.
      * apply remove_length.
    + apply lt_le_trans with (m:=list_min h).
      * apply H.
      * apply min_le_remove_min.
        apply H0.
Qed.

(****************************)
(* 手札マッチング数に関する補題 *)
(****************************)

(* 補題 : μ0 <= S (pred |h1|) |h1| = 0 のときに注意 *)
Lemma mu0_le_S_pred_nh1 : forall (h0 h1 : hand) (r : nat),
  0 < counth h1 ->
  mu0 h0 h1 r <= counth h1.
Proof.
  intros.
  unfold mu0.
  assert (counth h1 = counth (addh r (removeminh h1))).
  { rewrite insert_length.
    unfold removeminh.
    symmetry.
    apply remove_length_in.
    apply min_in.
    apply H. }
  rewrite H0.
  apply mu_le_length2.
Qed.

(* 補題 : μ1 <= pred |h0| |h0| = 0 のときに注意 *)
Lemma mu0_le_pred_nh0 : forall (h0 h1 : hand),
  mu1 h0 h1 <= pred (counth h0).
Proof.
  intros.
  unfold mu1.
  destruct h0 as [| x h0].
  - simpl.
    apply mu_le_length2.
  - remember (x :: h0) as hh0.
    unfold removeminh.
    rewrite <- remove_length_in with (a:=minh hh0).
    + simpl.
      apply mu_le_length2.
    + apply min_in.
      subst.
      simpl.
      apply Nat.lt_0_succ.
Qed.

(* 補題 : 出せる札がある -> μ0 > 0 *)
Lemma puttable_mu0_gt_0 : forall (h0 h1 : hand) (r : nat),
  sorted h0 /\ sorted h1 ->
  r < maxh h0 ->
  0 < mu0 h0 h1 r.
Proof.
  intros h0 h1 r [Hs0 Hs1] Hr.
  unfold mu0.
  assert (exists (h0f h0b : hand), h0 = h0f ++ (maxh h0) :: h0b) as H0.
  { apply in_split. apply max_in.
    destruct h0.
    - simpl in Hr. apply Nat.nlt_0_r in Hr. contradiction Hr.
    - simpl. apply Nat.lt_0_succ. }
  destruct H0 as [h0f [H0b H0]].
  assert (exists (h1f h1b : hand), addh r (removeminh h1) = h1f ++ r :: h1b) as H1.
  { apply in_split. apply insert_in. }
  destruct H1 as [h1f [H1b H1]].
  rewrite H0, H1.
  apply mu_squeeze_one.
  - rewrite <- H0, <- H1.
    split.
    + apply Hs0.
    + apply sorted_insert_sorted.
      apply sorted_remove_sorted.
      apply Hs1.
  - apply Hr.
Qed.

(* 補題 : μ0 = 0 -> 出せる札がない *)
Lemma mu0_eq_0_not_puttable : forall (h0 h1 : hand) (r : nat),
  sorted h0 /\ sorted h1 ->
  mu0 h0 h1 r = 0 ->
  maxh h0 <= r.
Proof.
  intros h0 h1 r Hs Hmu.
  assert (maxh h0 <= r \/ r < maxh h0) as Hr.
  { apply Nat.le_gt_cases. }
  destruct Hr.
  - apply H.
  - assert (0 < mu0 h0 h1 r) as Hcontra.
    { apply puttable_mu0_gt_0.
      apply Hs. apply H. }
    rewrite Hmu in Hcontra.
    inversion Hcontra.
Qed.

(* 補題 : 出せる札がない -> μ0 <= pred |h1| *)
Lemma not_puttable_mu0_le_pred_nh1 : forall (h0 h1 : hand) (r : nat),
  sorted h0 /\ sorted h1 ->
  0 < counth h1 ->
  maxh h0 <= r ->
  mu0 h0 h1 r <= pred (counth h1).
Proof.
  intros h0 h1 r [Hs0 Hs1] Hc1 Hr.
  unfold mu0.
  remember (removeminh h1) as hh1.
  remember (addh r hh1) as hhr1.
  assert (exists l1 l2 : list nat, hh1 = l1 ++ l2 /\ hhr1 = l1 ++ r :: l2) as H.
  { rewrite Heqhhr1.
    apply insert_split. }
  destruct H as [l1 [l2 [H1 H2]]].
  assert (mu h0 hh1 = mu h0 hhr1) as Emu.
  { rewrite H1, H2.
    apply mu_remove_ge_right_eq_mu.
    - split.
      + apply Hs0.
      + simpl.
        rewrite <- H2.
        rewrite Heqhhr1.
        apply sorted_insert_sorted.
        rewrite Heqhh1.
        unfold removeminh.
        apply sorted_remove_sorted.
        apply Hs1.
    - apply Hr. }
  rewrite <- Emu.
  assert (counth hh1 = pred (counth h1)).
  { rewrite Heqhh1.
    unfold removeminh.
    apply eq_add_S.
    rewrite remove_length_in.
    - apply S_pred_pos.
      apply Hc1.
    - apply min_in.
      apply Hc1. }
  rewrite <- H.
  apply mu_le_length2.
Qed.

(* 補題 : 一手勝ちなら μ0 = 1 *)
Lemma last_move_mu0_win : forall (h0 h1 : hand) (r : nat),
  counth h0 = 1
  -> r < minh h0
  -> mu0 h0 h1 r = 1.
Proof.
  intros h0 h1 r Hc Hr.
  destruct h0 as [| x0 h0].
  - simpl in Hc.
    discriminate Hc.
  - destruct h0 as [| x1 h0].
    + unfold mu0.
      simpl in Hr.
      remember (removeminh h1) as hh.
      destruct hh as [| y1 h0].
      * simpl.
        apply Nat.ltb_lt in Hr.
        rewrite Hr.
        reflexivity.
      * simpl.
        destruct (r <=? y1) eqn:E.
        -- apply Nat.ltb_lt in Hr.
           rewrite Hr.
           reflexivity.
        -- apply leb_complete_conv in E.
           assert (y1 < x0).
           { apply lt_trans with (m:=r).
             apply E. apply Hr. }
           apply Nat.ltb_lt in H.
           rewrite H.
           reflexivity.
    + simpl in Hc.
      inversion Hc.
Qed.

(* 補題 : 手札表現された μ (h0, h1) <= μ (h0 + {r}, h1) *)
Lemma mu1_le_imu0 : forall (h0 h1 : hand) (r : nat),
  sorted h0 /\ sorted h1 ->
  mu1 h1 h0 <= mu0 h0 h1 r.
Proof.
  intros h0 h1 r [Hs0 Hs1].
  unfold mu0, mu1.
  remember (removeminh h1) as hh1.
  remember (addh r hh1) as hhr1.
  assert (exists l1 l2 : list nat, hh1 = l1 ++ l2 /\ hhr1 = l1 ++ r :: l2) as H.
  { rewrite Heqhhr1.
    apply insert_split. }
  destruct H as [l1 [l2 [H1 H2]]].
  rewrite H1, H2.
  apply mu_le_mu_ins2.
  split.
  - apply Hs0.
  - simpl.
    rewrite <- H2.
    rewrite Heqhhr1.
    apply sorted_insert_sorted.
    rewrite Heqhh1.
    unfold removeminh.
    apply sorted_remove_sorted.
    apply Hs1.
Qed.

(* 補題 : 手札表現された μ (h0 + {r}, h1) <=  S (μ (h0, h1)) *)
Lemma mu0_le_S_imu1 : forall (h0 h1 : hand) (r : nat),
  sorted h0 /\ sorted h1 ->
  mu0 h0 h1 r <= S (mu1 h1 h0).
Proof.
  intros h0 h1 r [Hs0 Hs1].
  unfold mu0, mu1.
  remember (removeminh h1) as hh1.
  remember (addh r hh1) as hhr1.
  assert (exists l1 l2 : list nat, hh1 = l1 ++ l2 /\ hhr1 = l1 ++ r :: l2) as H.
  { rewrite Heqhhr1.
    apply insert_split. }
  destruct H as [l1 [l2 [H1 H2]]].
  rewrite H1, H2.
  apply mu_ins2_le_S_mu with (y:=r).
  split.
  - apply Hs0.
  - simpl.
    rewrite <- H2.
    rewrite Heqhhr1.
    apply sorted_insert_sorted.
    rewrite Heqhh1.
    unfold removeminh.
    apply sorted_remove_sorted.
    apply Hs1.
Qed.


(*********************************)
(* μ0 > μ1 のときの手の選び方の補題 *)
(*********************************)

(* 最小の札を出す条件 *)
Definition min_or_second_cond (h0 h1 : hand) (r : nat) := 
  mu1 h0 h1 = mu h1 (removeh (secondh h0) h0).

(* 補題 : 出せる札がなければパス *)
Lemma win_move_pass_if_not_puttable : forall (h0 h1 : hand) (r : nat),
  ap_sorted h0 /\ ap_sorted h1 ->
  maxh h0 <= r ->
  mu0 h0 h1 r > mu1 h0 h1 ->
  mu0 h1 h0 0 <= mu1 h1 h0.
Proof.
  intros h0 h1 r [Hs0 Hs1] Hr Hmu.
  (* 手番側 : 出せる札がなければ手番側マッチングが悪くなる条件に該当しない *)
  assert (mu0 h0 h1 r = mu1 h1 h0) as Hk0.
  {
    unfold mu0, mu1.
    remember (removeminh h1) as hh1.
    remember (addh r hh1) as hhr1.
    assert (exists l1 l2 : list nat, hh1 = l1 ++ l2 /\ hhr1 = l1 ++ r :: l2) as H.
    { rewrite Heqhhr1.
      apply insert_split. }
    destruct H as [l1 [l2 [H1 H2]]].
    rewrite H1, H2.
    symmetry.
    apply mu_remove_ge_right_eq_mu.
    - split.
      + apply Hs0.
      + rewrite <- H2.
        rewrite Heqhhr1.
        apply sorted_insert_sorted.
        rewrite Heqhh1.
        unfold removeminh.
        apply sorted_remove_sorted.
        apply Hs1.
    - apply Hr. }
  (* 非手番側 : パスをしても非手番側マッチング数は高々1しか増えない *)
  assert (mu0 h1 h0 0 <= S (mu1 h0 h1)) as Hk1.
  { apply mu0_le_S_imu1.
    split. apply Hs1. apply Hs0. }
  apply le_trans with (m:=S (mu1 h0 h1)).
  - apply Hk1.
  - rewrite <- Hk0.
    apply Nat.le_succ_l.
    apply Hmu.
Qed.

(* 補題 : 最小札が出せないならば出せる最小 *)
Lemma win_move_vmin_if_min_not_puttable : forall (h0 h1 : hand) (r : nat),
  ap_sorted h0 /\ ap_sorted h1 ->
  1 < counth h0 ->
  r < maxh h0 ->
  minh h0 <= r ->
  mu0 h0 h1 r > mu1 h0 h1 ->
  mu0 h1 (removeh (mingth h0 r) h0) (mingth h0 r)
    <= mu1 h1 (removeh (mingth h0 r) h0).
Proof.
  intros h0 h1 r [Hs0 Hs1] Hc0 Hr1 Hr2 Hmu.
  remember (mingth h0 r) as a.
  assert (exists l1 l2 : list nat, h0 = l1 ++ (mingth h0 r) :: l2 /\ maxh l1 <= r) as H.
  { apply sorted_mingt_split.
    - apply Hs0.
    - apply mingt_gt_if_max_gt.
      apply Hr1. }
  destruct H as [l1 [l2 [H1 H2]]].
  assert (l1 <> []) as H.
  { destruct l1 as [| x1 l1].
    - simpl in H1.
      rewrite H1 in Hr2.
      rewrite sorted_min_is_hd in Hr2.
      simpl in Hr2.
      apply mingt_gt_if_max_gt in Hr1.
      + apply lt_not_le in Hr1.
        apply Hr1 in Hr2.
        contradiction Hr2.
      + rewrite <- H1.
        apply Hs0.
    - apply not_eq_sym.
      apply nil_cons. }
  apply exists_last in H.
  destruct H as [l' [x1 H]].
  rewrite H in H1.
  rewrite H in H2.
  clear H.
  assert (removeh (mingth h0 r) ((l' ++ [x1]) ++ mingth h0 r :: l2)
          = (l' ++ [x1]) ++ l2) as Heqhh0.
  { apply sorted_remove_inv.
    rewrite <- H1.
    apply Hs0. }
  rewrite <- H1 in Heqhh0.
  (* 手番側 : 二番目以降の出せる最小札を出せばマッチング数は高々1しか悪くならない *)
  assert (mu0 h0 h1 r <= S (mu1 h1 (removeh (mingth h0 r) h0))) as Hk0.
  { unfold mu0, mu1.
    remember (removeminh h1) as hh1.
    remember (addh r hh1) as hhr1.
    assert (exists l3 l4 : list nat, hh1 = l3 ++ l4 /\ hhr1 = l3 ++ r :: l4) as H.
    { rewrite Heqhhr1.
      apply insert_split. }
    destruct H as [l3 [l4 [H3 H4]]].
    rewrite H3, H4.
    assert (removeh (mingth h0 r) ((l' ++ [x1]) ++ mingth h0 r :: l2)
            = (l' ++ [x1]) ++ l2) as H.
    { apply sorted_remove_inv.
      rewrite <- H1.
      apply Hs0. }
    rewrite <- H1 in H.
    rewrite <- app_assoc in H.
    simpl in H.
    rewrite H, H1.
    rewrite <- app_assoc.
    simpl.
    apply Nat.eq_le_incl.
    apply mu_ins_mingt_eq_S_mu.
    - split.
      + rewrite <- app_assoc in H1.
        simpl in H1.
        rewrite <- H1.
        apply Hs0.
      + rewrite <- H4.
        rewrite Heqhhr1.
        apply sorted_insert_sorted.
        rewrite Heqhh1.
        unfold removeminh.
        apply sorted_remove_sorted.
        apply Hs1.
    - rewrite sorted_max_is_last in H2.
      + rewrite last_last in H2.
        apply H2.
      + rewrite H1 in Hs0.
        apply sorted_split_left with (l2:=mingth h0 r :: l2).
        apply Hs0.
    - apply mingt_gt_if_max_gt.
      apply Hr1. }
  (* 非手番側はマッチング構造が変化しないのでマッチングが増えはしない *)
  assert (mu0 h1 (removeh a h0) a <= mu1 h0 h1) as Hk1.
  { apply Nat.eq_le_incl.
    unfold mu0, mu1.
    destruct h0 as [| z1 h0].
    - simpl in Hc0.
      inversion Hc0.
    - assert (removeminh (z1 :: h0) = h0).
      { apply unfold_removeminh.
        apply Hs0. }
      rewrite H. clear H.
      simpl.
      assert (z1 <> a) as E.
      { rewrite sorted_min_is_hd in Hr2.
        - simpl in Hr2.
          apply mingt_gt_if_max_gt in Hr1.
          unfold mingth in Heqa.
          rewrite <- Heqa in Hr1.
          apply Nat.lt_neq.
          apply le_lt_trans with (m:=r).
          + apply Hr2.
          + apply Hr1.
        - apply Hs0. }
      apply Nat.eqb_neq in E.
      rewrite E.
      assert (removeminh (z1 :: removeh a h0) = removeh a h0).
      { apply unfold_removeminh.
        apply mingt_gt_if_max_gt in Hr1.
        apply mingt_in_if_gt in Hr1.
        apply remove_split in Hr1.
        destruct Hr1 as [l3 [l4 [Hr11 Hr12]]].
        unfold mingth in Heqa.
        rewrite <- Heqa in Hr11.
        rewrite <- Heqa in Hr12.
        simpl in Hr12.
        rewrite E in Hr12.
        unfold removeh.
        rewrite Hr12.
        rewrite Hr11 in Hs0.
        apply sorted_remove_middle with (l2:=[a]).
        simpl.
        apply Hs0. }
      rewrite H. clear H.
      rewrite sorted_remove_insert.
      + reflexivity.
      + apply sorted_split_right with (l1:=[z1]).
        apply Hs0.
      + assert (In a (z1 :: h0)).
        { rewrite H1.
          rewrite <- Heqa.
          apply in_elt. }
        simpl in H.
        destruct H.
        * apply Nat.eqb_eq in H.
          rewrite E in H.
          discriminate H.
        * apply H. }
  remember (removeh a h0) as hh0.
  rewrite <- Heqa in Hk0.
  rewrite <- Heqhh1 in Hk0.
  (* 結論 *)
  apply le_trans with (m:=mu1 h0 h1).
  - apply Hk1.
  - apply lt_n_Sm_le.
    + apply lt_le_trans with (m:=mu0 h0 h1 r).
      * apply Hmu.
      * apply Hk0.
Qed.

(* 補題 : 最小でOKの条件を満たすならば最小 *)
Lemma win_move_min_if_cond_ok : forall (h0 h1 : hand) (r : nat),
  ap_sorted h0 /\ ap_sorted h1 ->
  1 < counth h0 ->
  r < minh h0 -> 
  min_or_second_cond h0 h1 r ->
  mu0 h0 h1 r > mu1 h0 h1 ->
  mu0 h1 (removeh (minh h0) h0) (minh h0)
    <= mu1 h1 (removeh (minh h0) h0).
Proof.
  intros h0 h1 r [Hs0 Hs1] Hc0 Hr Hcond Hmu.
  remember (minh h0) as a.
  remember (removeh a h0) as hh0.
  (* 手番側 : 最小札を出せばマッチング数は常に1しか悪くならない *)
  assert (mu0 h0 h1 r <= S (mu1 h1 hh0)) as Hk0.
  { apply Nat.eq_le_incl.
    rewrite Heqhh0.
    rewrite Heqa.
    unfold mu0, mu1.
    remember (removeminh h1) as hh1.
    remember (addh r hh1) as hhr1.
    destruct h0 as [| x1 h0].
    - simpl in Hc0.
      inversion Hc0.
    - assert (removeh (minh (x1 :: h0)) (x1 :: h0) = h0) as H.
      { rewrite sorted_min_is_hd.
        - simpl.
          rewrite Nat.eqb_refl.
          reflexivity.
        - apply Hs0. }
      rewrite H. clear H.
      assert (exists l3 l4 : list nat, hh1 = l3 ++ l4 /\ hhr1 = l3 ++ r :: l4) as H.
      { rewrite Heqhhr1.
        apply insert_split. }
      destruct H as [l1 [l2 [H1 H2]]].
      rewrite H1, H2.
      apply mu_ins_eq_S_mu_hd1.
      + split.
        * apply Hs0.
        * rewrite <- H2.
          rewrite Heqhhr1.
          apply sorted_insert_sorted.
          rewrite Heqhh1.
          unfold removeminh.
          apply sorted_remove_sorted.
          apply Hs1.
      + rewrite Heqa in Hr.
        rewrite sorted_min_is_hd in Hr.
        * simpl in Hr. apply Hr.
        * apply Hs0. }
  (* 手番側 : 条件を満たすとき最小札を出せばマッチング数は増えない *)
  assert (mu0 h1 hh0 a <= mu1 h0 h1) as Hk1.
  { apply Nat.eq_le_incl.
    unfold mu0, mu1.
    unfold min_or_second_cond in Hcond.
    destruct h0 as [| x1 h0].
    - simpl in Hc0.
      inversion Hc0.
    - destruct h0 as [| x2 h0].
      + simpl in Hc0.
        apply Nat.lt_irrefl in Hc0.
        contradiction Hc0.
      + rewrite Heqhh0.
        unfold mu0, mu1 in Hcond.
        rewrite Hcond.
        assert (a = x1).
        { rewrite sorted_min_is_hd in Heqa.
          - simpl in Heqa.
            apply Heqa.
          - apply Hs0. }
        rewrite H. clear H.
        assert (removeh x1 (x1 :: x2 :: h0) = x2 :: h0).
        { simpl.
          rewrite Nat.eqb_refl.
          reflexivity. }
        rewrite H. clear H.
        assert (removeminh (x2 :: h0) = h0).
        { rewrite unfold_removeminh.
          - reflexivity.
          - apply sorted_split_right with (l1:=[x1]).
            apply Hs0. }
        rewrite H. clear H.
        assert (addh x1 h0 = x1 :: h0).
        { apply sorted_insert_cons.
          - apply sorted_split_right with (l1:=[x1;x2]).
            apply Hs0.
          - assert (sorted (x1 :: h0)).
            { apply sorted_remove_middle with (l1:=[x1]) (l2:=[x2]).
              apply Hs0. }
            inversion H.
            apply H3. }
        rewrite H. clear H.
        assert (removeh (secondh (x1 :: x2 :: h0)) (x1 :: x2 :: h0) = x1 :: h0).
        { unfold secondh.
          rewrite sorted_nth_min_is_nth.
          - simpl.
            rewrite Nat.eqb_refl.
            destruct (x1 =? x2) eqn:E.
            + apply Nat.eqb_eq in E.
              rewrite E.
              reflexivity.
            + reflexivity.
          - apply Hs0. }
        rewrite H. clear H.
        reflexivity. }
  (* 結論 *)
  apply le_trans with (m:=mu1 h0 h1).
  - apply Hk1.
  - apply lt_n_Sm_le.
    + apply lt_le_trans with (m:=mu0 h0 h1 r).
      * apply Hmu.
      * apply Hk0.
Qed.

(* 補題 : 最小でOKの条件を満たさないならば二番目 *)
Lemma win_move_second_if_cond_not_ok : forall (h0 h1 : hand) (r : nat),
  ap_sorted h0 /\ ap_sorted h1 ->
  1 < counth h0 ->
  r < minh h0 ->
  ~ min_or_second_cond h0 h1 r ->
  mu0 h0 h1 r > mu1 h0 h1 ->
  mu0 h1 (removeh (secondh h0) h0) (secondh h0)
    <= mu1 h1 (removeh (secondh h0) h0).
Proof.
  intros h0 h1 r [Hs0 Hs1] Hc0 Hr Hcond Hmu.
  remember (secondh h0) as a.
  remember (removeh a h0) as hh0.
  remember (removeminh h1) as hh1.
  remember (addh r hh1) as hhr1.
  assert (exists (l : list nat) (x1 : nat), h0 = x1 :: a :: l /\ hh0 = x1 :: l) as H.
  { destruct h0 as [| z1 h0'].
    - simpl in Hc0.
      inversion Hc0.
    - destruct h0' as [| z2 h0''].
      + simpl in Hc0.
        apply Nat.lt_irrefl in Hc0.
        contradiction Hc0.
      + exists h0''.
        exists z1.
        unfold secondh in Heqa.
        rewrite sorted_nth_min_is_nth in Heqa.
        * simpl in Heqa.
          rewrite Heqa.
          split.
          -- reflexivity.
          -- rewrite Heqhh0.
             rewrite Heqa.
             simpl.
             rewrite Nat.eqb_refl.
             destruct (z1 =? z2) eqn:E.
             ++ apply Nat.eqb_eq in E.
                rewrite E.
                reflexivity.
             ++ reflexivity.
        * apply Hs0. }
  destruct H as [l [x1 [H1 H2]]].
  assert (exists l1 l2 : list nat, hh1 = l1 ++ l2 /\ hhr1 = l1 ++ r :: l2) as H.
  { rewrite Heqhhr1.
    apply insert_split. }
  destruct H as [l1 [l2 [H3 H4]]].
  assert (removeminh h0 = a :: l) as Heqhhh0.
  { rewrite H1.
    apply unfold_removeminh.
    rewrite <- H1.
    apply Hs0. }
  (* 手番側 : 条件を満たすとき二番目札を出せばマッチング数は常に1しか悪くならない
             もしくは差が2以上あってひっくり返らない *)
  assert (mu0 h0 h1 r <= S (mu1 h1 hh0) \/ mu1 h0 h1 <= mu1 h1 hh0) as Hk0.
  { unfold min_or_second_cond in Hcond.
    (* 条件を満たすとき二番目札がOKである条件を満たす *)
    assert (mu0 h0 h1 r <= S (mu hh0 hh1) \/ S (mu hh0 hh1) < mu0 h0 h1 r) as Hdiv.
    { apply Nat.le_gt_cases. }
    destruct Hdiv as [Hdiv | Hdiv].
    - left.
      unfold mu1.
      rewrite <- Heqhh1.
      apply Hdiv.
    - right.
      (* μ0の値を確定 *)
      assert (mu0 h0 h1 r = S (S (mu hh0 hh1))).
      { apply Nat.le_antisymm.
        - unfold mu0.
          rewrite <- Heqhh1.
          rewrite <- Heqhhr1.
          rewrite H1, H2, H3, H4.
          apply mu_ins_le_S_S_mu with (l1:=[x1]).
          split.
          + simpl.
            rewrite <- H1.
            apply Hs0.
          + rewrite <- H4.
            rewrite Heqhhr1.
            apply sorted_insert_sorted.
            rewrite Heqhh1.
            unfold removeminh.
            apply sorted_remove_sorted.
            apply Hs1.
        - apply Hdiv. }
      assert (mu0 h0 h1 r = counth h0) as Hmuc0.
      { unfold mu0.
        rewrite <- Heqhh1.
        rewrite <- Heqhhr1.
        rewrite H1, H4.
        apply mu_fm_if_SS_mu_remove21_eq_mu.
        - split.
          + rewrite <- H1.
            apply Hs0.
          + rewrite <- H4.
            rewrite Heqhhr1.
            apply sorted_insert_sorted.
            rewrite Heqhh1.
            unfold removeminh.
            apply sorted_remove_sorted.
            apply Hs1.
        - rewrite <- H1, <- H2, <- H3, <- H4.
          unfold mu0 in H.
          rewrite <- Heqhh1 in H.
          rewrite <- Heqhhr1 in H.
          apply H. }
      clear H.
      (* μ1 の値を限定 *)
      assert (removeh (secondh h0) h0 = x1 :: l) as Heqhhhh0.
      { rewrite H1.
        unfold secondh.
        rewrite sorted_nth_min_is_nth.
        - simpl.
          rewrite Nat.eqb_refl.
          destruct (x1 =? a) eqn:E.
          + apply Nat.eqb_eq in E.
            rewrite E.
            reflexivity.
          + reflexivity.
        - rewrite <- H1.
          apply Hs0. }
      assert (S (mu1 h0 h1) = mu h1 (removeh (secondh h0) h0)) as H.
      { rewrite <- Heqa.
        rewrite <- Heqa in Hcond.
        rewrite <- Heqhh0.
        rewrite <- Heqhh0 in Hcond.
        apply Nat.le_antisymm.
        - assert (mu1 h0 h1 < mu h1 hh0 \/
                  mu1 h0 h1 = mu h1 hh0 \/
                  mu h1 hh0 < mu1 h0 h1) as Hd.
          { apply Nat.lt_total. }
          destruct Hd as [Hd | Hd].
          + apply Hd.
          + destruct Hd as [Hd | Hd].
            * apply Hcond in Hd.
              contradiction Hd.
            * assert (mu1 h0 h1 <= mu h1 hh0).
              { unfold mu1.
                rewrite H2.
                rewrite Heqhhh0.
                apply mu_compare_hd2.
                - split.
                  + apply Hs1.
                  + rewrite H1 in Hs0.
                    apply sorted_split_right with (l1:=[x1]).
                    apply Hs0.
                - rewrite H1 in Hs0.
                  assert (sorted [x1;a]).
                  { apply sorted_split_left with (l2:=l).
                    apply Hs0. }
                  inversion H. simpl in H7. apply H7. }
              assert (mu h1 hh0 < mu h1 hh0) as Ec.
              { apply lt_le_trans with (m:=mu1 h0 h1).
                - apply Hd.
                - apply H. }
              apply Nat.lt_irrefl in Ec.
              contradiction Ec.
        - unfold mu1.
          rewrite H2.
          rewrite Heqhhh0.
          apply le_trans with (m:=S (mu h1 l)).
          + apply mu_cons2_le_S_mu.
            split.
            * apply Hs1.
            * rewrite <- H2.
              rewrite Heqhh0.
              apply sorted_remove_sorted.
              apply Hs0.
          + apply le_n_S.
            apply mu_le_mu_cons2.
            split.
            * apply Hs1.
            * rewrite H1 in Hs0.
              apply sorted_split_right with (l1:=[x1]).
              apply Hs0. }
      assert (S (mu1 h0 h1) < counth h0) as Hmuc1.
      { unfold mu1.
        rewrite Heqhhh0.
        rewrite H1.
        simpl.
        apply le_lt_n_Sm.
        apply le_n_S.
        apply mu_le_len2_if_mu_swap_eq_S_mu with (y1:=x1).
        - split.
          + apply Hs1.
          + rewrite <- H1.
            apply Hs0.
        - unfold mu1 in H.
          rewrite Heqhhh0 in H.
          rewrite Heqhhhh0 in H.
          symmetry.
          apply H. }
      rewrite <- Hmuc0 in Hmuc1.
      assert (mu0 h0 h1 r <= S (S (mu1 h1 hh0))).
      { unfold mu0, mu1.
        rewrite <- Heqhh1.
        rewrite <- Heqhhr1.
        rewrite H1, H2, H3, H4.
        apply mu_ins_le_S_S_mu with (l1:=[x1]).
        + split.
          * rewrite H1 in Hs0.
            apply Hs0.
          * rewrite <- H4.
            rewrite Heqhhr1.
            apply sorted_insert_sorted.
            rewrite Heqhh1.
            unfold removeminh.
            apply sorted_remove_sorted.
            apply Hs1. }
      apply le_S_n.
      apply le_S_n.
      apply le_trans with (m:=mu0 h0 h1 r).
      + apply Hmuc1.
      + apply H0. }
  (* 非手番側はマッチング構造が変化しないのでマッチングが増えはしない *)
  assert (mu0 h1 hh0 a <= mu1 h0 h1) as Hk1.
  { apply Nat.eq_le_incl.
    unfold mu0, mu1.
    rewrite H2.
    rewrite Heqhhh0.
    assert (removeminh (x1 :: l) = l) as H.
    { apply unfold_removeminh.
      rewrite H1 in Hs0.
      apply sorted_remove_middle with (l1:=[x1]) (l2:=[a]).
      apply Hs0. }
    rewrite H. clear H.
    rewrite sorted_insert_cons.
    - reflexivity.
    - rewrite H1 in Hs0.
      apply sorted_split_right with (l1:=[x1;a]).
      apply Hs0.
    - assert (sorted (a :: l)).
      { rewrite H1 in Hs0.
        apply sorted_split_right with (l1:=[x1]).
        apply Hs0. }
      inversion H. simpl in H7. apply H7. }
  (* 結論 *)
  destruct Hk0 as [Hk0 | Hk0].
  - apply le_trans with (m:=mu1 h0 h1).
    + apply Hk1.
    + apply lt_n_Sm_le.
      * apply lt_le_trans with (m:=mu0 h0 h1 r).
        -- apply Hmu.
        -- apply Hk0.
  - apply le_trans with (m:=mu1 h0 h1).
    + apply Hk1.
    + apply Hk0.
Qed.


(***********************************)
(* μ0 < μ1 のときどの手でも負けの補題 *)
(***********************************)

(* 補題 : パスで勝てない *)
Lemma lose_move_pass : forall (h0 h1 : hand) (r : nat),
  ap_sorted h0 /\ ap_sorted h1 ->
  mu0 h0 h1 r <= mu1 h0 h1 ->
  mu0 h1 h0 0 > mu1 h1 h0.
Proof.
  intros h0 h1 r [Hs0 Hs1] Hmu.
  (* 2つの場合に分ける
         μ0 < μ1 のとき 2以上良くはならないことを証明
         μ0 = μ1 のとき (手番側マッチングが減らない かつ 非手番側マッチングが増えない) を否定 *)
  apply le_S_gt.
  apply lt_le_S.
  assert (mu0 h0 h1 r < mu1 h0 h1 \/ mu1 h0 h1 <= mu0 h0 h1 r) as Hdiv.
  { apply Nat.lt_ge_cases. }
  destruct Hdiv as [Hdiv | Hdiv].
  - apply le_lt_trans with (m:=mu0 h0 h1 r).
    + apply mu1_le_imu0.
      split. apply Hs0. apply Hs1.
    + apply lt_le_trans with (m:=mu1 h0 h1).
      * apply Hdiv.
      * apply mu1_le_imu0.
        split. apply Hs1. apply Hs0.
  - assert (mu1 h1 h0 < mu0 h0 h1 r \/ mu0 h0 h1 r <= mu1 h1 h0) as Hmu0.
    { apply Nat.lt_ge_cases. }
    assert (mu1 h0 h1 < mu0 h1 h0 0 \/ mu0 h1 h0 0 <= mu1 h0 h1) as Hmu1.
    { apply Nat.lt_ge_cases. }
    (* ここから分岐 *)
    destruct Hmu0 as [Hmu0 | Hmu0].
    + apply lt_le_trans with (m:=mu0 h0 h1 r).
      * apply Hmu0.
      * apply le_trans with (m:=mu1 h0 h1).
        -- apply Hmu.
        -- apply mu1_le_imu0.
           split. apply Hs1. apply Hs0.
    + destruct Hmu1 as [Hmu1 | Hmu1].
      * apply le_lt_trans with (m:=mu1 h0 h1).
        -- apply le_trans with (m:=mu0 h0 h1 r).
           ++ apply mu1_le_imu0.
               split. apply Hs0. apply Hs1.
           ++ apply Hmu.
        -- apply Hmu1.
      * (* このパターンで矛盾を導く *)
        assert (mu0 h0 h1 r < counth h1) as Hmu0c.
        { apply le_lt_trans with (m:=mu1 h1 h0).
          - apply Hmu0.
          - unfold mu1.
            assert (S (counth (removeminh h1)) = counth h1) as Ec.
            { unfold removeminh. 
              apply remove_length_in.
              apply min_in. 
              apply Hs1. }
            rewrite <- Ec.
            apply le_lt_n_Sm.
            apply mu_le_length2. }
        assert (counth h1 <= mu1 h0 h1) as Hmu1c.
        { assert (mu1 h0 h1 < counth h1 \/ counth h1 <= mu1 h0 h1) as Hdiv2.
          { apply Nat.lt_ge_cases. }
          destruct Hdiv2 as [Hdiv2 | Hdiv2].
          - assert (mu1 h0 h1 < mu0 h1 h0 0).
            { unfold mu0, mu1.
              remember (removeminh h0) as hh0.
              remember (addh 0 hh0) as hhr0.
              assert (exists l1 l2 : list nat, hh0 = l1 ++ l2 /\ hhr0 = l1 ++ 0 :: l2) as H.
              { rewrite Heqhhr0.
                apply insert_split. }
              destruct H as [l1 [l2 [H1 H2]]].
              rewrite H1, H2.
              apply Nat.le_succ_l.
              apply Nat.eq_le_incl.
              symmetry.
              apply mu_cons2_w_eq_S_mu_if_ne.
              - split.
                + apply Hs1.
                + rewrite <- H2.
                  rewrite Heqhhr0.
                  apply sorted_insert_sorted.
                  rewrite Heqhh0.
                  unfold removeminh.
                  apply sorted_remove_sorted.
                  apply Hs0.
              - apply Hs1.
              - unfold mu1, counth in Hdiv2.
                rewrite <- Heqhh0 in Hdiv2.
                rewrite H1 in Hdiv2.
                apply Hdiv2. }
            assert (mu1 h0 h1 < mu1 h0 h1) as Ec.
            { apply lt_le_trans with (m:=mu0 h1 h0 0).
              - apply H.
              - apply Hmu1. }
            apply Nat.lt_irrefl in Ec.
            contradiction Ec.
          - apply Hdiv2. }
        assert (mu1 h0 h1 < mu1 h0 h1) as Ec.
        { apply le_lt_trans with (m:=mu0 h0 h1 r).
          - apply Hdiv.
          - apply lt_le_trans with (m:=counth h1).
            + apply Hmu0c.
            + apply Hmu1c. }
        apply Nat.lt_irrefl in Ec.
        contradiction Ec.
Qed.

(* 補題 : 出して勝てない *)
Lemma lose_move_put : forall (h0 h1 : hand) (r : nat),
  ap_sorted h0 /\ ap_sorted h1 ->
  1 < counth h0 ->
  forall a : nat, containsh a h0 /\ r < a ->
  mu0 h0 h1 r <= mu1 h0 h1 ->
  mu0 h1 (removeh a h0) a > mu1 h1 (removeh a h0).
Proof.
  intros h0 h1 r [Hs0 Hs1] Hc0 a [Hp Hr] Hmu.
  (* 手番側 : マッチングが1以上減る *)
  assert (mu1 h1 (removeh a h0) < mu0 h0 h1 r) as Hk0.
  { apply remove_split in Hp.
    destruct Hp as [l1 [l2 [H1 H2]]].
    unfold removeh.
    rewrite H2, H1.
    unfold mu0, mu1.
    remember (removeminh h1) as hh1.
    remember (addh r hh1) as hhr1.
    assert (exists l1 l2 : list nat, hh1 = l1 ++ l2 /\ hhr1 = l1 ++ r :: l2) as H.
    { rewrite Heqhhr1.
      apply insert_split. }
    destruct H as [l3 [l4 [H3 H4]]].
    rewrite H3.
    rewrite H4.
    apply mu_lt_mu_ins_prod.
    - split.
      + rewrite <- H1.
        apply Hs0.
      + rewrite <- H4.
        rewrite Heqhhr1.
        apply sorted_insert_sorted.
        rewrite Heqhh1.
        unfold removeminh.
        apply sorted_remove_sorted.
        apply Hs1.
    - apply Hr. }
  (* 非手番側はマッチングが減りはしない *)
  assert (mu1 h0 h1 <= mu0 h1 (removeh a h0) a) as Hk1.
  { unfold mu0, mu1.
    destruct h0 as [| x1 h0].
    - simpl in Hp.
      contradiction Hp.
    - simpl.
      destruct (x1 =? a) eqn:E.
      + (* 最小札を出した場合 *)
        destruct h0 as [| x2 h0].
        * simpl in Hc0.
          apply Nat.lt_irrefl in Hc0.
          contradiction Hc0.
        * rewrite !unfold_removeminh.
          -- apply Nat.eqb_eq in E.
             rewrite <- E.
             rewrite sorted_insert_cons.
             apply mu_compare_hd2.
             ++ split. apply Hs1.
                apply sorted_split_right with (l1:=[x1]). 
                apply Hs0.
             ++ assert (sorted [x1;x2]).
                { apply sorted_split_left with (l1:=[x1;x2]) (l2:=h0). 
                  apply Hs0. }
                inversion H. simpl in H3. apply H3.
             ++ apply sorted_split_right with (l1:=[x1;x2]).
                apply Hs0.
             ++ destruct h0 as [| x3 h0].
                ** simpl.
                   reflexivity.
                ** simpl.
                   apply sorted_all_le with (l1:=[]) (l2:=[x2]) (l3:=h0).
                   apply Hs0.
          -- { apply sorted_split_right with (l1:=[x1]). 
              apply Hs0. }
          -- apply Hs0.
      + (* 二番目以降の札を出した場合 *)
        rewrite !unfold_removeminh.
        * rewrite sorted_remove_insert.
          -- reflexivity.
          -- apply sorted_split_right with (l1:=[x1]). 
             apply Hs0.
          -- destruct Hp as [Hp | Hp].
             ++ apply Nat.eqb_eq in Hp.
                rewrite Hp in E.
                discriminate E.
             ++ apply Hp.
        * destruct Hp as [Hp | Hp].
          -- apply Nat.eqb_eq in Hp.
             rewrite Hp in E.
             discriminate E.
          -- apply remove_split in Hp.
             destruct Hp as [l1 [l2 [Hp1 Hp2]]].
             unfold removeh.
             rewrite Hp2.
             rewrite Hp1 in Hs0.
             apply sorted_remove_middle with (l1:=x1 :: l1) (l2:=[a]).
             apply Hs0.
        * apply Hs0. }
  apply lt_le_trans with (m:=mu0 h0 h1 r).
  - apply Hk0.
  - apply le_trans with (m:=mu1 h0 h1).
    + apply Hmu.
    + apply Hk1.
Qed.


(***********)
(* 終端局面 *)
(***********)

(* 終端 : 手札一枚で出せれば一手勝ち *)
Lemma mu_win_term : forall (h0 h1 : hand) (r : nat),
  counth h0 = 1 /\ 0 < counth h1 -> r < minh h0 ->
  inductive_result_is true h0 h1 r.
Proof.
  intros h0 h1 r [Hc0 Hc1] Hr.
  apply InductivePutWin with (a:=minh h0).
  - apply min_in.
    unfold counth in Hc0.
    rewrite Hc0. auto.
  - apply Hr.
  - apply InductiveTerm.
    + apply Hc1.
    + apply eq_add_S.
      rewrite remove_length_in.
      * apply Hc0.
      * apply min_in.
        unfold counth in Hc0.
        rewrite Hc0. auto.
Qed.

(* 終端 : 手札一枚ずつで出せずにパスで負け *)
Lemma mu_lose_term : forall (h0 h1 : hand) (r : nat),
  counth h0 = 1 /\ counth h1 = 1 -> minh h0 <= r -> 0 < minh h1 ->
  inductive_result_is false h0 h1 r.
Proof.
  intros h0 h1 r [Hc0 Hc1] Hr0 Hr1.
  apply InductiveLose.
  - (* 出す手の検証 -> 無い *)
    intros a Hp Hv.
    assert (maxh h0 <= r) as Hc0r.
    { rewrite <- min_eq_max_one.
      apply Hr0. apply Hc0. }
    apply forced_pass_cond with (r:=r) (a:=a) in Hc0r.
    + exfalso. apply Hc0r.
      split. apply Hp. apply Hv.
  - (* パスの検証 -> 次の手番で相手が一手勝ち *)
    apply mu_win_term.
    + split. apply Hc1. rewrite Hc0. auto.
    + apply Hr1.
Qed.


(*******************)
(* 帰納法 base step *)
(*******************)

(* base step : 手札一枚ずつで勝ちの場合 *)
Lemma mu_win_base : forall (h0 h1 : hand) (r : nat),
  ap_sorted h0 /\ ap_sorted h1 ->
  counth h0 = 1 /\ counth h1 = 1 -> mu_win_cond h0 h1 r.
Proof.
  intros h0 h1 r [Hs0 Hs1] [Hc0 Hc1] Hmu.
  assert (minh h0 <= r \/ r < minh h0) as Hd. (* 場に出せるか出せないかのどちらか *)
  { apply Nat.le_gt_cases. }
  destruct Hd as [Hd | Hd].
  - (* 場に出せない場合 *)
    assert (r = 0 \/ 0 < r) as Hr.
    { apply Nat.eq_0_gt_0_cases. }
    destruct Hr.
    + (* 空場なのに出せない -> 矛盾 *)
      rewrite H in Hd.
      exfalso.
      apply le_not_lt with (n:=minh h0) (m:=0).
      * apply Hd.
      * apply Hs0.
    + (* 場の札に出せない -> μの値に矛盾 *)
      rewrite min_eq_max_one in Hd.
      * assert (mu0 h0 h1 r <= 0) as Hmu0.
        { apply not_puttable_mu0_le_pred_nh1 with (h1:=h1) in Hd.
          rewrite Hc1 in Hd.
          simpl in Hd.
          apply Hd.
          - split. apply Hs0. apply Hs1.
          - apply Hs1. }
        apply le_n_0_eq in Hmu0.
        rewrite <- Hmu0 in Hmu.
        exfalso.
        apply Nat.nlt_0_r with (n:=mu1 h0 h1).
        apply Hmu.
      * apply Hc0.
  - (* 場に出せる場合 *)
    apply mu_win_term.
    split.
    + apply Hc0.
    + rewrite Hc1. auto.
    + apply Hd.
Qed.

(* base step : 手札一枚ずつで負けの場合 *)
Lemma mu_lose_base : forall (h0 h1 : hand) (r : nat),
  ap_sorted h0 /\ ap_sorted h1 ->
  counth h0 = 1 /\ counth h1 = 1 -> mu_lose_cond h0 h1 r.
Proof.
  intros h0 h1 r [Hs0 Hs1] [Hc0 Hc1] Hmu.
  assert (minh h0 <= r \/ r < minh h0) as Hd. (* 場に出せるか出せないかのどちらか *)
  { apply Nat.le_gt_cases. }
  destruct Hd as [Hd | Hd].
  - (* 場に出せない場合 *)
    apply mu_lose_term.
    + split. apply Hc0. apply Hc1.
    + apply Hd.
    + apply Hs1.
  - (* 場に出せる場合 -> 矛盾 *)
    assert (mu0 h0 h1 r = 1) as Hmu0.
    { apply last_move_mu0_win.
      apply Hc0. apply Hd. }
    assert (mu1 h0 h1 = 0) as Hmu1.
    { symmetry. apply le_n_0_eq.
      apply f_equal_pred in Hc0.
      simpl in Hc0.
      rewrite <- Hc0.
      apply mu0_le_pred_nh0. }
    rewrite Hmu0 in Hmu.
    rewrite Hmu1 in Hmu.
    inversion Hmu.
Qed.

(* base step まとめ *)
Lemma mu_win_lose_base : forall (h0 h1 : hand) (r : nat),
  ap_sorted h0 /\ ap_sorted h1 ->
  counth h0 = 1 /\ counth h1 = 1 ->
  mu_win_cond h0 h1 r /\ mu_lose_cond h0 h1 r.
Proof.
  split.
  - apply mu_win_base.
    apply H. apply H0.
  - apply mu_lose_base.
    apply H. apply H0.
Qed.


(************************************************)
(* induction steps : 以下の順番でないと証明できない *)
(************************************************)

(* induction step : μ0 > μ1 で出せる札があれば勝ちの手がある *)
Lemma mu_win_puttable_step : forall n : nat,
  (forall (h0' h1' : hand) (r' : nat),
   counth h0' + counth h1' = n ->
   ap_sorted h0' /\ ap_sorted h1' ->
   mu_lose_cond h0' h1' r'
  ) ->
  forall (h0 h1 : hand) (r : nat),
  counth h0 + counth h1 = S n ->
  ap_sorted h0 /\ ap_sorted h1 ->
  r < maxh h0 -> mu_win_cond h0 h1 r.
Proof.
  intros n H h0 h1 r Hn [Hs0 Hs1] Hv Hmu.
  assert (counth h0 <= 1 \/ 1 < counth h0) as Hc.
  { apply Nat.le_gt_cases. }
  destruct Hc as [Hc | Hc].
  - apply mu_win_term.
    + split.
      * apply Nat.le_antisymm.
        -- apply Hc.
        -- apply Hs0.
      * apply Hs1.
    + destruct h0.
      * inversion Hv.
      * destruct h0.
        -- simpl.
           simpl in Hv.
           rewrite max_0_r in Hv.
           apply Hv.
        -- simpl in Hc.
           apply le_S_n in Hc.
           apply Nat.nle_succ_0 in Hc.
           contradiction Hc.
  - assert (minh h0 <= r \/ r < minh h0) as Hr.
    { apply Nat.le_gt_cases. }
    destruct Hr as [Hr | Hr].
    + apply InductivePutWin with (a:=mingth h0 r).
      * apply mingt_in_if_gt.
        apply mingt_gt_if_max_gt.
        apply Hv.
      * apply mingt_gt_if_max_gt.
        apply Hv.
      * apply H.
        -- apply eq_add_S.
           rewrite plus_n_Sm.
           rewrite remove_length_in.
           ++ rewrite plus_comm.
              apply Hn.
           ++ apply mingt_in_if_gt.
              apply mingt_gt_if_max_gt.
              apply Hv.
        -- split.
           ++ apply Hs1.
           ++ apply ap_sorted_remove_ap_sorted.
              ** apply Hs0.
              ** apply Hc.
        -- apply win_move_vmin_if_min_not_puttable.
           ++ split. apply Hs0. apply Hs1.
           ++ apply Hc.
           ++ apply Hv.
           ++ apply Hr.
           ++ apply Hmu.
    + assert (min_or_second_cond h0 h1 r \/ ~ min_or_second_cond h0 h1 r) as Hcond.
      { unfold min_or_second_cond.
        rewrite <- Nat.eqb_neq.
        rewrite <- Nat.eqb_eq.
        destruct (mu1 h0 h1 =? mu h1 (removeh (secondh h0) h0)).
        - left. reflexivity.
        - right. reflexivity. }
      destruct Hcond as [Hcond | Hcond].
      * apply InductivePutWin with (a:=minh h0).
        -- apply min_in.
           apply Hs0.
        -- apply Hr.
        -- apply H.
           ++ apply eq_add_S.
              rewrite plus_n_Sm.
              rewrite remove_length_in.
              ** rewrite plus_comm.
                 apply Hn.
              ** apply min_in.
                 apply Nat.lt_succ_l.
                 apply Hc.
           ++ split.
              ** apply Hs1.
              ** apply ap_sorted_remove_ap_sorted.
                 --- apply Hs0.
                 --- apply Hc.
           ++ apply win_move_min_if_cond_ok with (r:=r).
              ** split. apply Hs0. apply Hs1.
              ** apply Hc.
              ** apply Hr.
              ** apply Hcond.
              ** apply Hmu.
      * apply InductivePutWin with (a:=secondh h0).
        -- apply nth_min_in.
           apply Hc.
        -- apply lt_le_trans with (m:=minh h0).
           ++ apply Hr.
           ++ apply in_range_min_max.
              apply nth_min_in.
              apply Hc.
        -- apply H.
           ++ apply eq_add_S.
              rewrite plus_n_Sm.
              rewrite remove_length_in.
              ** rewrite plus_comm.
                 apply Hn.
              ** apply nth_min_in.
                 apply Hc.
           ++ split.
              ** apply Hs1.
              ** apply ap_sorted_remove_ap_sorted.
                 --- apply Hs0.
                 --- apply Hc.
           ++ apply win_move_second_if_cond_not_ok with (r:=r).
              ** split. apply Hs0. apply Hs1.
              ** apply Hc.
              ** apply Hr.
              ** apply Hcond.
              ** apply Hmu.
Qed.

(* induction step : μ0 <= μ1 ならばどの手でも負け *)
Lemma mu_lose_step : forall n : nat,
  (forall (h0' h1' : hand) (r' : nat),
   counth h0' + counth h1' = n ->
   ap_sorted h0' /\ ap_sorted h1'->
   mu_win_cond h0' h1' r' /\ mu_lose_cond h0' h1' r'
  ) ->
  forall (h0 h1 : hand) (r : nat),
  counth h0 + counth h1 = S n ->
  ap_sorted h0 /\ ap_sorted h1 ->
  mu_lose_cond h0 h1 r.
Proof.
  intros n H h0 h1 r Hn [Hs0 Hs1] Hmu.
  apply InductiveLose.
  - (* 札を出す手 *)
    assert (counth h0 <= 1 \/ 1 < counth h0) as Hr.
    { apply Nat.le_gt_cases. }
    destruct Hr.
    + (* 自分の手札一枚以下 -> 出せない *)
      assert (counth h0 = 1) as Hc0r.
      { apply Nat.le_antisymm.
        - apply H0.
        - apply lt_le_S.
          apply Hs0. }
      assert (mu0 h0 h1 r = 0).
      { symmetry.
        apply le_n_0_eq.
        apply Nat.le_trans with (m:=mu1 h0 h1).
        - apply Hmu.
        - apply f_equal_pred in Hc0r.
          simpl in Hc0r.
          rewrite <- Hc0r.
          apply mu0_le_pred_nh0. }
      intros a Hv.
      apply mu0_eq_0_not_puttable in H1.
      apply forced_pass_cond with (a:=a) in H1.
      * intros Hr.
        exfalso. apply H1.
        split. apply Hv. apply Hr.
      * split. apply Hs0. apply Hs1.
    + (* 自分の手札二枚以上 -> 出しても負け条件に遷移 *)
      intros a Hin Hr.
      apply H.
      * apply eq_add_S.
        rewrite plus_n_Sm.
        rewrite remove_length_in.
        -- rewrite plus_comm.
           apply Hn.
        -- apply Hin.
      * split.
        -- apply Hs1.
        -- apply ap_sorted_remove_ap_sorted.
           ++ apply Hs0.
           ++ apply H0.
      * apply lose_move_put with (r:=r).
        -- split. apply Hs0. apply Hs1.
        -- apply H0.
        -- split. apply Hin. apply Hr.
        -- apply Hmu.
  - (* パス *)
    apply mu_win_puttable_step with (n:=n).
    + intros h0' h1' r' Hnn. apply H.
      apply Hnn.
    + rewrite plus_comm.
      apply Hn.
    + split. apply Hs1. apply Hs0.
    + apply lt_le_trans with (m:=minh h1).
      * apply Hs1.
      * apply min_le_max.
    + apply lose_move_pass with (r:=r).
      * split. apply Hs0. apply Hs1.
      * apply Hmu.
Qed.

(* induction step : μ0 > μ1 で出せる札がなければパスで勝ち *)
Lemma mu_win_not_puttable_step : forall n : nat,
  (forall (h0' h1' : hand) (r' : nat),
   counth h0' + counth h1' = n ->
   ap_sorted h0' /\ ap_sorted h1' ->
   mu_win_cond h0' h1' r' /\ mu_lose_cond h0' h1' r'
  ) ->
  forall (h0 h1 : hand) (r : nat),
  counth h0 + counth h1 = S n ->
  ap_sorted h0 /\ ap_sorted h1 ->
  maxh h0 <= r -> mu_win_cond h0 h1 r.
Proof.
  intros n H h0 h1 r Hn [Hs0 Hs1] Hv Hmu.
  apply InductivePassWin.
  apply mu_lose_step with (n:=n).
  - apply H.
  - rewrite plus_comm.
    apply Hn.
  - split. apply Hs1. apply Hs0.
  - apply win_move_pass_if_not_puttable with (r:=r).
    + split. apply Hs0. apply Hs1.
    + apply Hv.
    + apply Hmu.
Qed.

(* induction step まとめ *)
Lemma mu_win_lose_step : forall n : nat,
  (forall (h0' h1' : hand) (r' : nat),
   counth h0' + counth h1' = n ->
   ap_sorted h0' /\ ap_sorted h1' ->
   mu_win_cond h0' h1' r' /\ mu_lose_cond h0' h1' r'
  ) ->
  forall (h0 h1 : hand) (r : nat),
  counth h0 + counth h1 = S n ->
  ap_sorted h0 /\ ap_sorted h1 ->
  (mu_win_cond h0 h1 r /\ mu_lose_cond h0 h1 r).
Proof.
  split.
  - assert (maxh h0 <= r \/ r < maxh h0) as Hr.
    { apply Nat.le_gt_cases. }
    destruct Hr as [Hr | Hr].
    + apply mu_win_not_puttable_step with (n:=n).
      apply H. apply H0. apply H1. apply Hr.
    + apply mu_win_puttable_step with (n:=n).
      apply H. apply H0. apply H1. apply Hr.
  - apply mu_lose_step with (n:=n).
    apply H. apply H0. apply H1.
Qed.


(********************)
(* 手札枚数による帰納法 *)
(********************)

Lemma sum_2_divide : forall n m : nat,
  n + m = 2 -> 0 < n /\ 0 < m -> n = 1 /\ m = 1.
Proof.
  intros n m H [Hn0 Hn1].
  split.
  - destruct n.
    + inversion Hn0.
    + rewrite plus_Sn_m in H.
      apply eq_add_S in H.
      apply eq_S.
      destruct m.
      * inversion Hn1.
      * rewrite <- plus_n_Sm in H.
        apply eq_add_S in H.
        apply plus_is_O in H.
        apply H.
  - destruct m.
    + inversion Hn1.
    + rewrite <- plus_n_Sm in H.
      apply eq_add_S in H.
      apply eq_S.
      destruct n.
      * inversion Hn0.
      * rewrite plus_Sn_m in H.
        apply eq_add_S in H.
        apply plus_is_O in H.
        apply H.
Qed.

Lemma mu_win_lose_n : forall n : nat,
  forall (h0 h1 : hand) (r : nat),
  counth h0 + counth h1 = n ->
  ap_sorted h0 /\ ap_sorted h1 ->
  mu_win_cond h0 h1 r /\ mu_lose_cond h0 h1 r.
Proof.
  intros n.
  assert (n < 2 \/ 2 <= n).
  { apply Nat.lt_ge_cases. }
  destruct H.
  - (* n <= 1 :対象外 *)
    intros h0 h1 r Hn Hs.
     assert (2 <= n).
    { rewrite <- Hn.
      replace 2 with (1 + 1).
      - apply plus_le_compat.
        + apply Hs.
        + apply Hs.
      - reflexivity. }
    apply le_not_lt in H0.
    apply H0 in H.
    contradiction H.
  - induction H as [| n].
    + (* n = 2 : base step *)
      intros h0 h1 r Hn Hs.
      apply sum_2_divide in Hn.
      * apply mu_win_lose_base.
        -- apply Hs.
        -- apply Hn.
      * split. apply Hs. apply Hs.
    + (* n -> S n : induction step *)
      intros h0 h1 r Hn Hs.
      apply mu_win_lose_step with (n:=n).
      * apply IHle.
      * apply Hn.
      * apply Hs.
Qed.


(**************)
(* 順方向の定理 *)
(**************)

Theorem mu_win_lose : forall (h0 h1 : hand) (r : nat),
  ap_sorted h0 /\ ap_sorted h1 ->
  mu_win_cond h0 h1 r /\ mu_lose_cond h0 h1 r.
Proof.
  intros.
  apply mu_win_lose_n with (n:=counth h0 + counth h1).
  - reflexivity.
  - apply H.
Qed.
