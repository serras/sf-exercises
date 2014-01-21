Require Export chapter06.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2. Qed.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Lmn Lno.
  generalize dependent Lmn.
  generalize dependent m.
  induction Lno.
  Case "le_n". intros. apply Lmn.
  Case "le_S". intros. apply le_S. apply IHLno. apply Lmn.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros. induction n.
  apply le_n.
  apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H.
  apply le_n.
  apply le_S. apply IHle.
Qed.

Theorem n_le_Sn : forall n, n <= S n.
Proof. intros. apply le_S. apply le_n. Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros. inversion H.
    apply le_n.
    apply le_trans with (n := S n). apply n_le_Sn.
    apply H2.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros. induction a.
  Case "0". simpl. apply O_le_n.
  Case "S". simpl. apply n_le_m__Sn_le_Sm. apply IHa.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
Admitted.
 
Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros. apply le_S. apply H.
Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  intros n m. generalize dependent n. induction m.
  Case "0". destruct n.
    SCase "0". intros. apply le_n.
    SCase "S n". simpl. intros. inversion H.
  Case "S m". intros. destruct n.
    SCase "0". apply O_le_n.
    SCase "S n". apply n_le_m__Sn_le_Sm. apply IHm.
                 simpl in H. apply H.
Qed.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  intros. generalize dependent n. induction m.
  Case "0". destruct n.
    SCase "0". simpl. intros. reflexivity.
    SCase "S n". intros. inversion H.
  Case "S m". intros. destruct n.
    SCase "0". simpl. reflexivity.
    SCase "S n". simpl. apply IHm.
                 apply Sn_le_Sm__n_le_m.
                 apply H.
Qed.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.
Proof.
  intros.
  apply le_ble_nat.
  apply le_trans with (n := m).
    apply ble_nat_true. apply H.
    apply ble_nat_true. apply H0.
Qed.

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

Theorem R_add : forall m n o, R m n o -> m + n = o.
Proof.
  intros.
  induction H.
    simpl. reflexivity.
    simpl. apply f_equal. apply IHR.
    rewrite plus_comm. simpl. apply f_equal. rewrite -> plus_comm. apply IHR.
    simpl in IHR. inversion IHR. rewrite -> plus_comm in H1. simpl in H1.
                  inversion H1. rewrite -> plus_comm. reflexivity.
    rewrite -> plus_comm. apply IHR.
Qed.

