Require Export chapter01.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
(** Here's an example of how [Case] is used.  Step through the
   following proof and observe how the context changes. *)

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true". (* <----- here *)
    reflexivity.
  Case "b = false". (* <---- and here *)
    rewrite <- H.
    reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H.
    reflexivity.
Qed.

Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [|m].
  Case "n = 0". reflexivity.
  Case "n = S m". simpl. rewrite -> IHm. reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [|m].
  Case "0". reflexivity.
  Case "S m". simpl. rewrite -> IHm. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n'].
  Case "0". reflexivity.
  Case "S n'". simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [|n'].
  Case "0". simpl. rewrite -> plus_0_r. reflexivity.
  Case "S n'". simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n'].
  Case "0". rewrite -> plus_0_n. simpl. reflexivity.
  Case "S m". simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n. induction n as [|m].
  Case "0". reflexivity.
  Case "S m". simpl. rewrite <- plus_comm. simpl. rewrite <- IHm. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  assert (H : p + n = n + p).
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.
Qed.

Theorem mult_0 : forall n, n * 0 = 0.
Proof.
  induction n as [|q].
    reflexivity.
    simpl. rewrite -> IHq. reflexivity.
Qed.

Theorem mult_1 : forall n, n * 1 = n.
Proof.
  induction n as [|q].
    reflexivity.
    simpl. rewrite -> IHq. reflexivity.
Qed.

Theorem mult_comm_lemma : forall n m, m * S n = m + m * n.
Proof.
  intros n m.
  induction m as [|p].
    simpl. reflexivity.
    simpl. rewrite -> plus_swap. rewrite -> IHp. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat, m * n = n * m.
Proof.
  intros m n.
  induction n as [|p].
    simpl. rewrite -> mult_0. reflexivity.
    simpl. rewrite <- IHp. rewrite -> mult_comm_lemma. reflexivity.
    (* induction m as [|q].
      simpl. reflexivity.
      simpl. rewrite -> mult_comm_lemma. rewrite -> plus_swap. reflexivity. *)
Qed.

Theorem negb_negb : forall p : bool, negb (negb p) = p.
Proof.
  intros p. destruct p as [|q].
    reflexivity.
    reflexivity.
Qed.

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n.
  destruct n as [|m].
    Case "0". simpl. reflexivity.
    Case "S m". simpl.
      induction m as [|p].
        simpl. reflexivity.
        simpl. rewrite -> IHp. rewrite -> negb_negb. reflexivity.
Qed.

Theorem ble_nat_refl : forall n : nat, true = ble_nat n n.
Proof.
  induction n as [|m].
    reflexivity.
    simpl. rewrite <- IHm. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat, beq_nat 0 (S n) = false.
Proof.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool, andb b false = false.
Proof.
  destruct b. reflexivity. reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p as [|q].
    simpl. rewrite -> H. reflexivity.
    simpl. rewrite -> IHq. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n : nat, beq_nat (S n) 0 = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem mult_1_1 : forall n : nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite -> plus_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  intros b c. destruct b. destruct c.
  reflexivity. reflexivity. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros. induction p as [|q].
    rewrite -> mult_0. rewrite -> mult_0. rewrite -> mult_0. simpl. reflexivity.
    rewrite -> mult_comm_lemma. rewrite -> mult_comm_lemma. rewrite mult_comm_lemma.
    rewrite -> plus_swap. rewrite -> IHq.
    rewrite <- plus_assoc. rewrite <- plus_assoc. rewrite -> plus_swap.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat, n * (m * p) = (n * m) * p.
Proof.
  intros.
  induction n as [|r].
    simpl. reflexivity.
    simpl. rewrite -> mult_plus_distr_r. rewrite -> IHr. reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
Proof.
  intros. induction n as [|m].
    simpl. reflexivity.
    simpl. rewrite -> IHm. reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> plus_assoc. rewrite -> plus_assoc.
  replace (n + m) with (m + n). reflexivity.
  rewrite -> plus_comm. reflexivity.
Qed.

Inductive bin : Type :=
  | Zero  : bin
  | Twice : bin -> bin
  | TwicePlusOne : bin -> bin.

Fixpoint increment_bin (n : bin) : bin :=
  match n with
  | Zero     => TwicePlusOne Zero
  | Twice n' => TwicePlusOne n'
  | TwicePlusOne n' => Twice (increment_bin n')
  end.

Fixpoint convert_to_unary (n : bin) : nat :=
  match n with
  | Zero => 0
  | Twice n' => (convert_to_unary n') + (convert_to_unary n')
  | TwicePlusOne n' => S ((convert_to_unary n') + (convert_to_unary n'))
  end.

Theorem binary_commute : forall b,
  convert_to_unary (increment_bin b) = S (convert_to_unary b).
Proof.
  intros.
  induction b as [|c|c].
    Case "Zero". simpl. reflexivity.
    Case "Twice". simpl. reflexivity.
    Case "TwicePlusOne". simpl. rewrite -> IHc. simpl.
      assert (H : forall n m, S (n + S m) = S (S (n + m))).
        intros.
        induction n as [|p].
          simpl. reflexivity.
          simpl. rewrite -> IHp. reflexivity.
      rewrite -> H. reflexivity.
Qed.