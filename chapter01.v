Inductive day : Type :=
  | monday    : day
  | tuesday   : day
  | wednesday : day
  | thursday  : day
  | friday    : day
  | saturday  : day
  | sunday    : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Eval compute in (next_weekday friday).

Example test_net_weekay :
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true  : bool
  | false : bool.

Definition negb (b : bool) : bool :=
  match b with
  | true  => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => b2 
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. reflexivity. Qed.

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  match (b1, b2) with
  | (true,  true)  => false
  | _              => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match (b1,b2,b3) with
  | (true,true,true) => true
  | _                => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check true.
Check negb.

Module Playground1.

  Inductive nat : Type :=
    | O : nat
    | S : nat -> nat.

  Definition pred (n : nat) : nat :=
    match n with
      | O    => O
      | S n' => n'
    end.
  
End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Eval simpl in (minustwo 4).

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Eval simpl in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O    => 1
  | S n' => mult (S n') (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y) 
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x - y" := (minus x y) 
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x * y" := (mult x y) 
                       (at level 40, left associativity) 
                       : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  andb (ble_nat n m) (negb (beq_nat n m)).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.
Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof. intros n. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof. intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat, n = m -> n + n = m + m.
Proof. intros n m. intros H. rewrite -> H. reflexivity. Qed.
Theorem plus_id_exercise: forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. intros. rewrite -> H. rewrite <- H0. reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity. Qed.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity. Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [|n'].
    reflexivity.
    reflexivity. Qed.

Theorem Identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x: bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  reflexivity. Qed.

Theorem andb_eq_orb_lemma1 :
  forall (c : bool), andb true c = c.
Proof.
  destruct c.
    reflexivity.
    reflexivity. Qed.

Theorem andb_eq_orb_lemma2 :
  forall (c : bool), orb true c = true.
Proof.
  destruct c.
    reflexivity.
    reflexivity. Qed.

Theorem andb_eq_orb_lemma3 :
  forall (c : bool), andb false c = false.
Proof.
  destruct c.
    reflexivity.
    reflexivity. Qed.

Theorem andb_eq_orb_lemma4 :
  forall (c : bool), orb false c = c.
Proof.
  destruct c.
    reflexivity.
    reflexivity. Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
    (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct b.
    rewrite -> andb_eq_orb_lemma1.
    rewrite -> andb_eq_orb_lemma2.
    intro H.
    rewrite -> H.
    reflexivity.
    rewrite -> andb_eq_orb_lemma3.
    rewrite -> andb_eq_orb_lemma4.
    intro H.
    rewrite -> H.
    reflexivity.
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

Eval compute in convert_to_unary (increment_bin (Twice (Twice (TwicePlusOne Zero)))).

Theorem convert_increment :
  forall (n : bin), S (convert_to_unary n) = convert_to_unary (increment_bin n).
Proof.
  destruct n as [|n'|n'].
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    Admitted.
    