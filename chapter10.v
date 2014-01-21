Require Export chapter09.

Check nat_ind.

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.
Check tree_ind.

Inductive mytype (X:Type) : Type :=
  | constr1 : forall (x : X), mytype X
  | constr2 : forall (n : nat), mytype X
  | constr3 : forall (m : mytype X) (n : nat), mytype X
  | constr4 : mytype X.
Check mytype_ind.

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.
Check foo'_ind.

Definition P_m0r (n:nat) : Prop := 
  n * 0 = 0.

Theorem mult_0_r'' : forall n:nat, 
  P_m0r n.
Proof.
  apply nat_ind.
  Case "n = O". reflexivity.
  Case "n = S n'".
    (* Note the proof state at this point! *)
    intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.

Theorem plus_comm' : forall n m : nat, 
  n + m = m + n.
Proof.
  induction n as [| n'].
  Case "n = O". intros m. rewrite -> plus_0_r. reflexivity.
  Case "n = S n'". intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

Lemma one_not_beautiful_FAILED: ~ beautiful 1.
Proof.
  intro H.
  (* Just doing an inversion on H won't get us very far in the b_sum
    case. (Try it!). So we'll need induction. A naive first attempt: *)
  induction H.
  (* But now, although we get four cases, as we would expect from
     the definition of beautiful, we lose all information about H ! *)
Abort.

Inductive foo (X : Set) (Y : Set) : Set :=
     | foo1 : X -> foo X Y
     | foo2 : Y -> foo X Y
     | foo3 : foo X Y -> foo X Y.
Check foo_ind.

Inductive bar : Set :=
  | bar1 : nat -> bar
  | bar2 : nat -> bar
  | bar3 : bool -> bar -> bar.
Check bar_ind.

Inductive no_longer_than (X : Set) : (list X) -> nat -> Prop :=
    | nlt_nil  : forall n, no_longer_than X [] n
    | nlt_cons : forall x l n, no_longer_than X l n ->
                               no_longer_than X (x::l) (S n)
    | nlt_succ : forall l n, no_longer_than X l n ->
                             no_longer_than X l (S n).
Check no_longer_than_ind.

Check and_ind.
Check or_ind.

Check False_ind.