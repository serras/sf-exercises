Require Export chapter04.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros.
  apply H.
  apply H0.
Qed.

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Actually, this simpl is unnecessary, since 
            apply will do a simpl step first. *)
  apply H. Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros. rewrite H. symmetry. apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] -> 
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]). apply eq1. apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof. intros. apply trans_eq with m. apply H0. apply H. Qed.

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity. Qed.

Theorem silly5 : forall (n m o : nat),
     [n;m] = [o;o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

Example sillyex1 : forall(X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros. inversion H0. reflexivity.
Qed.

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros. inversion H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A), 
    x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros X v l. induction l as [| v' l'].
  Case "l = []". intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'". intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply f_equal. apply IHl'. inversion eq. reflexivity. Qed.

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros. destruct n as [|m].
  Case "0". reflexivity.
  Case "S m". inversion H.
Qed.

Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
  intros. destruct n as [|m].
  Case "0". reflexivity.
  Case "S m". inversion H.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Check plus_n_Sm.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "0". intros m H. destruct m as [|m'].
    reflexivity.
    inversion H.
  Case "S m'". intros m. destruct m as [|m'].
    intros. inversion H.
    intros eq. inversion eq.
    rewrite <- plus_n_Sm in H0. rewrite <- plus_n_Sm in H0.
    inversion H0. apply IHn' in H1. rewrite -> H1. reflexivity.
Qed.

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'".
    (* Notice that both the goal and the induction
       hypothesis have changed: the goal asks us to prove
       something more general (i.e., to prove the
       statement for _every_ m), but the IH is
       correspondingly more flexible, allowing us to
       choose any m we like when we apply the IH.  *)
    intros m eq.
    (* Now we choose a particular m and introduce the
       assumption that double n = double m.  Since we
       are doing a case analysis on n, we need a case
       analysis on m to keep the two "in sync." *)
    destruct m as [| m'].
    SCase "m = O".
      (* The 0 case is trivial *)
      inversion eq.
    SCase "m = S m'".
      apply f_equal.
      (* At this point, since we are in the second
         branch of the destruct m, the m' mentioned
         in the context at this point is actually the
         predecessor of the one we started out talking
         about.  Since we are also in the S branch of
         the induction, this is perfect: if we
         instantiate the generic m in the IH with the
         m' that we are talking about right now (this
         instantiation is performed automatically by
         apply), then IHn' gives us exactly what we
         need to finish the proof. *)
      apply IHn'. inversion eq. reflexivity. Qed.

Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [|p].
  Case "0". destruct m as [|q].
    reflexivity.
    intros H. inversion H.
  Case "S p". destruct m as [|q].
    intros H. inversion H.
    intros H. apply f_equal. apply IHp. inversion H. reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m'].
  Case "m = O". simpl. intros n eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'". apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  intros. generalize dependent n. induction l as [|x xs].
  Case "[]". reflexivity.
  Case "x :: xs". destruct n as [|m].
    SCase "0". simpl. intros H. inversion H.
    SCase "S m". intros H. apply IHxs. simpl. inversion H. reflexivity.
Qed.

Theorem length_snoc''' : forall (n : nat) (X : Type) 
                                (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros n X v l. generalize dependent v. generalize dependent n.
  induction l as [|x xs].
  Case "[]". simpl. intros. rewrite -> H. reflexivity.
  Case "x :: xs".  simpl. intros. destruct n as [|m].
    inversion H.
    apply f_equal. apply IHxs. inversion H. reflexivity.
Qed.

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) 
                                 (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  intros X l1. induction l1 as [|x xs].
  Case "[]". simpl. intros. rewrite <- H. reflexivity.
  Case "x :: xs". simpl. intros l2 y n. destruct n as [|m].
    SCase "0". intros contra. inversion contra.
    SCase "S m". intros eq. apply f_equal. apply IHxs with y.
                 inversion eq. reflexivity.
Qed.

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n l. generalize dependent n. induction l as [|x xs].
  Case "[]". simpl. intros. rewrite <- H. simpl. reflexivity.
  Case "x :: xs". simpl. intros. destruct n as [|m].
    SCase "0". inversion H.
    SCase "S m".
      assert (Lemma : forall a (b : X) c, length (a ++ b :: c) = S (length (a ++ c))).
        induction a as [|d ds].
        SSCase "[]". simpl. intros. reflexivity.
        SSCase "d :: ds". simpl. intros. rewrite IHds. reflexivity.
      rewrite Lemma. rewrite IHxs with (n := m).
      simpl. rewrite plus_n_Sm. reflexivity.
      inversion H. reflexivity.
Qed.

Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat -> X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros. unfold override. destruct (beq_nat k1 k2).
    Case "true". reflexivity.
    Case "false". reflexivity.
Qed.

Theorem eq_pair : forall X Y (x : X*Y), x = (fst x, snd x).
Proof. destruct x. reflexivity. Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [|x xs].
  Case "[]". simpl. intros. inversion H. reflexivity.
  Case "x :: xs". intros l1 l2. destruct x. simpl.
                  intros H. inversion H. simpl.
    assert (Lemma : forall t r, t = r -> (x, y) :: t = (x, y) :: r).
      intros. rewrite H0. reflexivity.
    apply Lemma. apply IHxs. rewrite <- eq_pair. reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got stuck
    above, except that the context contains an extra equality
    assumption, which is exactly what we need to make progress. *)
    Case "e3 = true". apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    Case "e3 = false".
     (* When we come to the second equality test in the body of the
       function we are reasoning about, we can use eqn: again in the
       same way, allow us to finish the proof. *)
      destruct (beq_nat n 5) eqn:Heqe5.
        SCase "e5 = true".
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        SCase "e5 = false". inversion eq. Qed.

Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  intros f b. destruct b.
  Case "b = true". destruct (f true) eqn:ft.
    SCase "f true = true". rewrite ft. rewrite ft. reflexivity.
    SCase "f true = false". destruct (f false) eqn:ff.
      SSCase "f false = true". rewrite ft. reflexivity.
      SSCase "f false = false". rewrite ff. reflexivity.
  Case "b = false". destruct (f false) eqn:ff.
    SCase "f false = true". destruct (f true) eqn:ft.
      SSCase "f false = true". rewrite ft. reflexivity.
      SSCase "f false = false". rewrite ff. reflexivity.
    SCase "f false = false". rewrite ff. rewrite ff. reflexivity.
Qed.

Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros. unfold override. destruct (beq_nat k1 k2) eqn:D.
  Case "true". apply beq_nat_true in D. rewrite D in H. rewrite H. reflexivity.
  Case "false". reflexivity.
Qed.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [|p].
  Case "0". destruct m as [|q].
    reflexivity.
    reflexivity.
  Case "S q". destruct m as [|q].
    reflexivity.
    simpl. apply IHp.
Qed.

Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  intros. apply beq_nat_true in H. apply beq_nat_true in H0.
  rewrite H0 in H. rewrite H.
  assert (Z : forall z, beq_nat z z = true).
    induction z as [|q].
      reflexivity.
      simpl. rewrite IHq. reflexivity.
  apply Z.
Qed.

Theorem split_combine : forall X Y (l1 : list X) (l2 : list Y) l
                      , length l1 = length l2
                      -> combine l1 l2 = l
                      -> split l = (l1, l2).
Proof.
  induction l1 as [|x xs].
  Case "[]". simpl. destruct l2 as [|y ys].
    SCase "[]". simpl. intros. rewrite <- H0. reflexivity.
    SCase "y :: ys". simpl. intros. inversion H.
  Case "x :: xs". destruct l2 as [|y ys].
    SCase "[]". simpl. intros. inversion H.
    SCase "y :: ys". simpl.
                     intros. inversion H. apply IHxs with (l := combine xs ys) in H2.
                     rewrite <- H0. simpl. rewrite -> H2. simpl. reflexivity.
                     reflexivity.
Qed.

Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat -> X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros. unfold override. destruct (beq_nat k1 k3) eqn:k1k3.
  Case "true". destruct (beq_nat k2 k3) eqn:k2k3.
    SCase "true". apply beq_nat_true in k1k3.
                 rewrite <- k1k3 in k2k3.
                 rewrite -> H in k2k3.
                 inversion k2k3.
    SCase "false". reflexivity.
  Case "false".  reflexivity.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l. generalize dependent test. generalize dependent x.
  induction l as [|x xs].
  Case "[]". simpl. intros. inversion H.
  Case "x :: xs".  simpl. intros. destruct (test x) eqn:t.
    SCase "test true". inversion H. rewrite <- H1. rewrite t. reflexivity.
    SCase "test false". apply IHxs in H. rewrite <- H. reflexivity.
Qed.

Fixpoint forallb {X : Type} (p : X -> bool) (lst : list X) : bool :=
  match lst with
  | [] => true
  | x :: xs => andb (p x) (forallb p xs)
  end.

Example forallb1 : forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example forallb2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example forallb3 : forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example forallb4 : forallb (beq_nat 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (p : X -> bool) (lst : list X) : bool :=
  match lst with
  | [] => false
  | x :: xs => orb (p x) (existsb p xs)
  end.

Example existsb1 : existsb (beq_nat 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example existsb2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example existsb3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example existsb4 : existsb evenb [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (p : X -> bool) (lst : list X) :=
  negb (forallb (fun x => negb (p x)) lst).

Theorem or_and : forall (a b : bool), orb a b = negb (andb (negb a) (negb b)).
Proof.
  intros. destruct a.
    destruct b. reflexivity. reflexivity.
    destruct b. reflexivity. reflexivity.
Qed.

Theorem negb_involutive : forall (a : bool), negb (negb a) = a.
Proof. intros. destruct a. reflexivity. reflexivity. Qed.

Theorem or_and2 : forall (a b : bool), orb a (negb b) = negb (andb (negb a) b).
Proof.
  intros. destruct a.
    destruct b. reflexivity. reflexivity.
    destruct b. reflexivity. reflexivity.
Qed.

Theorem two_exists : forall (X : Type) (p : X -> bool) (lst : list X)
                   , existsb p lst = existsb' p lst.
Proof.
  intros X p lst. generalize dependent p.
  induction lst as [|x xs].
  Case "[]". reflexivity.
  Case "x :: xs". simpl. unfold existsb'. simpl.
                  intros p. rewrite <- or_and2.
                  apply f_equal. rewrite IHxs. reflexivity.
Qed.