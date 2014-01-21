Require Export chapter07.

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Theorem and_example : 
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
  Case "left". apply b_0.
  Case "right". apply b_3. Qed.

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP. Qed.

Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HQ. Qed.

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HP HQ].
  split.
    Case "left". apply HQ.
    Case "right". apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
    split.
      apply HP.
      apply HQ.
    apply HR.
Qed.

Theorem even__ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  induction n.
  Case "0". split.
    intros. apply ev_0.
    intros. inversion H.
  Case "S n". intros.
    split. apply IHn.
           intro. apply ev_SS. unfold even in H. simpl in H.
                  apply IHn. apply H.
Qed.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [HAB HBA]. apply HAB. Qed.

Theorem iff_sym : forall P Q : Prop, 
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB. Qed.

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof.
  intros. split.
  intros. apply H.
  intros. apply H.
Qed.


Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros.
  inversion H. inversion H0.
  split. intros. apply H3. apply H1. apply H5.
         intros. apply H2. apply H4. apply H5.
Qed.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ. Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [HP | [HQ HR]].
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR. Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H. inversion H as [[HP1 | HQ] [HP2 | HR]].
  left. apply HP1.
  left. apply HP1.
  left. apply HP2.
  right. split. apply HQ. apply HR.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  split. apply or_distributes_over_and_1.
         apply or_distributes_over_and_2.
Qed.

Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H. Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b.
  Case "true". destruct c.
    SCase "true". simpl in H. inversion H.
    SCase "false". right. reflexivity.
  Case "false". left. reflexivity.
Qed.

Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.
  destruct b.
  Case "true". left. reflexivity.
  Case "false". destruct c.
    SCase "true". right. reflexivity.
    SCase "false". simpl in H. inversion H.
Qed.

Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H. destruct b.
  Case "true". destruct c.
    SCase "true". simpl in H. inversion H.
    SCase "false". simpl in H. inversion H.
  Case "false". destruct c.
    SCase "true". simpl in H. inversion H.
    SCase "false". split. reflexivity. reflexivity.
Qed.

Inductive False : Prop := .

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra. Qed.

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra. Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra. Qed.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA.
  apply HNA in HP. inversion HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H. Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H. unfold not. intros notQ Pass.
  apply notQ. apply H. apply Pass.
Qed.
  
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P. unfold not.
  intros H. inversion H.
    apply H1. apply H0.
Qed.
  
Theorem five_not_even : 
  ~ ev 5.
Proof.
  (* WORKED IN CLASS *)
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn].
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1. Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof.
  unfold not. intros n H. induction H. (* not n! *)
  Case "0". intros. inversion H.
  Case "S n". intros. apply IHev. apply SSev__even. apply H0.
Qed.

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H.
  (* But now what? There is no way to "invent" evidence for ~P 
     from evidence for P. *)
  Abort.

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity. Qed.

Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  intros. unfold not in H. generalize dependent m. induction n.
  Case "0". induction m.
    SCase "0". simpl. intros. apply ex_falso_quodlibet. apply H. reflexivity.
    SCase "S m". intros. simpl. reflexivity.
  Case "S n". induction m.
    SCase "0". intros. simpl. reflexivity.
    SCase "S m".  intros. simpl. apply IHn. intros. apply H. apply f_equal. apply H0.
Qed.

Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros. generalize dependent m. unfold not. induction n.
  Case "0". intros. induction m.
    SCase "0". simpl in H. inversion H.
    SCase "S m". inversion H0.
  Case "S n". intros. induction m.
    SCase "0". inversion H0.
    SCase "S m". apply (IHn m). simpl in H. apply H.
                 inversion H0. reflexivity.
Qed.
  
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  intros. generalize dependent m. unfold not. induction n.
  Case "0". intros. simpl in H. inversion H.
  Case "S m". intros. destruct m.
   SSCase "0". inversion H0.
   SSCase "S m". apply (IHn m). simpl in H. apply H.
                 apply Sn_le_Sm__n_le_m. apply H0.
Qed.

Inductive ex (X:Type) (P : X -> Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity. Qed.

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity. Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).
  apply Hm. Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not. intros.
  inversion H0.
  apply H1.
  apply H.
Qed.

Definition excluded_middle := forall P:Prop, 
  P \/ ~P.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros. unfold excluded_middle in H.
  unfold not in H0. unfold not in H.
  destruct H with (P := P x).
    apply H1.
    apply ex_falso_quodlibet. apply H0.
    exists x. apply H1.
Qed.
  
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   split.
   Case "->". intros. destruct H.
              destruct H as [HL | HR].
                left. exists witness. apply HL.
                right. exists witness. apply HR.
   Case "<-". intros. destruct H.
                destruct H. apply (or_introl (P witness) (Q witness)) in H.
                exists witness. apply H.
                destruct H. apply (or_intror (P witness) (Q witness)) in H.
                exists witness. apply H.
Qed.

Lemma leibniz_equality : forall (X : Type) (x y: X), 
 x = y -> forall P : X -> Prop, P x -> P y.
Proof.
  intros. rewrite <- H. apply H0.
Qed.

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" := (sumbool A B) : type_scope.

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'".
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal. apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined.

Definition override' {X: Type} (f: nat -> X) (k:nat) (x:X) : nat -> X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2). (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2".
    reflexivity. Qed.

Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat -> X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros. unfold override'.
  destruct (eq_nat_dec k1 k2).
  Case "k1 = k2". reflexivity.
  Case "k1 <> k2". reflexivity.
Qed.

Lemma dist_and_or_eq_implies_and : forall P Q R,
       P /\ (Q \/ R) /\ Q = R -> P /\ Q.
Proof.
  intros. split.
  Case "a". inversion H. apply H0.
  Case "b". inversion H. inversion H1.
            inversion H2. apply H4.
            rewrite H3. apply H4.
Qed.

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  all_nil : all X P []
| all_cons : forall x xs, P x -> all X P xs -> all X P (x :: xs).

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_all : forall (X : Type) (l : list X) (test : X -> bool),
  all X (fun x => test x = true) l <-> forallb test l = true.
Proof.
  split.
  Case "->". induction l as [|y ys].
    SCase "[]". intros. simpl. reflexivity.
    SCase "y :: ys". intros. simpl. destruct (test y) eqn:testY.
      SSCase "true". simpl. apply IHys. inversion H. apply H3.
      SSCase "false". inversion H. rewrite testY in H2. inversion H2.
  Case "<-". induction l as [|y ys].
    SCase "[]". intros. apply all_nil.
    SCase "y :: ys". simpl. intros. destruct (test y) eqn:testY.
      SSCase "true". apply all_cons. apply testY. apply IHys.
        destruct (forallb test ys).
        reflexivity.
        simpl in H. inversion H.
      SSCase "false". simpl in H. inversion H.
Qed.

Inductive inorder_merge {X : Type} : list X -> list X -> list X -> Prop :=
  inorder_nil : inorder_merge [] [] []
| inorder_1 : forall x xs ys zs, inorder_merge xs ys zs
                               -> inorder_merge (x :: xs) ys (x :: zs)
| inorder_2 : forall y xs ys zs, inorder_merge xs ys zs
                               -> inorder_merge xs (y :: ys) (y :: zs).

Theorem filter_challenge : forall (X : Type) (l1 l2 l12 : list X) (P : X -> bool),
  forallb P l1 = true -> forallb (fun x => negb (P x)) l2 = true
  -> inorder_merge l1 l2 l12 -> filter P l12 = l1.
Proof.
  intros. induction H1.
  Case "[]". simpl. reflexivity.
  Case "1st". simpl. destruct (P x) eqn:Px.
    SCase "true". apply f_equal. apply IHinorder_merge.
                  simpl in H. rewrite Px in H. simpl in H. apply H.
                  apply H0.
    SCase "false". simpl in H. rewrite Px in H. simpl in H. inversion H.
  Case "2nd". simpl. destruct (P y) eqn:Py.
    SCase "true". simpl in H0. rewrite Py in H0. simpl in H0. inversion H0.
    SCase "false". apply IHinorder_merge.
                   apply H.
                   simpl in H0. rewrite Py in H0. simpl in H0. apply H0.
Qed.