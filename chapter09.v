Require Export chapter08.

Theorem eight_is_beautiful'': beautiful 8.
Proof.
   Show Proof.
   apply b_sum with (n:=3) (m:=5).
   Show Proof.
   apply b_3.
   Show Proof.
   apply b_5.
   Show Proof.
Qed.

Theorem six_is_beautiful :
  beautiful 6.
Proof.
  apply b_sum with (n := 3) (m := 3).
  apply b_3. apply b_3.
Qed.

Definition six_is_beautiful' : beautiful 6 :=
  b_sum 3 3 b_3 b_3.

Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
  intros. simpl. apply b_sum. apply H. apply b_sum. apply H. apply b_0.
Qed.

Definition b_times2': forall n, beautiful n -> beautiful (2*n) :=
  fun (n : nat) => fun (e : beautiful n) => b_sum n (n + 0) e (b_sum n 0 e b_0).

Theorem and_example : 
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
   Case "left". apply b_0.
   Case "right". apply b_3. Qed.

Print and_example.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (PAndQ : P /\ Q) (QAndR : Q /\ R) =>
    match PAndQ with
    | conj HP HQ1 => match QAndR with
                     | conj HQ2 HR => conj P R HP HR
                     end
    end.