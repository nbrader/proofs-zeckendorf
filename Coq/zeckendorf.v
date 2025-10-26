Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Le.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Program.Wf.
Import ListNotations.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S n' => match n' with
            | 0 => 1  (* This handles the case for fib(1) correctly *)
            | S n'' => fib n' + fib n''  (* Recursive calls on structurally smaller arguments *)
            end
  end.

Require Import List.
Import ListNotations.

Fixpoint takeWhile {A : Type} (f : A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if f x then x :: takeWhile f xs else []
  end.

Definition fibs_upto (n : nat) : list nat :=
  takeWhile (fun x => Nat.leb x n) (map fib (seq 1 (S n))).

(* Computation lemma for fib *)
Lemma fib_SS : forall n, fib (S (S n)) = fib (S n) + fib n.
Proof.
  intro n. destruct n; simpl; reflexivity.
Qed.

(* Helper lemma: Fibonacci numbers are positive for n >= 1 *)
Lemma fib_pos : forall n, n >= 1 -> fib n > 0.
Proof.
  intro n. pattern n. apply lt_wf_ind. clear n.
  intros n IH Hge.
  destruct n as [|[|[|n'']]].
  - (* n = 0 *) inversion Hge.
  - (* n = 1 *) compute. auto.
  - (* n = 2 *) compute. auto.
  - (* n = S (S (S n'')) = S (S m) where m = S n'' *)
    rewrite fib_SS. apply Nat.add_pos_pos.
    + apply IH.
      * apply Nat.lt_succ_diag_r.
      * apply le_n_S. apply Nat.le_0_l.
    + apply IH.
      * apply Nat.lt_trans with (S (S n'')).
        -- apply Nat.lt_succ_diag_r.
        -- apply Nat.lt_succ_diag_r.
      * apply le_n_S. apply Nat.le_0_l.
Qed.

(* Fibonacci sequence is monotonically increasing for n >= 2 *)
Lemma fib_mono : forall n, n >= 2 -> fib n < fib (S n).
Proof.
  intro n. pattern n. apply lt_wf_ind. clear n.
  intros n IH Hge.
  destruct n as [|[|[|n'']]].
  - (* n = 0 *) inversion Hge.
  - (* n = 1 *) inversion Hge. inversion H0.
  - (* n = 2: fib 2 < fib 3, i.e., 1 < 2 *) simpl. auto.
  - (* n = S (S (S n'')), so S n = S (S (S (S n''))) *)
    assert (Hpos: fib (S (S n'')) > 0).
    { apply fib_pos. apply le_n_S. apply Nat.le_0_l. }
    (* Goal: fib (S (S (S n''))) < fib (S (S (S (S n'')))) *)
    (* Rewrite RHS using fib_SS *)
    assert (Heq: fib (S (S (S (S n'')))) = fib (S (S (S n''))) + fib (S (S n''))).
    { replace (S (S (S (S n'')))) with (S (S (S (S n'')))) by reflexivity.
      rewrite fib_SS. reflexivity. }
    rewrite Heq.
    apply Nat.lt_add_pos_r. assumption.
Qed.

(* Helper lemma: elements in seq start len are >= start *)
Lemma seq_ge : forall x start len,
  In x (seq start len) -> x >= start.
Proof.
  intros x start len.
  generalize dependent start.
  induction len; intros start Hin.
  - simpl in Hin. inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + rewrite Heq. auto.
    + apply IHlen in Hin'. auto with arith.
Qed.

(* Elements in fibs_upto are Fibonacci numbers *)
Lemma in_fibs_upto_fib : forall x n,
  In x (fibs_upto n) -> exists k, k >= 1 /\ fib k = x.
Proof.
  intros x n Hin.
  unfold fibs_upto in Hin.
  remember (seq 1 (S n)) as l.
  assert (Hge: forall y, In y l -> y >= 1).
  { intros y Hiny. rewrite Heql in Hiny.
    apply seq_ge in Hiny. assumption. }
  clear Heql.
  induction l as [|a l' IH].
  - simpl in Hin. inversion Hin.
  - simpl in Hin.
    destruct (Nat.leb (fib a) n) eqn:Hleb.
    + simpl in Hin. destruct Hin as [Heq | Hin'].
      * exists a. split.
        -- apply Hge. left. reflexivity.
        -- rewrite <- Heq. reflexivity.
      * assert (Hge': forall y, In y l' -> y >= 1).
        { intros y Hiny. apply Hge. right. assumption. }
        apply IH; assumption.
    + inversion Hin.
Qed.

(* Elements in fibs_upto are positive *)
Lemma in_fibs_upto_pos : forall x n,
  In x (fibs_upto n) -> x > 0.
Proof.
  intros x n Hin.
  destruct (in_fibs_upto_fib x n Hin) as [k [Hk Heq]].
  rewrite <- Heq.
  apply fib_pos. assumption.
Qed.

Lemma fib_decrease : forall x n, In x (fibs_upto n) -> x > 0 -> x < n -> n - x < n.
Proof.
  intros x n Hin Hpos Hlt.
  apply Nat.sub_lt; auto with arith.
Qed.

(* Helper lemma: In x (rev l) -> In x l *)
Lemma in_list_rev : forall {A} (x : A) l,
  In x (rev l) -> In x l.
Proof.
  intros. apply in_rev. assumption.
Qed.

Program Fixpoint zeckendorf (n : nat) (acc : list nat) {measure n} : list nat :=
  match n with
  | 0 => acc
  | _ => let fibs := rev (fibs_upto n) in
         match fibs with
         | [] => acc
         | x :: xs =>
           match lt_dec x n with
           | left Hx => zeckendorf (n - x) (x :: acc)
           | right _ => acc
           end
         end
  end.
Next Obligation.
Proof.
  (* Need to prove: n - x < n *)
  (* x :: xs = rev (fibs_upto n), so x is in fibs_upto n *)
  assert (Hin: In x (fibs_upto n)).
  { apply in_list_rev. rewrite <- Heq_fibs. simpl. left. reflexivity. }
  (* Therefore x > 0 *)
  assert (Hpos: x > 0) by (apply (in_fibs_upto_pos x n Hin)).
  (* We have Hx : x < n and Hpos : x > 0, so n - x < n *)
  (* Nat.sub_lt : forall n m, m <= n -> 0 < m -> n - m < n *)
  apply Nat.sub_lt.
  - apply Nat.lt_le_incl. assumption.
  - assumption.
Qed.

(* Theorem zeckendorf_correct : forall n,
  let zs := zeckendorf n [] in
  (forall z, In z zs -> exists k, z = fib k) /\
  (forall z1 z2, In z1 zs -> In z2 zs -> z1 <> z2 -> ~exists k, z1 = fib k /\ z2 = fib (S k)) /\
  sum_list zs = n.
Proof.
  (* This proof would involve induction on n and case analysis on the recursive construction of zeckendorf lists. *)
Admitted. *)
