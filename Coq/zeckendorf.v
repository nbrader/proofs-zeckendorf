Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Le.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Program.Wf.
Require Import Recdef.
Require Import Lia.
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

(* Elements in fibs_upto n are <= n *)
Lemma in_fibs_upto_le : forall x n,
  In x (fibs_upto n) -> x <= n.
Proof.
  intros x n Hin.
  unfold fibs_upto in Hin.
  induction (seq 1 (S n)) as [|a l IH].
  - simpl in Hin. inversion Hin.
  - simpl in Hin.
    destruct (Nat.leb (fib a) n) eqn:Hleb.
    + simpl in Hin. destruct Hin as [Heq | Hin'].
      * subst x. apply Nat.leb_le. assumption.
      * apply IH. assumption.
    + inversion Hin.
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

Fixpoint zeckendorf_fuel (fuel n : nat) (acc : list nat) : list nat :=
  match fuel with
  | 0 => acc
  | S fuel' =>
    match n with
    | 0 => acc
    | _ => let fibs := rev (fibs_upto n) in
           match fibs with
           | [] => acc
           | x :: xs =>
             if Nat.leb x n
             then zeckendorf_fuel fuel' (n - x) (x :: acc)
             else acc
           end
    end
  end.

Definition zeckendorf (n : nat) (acc : list nat) : list nat :=
  zeckendorf_fuel n n acc.

(* Define sum of a list *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

(* Computation lemmas for zeckendorf *)
Lemma zeckendorf_0 : forall acc, zeckendorf 0 acc = acc.
Proof. intro. simpl. reflexivity. Qed.

(* Helper lemmas for zeckendorf_fuel *)
Lemma zeckendorf_fuel_acc_fib : forall fuel n acc,
  (forall z, In z acc -> exists k, z = fib k) ->
  forall z, In z (zeckendorf_fuel fuel n acc) -> exists k, z = fib k.
Proof.
  induction fuel as [|fuel' IHfuel].
  - (* fuel = 0 *)
    intros n acc Hacc_fib z Hz. simpl in Hz. apply Hacc_fib. exact Hz.
  - (* fuel = S fuel' *)
    intros n acc Hacc_fib z Hz.
    destruct n as [|n'].
    + (* n = 0 *) simpl in Hz. apply Hacc_fib. exact Hz.
    + (* n = S n' *)
      unfold zeckendorf_fuel in Hz. fold zeckendorf_fuel in Hz.
      destruct (rev (fibs_upto (S n'))) as [|x xs] eqn:Heqfibs.
      * (* fibs = [] *)
        apply Hacc_fib. exact Hz.
      * (* fibs = x :: xs *)
        destruct (Nat.leb x (S n')) eqn:Hleb.
        -- (* x <= S n' *)
           apply IHfuel in Hz.
           ++ exact Hz.
           ++ (* Prove: forall z, In z (x :: acc) -> exists k, z = fib k *)
              intros w Hin_w. simpl in Hin_w.
              destruct Hin_w as [Heq | Hin_acc].
              ** (* w = x *)
                 subst w.
                 (* x is in fibs_upto (S n') *)
                 assert (Hin_x: In x (fibs_upto (S n'))).
                 { apply in_list_rev. rewrite Heqfibs. left. reflexivity. }
                 destruct (in_fibs_upto_fib x (S n') Hin_x) as [k [_ Heq_fib]].
                 exists k. symmetry. exact Heq_fib.
              ** (* w in acc *)
                 apply Hacc_fib. exact Hin_acc.
        -- (* x > S n' (impossible case) *)
           (* x is in fibs_upto (S n'), so x <= S n', but Hleb says x > S n' *)
           exfalso.
           assert (Hin_x: In x (fibs_upto (S n'))).
           { apply in_list_rev. rewrite Heqfibs. left. reflexivity. }
           assert (Hx_le: x <= S n') by (apply in_fibs_upto_le; assumption).
           apply Nat.leb_gt in Hleb. lia.
Qed.

(* Main strengthened lemmas *)
Lemma zeckendorf_acc_fib : forall n acc,
  (forall z, In z acc -> exists k, z = fib k) ->
  forall z, In z (zeckendorf n acc) -> exists k, z = fib k.
Proof.
  intros n acc Hacc_fib z Hz.
  unfold zeckendorf in Hz.
  apply (zeckendorf_fuel_acc_fib n n acc Hacc_fib z Hz).
Qed.

Lemma zeckendorf_fuel_acc_sum : forall fuel n acc,
  fuel >= n ->
  sum_list (zeckendorf_fuel fuel n acc) = sum_list acc + n.
Proof.
  induction fuel as [|fuel' IHfuel].
  - (* fuel = 0 *)
    intros n acc Hge.
    assert (Heq: n = 0) by lia. subst n.
    simpl. lia.
  - (* fuel = S fuel' *)
    intros n acc Hge.
    destruct n as [|n'].
    + (* n = 0 *) simpl. lia.
    + (* n = S n' *)
      unfold zeckendorf_fuel. fold zeckendorf_fuel.
      destruct (rev (fibs_upto (S n'))) as [|x xs] eqn:Heqfibs.
      * (* fibs = [] *)
        (* This case is impossible: fibs_upto (S n') always contains fib(1)=1 *)
        exfalso.
        assert (H1: In 1 (fibs_upto (S n'))).
        { unfold fibs_upto. simpl.
          destruct n'; simpl; auto.
        }
        assert (H2: In 1 (rev (fibs_upto (S n')))) by (rewrite <- in_rev; exact H1).
        rewrite Heqfibs in H2. inversion H2.
      * (* fibs = x :: xs *)
        destruct (Nat.leb x (S n')) eqn:Hleb.
        -- (* x <= S n' *)
           assert (Hle: x <= S n') by (apply Nat.leb_le; assumption).
           assert (Hin_x: In x (fibs_upto (S n'))).
           { assert (Hin_rev: In x (rev (fibs_upto (S n')))).
             { rewrite Heqfibs. left. reflexivity. }
             apply in_rev in Hin_rev. exact Hin_rev.
           }
           assert (Hpos: x > 0) by (apply (in_fibs_upto_pos x (S n') Hin_x)).
           assert (Hfuel_ge: fuel' >= S n' - x).
           { destruct (Nat.eq_dec x (S n')) as [Heq_x | Hneq_x].
             - (* x = S n' *) subst x. rewrite Nat.sub_diag. lia.
             - (* x < S n' *) assert (Hsub: S n' - x < S n') by (apply Nat.sub_lt; lia). lia.
           }
           assert (Heq_sum: sum_list (zeckendorf_fuel fuel' (S n' - x) (x :: acc)) =
                           sum_list (x :: acc) + (S n' - x)).
           { apply IHfuel. exact Hfuel_ge. }
           rewrite Heq_sum.
           (* Goal: sum_list (x :: acc) + (S n' - x) = sum_list acc + S n' *)
           unfold sum_list at 1. fold sum_list.
           (* Goal: (x + sum_list acc) + (S n' - x) = sum_list acc + S n' *)
           rewrite <- Nat.add_assoc.
           (* Goal: x + (sum_list acc + (S n' - x)) = sum_list acc + S n' *)
           rewrite (Nat.add_comm (sum_list acc) (S n' - x)).
           (* Goal: x + ((S n' - x) + sum_list acc) = sum_list acc + S n' *)
           rewrite Nat.add_assoc.
           (* Goal: (x + (S n' - x)) + sum_list acc = sum_list acc + S n' *)
           rewrite (Nat.add_comm x (S n' - x)).
           (* Goal: ((S n' - x) + x) + sum_list acc = sum_list acc + S n' *)
           rewrite Nat.sub_add by exact Hle.
           (* Goal: S n' + sum_list acc = sum_list acc + S n' *)
           apply Nat.add_comm.
        -- (* x > S n' (impossible case) *)
           (* x is in fibs_upto (S n'), so x <= S n', but Hleb says x > S n' *)
           exfalso.
           assert (Hin_x: In x (fibs_upto (S n'))).
           { assert (Hin_rev: In x (rev (fibs_upto (S n')))).
             { rewrite Heqfibs. left. reflexivity. }
             apply in_rev in Hin_rev. exact Hin_rev.
           }
           assert (Hx_le: x <= S n') by (apply in_fibs_upto_le; assumption).
           apply Nat.leb_gt in Hleb. lia.
Qed.

Lemma zeckendorf_acc_sum : forall n acc,
  sum_list (zeckendorf n acc) = sum_list acc + n.
Proof.
  intros n acc.
  unfold zeckendorf.
  apply zeckendorf_fuel_acc_sum. lia.
Qed.

Lemma zeckendorf_acc_correct : forall n acc,
  (forall z, In z acc -> exists k, z = fib k) ->
  let zs := zeckendorf n acc in
  (forall z, In z zs -> exists k, z = fib k) /\
  sum_list zs = sum_list acc + n.
Proof.
  intros. split.
  - apply zeckendorf_acc_fib. assumption.
  - apply zeckendorf_acc_sum.
Qed.

(* The main zeckendorf correctness theorem *)
Theorem zeckendorf_fib_property : forall n,
  let zs := zeckendorf n [] in
  forall z, In z zs -> exists k, z = fib k.
Proof.
  intros n zs z Hz.
  unfold zs in Hz.
  apply (zeckendorf_acc_fib n [] (fun z H => match H with end) z Hz).
Qed.

Theorem zeckendorf_sum_property : forall n,
  sum_list (zeckendorf n []) = n.
Proof.
  intro n.
  assert (H: sum_list (zeckendorf n []) = sum_list [] + n).
  { apply zeckendorf_acc_sum. }
  simpl in H. exact H.
Qed.

(* Full correctness theorem *)
Theorem zeckendorf_correct : forall n,
  let zs := zeckendorf n [] in
  (forall z, In z zs -> exists k, z = fib k) /\
  sum_list zs = n.
Proof.
  intro n.
  split.
  - apply zeckendorf_fib_property.
  - apply zeckendorf_sum_property.
Qed.
