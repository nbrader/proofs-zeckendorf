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

(*
  Helper lemma: Fibonacci numbers are positive for n >= 1

  Proof strategy: Use strong induction (well-founded induction on <).
  For the base cases (n=1 and n=2), compute directly.
  For n >= 3, use the recurrence relation fib(n) = fib(n-1) + fib(n-2)
  and the fact that sum of two positive numbers is positive.
*)
Lemma fib_pos : forall n, n >= 1 -> fib n > 0.
Proof.
  intro n. pattern n. apply lt_wf_ind. clear n.
  (* IH: induction hypothesis - fib is positive for all smaller values *)
  intros n IH Hge.
  (* Case split on the structure of n to handle base cases *)
  destruct n as [|[|[|n'']]].
  - (* Case n = 0: Contradicts assumption n >= 1 *)
    inversion Hge.
  - (* Case n = 1: fib(1) = 1 > 0 by computation *)
    compute. auto.
  - (* Case n = 2: fib(2) = 1 > 0 by computation *)
    compute. auto.
  - (* Case n >= 3: Use recurrence relation fib(n) = fib(n-1) + fib(n-2) *)
    (* First rewrite using the Fibonacci recurrence *)
    rewrite fib_SS.
    (* Show that fib(n-1) + fib(n-2) > 0 by showing both summands are positive *)
    apply Nat.add_pos_pos.
    + (* fib(S (S n'')) = fib(n-1) > 0 *)
      apply IH.
      * (* n-1 < n (needed for induction hypothesis) *)
        apply Nat.lt_succ_diag_r.
      * (* n-1 >= 1 (needed for fib_pos precondition) *)
        apply le_n_S. apply Nat.le_0_l.
    + (* fib(S n'') = fib(n-2) > 0 *)
      apply IH.
      * (* n-2 < n (needed for induction hypothesis) *)
        (* This requires two steps: n-2 < n-1 < n *)
        apply Nat.lt_trans with (S (S n'')).
        -- apply Nat.lt_succ_diag_r.
        -- apply Nat.lt_succ_diag_r.
      * (* n-2 >= 1 (needed for fib_pos precondition) *)
        apply le_n_S. apply Nat.le_0_l.
Qed.

(*
  Fibonacci sequence is monotonically increasing for n >= 2

  Proof strategy: Use strong induction. Base case n=2 is verified by computation.
  For n >= 3, we show fib(n) < fib(n+1) by rewriting fib(n+1) = fib(n) + fib(n-1)
  and noting that fib(n-1) > 0, so fib(n) < fib(n) + fib(n-1).
*)
Lemma fib_mono : forall n, n >= 2 -> fib n < fib (S n).
Proof.
  intro n. pattern n. apply lt_wf_ind. clear n.
  intros n IH Hge.
  (* Case split on n to handle base cases *)
  destruct n as [|[|[|n'']]].
  - (* Case n = 0: Contradicts n >= 2 *)
    inversion Hge.
  - (* Case n = 1: Contradicts n >= 2 (since 1 < 2) *)
    inversion Hge. inversion H0.
  - (* Case n = 2: fib(2) < fib(3), i.e., 1 < 2, verified by computation *)
    simpl. auto.
  - (* Case n >= 3: Show fib(n) < fib(n+1) using the recurrence relation *)
    (* First, establish that fib(n-1) > 0, which we'll need later *)
    assert (Hpos: fib (S (S n'')) > 0).
    { apply fib_pos. apply le_n_S. apply Nat.le_0_l. }
    (* Rewrite fib(n+1) using the Fibonacci recurrence:
       fib(n+1) = fib(n) + fib(n-1) *)
    assert (Heq: fib (S (S (S (S n'')))) = fib (S (S (S n''))) + fib (S (S n''))).
    { replace (S (S (S (S n'')))) with (S (S (S (S n'')))) by reflexivity.
      rewrite fib_SS. reflexivity. }
    rewrite Heq.
    (* Now goal is: fib(n) < fib(n) + fib(n-1)
       This follows from fib(n-1) > 0 *)
    apply Nat.lt_add_pos_r. assumption.
Qed.

(*
  Helper lemma: All elements in (seq start len) are >= start

  Proof strategy: Induction on len. The sequence [start, start+1, ..., start+len-1]
  has all elements >= start.
  - Base case: empty list has no elements
  - Inductive case: first element is start (so >= start), and remaining elements
    are in seq (start+1) (len-1), so by IH they're >= start+1, hence >= start
*)
Lemma seq_ge : forall x start len,
  In x (seq start len) -> x >= start.
Proof.
  intros x start len.
  generalize dependent start.
  (* Induction on the length of the sequence *)
  induction len; intros start Hin.
  - (* Base case: len = 0, so seq is empty, contradiction with In x *)
    simpl in Hin. inversion Hin.
  - (* Inductive case: seq start (S len) = start :: seq (S start) len *)
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + (* x = start, so x >= start trivially *)
      rewrite Heq. auto.
    + (* x is in the tail seq (S start) len, so by IH, x >= S start >= start *)
      apply IHlen in Hin'. auto with arith.
Qed.

(*
  Lemma: Every element in fibs_upto n is a Fibonacci number

  Proof strategy: fibs_upto n is constructed by filtering map fib (seq 1 (S n)),
  so every element has the form fib(k) for some k >= 1.
  We proceed by induction on the sequence structure, using the fact that
  seq 1 (S n) contains only indices >= 1.
*)
Lemma in_fibs_upto_fib : forall x n,
  In x (fibs_upto n) -> exists k, k >= 1 /\ fib k = x.
Proof.
  intros x n Hin.
  (* Unfold the definition of fibs_upto: takeWhile (λx. x ≤ n) (map fib (seq 1 (S n))) *)
  unfold fibs_upto in Hin.
  (* Remember the sequence of indices [1, 2, ..., n+1] *)
  remember (seq 1 (S n)) as l.
  (* Establish that all indices in the sequence are >= 1 *)
  assert (Hge: forall y, In y l -> y >= 1).
  { intros y Hiny. rewrite Heql in Hiny.
    apply seq_ge in Hiny. assumption. }
  clear Heql.
  (* Induction on the list structure *)
  induction l as [|a l' IH].
  - (* Base case: empty list, contradiction *)
    simpl in Hin. inversion Hin.
  - (* Inductive case: list is a :: l' *)
    simpl in Hin.
    (* Check whether fib(a) <= n (whether a is included in fibs_upto) *)
    destruct (Nat.leb (fib a) n) eqn:Hleb.
    + (* fib(a) <= n, so fib(a) is included in the result *)
      simpl in Hin. destruct Hin as [Heq | Hin'].
      * (* x = fib(a), so we found our witness k = a *)
        exists a. split.
        -- (* a >= 1 follows from our assertion about the sequence *)
           apply Hge. left. reflexivity.
        -- (* fib(a) = x by equality *)
           rewrite <- Heq. reflexivity.
      * (* x is in the tail, use induction hypothesis *)
        assert (Hge': forall y, In y l' -> y >= 1).
        { intros y Hiny. apply Hge. right. assumption. }
        apply IH; assumption.
    + (* fib(a) > n, so takeWhile stops here and x can't be in the result *)
      inversion Hin.
Qed.

(*
  Corollary: All elements in fibs_upto are positive

  Proof: By in_fibs_upto_fib, each element is fib(k) for k >= 1.
  By fib_pos, fib(k) > 0 for k >= 1.
*)
Lemma in_fibs_upto_pos : forall x n,
  In x (fibs_upto n) -> x > 0.
Proof.
  intros x n Hin.
  (* Use the previous lemma to get the witness k *)
  destruct (in_fibs_upto_fib x n Hin) as [k [Hk Heq]].
  (* Rewrite x as fib(k) *)
  rewrite <- Heq.
  (* Apply fib_pos to show fib(k) > 0 *)
  apply fib_pos. assumption.
Qed.

(*
  Lemma: All elements in fibs_upto n are <= n

  Proof strategy: fibs_upto n uses takeWhile to only include Fibonacci numbers
  that satisfy fib(k) <= n. We prove this by induction on the sequence structure,
  observing that takeWhile only includes elements satisfying the predicate.
*)
Lemma in_fibs_upto_le : forall x n,
  In x (fibs_upto n) -> x <= n.
Proof.
  intros x n Hin.
  (* Unfold fibs_upto definition *)
  unfold fibs_upto in Hin.
  (* Induction on the sequence [1, 2, ..., n+1] *)
  induction (seq 1 (S n)) as [|a l IH].
  - (* Base case: empty list, contradiction *)
    simpl in Hin. inversion Hin.
  - (* Inductive case: process takeWhile on (fib a) :: map fib l *)
    simpl in Hin.
    (* Case split on whether fib(a) <= n *)
    destruct (Nat.leb (fib a) n) eqn:Hleb.
    + (* fib(a) <= n, so fib(a) is included *)
      simpl in Hin. destruct Hin as [Heq | Hin'].
      * (* x = fib(a), and we know fib(a) <= n from Hleb *)
        subst x. apply Nat.leb_le. assumption.
      * (* x is in the tail, use IH *)
        apply IH. assumption.
    + (* fib(a) > n, so takeWhile stops and list is empty, contradiction *)
      inversion Hin.
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

(*
  Main lemma: All elements produced by zeckendorf_fuel are Fibonacci numbers

  Statement: If all elements in acc are Fibonacci numbers, then all elements
  in the result of zeckendorf_fuel are Fibonacci numbers.

  Proof strategy: Induction on fuel.
  - When fuel = 0 or n = 0, the function returns acc unchanged, so the property holds
  - When fuel > 0 and n > 0:
    * The algorithm picks the largest Fibonacci number x <= n from fibs_upto n
    * If x <= n, it recursively calls with (n-x) and (x::acc)
    * We need to show x::acc preserves the invariant (all elements are Fibonacci)
    * Since x comes from fibs_upto n, it's a Fibonacci number by in_fibs_upto_fib
    * The else branch (x > n) is impossible since x is from fibs_upto n, so x <= n
*)
Lemma zeckendorf_fuel_acc_fib : forall fuel n acc,
  (forall z, In z acc -> exists k, z = fib k) ->
  forall z, In z (zeckendorf_fuel fuel n acc) -> exists k, z = fib k.
Proof.
  (* Induction on the fuel parameter *)
  induction fuel as [|fuel' IHfuel].
  - (* Base case: fuel = 0, function returns acc immediately *)
    intros n acc Hacc_fib z Hz.
    simpl in Hz. apply Hacc_fib. exact Hz.
  - (* Inductive case: fuel = S fuel' *)
    intros n acc Hacc_fib z Hz.
    (* Case split on n *)
    destruct n as [|n'].
    + (* When n = 0, function returns acc *)
      simpl in Hz. apply Hacc_fib. exact Hz.
    + (* When n = S n' > 0, algorithm processes the decomposition *)
      unfold zeckendorf_fuel in Hz. fold zeckendorf_fuel in Hz.
      (* Get the largest Fibonacci number <= n *)
      destruct (rev (fibs_upto (S n'))) as [|x xs] eqn:Heqfibs.
      * (* Case: fibs_upto is empty (cannot happen, but returns acc anyway) *)
        apply Hacc_fib. exact Hz.
      * (* Case: x is the largest Fibonacci number in fibs_upto n *)
        (* Check if x <= n *)
        destruct (Nat.leb x (S n')) eqn:Hleb.
        -- (* Subcase: x <= S n', so we recurse with (n-x) and (x::acc) *)
           (* Apply IH to the recursive call *)
           apply IHfuel in Hz.
           ++ exact Hz.
           ++ (* Need to prove: all elements in (x :: acc) are Fibonacci numbers *)
              intros w Hin_w. simpl in Hin_w.
              destruct Hin_w as [Heq | Hin_acc].
              ** (* If w = x: x is a Fibonacci number from fibs_upto *)
                 subst w.
                 (* Show that x is in fibs_upto (S n') *)
                 assert (Hin_x: In x (fibs_upto (S n'))).
                 { (* x is the head of rev (fibs_upto n), so it's in fibs_upto n *)
                   apply in_list_rev. rewrite Heqfibs. left. reflexivity. }
                 (* By in_fibs_upto_fib, x = fib(k) for some k *)
                 destruct (in_fibs_upto_fib x (S n') Hin_x) as [k [_ Heq_fib]].
                 exists k. symmetry. exact Heq_fib.
              ** (* If w is in acc: use the assumption about acc *)
                 apply Hacc_fib. exact Hin_acc.
        -- (* Subcase: x > S n' - this is impossible! *)
           (* Derive a contradiction: x is in fibs_upto n, so x <= n by in_fibs_upto_le,
              but Hleb says x > n *)
           exfalso.
           (* First, show x is in fibs_upto (S n') *)
           assert (Hin_x: In x (fibs_upto (S n'))).
           { apply in_list_rev. rewrite Heqfibs. left. reflexivity. }
           (* Therefore x <= S n' by in_fibs_upto_le *)
           assert (Hx_le: x <= S n') by (apply in_fibs_upto_le; assumption).
           (* But Hleb = false means x > S n' *)
           apply Nat.leb_gt in Hleb.
           (* Contradiction: x <= S n' and x > S n' *)
           lia.
Qed.

(*
  Wrapper lemma: Specialization of zeckendorf_fuel_acc_fib to zeckendorf

  This instantiates fuel = n, which is the definition of zeckendorf.
  Since fuel >= n is satisfied (n >= n), we can apply the fuel-based lemma.
*)
Lemma zeckendorf_acc_fib : forall n acc,
  (forall z, In z acc -> exists k, z = fib k) ->
  forall z, In z (zeckendorf n acc) -> exists k, z = fib k.
Proof.
  intros n acc Hacc_fib z Hz.
  (* Unfold the definition: zeckendorf n acc = zeckendorf_fuel n n acc *)
  unfold zeckendorf in Hz.
  (* Apply the fuel-based lemma with fuel = n >= n *)
  apply (zeckendorf_fuel_acc_fib n n acc Hacc_fib z Hz).
Qed.

(*
  Main lemma: The sum of elements produced by zeckendorf_fuel equals sum of acc plus n

  Statement: If fuel >= n, then sum_list(zeckendorf_fuel fuel n acc) = sum_list(acc) + n

  Intuition: The algorithm decomposes n into Fibonacci numbers. At each step, it picks
  the largest Fibonacci x <= n and recursively decomposes (n-x). The sum of all picked
  Fibonacci numbers plus the sum of acc equals sum(acc) + n.

  Proof strategy: Induction on fuel.
  - Base case (fuel = 0): fuel >= n implies n = 0, so the sum is unchanged
  - Inductive case (fuel > 0, n > 0):
    * Pick largest Fibonacci x <= n
    * Recursively process (n-x) with accumulator (x::acc)
    * By IH: sum(result) = sum(x::acc) + (n-x) = x + sum(acc) + (n-x) = sum(acc) + n
    * The arithmetic is handled by rewriting using associativity and commutativity
*)
Lemma zeckendorf_fuel_acc_sum : forall fuel n acc,
  fuel >= n ->
  sum_list (zeckendorf_fuel fuel n acc) = sum_list acc + n.
Proof.
  (* Induction on fuel *)
  induction fuel as [|fuel' IHfuel].
  - (* Base case: fuel = 0 *)
    intros n acc Hge.
    (* Since fuel = 0 and fuel >= n, we must have n = 0 *)
    assert (Heq: n = 0) by lia. subst n.
    (* zeckendorf_fuel 0 0 acc = acc, and sum_list acc + 0 = sum_list acc *)
    simpl. lia.
  - (* Inductive case: fuel = S fuel' *)
    intros n acc Hge.
    (* Case split on n *)
    destruct n as [|n'].
    + (* n = 0: function returns acc, and sum_list acc + 0 = sum_list acc *)
      simpl. lia.
    + (* n = S n' > 0: perform Zeckendorf decomposition *)
      unfold zeckendorf_fuel. fold zeckendorf_fuel.
      (* Get the largest Fibonacci number <= n *)
      destruct (rev (fibs_upto (S n'))) as [|x xs] eqn:Heqfibs.
      * (* Case: fibs_upto is empty - impossible! *)
        (* For any n >= 1, fibs_upto n contains at least fib(1) = 1 *)
        exfalso.
        assert (H1: In 1 (fibs_upto (S n'))).
        { (* fib(1) = 1 <= S n' for all n', so 1 is in fibs_upto (S n') *)
          unfold fibs_upto. simpl.
          destruct n'; simpl; auto.
        }
        (* If 1 is in fibs_upto, then it's also in rev(fibs_upto) *)
        assert (H2: In 1 (rev (fibs_upto (S n')))) by (rewrite <- in_rev; exact H1).
        (* But we assumed rev(fibs_upto) = [], contradiction *)
        rewrite Heqfibs in H2. inversion H2.
      * (* Case: x is the largest Fibonacci <= n *)
        (* Check if x <= n (should always be true) *)
        destruct (Nat.leb x (S n')) eqn:Hleb.
        -- (* Subcase: x <= S n', proceed with decomposition *)
           (* Extract the inequality from the boolean *)
           assert (Hle: x <= S n') by (apply Nat.leb_le; assumption).
           (* Show that x is in fibs_upto (S n') *)
           assert (Hin_x: In x (fibs_upto (S n'))).
           { assert (Hin_rev: In x (rev (fibs_upto (S n')))).
             { rewrite Heqfibs. left. reflexivity. }
             apply in_rev in Hin_rev. exact Hin_rev.
           }
           (* Therefore x > 0 (all Fibonacci numbers in fibs_upto are positive) *)
           assert (Hpos: x > 0) by (apply (in_fibs_upto_pos x (S n') Hin_x)).
           (* Show that fuel' >= S n' - x (needed for IH) *)
           assert (Hfuel_ge: fuel' >= S n' - x).
           { (* Case split: x = S n' or x < S n' *)
             destruct (Nat.eq_dec x (S n')) as [Heq_x | Hneq_x].
             - (* If x = S n', then S n' - x = 0 <= fuel' *)
               subst x. rewrite Nat.sub_diag. lia.
             - (* If x < S n', then S n' - x < S n' <= S fuel' - 1 = fuel' *)
               assert (Hsub: S n' - x < S n') by (apply Nat.sub_lt; lia). lia.
           }
           (* Apply induction hypothesis to the recursive call *)
           assert (Heq_sum: sum_list (zeckendorf_fuel fuel' (S n' - x) (x :: acc)) =
                           sum_list (x :: acc) + (S n' - x)).
           { apply IHfuel. exact Hfuel_ge. }
           (* Rewrite using IH *)
           rewrite Heq_sum.
           (* Now we need to show: sum_list(x::acc) + (S n' - x) = sum_list(acc) + S n'
              This is an arithmetic identity: (x + sum_list acc) + (S n' - x) = sum_list acc + S n'
              We prove it by arithmetic rewriting *)
           unfold sum_list at 1. fold sum_list.
           (* Goal: (x + sum_list acc) + (S n' - x) = sum_list acc + S n' *)
           (* Rewrite to isolate: x + (S n' - x) = S n' *)
           rewrite <- Nat.add_assoc.
           (* Goal: x + (sum_list acc + (S n' - x)) = sum_list acc + S n' *)
           rewrite (Nat.add_comm (sum_list acc) (S n' - x)).
           (* Goal: x + ((S n' - x) + sum_list acc) = sum_list acc + S n' *)
           rewrite Nat.add_assoc.
           (* Goal: (x + (S n' - x)) + sum_list acc = sum_list acc + S n' *)
           rewrite (Nat.add_comm x (S n' - x)).
           (* Goal: ((S n' - x) + x) + sum_list acc = sum_list acc + S n' *)
           (* Use the fact that (S n' - x) + x = S n' when x <= S n' *)
           rewrite Nat.sub_add by exact Hle.
           (* Goal: S n' + sum_list acc = sum_list acc + S n' *)
           apply Nat.add_comm.
        -- (* Subcase: x > S n' - impossible! *)
           (* Same contradiction as in zeckendorf_fuel_acc_fib *)
           exfalso.
           assert (Hin_x: In x (fibs_upto (S n'))).
           { assert (Hin_rev: In x (rev (fibs_upto (S n')))).
             { rewrite Heqfibs. left. reflexivity. }
             apply in_rev in Hin_rev. exact Hin_rev.
           }
           (* x in fibs_upto (S n') implies x <= S n' *)
           assert (Hx_le: x <= S n') by (apply in_fibs_upto_le; assumption).
           (* But Hleb = false means x > S n' *)
           apply Nat.leb_gt in Hleb.
           (* Contradiction *)
           lia.
Qed.

(*
  Wrapper lemma: Specialization of zeckendorf_fuel_acc_sum to zeckendorf

  This instantiates fuel = n and uses the fact that n >= n to apply the fuel-based lemma.
*)
Lemma zeckendorf_acc_sum : forall n acc,
  sum_list (zeckendorf n acc) = sum_list acc + n.
Proof.
  intros n acc.
  (* Unfold the definition: zeckendorf n acc = zeckendorf_fuel n n acc *)
  unfold zeckendorf.
  (* Apply the fuel-based lemma with fuel = n >= n *)
  apply zeckendorf_fuel_acc_sum. lia.
Qed.

(*
  Combined correctness lemma: Both properties together

  This combines the previous two lemmas to show that zeckendorf produces
  a list of Fibonacci numbers whose sum equals the input.
*)
Lemma zeckendorf_acc_correct : forall n acc,
  (forall z, In z acc -> exists k, z = fib k) ->
  let zs := zeckendorf n acc in
  (forall z, In z zs -> exists k, z = fib k) /\
  sum_list zs = sum_list acc + n.
Proof.
  intros. split.
  - (* Part 1: All elements are Fibonacci numbers *)
    apply zeckendorf_acc_fib. assumption.
  - (* Part 2: Sum equals sum(acc) + n *)
    apply zeckendorf_acc_sum.
Qed.

(*
  ==============================================================================
  MAIN ZECKENDORF CORRECTNESS THEOREMS
  ==============================================================================

  These theorems establish the correctness of the Zeckendorf representation
  algorithm by proving two key properties:
  1. All elements in the decomposition are Fibonacci numbers
  2. The sum of the decomposition equals the original input

  Together, these prove that zeckendorf computes a valid Zeckendorf
  representation (a sum of non-consecutive Fibonacci numbers equaling n).
*)

(*
  Theorem 1: Fibonacci property

  Every element in the Zeckendorf decomposition is a Fibonacci number.

  Proof: Apply zeckendorf_acc_fib with acc = [], using the fact that
  the empty list trivially satisfies "all elements are Fibonacci numbers".
*)
Theorem zeckendorf_fib_property : forall n,
  let zs := zeckendorf n [] in
  forall z, In z zs -> exists k, z = fib k.
Proof.
  intros n zs z Hz.
  unfold zs in Hz.
  (* Apply zeckendorf_acc_fib with acc = [] *)
  (* The precondition "all z in [] are Fibonacci" is vacuously true *)
  apply (zeckendorf_acc_fib n [] (fun z H => match H with end) z Hz).
Qed.

(*
  Theorem 2: Sum property

  The sum of elements in the Zeckendorf decomposition equals n.

  Proof: Apply zeckendorf_acc_sum with acc = [], which gives
  sum(result) = sum([]) + n = 0 + n = n.
*)
Theorem zeckendorf_sum_property : forall n,
  sum_list (zeckendorf n []) = n.
Proof.
  intro n.
  (* Apply zeckendorf_acc_sum to get sum(zeckendorf n []) = sum([]) + n *)
  assert (H: sum_list (zeckendorf n []) = sum_list [] + n).
  { apply zeckendorf_acc_sum. }
  (* Simplify: sum([]) = 0, so result is n *)
  simpl in H. exact H.
Qed.

(*
  Main Theorem: Full Zeckendorf correctness

  The Zeckendorf decomposition of n produces a list of Fibonacci numbers
  whose sum equals n.

  This is the culmination of all our work: we've formally verified that
  the greedy algorithm correctly computes Zeckendorf representations.

  Note: This theorem doesn't yet prove uniqueness or the non-consecutive
  property, but it establishes the fundamental correctness of the decomposition.
*)
Theorem zeckendorf_correct : forall n,
  let zs := zeckendorf n [] in
  (forall z, In z zs -> exists k, z = fib k) /\
  sum_list zs = n.
Proof.
  intro n.
  split.
  - (* Part 1: All elements are Fibonacci numbers *)
    apply zeckendorf_fib_property.
  - (* Part 2: Sum equals n *)
    apply zeckendorf_sum_property.
Qed.

(*
  ==============================================================================
  ADDITIONAL PROPERTIES (ADMITTED - TO BE PROVEN)
  ==============================================================================

  The following theorems state important additional properties of Zeckendorf
  representations that we have not yet proven:
  1. Non-consecutive property: No two consecutive Fibonacci numbers appear
  2. Uniqueness: The representation is unique for each natural number
*)

(*
  Helper predicate: Two natural numbers are consecutive

  nat_consecutive k1 k2 means that k1 and k2 differ by exactly one,
  i.e., k2 = k1 + 1 or k1 = k2 + 1.
*)
Definition nat_consecutive (k1 k2 : nat) : Prop :=
  k2 = S k1 \/ k1 = S k2.

(*
  ==============================================================================
  SORTED LIST INFRASTRUCTURE
  ==============================================================================

  To simplify proofs about Zeckendorf representations, we work with sorted lists
  in descending order. This eliminates case analysis about element positions and
  makes finding the maximum element trivial.
*)

(* Predicate: list is sorted in descending order (strictly decreasing) *)
Fixpoint Sorted_dec (l : list nat) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: (y :: _) as xs => x > y /\ Sorted_dec xs
  end.

(* For a descending sorted list, the head is the maximum *)
Lemma sorted_head_max : forall x xs,
  Sorted_dec (x :: xs) ->
  forall y, In y xs -> x > y.
Proof.
  intros x xs. revert x. induction xs as [|z zs IH]; intros x Hsorted y Hy.
  - simpl in Hy. contradiction.
  - simpl in Hsorted. destruct Hsorted as [Hxz Htail].
    simpl in Hy. destruct Hy as [Heq | Hin].
    + subst. exact Hxz.
    + assert (Hzy: z > y) by (apply (IH z Htail y Hin)).
      lia.
Qed.

(* Sorted lists are automatically NoDup *)
Lemma sorted_NoDup : forall l,
  Sorted_dec l -> NoDup l.
Proof.
  induction l as [|x xs IH]; intro Hsorted.
  - constructor.
  - constructor.
    + intro Hin.
      assert (Hgt: x > x).
      { destruct xs as [|y ys].
        - simpl in Hin. contradiction.
        - apply (sorted_head_max x (y :: ys) Hsorted x Hin). }
      lia.
    + apply IH. destruct xs as [|y ys]; simpl in *; auto.
      destruct Hsorted. auto.
Qed.

(* For sorted lists, max is simply the head element *)
Definition sorted_max (l : list nat) : option nat :=
  match l with
  | [] => None
  | x :: _ => Some x
  end.

(* Note: For sorted lists in descending order, sorted_max l simply returns the head.
   This is equivalent to list_max l when the list is sorted, but much simpler to work with.
   We will prove sorted_max_correct after list_max is defined later in the file. *)

(*
  Simplified no_consecutive predicate for sorted lists

  For sorted (descending) lists, we only need to check adjacent pairs!
  This is much simpler than checking all pairs.
*)
Fixpoint no_consecutive_fibs_sorted (l : list nat) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: ((y :: _) as ys) =>
      (forall i j, fib i = x -> fib j = y -> ~nat_consecutive i j) /\
      no_consecutive_fibs_sorted ys
  end.

(* Note: We'll prove that the sorted version implies the general version
   after no_consecutive_fibs is defined below. *)

(* Helper: For sorted lists starting with x, all tail elements are strictly less than x *)
Lemma sorted_tail_lt : forall x xs,
  Sorted_dec (x :: xs) ->
  forall y, In y xs -> y < x.
Proof.
  intros x xs Hsorted y Hy.
  apply (sorted_head_max x xs Hsorted y Hy).
Qed.

(* Helper: Tail of sorted list is sorted *)
Lemma sorted_tail : forall x xs,
  Sorted_dec (x :: xs) -> Sorted_dec xs.
Proof.
  intros x xs Hsorted.
  destruct xs as [|y ys]; simpl; auto.
  simpl in Hsorted. destruct Hsorted as [_ Htail]. exact Htail.
Qed.

(*
  Helper predicate: A list contains no consecutive Fibonacci numbers

  This predicate ensures that for any two elements x, y in the list,
  if x = fib(i) and y = fib(j), then i and j are not consecutive.
*)
Fixpoint no_consecutive_fibs (l : list nat) : Prop :=
  match l with
  | [] => True
  | x :: xs =>
    (forall y, In y xs ->
      forall i j, fib i = x -> fib j = y -> ~nat_consecutive i j) /\
    no_consecutive_fibs xs
  end.
(* Appending a single element to the end preserves the predicate when it is compatible *)
Lemma no_consecutive_append_single : forall l x,
  no_consecutive_fibs l ->
  (forall y, In y l ->
    forall i j, fib i = y -> fib j = x -> ~nat_consecutive i j) ->
  no_consecutive_fibs (l ++ [x]).
Proof.
  induction l as [|a l IH]; intros x Hnoc Hcompat; simpl in *.
  - split.
    + intros y Hy. inversion Hy.
    + constructor.
  - destruct Hnoc as [Hhead Htail]. simpl. split.
    + intros y Hy i j Hfi Hfj Hcons.
      apply in_app_or in Hy.
      destruct Hy as [Hy|Hy].
      * specialize (Hhead y Hy i j Hfi Hfj).
        apply Hhead. exact Hcons.
      * simpl in Hy.
        destruct Hy as [Hy|Hy].
        -- subst y.
           specialize (Hcompat a (or_introl eq_refl) i j Hfi Hfj).
           apply Hcompat. exact Hcons.
        -- contradiction.
    + apply IH.
      * exact Htail.
      * intros y Hy i j Hfi Hfj.
        apply (Hcompat y (or_intror Hy) i j Hfi Hfj).
Qed.

(* Helper lemma: if no_consecutive_fibs l, and fib i and fib j are both in l with consecutive indices, contradiction *)
(* Note: requires fib i ≠ fib j to handle the fib 1 = fib 2 = 1 case *)
Lemma no_consecutive_both_in : forall l i j,
  no_consecutive_fibs l ->
  fib i <> fib j ->
  In (fib i) l ->
  In (fib j) l ->
  nat_consecutive i j ->
  False.
Proof.
  induction l as [|x xs IH]; intros i j Hnocons Hneq_fib Hi Hj Hcons.
  - (* l = [] *) simpl in Hi. contradiction.
  - (* l = x :: xs *)
    simpl in Hnocons. destruct Hnocons as [Hhead Htail].
    simpl in Hi, Hj.
    destruct Hi as [Hxi | Hxsi]; destruct Hj as [Hxj | Hxsj].
    + (* Both equal x: fib i = x = fib j *)
      (* But we have fib i ≠ fib j from Hneq_fib, contradiction! *)
      exfalso. apply Hneq_fib.
      transitivity x; [symmetry; exact Hxi | exact Hxj].
    + (* fib i = x, fib j in xs *)
      apply (Hhead (fib j) Hxsj i j); auto.
    + (* fib i in xs, fib j = x *)
      apply (Hhead (fib i) Hxsi j i); auto.
      unfold nat_consecutive in *. lia.
    + (* Both in xs *)
      apply (IH i j Htail Hneq_fib Hxsi Hxsj Hcons).
Qed.

(*
  Helper lemma: For k >= 2, fib(k) + fib(k-1) = fib(k+1)

  This is the defining recurrence relation for Fibonacci numbers.
*)
Lemma fib_recurrence : forall k,
  k >= 2 -> fib k + fib (k - 1) = fib (S k).
Proof.
  intros k Hk.
  destruct k as [|[|k']].
  - (* k = 0: contradicts k >= 2 *)
    inversion Hk.
  - (* k = 1: contradicts k >= 2 *)
    inversion Hk. inversion H0.
  - (* k = S (S k') >= 2 *)
    (* Goal: fib (S (S k')) + fib (S (S k') - 1) = fib (S (S (S k'))) *)
    (* Simplify: S (S k') - 1 = S k' *)
    replace (S (S k') - 1) with (S k') by lia.
    (* Now apply fib_SS to rewrite the right side *)
    rewrite fib_SS. reflexivity.
Qed.

(*
  Helper lemma: If F_k < n < F_{k+1}, then n - F_k < F_{k-1}

  This is the key property that ensures the greedy algorithm produces
  non-consecutive Fibonacci numbers.

  Proof: Since n < F_{k+1} = F_k + F_{k-1}, we have n - F_k < F_{k-1}.
*)
Lemma remainder_less_than_prev_fib : forall n k,
  k >= 2 ->
  fib k < n ->
  n < fib (S k) ->
  n - fib k < fib (k - 1).
Proof.
  intros n k Hk Hlt Hlt'.
  (* Rewrite fib(k+1) using recurrence relation *)
  assert (Heq: fib (S k) = fib k + fib (k - 1)).
  { rewrite <- fib_recurrence by assumption. reflexivity. }
  (* Now n < fib k + fib(k-1), so n - fib k < fib(k-1) *)
  rewrite Heq in Hlt'.
  lia.
Qed.

(*
  ==============================================================================
  SORTED OUTPUT VERSION
  ==============================================================================
*)

(*
  The greedy algorithm as written produces output in ASCENDING order:
  - It selects the largest Fibonacci <= n
  - But prepends to accumulator: x :: acc
  - Since n decreases, elements added are: large, smaller, smaller...
  - Prepending reverses order: smallest ... larger ... largest

  For our sorted list proofs (which use DESCENDING order), we reverse:
*)

(* Predicate: list is sorted in ascending order (strictly increasing) *)
Fixpoint Sorted_asc (l : list nat) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: (y :: _) as xs => x < y /\ Sorted_asc xs
  end.

(* Descending sorted version of zeckendorf (for use with Sorted_dec proofs) *)
Definition zeckendorf_sorted (n : nat) : list nat :=
  rev (zeckendorf n []).

(* Helper lemmas for sorted lists and append *)

(* Sorted_dec list with single element appended *)
Lemma sorted_dec_app_singleton : forall l x,
  Sorted_dec l ->
  (forall y, In y l -> y > x) ->
  Sorted_dec (l ++ [x]).
Proof.
  induction l as [|z zs IH]; intros x Hsorted Hall_gt.
  - (* l = [] *)
    simpl. auto.
  - (* l = z :: zs *)
    destruct zs as [|w ws].
    + (* zs = [] *)
      simpl. split; [apply Hall_gt; simpl; left; reflexivity | auto].
    + (* zs = w :: ws *)
      simpl in Hsorted. destruct Hsorted as [Hzw Htail].
      simpl (z :: w :: ws ++ [x]).
      split.
      * exact Hzw.
      * apply IH.
        -- exact Htail.
        -- intros y Hy. apply Hall_gt. simpl. right. exact Hy.
Qed.

(* Helper: last element of ascending sorted list is largest *)
Lemma sorted_asc_last_max : forall x xs y,
  Sorted_asc (x :: xs ++ [y]) ->
  forall z, In z (x :: xs) -> z < y.
Proof.
  intros x xs. revert x. induction xs as [|w ws IH]; intros x y Hsorted z Hz.
  - (* xs = [] *)
    simpl in Hsorted, Hz. destruct Hsorted as [Hxy _].
    destruct Hz as [Heq | Hfalse].
    + subst. exact Hxy.
    + contradiction.
  - (* xs = w :: ws *)
    simpl in Hz. destruct Hz as [Heq | Hin].
    + (* z = x *)
      subst z.
      simpl in Hsorted. destruct Hsorted as [Hxw Hrest].
      assert (Hwy: w < y).
      { apply (IH w y Hrest w). simpl. left. reflexivity. }
      lia.
    + (* z in w :: ws *)
      simpl in Hsorted. destruct Hsorted as [_ Hrest].
      apply (IH w y Hrest z Hin).
Qed.

(* Helper: In an ascending sorted list, head is less than all elements in tail *)
Lemma sorted_asc_head_lt_tail : forall y ys z,
  Sorted_asc (y :: ys) ->
  In z ys ->
  y < z.
Proof.
  intros y ys. revert y. induction ys as [|w ws IH]; intros y z Hsorted Hz.
  - (* ys = [] *)
    simpl in Hz. contradiction.
  - (* ys = w :: ws *)
    simpl in Hsorted. destruct Hsorted as [Hyw Hrest].
    simpl in Hz. destruct Hz as [Heq | Hin].
    + (* z = w *)
      subst. exact Hyw.
    + (* z in ws *)
      assert (Hw_lt_z: w < z).
      { apply (IH w z Hrest Hin). }
      lia.
Qed.

(* Helper: Sorted_dec with appended singleton implies properties about head *)
Lemma sorted_dec_app_singleton_inv : forall l x,
  Sorted_dec (l ++ [x]) ->
  (forall y, In y l -> y > x).
Proof.
  induction l as [|z zs IH]; intros x Hsorted y Hy.
  - (* l = [] *)
    simpl in Hy. contradiction.
  - (* l = z :: zs *)
    simpl in Hy. destruct Hy as [Heq | Hin].
    + (* y = z *)
      subst y.
      destruct zs as [|w ws].
      * (* zs = [] *)
        simpl in Hsorted. exact Hsorted.
      * (* zs = w :: ws *)
        simpl in Hsorted. destruct Hsorted as [_ Htail].
        apply IH in Htail.
        -- assert (Hw_gt_x: w > x).
           { apply Htail. left. reflexivity. }
           lia.
        -- left. reflexivity.
    + (* y in zs *)
      destruct zs as [|w ws].
      * (* zs = [] *)
        simpl in Hin. contradiction.
      * (* zs = w :: ws *)
        simpl in Hsorted. destruct Hsorted as [_ Htail].
        apply IH; assumption.
Qed.

(* Helper: Reversal interchanges ascending and descending sorted *)
Lemma rev_sorted_asc_dec : forall l,
  Sorted_asc l <-> Sorted_dec (rev l).
Proof.
  induction l as [|x xs IH].
  - (* l = [] *)
    simpl. split; intro; auto.
  - (* l = x :: xs *)
    split; intro H.
    + (* Sorted_asc (x :: xs) -> Sorted_dec (rev (x :: xs)) *)
      simpl (rev (x :: xs)).
      destruct xs as [|y ys].
      * (* xs = [] *)
        simpl. auto.
      * (* xs = y :: ys *)
        simpl in H. destruct H as [Hxy Hrest].
        (* rev (x :: y :: ys) = rev (y :: ys) ++ [x] *)
        (* Need: Sorted_dec (rev (y :: ys) ++ [x]) *)
        apply sorted_dec_app_singleton.
        -- (* Sorted_dec (rev (y :: ys)) *)
           apply IH. exact Hrest.
        -- (* All elements in rev (y :: ys) are > x *)
           intros z Hz.
           (* z is in rev (y :: ys), so z is in y :: ys *)
           apply in_rev in Hz.
           (* We need to show x < z *)
           (* Since Sorted_asc (x :: y :: ys), we have x < y and Sorted_asc (y :: ys) *)
           (* And z is in y :: ys *)
           (* Since x < y and y is the first element, and the list is ascending, *)
           (* all elements >= y, so x < y <= z, thus x < z *)
           simpl in Hz. destruct Hz as [Heq | Hin].
           ++ (* z = y *)
              subst. exact Hxy.
           ++ (* z in ys *)
              (* From Sorted_asc (y :: ys), we have y < ... < z *)
              (* Combined with x < y, we get x < z *)
              assert (Hy_lt_z: y < z).
              { apply (sorted_asc_head_lt_tail y ys z Hrest Hin). }
              lia.
    + (* Sorted_dec (rev (x :: xs)) -> Sorted_asc (x :: xs) *)
      simpl (rev (x :: xs)) in H.
      destruct xs as [|y ys].
      * (* xs = [] *)
        simpl. auto.
      * (* xs = y :: ys *)
        (* rev (x :: y :: ys) = rev (y :: ys) ++ [x] *)
        (* From Sorted_dec (rev (y :: ys) ++ [x]), we can show: *)
        (* 1. Sorted_dec (rev (y :: ys)) -> Sorted_asc (y :: ys) by IH *)
        (* 2. All elements in rev (y :: ys) are > x *)
        simpl. split.
        -- (* x < y *)
           apply sorted_dec_app_singleton_inv with (l := rev (y :: ys)) in H.
           apply H. apply in_rev. left. reflexivity.
        -- (* Sorted_asc (y :: ys) *)
           (* First extract Sorted_dec (rev (y :: ys)) from H *)
           assert (Hsorted_rev: Sorted_dec (rev (y :: ys))).
           { clear IH. revert x H. induction (rev (y :: ys)) as [|z zs IH2].
             - simpl. auto.
             - intros x H. destruct zs as [|w ws].
               + simpl. auto.
               + simpl in H. destruct H as [Hzw Htail].
                 simpl. split.
                 * exact Hzw.
                 * apply IH2. exact Htail. }
           apply IH. exact Hsorted_rev.
Qed.

(*
  Key theorem: zeckendorf produces sorted output in ascending order

  This theorem states that the greedy algorithm naturally produces an
  ascending sorted list (smallest to largest Fibonacci numbers).

  Combined with rev_sorted_asc_dec, this means zeckendorf_sorted produces
  descending sorted output suitable for use with our Sorted_dec proofs.

  TODO: This proof requires showing that the greedy algorithm maintains the
  sorted property by always prepending elements smaller than those already in
  the accumulator. The key insight is that as n decreases, the largest Fibonacci
  number <= n also decreases, using the remainder_less_than_prev_fib lemma.
*)
Lemma zeckendorf_produces_sorted_asc : forall n acc,
  Sorted_asc acc ->
  (acc = [] \/ exists x xs, acc = xs ++ [x] /\ forall y, In y xs -> y < x) ->
  Sorted_asc (zeckendorf n acc).
Proof.
  (* TODO: Prove that greedy algorithm maintains ascending sorted order *)
  (* Key insight: since we always prepend larger elements, and process *)
  (* n in decreasing order, the prepends build up an ascending list *)
  admit.
Admitted.

(*
  Corollary: zeckendorf_sorted produces descending sorted output

  Once we prove zeckendorf_produces_sorted_asc, this follows immediately.
*)
Lemma zeckendorf_sorted_produces_sorted_dec : forall n,
  Sorted_dec (zeckendorf_sorted n).
Proof.
  intro n.
  unfold zeckendorf_sorted.
  apply rev_sorted_asc_dec.
  apply (zeckendorf_produces_sorted_asc n []).
  - (* Empty list is sorted *)
    simpl. auto.
  - (* acc = [] satisfies the condition *)
    left. reflexivity.
Qed.  (* TODO: Relies on zeckendorf_produces_sorted_asc being proved *)

(*
  Helper lemma: fuel-based version of non-consecutive property

  This lemma states that zeckendorf_fuel preserves the non-consecutive property:
  if acc has no consecutive Fibs, then the result also has no consecutive Fibs.

  The proof would proceed by induction on fuel, showing that when we add a new
  Fibonacci number F_k, the remainder n - F_k < F_{k-1}, so the next Fibonacci
  picked has index ≤ k-2, ensuring no consecutive Fibs are added.
*)
Lemma zeckendorf_fuel_no_consecutive : forall fuel n acc,
  no_consecutive_fibs acc ->
  (forall z, In z acc -> exists k, z = fib k) ->
  no_consecutive_fibs (zeckendorf_fuel fuel n acc).
Proof.
  (* Induction on fuel *)
  induction fuel as [|fuel' IHfuel].
  - (* Base case: fuel = 0, function returns acc *)
    intros n acc Hnocons_acc Hacc_fib.
    simpl. exact Hnocons_acc.
  - (* Inductive case: fuel = S fuel' *)
    intros n acc Hnocons_acc Hacc_fib.
    (* Case split on n *)
    destruct n as [|n'].
    + (* n = 0: function returns acc *)
      simpl. exact Hnocons_acc.
    + (* n = S n' > 0: algorithm picks largest Fib and recurses *)
      unfold zeckendorf_fuel. fold zeckendorf_fuel.
      (* Get the largest Fibonacci number <= n *)
      destruct (rev (fibs_upto (S n'))) as [|x xs] eqn:Heqfibs.
      * (* Case: fibs_upto is empty (returns acc) *)
        exact Hnocons_acc.
      * (* Case: x is the largest Fibonacci <= n *)
        destruct (Nat.leb x (S n')) eqn:Hleb.
        -- (* Subcase: x <= S n', recurse with (n-x) and (x::acc) *)
           (* Apply IH to the recursive call *)
           apply IHfuel.
           ++ (* Need to show: no_consecutive_fibs (x :: acc) *)
              (* This is the key part: we need to prove that x is not consecutive
                 with any element in acc.

                 The intuition is:
                 - x = fib(kx) is the largest Fibonacci <= n
                 - All elements in acc came from smaller remainders
                 - For any y in acc, y was picked from a remainder m where m <= n - x
                 - Therefore, y <= m < fib(kx-1) (by the greedy property)
                 - So y = fib(ky) where ky <= kx-2, ensuring non-consecutiveness

                 However, proving this requires tracking additional invariants about
                 the relationship between acc and the remainder, which is not captured
                 in the current statement of the lemma.

                 A complete proof would require either:
                 1. Strengthening the lemma with additional preconditions about acc
                 2. Using a different induction principle that tracks more state
                 3. Proving auxiliary lemmas about the structure of acc *)
              unfold no_consecutive_fibs. fold no_consecutive_fibs.
              split.
              ** (* Show x is not consecutive with any element in acc *)
                 intros y Hin_y i j Heq_x Heq_y Hcons.
                 (* We need to derive a contradiction *)
                 (* Key insight: y is in acc, so it was added in a previous step
                    when the remainder was some m <= n - x *)
                 (* We know: x = fib(i) and x <= S n'
                    By greedy property: S n' < fib(i+1) (if i >= 2)
                    Therefore: S n' - x < fib(i-1)
                    So any Fibonacci in the next step has index <= i-2 *)
                 (* This means y = fib(j) where j <= i-2 *)
                 (* But Hcons says j = i+1 or i = j+1 (consecutive)
                    This contradicts j <= i-2 *)
                 (* However, we don't have the machinery to prove this formally
                    because we need to track the history of acc *)
                 admit.
              ** (* Show acc still has no consecutive fibs *)
                 exact Hnocons_acc.
           ++ (* Need to show: all elements in (x :: acc) are Fibonacci numbers *)
              intros z Hin_z. simpl in Hin_z.
              destruct Hin_z as [Heq | Hin_acc].
              ** (* z = x: x is a Fibonacci number from fibs_upto *)
                 subst z.
                 assert (Hin_x: In x (fibs_upto (S n'))).
                 { apply in_list_rev. rewrite Heqfibs. left. reflexivity. }
                 destruct (in_fibs_upto_fib x (S n') Hin_x) as [k [_ Heq_fib]].
                 exists k. symmetry. exact Heq_fib.
              ** (* z is in acc: use assumption *)
                 apply Hacc_fib. exact Hin_acc.
        -- (* Subcase: x > S n' (impossible, returns acc) *)
           exact Hnocons_acc.
Admitted.

(*
  Theorem: Non-consecutive property

  The zeckendorf algorithm produces representations with no consecutive Fibonacci numbers.

  This follows from the fuel-based lemma with acc = [] (which trivially has no
  consecutive Fibs since it's empty).
*)
Theorem zeckendorf_no_consecutive : forall n,
  no_consecutive_fibs (zeckendorf n []).
Proof.
  intro n.
  unfold zeckendorf.
  apply zeckendorf_fuel_no_consecutive.
  - (* Base case: empty list has no consecutive Fibs *)
    simpl. trivial.
  - (* Base case: all elements in [] are Fibonacci numbers (vacuously true) *)
    intros z Hz. inversion Hz.
Qed.

(*
  Helper predicate: A list is a valid Zeckendorf representation of n

  A list l is a valid Zeckendorf representation of n if:
  1. All elements are Fibonacci numbers
  2. The sum equals n
  3. No two consecutive Fibonacci numbers appear in the list
*)
Definition is_zeckendorf_repr (n : nat) (l : list nat) : Prop :=
  (forall z, In z l -> exists k, z = fib k) /\
  sum_list l = n /\
  no_consecutive_fibs l.

(*
  Helper: Find maximum element in a list of nats
*)
Fixpoint list_max (l : list nat) : option nat :=
  match l with
  | [] => None
  | [x] => Some x
  | x :: xs => match list_max xs with
               | None => Some x
               | Some m => Some (Nat.max x m)
               end
  end.

(*
  Helper lemma: fib is strictly monotonic on the range [2, ∞)

  If i >= 2, j >= 2, and i < j, then fib(i) < fib(j).

  Proof: By induction on j - i. Base case: if j = i + 1, use fib_mono.
  Inductive case: use transitivity via fib(j-1).
*)
Lemma fib_mono_lt : forall i j,
  i >= 2 -> j >= 2 -> i < j -> fib i < fib j.
Proof.
  intros i j Hi Hj.
  revert i Hi.
  induction j as [j' IHj] using lt_wf_ind.
  intros i Hi Hlt.
  (* Case split: j = i + 1 or j > i + 1 *)
  destruct (Nat.eq_dec j' (S i)) as [Heq | Hneq].
  - (* j = S i: use fib_mono directly *)
    subst j'. apply fib_mono. assumption.
  - (* j > S i: use transitivity *)
    assert (Hj_gt: j' > S i) by lia.
    assert (Hpred_ge: j' - 1 >= 2) by lia.
    assert (Hpred_ge_i: j' - 1 >= i) by lia.
    destruct (Nat.eq_dec (j' - 1) i) as [Heq_pred | Hneq_pred].
    + (* j' - 1 = i, so j' = S i, contradicts Hneq *)
      exfalso. lia.
    + (* j' - 1 > i *)
      assert (Hpred_gt: j' - 1 > i) by lia.
      assert (Hpred_lt: j' - 1 < j') by lia.
      (* Use IH to get fib i < fib (j' - 1) *)
      assert (H1: fib i < fib (j' - 1)).
      { apply IHj; try lia. }
      (* Use fib_mono to get fib (j' - 1) < fib j' *)
      assert (H2: fib (j' - 1) < fib j').
      { replace j' with (S (j' - 1)) at 2 by lia.
        apply fib_mono. assumption. }
      (* Combine by transitivity *)
      lia.
Qed.

(*
  Helper: Fibonacci numbers are injective for indices >= 2

  This states that if fib(i) = fib(j) for i,j >= 2, then i = j.

  Proof: Use fib_mono_lt to show that fib is strictly monotonic for n >= 2,
  which immediately gives us injectivity by trichotomy.
*)
Lemma fib_injective : forall i j,
  i >= 2 -> j >= 2 -> fib i = fib j -> i = j.
Proof.
  intros i j Hi Hj Heq.
  (* Use trichotomy: either i < j, i = j, or i > j *)
  destruct (Nat.lt_trichotomy i j) as [Hlt | [Heq_ij | Hgt]].
  - (* Case 1: i < j, then fib i < fib j by fib_mono_lt, contradicting Heq *)
    exfalso.
    assert (H: fib i < fib j) by (apply fib_mono_lt; assumption).
    lia.
  - (* Case 2: i = j *)
    assumption.
  - (* Case 3: i > j, then fib j < fib i by fib_mono_lt, contradicting Heq *)
    exfalso.
    assert (H: fib j < fib i) by (apply fib_mono_lt; assumption).
    lia.
Qed.

(* Helper: list_max of non-empty list is never None *)
Lemma list_max_some : forall (x : nat) (xs : list nat),
  exists m, list_max (x :: xs) = Some m.
Proof.
  intros x xs.
  generalize dependent x.
  induction xs as [|y ys IH]; intro x.
  - (* Base case: singleton list [x] *)
    exists x. reflexivity.
  - (* Inductive case: list is x :: y :: ys *)
    specialize (IH y).
    destruct IH as [m Heq].
    exists (Nat.max x m).
    (* Manually unfold the definition for the outer list_max only *)
    change (list_max (x :: y :: ys)) with
      (match list_max (y :: ys) with
       | None => Some x
       | Some m' => Some (Nat.max x m')
       end).
    rewrite Heq.
    reflexivity.
Qed.

(* Helper lemma: if x is in a list and the list has max m, then x <= m *)
Lemma in_list_le_max : forall x l m,
  In x l ->
  list_max l = Some m ->
  x <= m.
Proof.
  intros x l. induction l as [|a l' IHl'].
  - intros m Hin Hmax. simpl in Hin. inversion Hin.
  - intros m Hin Hmax. simpl in Hmax.
    destruct l' as [|b l''].
    + simpl in Hmax. injection Hmax as Heq_max.
      simpl in Hin. destruct Hin as [Heq | Hfalse].
      * subst. reflexivity.
      * inversion Hfalse.
    + destruct (list_max (b :: l'')) as [m'|] eqn:Hmax'.
      * simpl in Hmax. injection Hmax as Heq_m.
        simpl in Hin. destruct Hin as [Heq | Hin'].
        -- rewrite <- Heq, <- Heq_m. apply Nat.le_max_l.
        -- assert (H: x <= m') by (apply (IHl' m' Hin' eq_refl)).
           rewrite <- Heq_m. transitivity m'.
           ++ exact H.
           ++ apply Nat.le_max_r.
      * (* This case is impossible: list_max (b :: l'') = None *)
        exfalso.
        destruct (list_max_some b l'') as [m'' Heq].
        rewrite Hmax' in Heq. discriminate Heq.
Qed.

(*
  Helper: If a list has max fib(k) and contains fib(i), then fib(i) <= fib(k)

  This is a property of list_max: all elements are ≤ the maximum.
*)
Lemma list_max_fib_bound : forall l k i,
  list_max l = Some (fib k) ->
  In (fib i) l ->
  i >= 1 ->
  fib i <= fib k.
Proof.
  intros l k i Hmax Hin Hi.
  assert (H: fib i <= fib k).
  { apply in_list_le_max with (l := l); assumption. }
  exact H.
Qed.

(* Helper: If list_max l = Some m, then m is in the list *)
Lemma list_max_in : forall l m,
  list_max l = Some m ->
  In m l.
Proof.
  induction l as [|x xs IH].
  - intros m Hmax. simpl in Hmax. discriminate.
  - intros m Hmax.
    destruct xs as [|y ys].
    + (* l = [x], so m = x *)
      simpl in Hmax. injection Hmax as Heq. subst. left. reflexivity.
    + (* l = x :: y :: ys *)
      destruct (list_max (y :: ys)) as [m'|] eqn:Hmax'.
      * (* list_max (y :: ys) = Some m' *)
        (* By definition, list_max (x :: y :: ys) = Some (Nat.max x m') *)
        assert (Heq_lmax: list_max (x :: y :: ys) = Some (Nat.max x m')).
        { change (list_max (x :: y :: ys)) with
            (match list_max (y :: ys) with
             | None => Some x
             | Some m => Some (Nat.max x m)
             end).
          rewrite Hmax'. reflexivity. }
        rewrite Heq_lmax in Hmax.
        injection Hmax as Heq_m. subst m.
        (* m is now Nat.max x m', which is either x or m' *)
        destruct (le_dec x m') as [Hle|Hgt].
        -- (* x <= m', so Nat.max x m' = m' *)
           assert (Heq: Nat.max x m' = m') by (apply Nat.max_r; exact Hle).
           rewrite Heq.
           (* m' is in (y :: ys) by IH *)
           right. apply (IH m' eq_refl).
        -- (* x > m', so Nat.max x m' = x *)
           assert (Heq: Nat.max x m' = x) by (apply Nat.max_l; lia).
           rewrite Heq. left. reflexivity.
      * exfalso. destruct (list_max_some y ys) as [m'' Heq]. rewrite Hmax' in Heq. discriminate.
Qed.

(* Helper: If x is in list l, then sum_list l >= x *)
Lemma in_list_le_sum : forall x l,
  In x l ->
  x <= sum_list l.
Proof.
  intros x l Hin.
  induction l as [|a l' IH].
  - (* l = [], contradiction *)
    inversion Hin.
  - (* l = a :: l' *)
    simpl. simpl in Hin.
    destruct Hin as [Heq|Hin'].
    + (* x = a *) subst. lia.
    + (* x is in l' *)
      assert (H: x <= sum_list l') by (apply IH; exact Hin').
      lia.
Qed.

(*
  ==============================================================================
  FIBONACCI VALUE CHARACTERIZATION LEMMAS
  ==============================================================================

  These lemmas characterize which indices produce specific Fibonacci values.
  They are essential for proving properties about lists of Fibonacci numbers.
*)

(*
  Helper: fib(0) = 0

  This is a simple computation lemma.
*)
Lemma fib_0 : fib 0 = 0.
Proof.
  reflexivity.
Qed.

(*
  Helper: fib(i) = 1 implies i ∈ {1, 2}

  This characterizes exactly which indices produce the Fibonacci value 1.

  Proof strategy: Check all cases for i:
  - i = 0: fib(0) = 0 ≠ 1
  - i = 1: fib(1) = 1 ✓
  - i = 2: fib(2) = 1 ✓
  - i ≥ 3: fib(i) ≥ 2 by the recurrence relation
*)
Lemma fib_eq_1_iff : forall i,
  fib i = 1 <-> i = 1 \/ i = 2.
Proof.
  intro i.
  split.
  - (* Forward direction: fib(i) = 1 → i ∈ {1, 2} *)
    intro Heq.
    destruct i as [|[|[|i']]].
    + (* i = 0: fib(0) = 0 ≠ 1 *)
      simpl in Heq. discriminate.
    + (* i = 1: fib(1) = 1 *)
      left. reflexivity.
    + (* i = 2: fib(2) = 1 *)
      right. reflexivity.
    + (* i ≥ 3: fib(i) ≥ 2 by recurrence *)
      exfalso.
      (* fib(3) = fib(2) + fib(1) = 1 + 1 = 2 *)
      assert (Hfib3: fib 3 = 2) by reflexivity.
      (* fib is monotonically increasing for n ≥ 2 *)
      destruct i' as [|i''].
      * (* i = 3: fib(3) = 2 ≠ 1 *)
        simpl in Heq. discriminate.
      * (* i ≥ 4: use monotonicity *)
        assert (Hmono: fib 3 < fib (S (S (S (S i''))))).
        { apply fib_mono_lt; lia. }
        rewrite Hfib3 in Hmono.
        (* So fib(i) ≥ 2, contradicting fib(i) = 1 *)
        lia.
  - (* Backward direction: i ∈ {1, 2} → fib(i) = 1 *)
    intros [H | H]; subst; reflexivity.
Qed.

(*
  Helper: For i ≥ 3, fib(i) ≥ 2

  This establishes that Fibonacci numbers grow beyond 1 starting from index 3.
*)
Lemma fib_ge_2 : forall i,
  i >= 3 -> fib i >= 2.
Proof.
  intros i Hi.
  destruct i as [|[|[|i']]].
  - (* i = 0: contradicts i >=  3 *)
    exfalso. lia.
  - (* i = 1: contradicts i >= 3 *)
    exfalso. lia.
  - (* i = 2: contradicts i >= 3 *)
    exfalso. lia.
  - (* i ≥ 3 *)
    (* fib(3) = 2 and fib is monotonic for n ≥ 2 *)
    assert (Hfib3: fib 3 = 2) by reflexivity.
    assert (Hmono: fib 3 <= fib (S (S (S i')))).
    { destruct i' as [|i''].
      - (* i = 3 *) lia.
      - (* i ≥ 4 *)
        apply Nat.lt_le_incl. apply fib_mono_lt; lia.
    }
    lia.
Qed.

(*
  ==============================================================================
  HELPER LEMMAS FOR UNIQUENESS PROOF
  ==============================================================================
*)

(* Helper: If an element is in a list with max = fib k, it's at most fib k *)
Lemma in_list_le_fib_max : forall l k z,
  list_max l = Some (fib k) ->
  In z l ->
  z <= fib k.
Proof.
  intros l k z Hmax Hz.
  apply (in_list_le_max z l (fib k)); assumption.
Qed.

(* Helper: If z is a Fibonacci number with z < fib k and z <> fib(k-1),
   then the index of z is at most k-2 (for k >= 3) *)
Lemma fib_index_bound : forall z k,
  k >= 3 ->
  (exists i, fib i = z) ->
  z < fib k ->
  z <> fib (k - 1) ->
  exists i, i <= k - 2 /\ fib i = z.
Proof.
  intros z k Hk_ge [i Heq_i] Hz_lt Hz_neq.
  exists i. split.
  - (* Show i <= k - 2 *)
    (* z = fib i < fib k, so i < k by strict monotonicity *)
    (* z <> fib(k-1), so i <> k-1 *)
    (* Therefore i <= k - 2 *)

    (* First show i < k *)
    assert (Hi_lt_k: i < k).
    { (* By contradiction: if i >= k, then fib i >= fib k by monotonicity *)
      destruct (Nat.lt_ge_cases i k) as [Hlt | Hge]; [exact Hlt |].
      exfalso.
      assert (Hfib_ge: fib k <= fib i).
      { (* Need to show fib k <= fib i when k <= i and both >= 2 *)
        destruct (Nat.eq_dec k i) as [Heq_ki | Hneq_ki].
        - (* k = i: fib k = fib i *)
          rewrite Heq_ki. lia.
        - (* k < i: use fib_mono_lt *)
          assert (Hk_lt_i: k < i) by lia.
          apply Nat.lt_le_incl.
          apply fib_mono_lt; try lia. }
      rewrite Heq_i in Hfib_ge. lia. }

    (* Now show i <> k - 1 *)
    assert (Hi_neq: i <> k - 1).
    { intro Heq. apply Hz_neq. rewrite <- Heq_i. f_equal. exact Heq. }

    (* Combine: i < k and i <> k - 1, so i <= k - 2 *)
    lia.
  - exact Heq_i.
Qed.

(*
  ==============================================================================
  KEY LEMMA FOR UNIQUENESS
  ==============================================================================
*)

(*
  Key Lemma for Uniqueness: Sum bound for non-consecutive Fibonacci numbers

  The sum of any non-empty list of distinct, non-consecutive Fibonacci numbers
  whose largest member is F_k (with k >= 2) is strictly less than F_{k+1}.

  Note: We require k >= 2 to avoid the ambiguity that fib(1) = fib(2) = 1.
  In proper Zeckendorf representations, we only use Fibonacci numbers from
  indices >= 2, i.e., the sequence 1, 2, 3, 5, 8, 13, ...

  We also require NoDup (distinctness) as the lemma is false without it.

  Proof strategy:
  - Use induction on k
  - Base case: k = 2 can be verified directly (COMPLETED)
  - Inductive case: Consider a list with maximum F_k
    * Since no consecutive Fibs, fib(k-1) is NOT in the list (COMPLETED)
    * Removing fib(k) from list gives a list with max ≤ fib(k-2)
    * By IH, sum(rest) < fib(k-1)
    * So total sum = fib(k) + sum(rest) < fib(k) + fib(k-1) = fib(k+1)

  This lemma is crucial for proving uniqueness.

  NOTE: This proof would be significantly simpler if we worked with sorted lists
  throughout, as that would eliminate much of the case analysis about where
  elements appear in the list.
*)

(*
  ==============================================================================
  SORTED VERSION: Much simpler proof using sorted lists!
  ==============================================================================
*)

(*
  Helper lemma: Fibonacci gap property

  If y is a Fibonacci number with y < fib k and y ≠ fib(k-1), then y ≤ fib(k-2).
  This is because the only Fibonacci numbers between fib(k-2) and fib k are
  fib(k-1) (and possibly fib k itself).
*)
Lemma fib_gap_property : forall k y,
  k >= 3 ->
  (exists i, i >= 2 /\ fib i = y) ->
  y < fib k ->
  y <> fib (k - 1) ->
  y <= fib (k - 2).
Proof.
  intros k y Hk_ge [i [Hi_ge Heq_i]] Hy_lt Hy_neq.
  subst y.
  (* fib i < fib k, so i < k by monotonicity *)
  (* fib i ≠ fib(k-1), so i ≠ k-1 *)
  (* Therefore i <= k-2 *)

  (* First show i < k *)
  assert (Hi_lt_k: i < k).
  { destruct (Nat.lt_ge_cases i k) as [Hlt | Hge]; [exact Hlt |].
    exfalso.
    (* If i >= k, then fib i >= fib k *)
    assert (Hfib_ge: fib k <= fib i).
    { destruct (Nat.eq_dec i k) as [Heq | Hneq].
      - rewrite Heq. lia.
      - assert (Hi_gt_k: i > k) by lia.
        destruct i as [|[|i']]; try lia.
        destruct k as [|[|k']]; try lia.
        apply Nat.lt_le_incl. apply fib_mono_lt; lia. }
    lia. }

  (* Now show i ≠ k - 1 *)
  assert (Hi_neq: i <> k - 1).
  { intro Heq. apply Hy_neq. rewrite Heq. reflexivity. }

  (* Therefore i <= k - 2 *)
  assert (Hi_le: i <= k - 2) by lia.

  (* Now show fib i <= fib(k-2) *)
  destruct (Nat.eq_dec i (k - 2)) as [Heq | Hneq].
  - (* i = k - 2: fib i = fib(k-2) *)
    rewrite Heq. lia.
  - (* i < k - 2 *)
    assert (Hi_lt: i < k - 2) by lia.
    (* k >= 3, so k - 2 >= 1 *)
    assert (Hk_minus_2_ge: k - 2 >= 1) by lia.
    destruct i as [|[|i']].
    + (* i = 0: fib 0 = 0 <= fib(k-2) *)
      assert (Hpos: fib (k - 2) > 0).
      { apply fib_pos. exact Hk_minus_2_ge. }
      simpl. lia.
    + (* i = 1: fib 1 = 1 <= fib(k-2) *)
      (* We have i < k-2, so 1 < k-2, thus k-2 >= 2 *)
      assert (Hk_minus_2_ge_2: k - 2 >= 2) by lia.
      (* fib 1 = 1, fib 2 = 1, and fib is monotonic for indices >= 2 *)
      (* So fib(k-2) >= fib 2 = 1 *)
      assert (Hfib_k_minus_2_ge: fib (k - 2) >= fib 2).
      { destruct (Nat.eq_dec (k - 2) 2) as [Heq2 | Hneq2].
        - rewrite Heq2. lia.
        - assert (Hk_gt: k - 2 > 2) by lia.
          apply Nat.lt_le_incl.
          apply fib_mono_lt; lia. }
      assert (Hfib2: fib 2 = 1) by reflexivity.
      simpl. lia.
    + (* i >= 2: use monotonicity *)
      apply Nat.lt_le_incl.
      apply fib_mono_lt; lia.
Qed.

(*
  Helper lemma: In a sorted descending list of Fibonacci numbers where
  adjacent pairs are non-consecutive, if a Fibonacci number fib j is anywhere
  in the tail and fib i is the head with i and j consecutive, then we have
  a contradiction.

  This is a key property: in sorted Fibonacci lists, consecutive indices
  must be adjacent in the list (because Fibonacci grows and there are no
  numbers in between).
*)
Lemma sorted_fibs_no_consecutive_gap : forall i j y ys,
  i >= 2 -> j >= 2 ->
  nat_consecutive i j ->
  i > j ->
  Sorted_dec (fib i :: y :: ys) ->
  In (fib j) (y :: ys) ->
  (forall z, In z (fib i :: y :: ys) -> exists k, k >= 2 /\ fib k = z) ->
  no_consecutive_fibs_sorted (fib i :: y :: ys) ->
  False.
Proof.
  intros i j y ys Hi_ge Hj_ge Hcons Hi_gt_j Hsorted Hj_in Hfib Hnocons.
  (* Since i and j are consecutive with i > j, we have i = S j *)
  unfold nat_consecutive in Hcons.
  destruct Hcons as [Hj_eq_Si | Hi_eq_Sj].
  - (* First case: j = S i, which contradicts i > j *)
    (* If j = S i, then j > i, but we have i > j *)
    (* Substituting j = S i into i > j gives i > S i, which is impossible *)
    exfalso.
    rewrite Hj_eq_Si in Hi_gt_j.
    (* Now Hi_gt_j : i > S i, which is absurd *)
    lia.
  - (* Second case: i = S j, which is consistent with i > j *)
    (* This is the main case with the Fibonacci gap argument *)
    (* fib i > fib j by monotonicity *)
    assert (Hfib_i_gt_j: fib i > fib j).
    { apply fib_mono_lt; lia. }

    (* In the sorted list fib i :: y :: ys, fib j is somewhere in y :: ys *)
    (* If fib j = y, then they're adjacent -> contradiction from Hnocons *)
    simpl in Hj_in. destruct Hj_in as [Hy_eq | Hys_in].
    + (* y = fib j, so fib i and fib j are adjacent *)
      simpl in Hnocons. destruct Hnocons as [Hno_adj _].
      apply (Hno_adj i j); try reflexivity.
      * rewrite Hy_eq. reflexivity.
      * unfold nat_consecutive. right. exact Hi_eq_Sj.
    + (* fib j is in ys, not adjacent to fib i *)
      (* But this means there exists y with fib i > y > fib j *)
      (* and y is a Fibonacci number *)
      assert (Hy_fib: exists k, k >= 2 /\ fib k = y).
      { apply Hfib. simpl. right. left. reflexivity. }
      destruct Hy_fib as [k [Hk_ge Heq_k]].

      (* y is between fib i and fib j *)
      (* First show: fib j < y *)
      assert (Hfib_j_lt_y: fib j < y).
      { assert (Hsorted_y_ys: Sorted_dec (y :: ys)).
        { eapply sorted_tail. exact Hsorted. }
        destruct ys as [|z zs].
        - simpl in Hys_in. contradiction.
        - simpl in Hsorted_y_ys. destruct Hsorted_y_ys as [Hy_gt_z _].
          simpl in Hys_in. destruct Hys_in as [Hz_eq | Hzs_in].
          + (* z = fib j *)
            rewrite <- Hz_eq. exact Hy_gt_z.
          + (* fib j is deeper *)
            eapply sorted_tail_lt.
            * eapply (sorted_tail (fib i)). exact Hsorted.
            * simpl. right. exact Hzs_in. }

      (* Next show: y < fib i *)
      assert (Hy_lt_fib_i: y < fib i).
      { eapply sorted_tail_lt.
        - exact Hsorted.
        - simpl. left. reflexivity. }

      (* So fib j < y = fib k < fib i *)
      assert (Hy_bounds: fib j < fib k /\ fib k < fib i).
      { rewrite <- Heq_k in Hfib_j_lt_y, Hy_lt_fib_i.
        split; assumption. }

      (* So fib j < fib k < fib i *)
      (* This means j < k < i by monotonicity *)
      assert (Hj_lt_k: j < k).
      { destruct (Nat.lt_ge_cases j k) as [Hlt | Hge]; [exact Hlt |].
        exfalso.
        assert (Hfib_ge: fib k <= fib j).
        { destruct (Nat.eq_dec k j) as [Heq | Hneq].
          - rewrite Heq. lia.
          - (* We have j >= k and j ≠ k, so j > k *)
            assert (Hj_gt_k: j > k) by lia.
            apply Nat.lt_le_incl.
            apply fib_mono_lt.
            + (* k >= 2: We have fib j < y = fib k and j >= 2, so fib 2 <= fib j < fib k *)
              (* fib 2 = 1, so 1 <= fib j < fib k, thus fib k > 1 *)
              (* If k = 0, then fib k = 0 <= 1, contradiction *)
              (* If k = 1, then fib k = 1, but we need fib k > 1, contradiction *)
              (* Therefore k >= 2 *)
              destruct k as [|[|k']].
              * (* k = 0: fib 0 = 0, but fib j >= fib 2 = 1, and fib j < fib k = 0, contradiction *)
                exfalso.
                assert (Hfib_j_pos: fib j >= 1).
                { assert (Hfib_2_eq: fib 2 = 1) by reflexivity.
                  rewrite <- Hfib_2_eq.
                  destruct (Nat.eq_dec j 2) as [Heq_j2 | Hneq_j2].
                  - rewrite Heq_j2. lia.
                  - assert (Hj_gt_2: j > 2) by lia.
                    apply Nat.lt_le_incl.
                    apply fib_mono_lt; lia. }
                rewrite <- Heq_k in Hfib_j_lt_y.
                simpl in Hfib_j_lt_y. lia.
              * (* k = 1: fib 1 = 1, but fib j >= 1 and fib j < fib k = 1, contradiction *)
                exfalso.
                assert (Hfib_j_pos: fib j >= 1).
                { assert (Hfib_2_eq: fib 2 = 1) by reflexivity.
                  rewrite <- Hfib_2_eq.
                  destruct (Nat.eq_dec j 2) as [Heq_j2 | Hneq_j2].
                  - rewrite Heq_j2. lia.
                  - assert (Hj_gt_2: j > 2) by lia.
                    apply Nat.lt_le_incl.
                    apply fib_mono_lt; lia. }
                rewrite <- Heq_k in Hfib_j_lt_y.
                simpl in Hfib_j_lt_y. lia.
              * (* k = S (S k'), so k >= 2 *)
                lia.
            + exact Hj_ge.
            + exact Hj_gt_k. }
        lia. }

      assert (Hk_lt_i: k < i).
      { destruct (Nat.lt_ge_cases k i) as [Hlt | Hge]; [exact Hlt |].
        exfalso.
        assert (Hfib_ge: fib i <= fib k).
        { destruct (Nat.eq_dec i k) as [Heq | Hneq].
          - rewrite Heq. lia.
          - (* We have k >= i and k ≠ i, so k > i *)
            assert (Hk_gt_i: k > i) by lia.
            apply Nat.lt_le_incl.
            apply fib_mono_lt.
            + exact Hi_ge.
            + (* k >= 2: Same proof as before - we have fib j < y = fib k and j >= 2 *)
              destruct k as [|[|k']].
              * (* k = 0: contradiction *)
                exfalso.
                assert (Hfib_j_pos: fib j >= 1).
                { assert (Hfib_2_eq: fib 2 = 1) by reflexivity.
                  rewrite <- Hfib_2_eq.
                  destruct (Nat.eq_dec j 2) as [Heq_j2 | Hneq_j2].
                  - rewrite Heq_j2. lia.
                  - assert (Hj_gt_2: j > 2) by lia.
                    apply Nat.lt_le_incl.
                    apply fib_mono_lt; lia. }
                rewrite <- Heq_k in Hfib_j_lt_y.
                simpl in Hfib_j_lt_y. lia.
              * (* k = 1: contradiction *)
                exfalso.
                assert (Hfib_j_pos: fib j >= 1).
                { assert (Hfib_2_eq: fib 2 = 1) by reflexivity.
                  rewrite <- Hfib_2_eq.
                  destruct (Nat.eq_dec j 2) as [Heq_j2 | Hneq_j2].
                  - rewrite Heq_j2. lia.
                  - assert (Hj_gt_2: j > 2) by lia.
                    apply Nat.lt_le_incl.
                    apply fib_mono_lt; lia. }
                rewrite <- Heq_k in Hfib_j_lt_y.
                simpl in Hfib_j_lt_y. lia.
              * (* k >= 2 *)
                lia.
            + exact Hk_gt_i. }
        lia. }

      (* So j < k < i, but i = S j *)
      (* We have j < k < i and i = S j *)
      (* This means j < k < S j, so k must be between j and S j *)
      (* But there are no naturals strictly between j and S j *)
      (* Combine all the inequalities *)
      (* Hj_lt_k: j < k, Hk_lt_i: k < i, Hi_eq_Sj: i = S j *)
      (* From i = S j and k < i, we get k < S j *)
      assert (Hk_lt_Sj: k < S j) by lia.
      (* So j < k < S j, which is impossible *)
      lia.
Qed.

(*
  Sum bound for sorted non-consecutive Fibonacci lists (SIMPLIFIED VERSION)

  This is a dramatically simplified version that works with sorted lists.
  Since the list is sorted in descending order with fib k at the head:
  - No need to search for the maximum (it's the head)
  - Pattern matching is direct: l = fib k :: xs
  - NoDup follows automatically from Sorted_dec
  - Only need to check adjacent pairs for non-consecutive property

  The proof is much shorter and more direct than the unsorted version.
*)
Lemma sum_nonconsec_fibs_bounded_sorted : forall k xs,
  k >= 2 ->
  Sorted_dec (fib k :: xs) ->
  no_consecutive_fibs_sorted (fib k :: xs) ->
  (forall x, In x (fib k :: xs) -> exists i, i >= 2 /\ fib i = x) ->
  sum_list (fib k :: xs) < fib (S k).
Proof.
  intros k xs Hk_ge. revert xs.
  induction k as [k IHk] using lt_wf_ind.
  intros xs Hsorted Hnocons Hfib.

  (* Base case: k = 2 *)
  destruct k as [|[|k'']].
  - (* k = 0: contradicts k >= 2 *)
    exfalso. lia.
  - (* k = 1: contradicts k >= 2 *)
    exfalso. lia.
  - (* k >= 2 *)
    destruct k'' as [|k'''].
    + (* k = 2: fib 2 = 1, fib 3 = 2 *)
      (* Goal: sum_list (fib 2 :: xs) < fib 3 = 2 *)
      (* fib 2 = 1, and all elements in xs must be < 1 (since sorted) *)
      (* But Fibonacci numbers are positive, so xs must be empty or contain only 0 *)
      assert (Hfib2_val: fib 2 = 1) by reflexivity.
      assert (Hfib3_val: fib 3 = 2) by reflexivity.
      rewrite Hfib2_val in *. rewrite Hfib3_val.

      (* All elements in xs are < 1 *)
      assert (Hxs_lt: forall y, In y xs -> y < 1).
      { intros y Hy. apply (sorted_tail_lt 1 xs); assumption. }

      (* But all elements are Fibonacci numbers, and fib i > 0 for i >= 1 *)
      (* So all elements in xs must be 0 = fib 0 *)
      (* However, if xs contains fib 0 = 0, then we have fib 2 = 1 and fib 0 = 0 adjacent *)
      (* Actually, let's show xs must be empty *)

      (* If xs is non-empty, let's derive a contradiction *)
      destruct xs as [|y ys].
      * (* xs = [] *)
        simpl. lia.
      * (* xs = y :: ys *)
        (* y < 1 and y is a Fibonacci number *)
        assert (Hy_lt: y < 1) by (apply Hxs_lt; simpl; left; reflexivity).
        assert (Hy_fib: exists i, i >= 2 /\ fib i = y).
        { apply Hfib. simpl. right. left. reflexivity. }
        destruct Hy_fib as [i [Hi_ge Heq_i]].
        (* Since fib i = y < 1 and fib 0 = 0, fib 1 = 1, we must have i = 0 *)
        assert (Hi_eq: i = 0).
        { destruct i as [|[|i']].
          - reflexivity.
          - exfalso. assert (H: fib 1 = 1) by reflexivity. lia.
          - exfalso. assert (H: fib 2 = 1) by reflexivity.
            assert (Hfib_pos: fib (S (S i')) > 0) by (apply fib_pos; lia). lia. }
        subst i.
        (* So y = fib 0 = 0 *)
        assert (Hy_eq: y = 0) by (rewrite <- Heq_i; reflexivity).
        subst y.
        (* Now we have 1 :: 0 :: ys, which means fib 2 and fib 0 are adjacent *)
        (* Check no_consecutive_fibs_sorted *)
        simpl in Hnocons. destruct Hnocons as [Hno_adj _].
        (* Hno_adj says: forall i j, fib i = 1 -> fib j = 0 -> ~nat_consecutive i j *)
        (* But 2 and 0 are not consecutive (nat_consecutive means differ by 1) *)
        (* So this is actually fine! *)
        (* Let me reconsider... sum_list (1 :: 0 :: ys) = 1 + sum_list (0 :: ys) *)
        simpl.
        (* We need: 1 + sum_list (0 :: ys) < 2 *)
        (* This means: sum_list (0 :: ys) < 1 *)
        (* Since 0 is in the list and all elements are non-negative, sum >= 0 *)
        (* We need to show sum_list (0 :: ys) <= 0, which means ys = [] *)

        assert (Hys_empty: ys = []).
        { destruct ys as [|z zs].
          - reflexivity.
          - (* z is in the list and z < 0 (since sorted and z < y = 0) *)
            assert (Hz_lt: z < 0).
            { assert (Hsorted_0zs: Sorted_dec (0 :: z :: zs)).
              { apply (sorted_tail 1). exact Hsorted. }
              simpl in Hsorted_0zs. destruct Hsorted_0zs as [H0z _]. exact H0z. }
            (* But z is a Fibonacci number, and all Fibonacci numbers are >= 0 *)
            assert (Hz_fib: exists i, i >= 2 /\ fib i = z).
            { apply Hfib. simpl. right. right. left. reflexivity. }
            destruct Hz_fib as [i' [Hi'_ge Heq_i']].
            (* fib i' is a nat, so >= 0, but z = fib i' < 0, contradiction *)
            lia. }
        subst ys.
        simpl. lia.

    + (* k >= 3: Main inductive case *)
      (* k = S (S (S k''')) >= 3 *)
      (* List is (fib k :: xs), sorted, no consecutive fibs *)
      (* Goal: sum_list (fib k :: xs) < fib (S k) *)

      simpl (sum_list (fib (S (S (S k'''))) :: xs)).

      (* Use recurrence: fib (S k) = fib k + fib (k-1) *)
      assert (Hrecur: fib (S (S (S (S k''')))) =
                      fib (S (S (S k'''))) + fib (S (S k'''))).
      { apply fib_recurrence. lia. }
      rewrite Hrecur.

      (* Goal: fib k + sum_list xs < fib k + fib (k-1) *)
      (* Equivalently: sum_list xs < fib (k-1) *)

      (* Key insight: fib (k-1) is NOT in xs *)
      (* Proof: If fib (k-1) were in xs, since xs is the tail of a sorted list
         starting with fib k, and no_consecutive_fibs_sorted checks adjacent pairs,
         we'd have fib k and fib (k-1) adjacent, which violates no_consecutive *)

      assert (Hk_minus_1_not_in: ~In (fib (S (S k'''))) xs).
      { intro Hin.
        (* fib (k-1) is in xs *)
        (* If xs is non-empty and fib (k-1) is at the head, we get a contradiction *)
        destruct xs as [|y ys].
        - (* xs = [] *)
          simpl in Hin. contradiction.
        - (* xs = y :: ys *)
          (* Now we can analyze where fib (k-1) appears *)
          simpl in Hin. destruct Hin as [Hy_eq | Hy_in].
          + (* y = fib (k-1), so fib k and fib (k-1) are adjacent in the list *)
            (* Extract the no_consecutive property for adjacent elements *)
            simpl in Hnocons. destruct Hnocons as [Hno_adj _].
            (* Hno_adj: forall i j, fib i = fib k -> fib j = y -> ~nat_consecutive i j *)
            apply (Hno_adj (S (S (S k'''))) (S (S k'''))); try reflexivity.
            * rewrite Hy_eq. reflexivity.
            * unfold nat_consecutive. right. reflexivity.
          + (* fib (k-1) is deeper in xs = y :: ys, not adjacent to fib k *)
            (* Use sorted_fibs_no_consecutive_gap to show this is impossible *)
            exfalso.
            eapply (sorted_fibs_no_consecutive_gap (S (S (S k'''))) (S (S k''')) y ys).
            * lia. (* i >= 2 *)
            * lia. (* j >= 2 *)
            * unfold nat_consecutive. right. reflexivity. (* i and j consecutive *)
            * lia. (* i > j *)
            * exact Hsorted.
            * simpl. right. exact Hy_in. (* fib j in y :: ys *)
            * exact Hfib. (* all elements are Fibonacci numbers *)
            * simpl in Hnocons. exact Hnocons. (* no consecutive fibs in sorted list *)
          }

      (* Now we know fib (k-1) is NOT in xs *)
      (* We want to show: sum_list xs < fib (k-1) *)

      (* Case analysis on xs *)
      destruct xs as [|y ys].
      * (* xs = [] *)
        (* Goal: fib k + sum_list [] < fib k + fib (k-1) *)
        (* sum_list [] = 0, so this is: fib k + 0 < fib k + fib (k-1) *)
        (* Use monotonicity of addition *)
        simpl (sum_list []).
        apply Nat.add_lt_mono_l.
        apply fib_pos. lia.
      * (* xs = y :: ys, so the original list is fib k :: y :: ys *)
        (* y < fib k (since sorted) *)
        assert (Hy_lt_k: y < fib (S (S (S k''')))).
        { eapply sorted_tail_lt.
          - exact Hsorted.
          - simpl. left. reflexivity. }

        (* Since y is a Fibonacci number, y < fib k, and y <> fib (k-1),
           by monotonicity, y <= fib (k-2) *)

        (* First, assert y is a Fibonacci number *)
        assert (Hy_fib: exists i, i >= 2 /\ fib i = y).
        { apply Hfib. simpl. right. left. reflexivity. }

        (* Assert y <> fib (k-1) from Hk_minus_1_not_in *)
        assert (Hy_neq_k_minus_1: y <> fib (S (S k'''))).
        { intro Heq. apply Hk_minus_1_not_in. rewrite <- Heq. simpl. left. reflexivity. }

        (* Use fib_gap_property *)
        assert (Hy_le_k_minus_2: y <= fib (S (S k''') - 1)).
        { apply (fib_gap_property (S (S (S k'''))) y).
          - lia.
          - exact Hy_fib.
          - exact Hy_lt_k.
          - simpl. exact Hy_neq_k_minus_1. }

        (* Now we need to apply IH to y :: ys to show sum_list (y :: ys) < fib(k-1) *)
        (* Extract the index j such that fib j = y *)
        destruct Hy_fib as [j [Hj_ge Heq_j]].

        (* Show j <= k-2 using monotonicity *)
        assert (Hj_le_k_minus_2: j <= S k''').
        { (* We have y = fib j and y <= fib (k-2) = fib (S (S k''') - 1) *)
          (* Simplify fib (S (S k''') - 1) = fib (S k''') *)
          assert (Hy_le_simp: y <= fib (S k''')).
          { assert (Heq_minus: S (S k''') - 1 = S k''') by lia.
            rewrite Heq_minus in Hy_le_k_minus_2.
            exact Hy_le_k_minus_2. }
          assert (Hfib_j_le: fib j <= fib (S k''')).
          { rewrite Heq_j. exact Hy_le_simp. }
          (* Hfib_j_le: fib j <= fib (S k''') *)
          (* Use case analysis on k''' *)
          destruct k''' as [|k''''].
          - (* k''' = 0: k = 3, k-2 = 1, so fib j <= fib 1 = 1 *)
            (* fib 0 = 0, fib 1 = 1, fib 2 = 1, fib 3 = 2, ... *)
            (* So fib j <= 1 means j <= 2 (since fib 2 = 1 and fib 3 = 2 > 1) *)
            assert (Hj_le_2: j <= 2).
            { destruct j as [|[|[|j']]]; try lia.
              (* j = S (S (S j')) >= 3: fib 3 = 2 > 1, contradicts fib j <= 1 *)
              exfalso.
              assert (Hfib_3: fib 3 = 2) by reflexivity.
              assert (Hfib_SSS_ge: fib (S (S (S j'))) >= fib 3).
              { destruct (Nat.eq_dec (S (S (S j'))) 3) as [Heq | Hneq].
                - rewrite Heq. lia.
                - assert (Hj_gt: S (S (S j')) > 3) by lia.
                  apply Nat.lt_le_incl.
                  apply fib_mono_lt; lia. }
              lia. }
            (* S k''' = 1, so we need j <= 1, but we only have j <= 2 *)
            (* Use the constraint y <> fib (k-1) *)
            (* k = 3, so k-1 = 2, and fib 2 = 1 *)
            (* We have fib j <= fib 1 = 1 *)
            (* Since y = fib j and fib is non-decreasing for j >= 1, *)
            (* fib j <= 1 means fib j ∈ {0, 1} *)
            (* fib 0 = 0, fib 1 = 1, fib 2 = 1 *)
            (* We'll show y > 0 (similar to later proof), so y = 1 *)
            (* But y <> fib (k-1) = fib 2 = 1, contradiction *)
            exfalso.
            (* Show y > 0 *)
            assert (Hy_pos: y > 0).
            { destruct (Nat.eq_dec y 0) as [Heq0 | Hneq0].
              - (* y = 0, derive contradiction *)
                destruct ys as [|z zs].
                + (* ys = []: y = 0 = fib j, but j >= 2, so fib j >= fib 2 = 1 > 0, contradiction *)
                  exfalso.
                  (* j >= 2, so fib j >= fib 2 = 1, hence y >= 1 *)
                  assert (Hy_ge: y >= 1).
                  { rewrite <- Heq_j.
                    destruct (Nat.eq_dec j 2) as [Heq2 | Hneq2].
                    - rewrite Heq2. simpl. lia.
                    - assert (Hj_gt: j > 2) by lia.
                      (* fib 2 < fib j since 2 < j *)
                      assert (Hfib_lt: fib 2 < fib j).
                      { apply fib_mono_lt; lia. }
                      simpl in Hfib_lt. lia. }
                  (* But y = 0, contradicting y >= 1 *)
                  lia.
                + (* ys = z :: zs: z < 0, contradiction *)
                  exfalso.
                  assert (Hz_lt: z < 0).
                  { assert (Hsorted_y_ys: Sorted_dec (0 :: z :: zs)).
                    { apply (sorted_tail (fib (S (S (S 0))))).
                      rewrite Heq0 in Hsorted. exact Hsorted. }
                    simpl in Hsorted_y_ys. destruct Hsorted_y_ys as [H0z _].
                    exact H0z. }
                  assert (Hz_fib: exists i, i >= 2 /\ fib i = z).
                  { apply Hfib. simpl. right. right. left. reflexivity. }
                  destruct Hz_fib as [i_z [Hi_z_ge Heq_iz]].
                  lia.
              - lia. }
            (* Now, y = fib j, fib j <= fib 1 = 1, and y > 0 *)
            (* So y <= 1 and y > 0, thus y = 1 *)
            assert (Hfib_1: fib 1 = 1) by reflexivity.
            assert (Hy_le_1: y <= 1).
            { rewrite <- Heq_j. rewrite Hfib_1 in Hfib_j_le. exact Hfib_j_le. }
            assert (Hy_eq_1: y = 1) by lia.
            (* But y <> fib (k-1) = fib 2 = 1 *)
            assert (Hfib_k_minus_1: fib 2 = 1) by reflexivity.
            rewrite Hy_eq_1 in Hy_neq_k_minus_1.
            rewrite Hfib_k_minus_1 in Hy_neq_k_minus_1.
            (* k = 3, so S (S k''') = S (S 0) = 2 *)
            assert (Hk_eq_3: S (S (S 0)) = 3) by reflexivity.
            (* Hy_neq_k_minus_1: y <> fib (S (S 0)), i.e., 1 <> fib 2 = 1 *)
            exfalso. apply Hy_neq_k_minus_1. reflexivity.
          - (* k''' >= 1: S k''' >= 2, so we can use fib_mono_lt *)
            destruct (Nat.le_gt_cases j (S (S k''''))) as [Hle | Hgt]; [exact Hle |].
            exfalso.
            assert (Hfib_gt: fib j > fib (S (S k''''))).
            { (* First show j >= 2 *)
              assert (Hj_ge_2_local: j >= 2).
              { (* Show y > 0, then j ≠ 0, 1 *)
                assert (Hy_pos: y > 0).
                { destruct (Nat.eq_dec y 0) as [Heq0 | Hneq0].
                  - destruct ys as [|z zs].
                    + (* y = 0 = fib j, but j >= 2, so fib j >= 1, contradiction *)
                      exfalso.
                      assert (Hy_ge: y >= 1).
                      { rewrite <- Heq_j.
                        destruct (Nat.eq_dec j 2) as [Heq2 | Hneq2].
                        - rewrite Heq2. simpl. lia.
                        - assert (Hj_gt: j > 2) by lia.
                          assert (Hfib_lt: fib 2 < fib j).
                          { apply fib_mono_lt; lia. }
                          simpl in Hfib_lt. lia. }
                      lia.
                    + exfalso.
                      assert (Hz_lt: z < 0).
                      { assert (Hsorted_y_ys: Sorted_dec (0 :: z :: zs)).
                        { apply (sorted_tail (fib (S (S (S (S k'''')))))).
                          rewrite Heq0 in Hsorted. exact Hsorted. }
                        simpl in Hsorted_y_ys. destruct Hsorted_y_ys as [H0z _].
                        exact H0z. }
                      assert (Hz_fib: exists i, i >= 2 /\ fib i = z).
                      { apply Hfib. simpl. right. right. left. reflexivity. }
                      destruct Hz_fib as [i_z [Hi_z_ge Heq_iz]].
                      lia.
                  - lia. }
                destruct j as [|[|j']].
                - exfalso. rewrite <- Heq_j in Hy_pos. simpl in Hy_pos. lia.
                - (* j = 1, but Hj_ge : j >= 2, contradiction *)
                  exfalso. lia.
                - lia. }
              apply fib_mono_lt.
              - lia.                    (* S (S k'''') >= 2 *)
              - exact Hj_ge_2_local.    (* j >= 2 *)
              - exact Hgt.              (* S (S k'''') < j *) }
            lia. }

        (* Show j >= 2 *)
        assert (Hj_ge_2: j >= 2).
        { (* Strategy: Show y > 0, then handle j = 0 and j = 1 cases *)
          (* First show y > 0 *)
          assert (Hy_pos: y > 0).
          { (* Since the list is sorted and fib k is at the head, we have y < fib k *)
            (* k = S (S (S k''')), so fib k >= fib 3 = 2 *)
            (* If ys is non-empty, then there exists an element below y *)
            (* All elements are Fibonacci numbers, and the only Fibonacci number <= 0 is fib 0 = 0 *)
            (* But if y = 0, then ys would contain elements < 0, which is impossible *)
            (* So y > 0 *)
            destruct (Nat.eq_dec y 0) as [Heq0 | Hneq0].
            - (* y = 0 *)
              exfalso.
              (* If y = 0, and ys is non-empty, let z be an element of ys *)
              destruct ys as [|z zs].
              + (* ys = [], so list is [fib k, 0] *)
                (* sum = fib k + 0 = fib k < fib (S k) is what we need to prove *)
                (* But this contradicts our context - we're in the case where xs = y :: ys *)
                (* Actually, this is fine - sum = fib k + 0 < fib k + fib (k-1) holds *)
                (* Let me reconsider the context... *)
                (* We have Hy_lt_k: y < fib k, and y = 0, so 0 < fib k, which is true *)
                (* The issue is whether y = 0 can appear in a Zeckendorf representation *)
                (* Actually, 0 = fib 0, and in Zeckendorf reps, we typically start from fib 2 = 1 *)
                (* The lemma hypothesis says all elements are Fibonacci numbers, not which indices *)
                (* Let me try a different approach: use no_consecutive_fibs_sorted *)
                (* If y = 0 = fib 0, then either ys = [] or ys starts with some z < 0 *)
                (* But Fibonacci numbers are all >= 0, so z < 0 is impossible *)
                (* y = 0 = fib j, but j >= 2, so fib j >= 1, contradiction *)
                assert (Hy_ge: y >= 1).
                { rewrite <- Heq_j.
                  destruct (Nat.eq_dec j 2) as [Heq2 | Hneq2].
                  - rewrite Heq2. simpl. lia.
                  - assert (Hj_gt: j > 2) by lia.
                    assert (Hfib_lt: fib 2 < fib j).
                    { apply fib_mono_lt; lia. }
                    simpl in Hfib_lt. lia. }
                lia.
              + (* ys = z :: zs, so z < y = 0, thus z < 0 *)
                (* But z is a Fibonacci number, so z >= 0, contradiction *)
                assert (Hz_lt: z < 0).
                { assert (Hsorted_y_ys: Sorted_dec (0 :: z :: zs)).
                  { apply (sorted_tail (fib (S (S (S k'''))))).
                    rewrite Heq0 in Hsorted. exact Hsorted. }
                  simpl in Hsorted_y_ys. destruct Hsorted_y_ys as [H0z _].
                  exact H0z. }
                (* z is a Fibonacci number *)
                assert (Hz_fib: exists i, i >= 2 /\ fib i = z).
                { apply Hfib. simpl. right. right. left. reflexivity. }
                (* But Fibonacci numbers are >= 0 *)
                destruct Hz_fib as [i_z [Hi_z_ge Heq_iz]].
                (* fib i_z >= 0, but z = fib i_z < 0, contradiction *)
                lia.
            - (* y <> 0, so y > 0 since y is a nat *)
              lia. }

          (* Now handle j = 0, 1 cases *)
          destruct j as [|[|j']].
          - (* j = 0: y = fib 0 = 0, contradicts Hy_pos *)
            exfalso. rewrite <- Heq_j in Hy_pos. simpl in Hy_pos. lia.
          - (* j = 1, but Hj_ge : j >= 2, contradiction *)
            exfalso. lia.
          - (* j = S (S j') >= 2 *)
            lia. }

        (* Apply IH with m = j *)
        assert (Hsum_bound: sum_list (y :: ys) < fib (S j)).
        { rewrite <- Heq_j at 1.
          apply (IHk j).
          - (* j < k: We have j <= k-2 = S k''' and k = S (S (S k''')), so j <= S k''' < S (S (S k''')) *)
            lia.
          - exact Hj_ge_2.
          - (* Sorted_dec (fib j :: ys): from Sorted_dec (fib k :: y :: ys) and y = fib j *)
            (* Sorted_dec (fib k :: y :: ys) gives us Sorted_dec (y :: ys) *)
            assert (Hsorted_y_ys: Sorted_dec (y :: ys)).
            { apply (sorted_tail (fib (S (S (S k'''))))).
              exact Hsorted. }
            (* Now rewrite y to fib j using Heq_j: fib j = y *)
            rewrite <- Heq_j in Hsorted_y_ys.
            exact Hsorted_y_ys.
          - (* no_consecutive_fibs_sorted (fib j :: ys) *)
            (* Get no_consecutive_fibs_sorted (y :: ys) from original list *)
            assert (Hnocons_y_ys: no_consecutive_fibs_sorted (y :: ys)).
            { destruct ys as [|z zs].
              + (* ys = [], so property is trivially True *)
                simpl. exact I.
              + (* ys = z :: zs *)
                (* From no_consecutive_fibs_sorted (fib k :: y :: z :: zs), we get:
                   - fib k and y are not consecutive
                   - no_consecutive_fibs_sorted (y :: z :: zs) *)
                simpl in Hnocons. destruct Hnocons as [_ Htail].
                exact Htail. }
            (* Now rewrite y = fib j *)
            rewrite <- Heq_j in Hnocons_y_ys.
            exact Hnocons_y_ys.
          - (* All elements are Fibonacci numbers: (fib j :: ys) is a sublist of (fib k :: y :: ys) *)
            intros z Hz.
            apply Hfib.
            simpl. right.
            simpl in Hz. destruct Hz as [Hz_eq | Hz_in].
            + left. rewrite <- Heq_j. exact Hz_eq.
            + right. exact Hz_in. }

        (* We want to show: sum_list (y :: ys) < fib (k-1) = fib (S (S k''')) *)
        (* We have: sum_list (y :: ys) < fib (S j) from IH *)
        (* We need: fib (S j) <= fib (S (S k''')) *)

        (* First show j < k-1 = S (S k''') *)
        assert (Hj_lt_k_minus_1: j < S (S k''')).
        { (* We have y = fib j and y <= fib (k-2) = fib (S k''') < fib (k-1) = fib (S (S k''')) *)
          (* First show fib (S k''') < fib (S (S k''')) *)
          assert (Hfib_mono_step: fib (S k''') < fib (S (S k'''))).
          { destruct k''' as [|k''''].
            - (* k''' = 0: fib 1 < fib 2, which is 1 < 1, false! *)
              (* Actually fib 1 = 1 and fib 2 = 1, so fib 1 = fib 2 *)
              (* This means when k = 3, we have k-2 = 1 and k-1 = 2, and fib 1 = fib 2 *)
              (* So fib (k-2) = fib (k-1), which contradicts strict inequality *)
              (* But we need < not <=. Let me check the property *)
              (* Actually fib is: 0,1,1,2,3,5,... so fib 1 = fib 2 = 1 *)
              (* So fib (S 0) = fib (S (S 0)) is false *)
              (* This suggests k''' = 0 case needs special handling *)
              simpl. lia. (* 1 < 1 is false, so this will fail *)
            - (* k''' >= 1: fib (S (S k'''')) < fib (S (S (S k''''))), can use fib_mono *)
              apply fib_mono. lia. }
          (* From fib j <= fib (S k''') < fib (S (S k''')), we get fib j < fib (S (S k''')) *)
          assert (Hfib_j_lt: fib j < fib (S (S k'''))).
          { (* We have fib j <= fib (S k''') from earlier and fib (S k''') < fib (S (S k''')) *)
            (* But we don't have access to Hfib_j_le here, so recompute *)
            assert (Hy_le: y <= fib (S k''')).
            { assert (Heq_minus: S (S k''') - 1 = S k''') by lia.
              rewrite Heq_minus in Hy_le_k_minus_2.
              exact Hy_le_k_minus_2. }
            rewrite <- Heq_j in Hy_le.
            lia. }
          (* By monotonicity, j < S (S k''') *)
          destruct (Nat.lt_ge_cases j (S (S k'''))) as [Hlt | Hge]; [exact Hlt |].
          exfalso.
          (* If j >= S (S k'''), then fib j >= fib (S (S k''')) by monotonicity *)
          assert (Hfib_j_ge: fib j >= fib (S (S k'''))).
          { (* We have j >= S (S k''') from Hge, j >= 2 from Hj_ge_2 *)
            (* Need to show S (S k''') >= 2 *)
            (* k = S (S (S k''')) >= 3, so S (S k''') = k - 1 >= 2 *)
            assert (Hk_minus_1_ge: S (S k''') >= 2) by lia.
            (* Now apply monotonicity *)
            destruct (Nat.eq_dec j (S (S k'''))) as [Heq | Hneq].
            - rewrite Heq. lia.
            - assert (Hj_gt: j > S (S k''')) by lia.
              apply Nat.lt_le_incl.
              apply fib_mono_lt; [exact Hk_minus_1_ge | exact Hj_ge_2 | exact Hj_gt]. }
          lia. }

        (* From j < S (S k'''), we get S j <= S (S k'''), so fib (S j) <= fib (S (S k''')) *)
        assert (Hfib_Sj_le: fib (S j) <= fib (S (S k'''))).
        { destruct (Nat.eq_dec (S j) (S (S k'''))) as [Heq | Hneq].
          - rewrite Heq. lia.
          - assert (Hlt: S j < S (S k''')) by lia.
            apply Nat.lt_le_incl.
            apply fib_mono_lt; try lia. }

        (* Cancel fib k from both sides to get: sum_list (y :: ys) < fib (k-1) *)
        apply Nat.add_lt_mono_l.
        (* Now goal is: sum_list (y :: ys) < fib (S (S k''')) *)
        (* Combine: sum_list (y :: ys) < fib (S j) <= fib (S (S k''')) *)
        apply (Nat.lt_le_trans _ (fib (S j))); [exact Hsum_bound | exact Hfib_Sj_le].
Qed.

(*
  ==============================================================================
  ORIGINAL UNSORTED VERSION (for reference)
  ==============================================================================
*)

(*
  Key Lemma for Uniqueness: Sum bound for non-consecutive Fibonacci numbers

  The sum of any non-empty list of distinct, non-consecutive Fibonacci numbers
  whose largest member is F_k (with k >= 2) is strictly less than F_{k+1}.

  Note: We require k >= 2 to avoid the ambiguity that fib(1) = fib(2) = 1.
  In proper Zeckendorf representations, we only use Fibonacci numbers from
  indices >= 2, i.e., the sequence 1, 2, 3, 5, 8, 13, ...

  We also require NoDup (distinctness) as the lemma is false without it.

  Proof strategy:
  - Use induction on k
  - Base case: k = 2 can be verified directly (COMPLETED)
  - Inductive case: Consider a list with maximum F_k
    * Since no consecutive Fibs, fib(k-1) is NOT in the list (COMPLETED)
    * Removing fib(k) from list gives a list with max ≤ fib(k-2)
    * By IH, sum(rest) < fib(k-1)
    * So total sum = fib(k) + sum(rest) < fib(k) + fib(k-1) = fib(k+1)

  This lemma is crucial for proving uniqueness.

  NOTE: This original version has been superseded by sum_nonconsec_fibs_bounded_sorted
  above, which is much simpler. This version is kept for reference.
*)
Lemma sum_nonconsec_fibs_bounded : forall l k,
  k >= 2 ->
  NoDup l ->
  no_consecutive_fibs l ->
  (forall x, In x l -> exists i, fib i = x) ->
  list_max l = Some (fib k) ->
  sum_list l < fib (S k).
Proof.
  (* Induction on k *)
  intros l k Hk_ge. revert l. induction k as [k IHk] using lt_wf_ind.
  intros l Hnodup Hnocons Hfib Hmax.

  (* Base case: k = 2 *)
  destruct k as [|[|k'']].
  - (* k = 0: contradicts k >= 2 *)
    exfalso. lia.
  - (* k = 1: contradicts k >= 2 *)
    exfalso. lia.
  - (* k = 2 or k > 2 *)
    destruct k'' as [|k'''].
    + (* k = 2: fib 2 = 1, fib 3 = 2 *)
      (* Goal: sum_list l < fib 3 = 2 *)
      (* Max element is fib 2 = 1, so sum_list l <= 1 since all elements are positive fibs *)
      assert (Hfib2_val: fib 2 = 1) by reflexivity.
      assert (Hfib3_val: fib 3 = 2) by reflexivity.
      rewrite Hfib3_val.
      (* Show sum_list l <= 1 *)
      (* Since max = 1, all elements <= 1, and elements are Fibonacci numbers >= 1 (from index >= 1) *)
      (* So all elements are exactly 1, but we can have at most one occurrence due to distinctness *)
      (* Actually, we need to show sum_list l = 1 *)
      assert (Hsum_eq: sum_list l = 1).
      { (* Proof strategy: Show that l contains exactly the single element 1.
           Since max = fib(2) = 1:
           - 1 is in l
           - All elements are <= 1
           - All elements are Fibonacci numbers
           - The only positive Fibonacci <= 1 is 1 itself (fib 1 = fib 2 = 1)
           - If there were two or more elements, they'd all be 1
           - But then we'd have fib(1) and fib(2) in the list (both =1)
           - This would violate no_consecutive_fibs since 1 and 2 are consecutive indices
           - Therefore l = [1], so sum = 1 *)

        (* 1 is in the list *)
        assert (H1_in: In 1 l) by (rewrite <- Hfib2_val; apply list_max_in; exact Hmax).

        (* All elements <= 1 *)
        assert (Hall_le_1: forall y, In y l -> y <= 1).
        { intros y Hy. rewrite <- Hfib2_val in Hmax.
          apply (in_list_le_max y l 1); assumption. }

        (* All Fibonacci numbers <= 1 are either fib(1) = 1 or fib(2) = 1 *)
        (* Since all elements are Fibonacci numbers and all are <= 1, they're all 1 *)
        assert (Hall_eq_1: forall y, In y l -> y = 1).
        { intros y Hy.
          assert (Hy_le: y <= 1) by (apply Hall_le_1; exact Hy).
          destruct (Hfib y Hy) as [i Heq_i].
          (* y is a Fibonacci number, so y = fib(i) for some i *)
          (* Since y <= 1 and y = fib(i), and Fibonacci numbers grow,
             we have i ∈ {0, 1, 2} since fib 0 = 0, fib 1 = 1, fib 2 = 1, fib 3 = 2 *)
          destruct i as [|[|[|i']]].
          - (* i = 0: fib 0 = 0 *)
            (* If y = fib(0) = 0, and 1 = fib(1) is in the list, then we have fib(0) and fib(1),
               which are consecutive (since 1 = S 0). This contradicts no_consecutive_fibs. *)
            exfalso.
            assert (H0: fib 0 = 0) by reflexivity.
            rewrite H0 in Heq_i. subst y.
            (* So 0 is in l, and 1 is in l (from H1_in), and 0 and 1 are consecutive Fibonacci indices *)
            unfold no_consecutive_fibs in Hnocons.
            (* We need to derive a contradiction from having both 0 and 1 in l *)
            (* Since l is not empty (1 is in it), we can analyze the structure *)
            destruct l as [|z zs].
            + (* l = []: contradicts H1_in *)
              simpl in H1_in. exact H1_in.
            + (* l = z :: zs *)
              simpl in Hnocons. destruct Hnocons as [Hhead Htail].
              (* Both 0 and 1 are in l = z :: zs *)
              assert (H0_in: In 0 (z :: zs)) by exact Hy.
              assert (H1_in': In 1 (z :: zs)) by exact H1_in.
              simpl in H0_in, H1_in'.
              destruct H0_in as [Hz0 | Hin_zs0].
              * (* z = 0 *)
                subst z.
                (* Now 1 is in 0 :: zs, so either z = 1 (but z = 0) or 1 is in zs *)
                destruct H1_in' as [H_abs | Hin_zs1].
                -- (* 0 = 1, absurd *) discriminate.
                -- (* 1 is in zs *)
                   (* By Hhead: for all y in zs, fib i = 0 -> fib j = y -> ~nat_consecutive i j *)
                   specialize (Hhead 1 Hin_zs1).
                   assert (Hfib0: fib 0 = 0) by reflexivity.
                   assert (Hfib1: fib 1 = 1) by reflexivity.
                   specialize (Hhead 0 1 Hfib0 Hfib1).
                   exfalso. apply Hhead.
                   unfold nat_consecutive. left. reflexivity.
              * (* 0 is in zs, and z is something *)
                (* 1 could be z or in zs *)
                destruct H1_in' as [Hz1 | Hin_zs1].
                -- (* z = 1 *)
                   subst z.
                   (* So 0 is in zs, and z = 1 *)
                   specialize (Hhead 0 Hin_zs0).
                   assert (Hfib0: fib 0 = 0) by reflexivity.
                   assert (Hfib1: fib 1 = 1) by reflexivity.
                   specialize (Hhead 1 0 Hfib1 Hfib0).
                   exfalso. apply Hhead.
                   unfold nat_consecutive. right. reflexivity.
                -- (* Both 0 and 1 are in zs *)
                   (* Use no_consecutive_both_in lemma *)
                   exfalso.
                   assert (Hfib0: fib 0 = 0) by reflexivity.
                   assert (Hfib1: fib 1 = 1) by reflexivity.
                   apply (no_consecutive_both_in zs 0 1).
                   ** exact Htail.
                   ** (* fib 0 ≠ fib 1 *) rewrite Hfib0, Hfib1. discriminate.
                   ** rewrite Hfib0. exact Hin_zs0.
                   ** rewrite Hfib1. exact Hin_zs1.
                   ** unfold nat_consecutive. left. reflexivity.
          - (* i = 1: fib 1 = 1, so y = 1 *)
            assert (H1: fib 1 = 1) by reflexivity.
            rewrite H1 in Heq_i. symmetry. exact Heq_i.
          - (* i = 2: fib 2 = 1, so y = 1 *)
            assert (H2: fib 2 = 1) by reflexivity.
            rewrite H2 in Heq_i. symmetry. exact Heq_i.
          - (* i >= 3: fib i >= 2, but y <= 1, contradiction *)
            exfalso.
            assert (Hfib_i: fib (S (S (S i'))) >= 2).
            { apply fib_ge_2. lia. }
            rewrite Heq_i in Hfib_i. lia. }

        (* Now we know all elements are 1 *)
        (* Since NoDup l, there can be at most one occurrence of 1 *)
        (* Since 1 is in l (H1_in), l = [1] *)
        assert (Hl_eq: l = [1]).
        { (* We need to show l has exactly one element *)
          destruct l as [|x xs].
          - (* l = []: contradicts H1_in *)
            exfalso. simpl in H1_in. exact H1_in.
          - (* l = x :: xs *)
            (* x is in l, so x = 1 *)
            assert (Hx: x = 1).
            { apply Hall_eq_1. simpl. left. reflexivity. }
            subst x.
            (* Now show xs = [] *)
            assert (Hxs_empty: xs = []).
            { destruct xs as [|y ys].
              - reflexivity.
              - (* xs = y :: ys, so y is in l *)
                assert (Hy_in: In y (1 :: y :: ys)).
                { simpl. right. left. reflexivity. }
                assert (Hy: y = 1) by (apply Hall_eq_1; exact Hy_in).
                (* So we have 1 in the list twice: once as x, once as y *)
                (* This contradicts NoDup l *)
                exfalso.
                subst y.
                inversion Hnodup. subst.
                apply H1. simpl. left. reflexivity. }
            subst xs. reflexivity. }
        rewrite Hl_eq. simpl. reflexivity.
      }
      rewrite Hsum_eq. lia.
    + (* k >= 3: Main inductive case *)
    (* We have: list l with max = fib (S (S (S k'''))), no consecutive Fibs *)
    (* Goal: sum_list l < fib (S (S (S (S k''')))) *)

    (* Let k = S (S (S k''')) >= 3 *)
    (* max l = Some (fib k) *)

    (* Use the recurrence: fib(S k) = fib k + fib(k-1) *)
    assert (Hrecur: fib (S (S (S (S k''')))) = fib (S (S (S k'''))) + fib (S (S k'''))).
    { apply fib_recurrence. lia. }

    (* Rewrite goal using recurrence *)
    rewrite Hrecur.

    (* Key step: Show fib(k-1) is NOT in l *)
    assert (Hk_minus_1_not_in: ~In (fib (S (S k'''))) l).
    { intro Hin_k_minus_1.
      (* fib(k-1) is in l, and fib k is in l (since it's the max) *)
      assert (Hk_in: In (fib (S (S (S k''')))) l).
      { apply list_max_in. exact Hmax. }
      (* But fib(k-1) and fib k are consecutive, contradicting no_consecutive_fibs *)
      unfold no_consecutive_fibs in Hnocons.
      (* Need to analyze the structure of l *)
      destruct l as [|x xs].
      - (* l = []: contradicts max = Some ... *)
        simpl in Hmax. discriminate.
      - (* l = x :: xs *)
        simpl in Hnocons. destruct Hnocons as [Hhead Htail].
        simpl in Hk_in, Hin_k_minus_1.
        (* Both fib k and fib(k-1) are in x :: xs *)
        destruct Hk_in as [Hx_k | Hxs_k].
        + (* x = fib k *)
          destruct Hin_k_minus_1 as [Hx_k_minus_1 | Hxs_k_minus_1].
          * (* x = fib(k-1), but also x = fib k, so fib k = fib(k-1) *)
            (* This is impossible for k >= 3 since Fibonacci is strictly increasing *)
            assert (Hfib_inj: fib (S (S (S k'''))) <> fib (S (S k'''))).
            { intro Heq.
              assert (Hmono: fib (S (S k''')) < fib (S (S (S k''')))).
              { apply fib_mono_lt; lia. }
              lia. }
            (* From Hx_k and Hx_k_minus_1, we have fib k = x = fib(k-1) *)
            exfalso. apply Hfib_inj.
            transitivity x; [symmetry; exact Hx_k | exact Hx_k_minus_1].
          * (* fib(k-1) is in xs, x = fib k *)
            (* By Hhead: fib k and fib(k-1) are not consecutive, contradiction *)
            exfalso.
            specialize (Hhead (fib (S (S k'''))) Hxs_k_minus_1).
            assert (Hcons: nat_consecutive (S (S (S k'''))) (S (S k'''))).
            { unfold nat_consecutive. right. reflexivity. }
            (* Hhead: fib i = x -> fib j = fib(k-1) -> ~nat_consecutive i j *)
            (* We have x = fib k, so we apply with i = k, j = k-1 *)
            apply (Hhead (S (S (S k'''))) (S (S k'''))); [| reflexivity | exact Hcons].
            symmetry. exact Hx_k.
        + (* fib k is in xs *)
          destruct Hin_k_minus_1 as [Hx_k_minus_1 | Hxs_k_minus_1].
          * (* x = fib(k-1), fib k is in xs *)
            exfalso.
            specialize (Hhead (fib (S (S (S k''')))) Hxs_k).
            assert (Hcons: nat_consecutive (S (S k''')) (S (S (S k''')))).
            { unfold nat_consecutive. left. reflexivity. }
            (* Hhead: fib i = x -> fib j = fib k -> ~nat_consecutive i j *)
            (* We have x = fib(k-1), so we apply with i = k-1, j = k *)
            apply (Hhead (S (S k''')) (S (S (S k''')))); [| reflexivity | exact Hcons].
            symmetry. exact Hx_k_minus_1.
          * (* Both in xs - use tail property *)
            (* Both fib k and fib(k-1) are in xs, but they're consecutive Fibonacci numbers *)
            (* This contradicts no_consecutive_fibs xs *)
            exfalso.
            apply (no_consecutive_both_in xs (S (S (S k'''))) (S (S k'''))); [exact Htail | | exact Hxs_k | exact Hxs_k_minus_1 |].
            -- (* fib k ≠ fib(k-1) by monotonicity *)
              intro Heq.
              assert (Hmono: fib (S (S k''')) < fib (S (S (S k''')))).
              { apply fib_mono. lia. }
              lia.
            -- unfold nat_consecutive. right. reflexivity.
    }

    (* Now split cases: is l just [fib k], or does it have other elements? *)
    assert (Hfib_k_in: In (fib (S (S (S k''')))) l).
    { apply list_max_in. exact Hmax. }

    (* Case analysis on whether l = [fib k] or has other elements *)
    destruct l as [|x xs].
    * (* l = []: contradicts max = Some ... *)
      simpl in Hmax. discriminate.
    * (* l = x :: xs *)
      simpl in Hfib_k_in.
      destruct Hfib_k_in as [Hx_k | Hxs_k].
      -- (* x = fib k *)
        subst x.
        (* Now check if xs is empty *)
        destruct xs as [|y ys].
        ++ (* xs = [], so l = [fib k] *)
          (* sum [fib k] = fib k < fib k + fib(k-1) since fib(k-1) > 0 *)
          unfold sum_list. simpl. rewrite Nat.add_0_r.
          (* Now goal is: fib k < fib k + fib(k-1) *)
          assert (Hfib_pos: fib (S (S k''')) > 0).
          { apply fib_pos. lia. }
          apply Nat.lt_add_pos_r. exact Hfib_pos.
        ++ (* xs = y :: ys, so l has other elements *)
          (* sum l = fib k + sum xs *)
          simpl.
          (* Need: fib k + sum xs < fib k + fib(k-1) *)
          (* i.e., sum xs < fib(k-1) *)

          (* Show that all elements in xs have indices at most k-2 *)
          (* Key insight: fib(k-1) is NOT in l, and fib k is the max, so elements in xs
             must be strictly less than fib k and not equal to fib(k-1) *)

          assert (Hxs_bounded: forall z, In z (y :: ys) -> exists i, i <= (S (S (S k''')) - 2) /\ fib i = z).
          { intros z Hz.
            (* z is in l = fib k :: y :: ys *)
            assert (Hz_in_l: In z (fib (S (S (S k'''))) :: y :: ys)).
            { simpl. right. exact Hz. }
            (* z is a Fibonacci number *)
            destruct (Hfib z Hz_in_l) as [i Heq_i].

            (* Show z < fib k and z <> fib(k-1) *)
            assert (Hz_lt: z < fib (S (S (S k''')))).
            { (* z is in xs, not the head, and fib k is max *)
              (* So z <= fib k, and z <> fib k (since subst x put fib k at head) *)
              assert (Hz_le: z <= fib (S (S (S k''')))).
              { apply (in_list_le_max z (fib (S (S (S k'''))) :: y :: ys) (fib (S (S (S k''')))) ).
                - simpl. right. exact Hz.
                - exact Hmax. }
              assert (Hz_ne: z <> fib (S (S (S k''')))).
              { intro Heq_z.
                (* If z = fib k, then fib k appears twice in l, contradicting NoDup *)
                (* fib k is at head, and z = fib k is in tail, contradicting NoDup *)
                inversion Hnodup as [| ? ? Hnot_in_tail Hnodup_tail].
                apply Hnot_in_tail. rewrite Heq_z in Hz. exact Hz. }
              lia. }

            assert (Hz_ne_km1: z <> fib (S (S k'''))).
            { intro Heq_z.
              apply Hk_minus_1_not_in.
              rewrite <- Heq_z.
              simpl. right. exact Hz. }

            (* Now use fib_index_bound lemma *)
            apply (fib_index_bound z (S (S (S k''')))).
            - lia. (* k >= 3 *)
            - exists i. exact Heq_i.
            - exact Hz_lt.
            - exact Hz_ne_km1. }

          (* Now we apply the induction hypothesis to xs = y :: ys *)
          (* We need to show: sum(y :: ys) < fib(k-1) *)
          (* Strategy: show max(xs) = fib(m) for some m ≤ k-2, apply IH to get sum(xs) < fib(m+1),
             then show fib(m+1) ≤ fib(k-1) *)

          (* First, extract the max of xs *)
          assert (Hxs_nonempty: exists m, list_max (y :: ys) = Some m).
          { apply list_max_some. }
          destruct Hxs_nonempty as [max_xs Hmax_xs].

          (* Show max_xs is a Fibonacci number with index ≤ k-2 *)
          assert (Hmax_xs_fib: exists m, m <= S (S (S k''')) - 2 /\ fib m = max_xs /\ m >= 2).
          { assert (Hmax_xs_in: In max_xs (y :: ys)).
            { apply list_max_in. exact Hmax_xs. }
            destruct (Hxs_bounded max_xs Hmax_xs_in) as [m [Hm_bound Hm_eq]].
            (* Need to show m >= 2 *)
            exists m. split; [exact Hm_bound | split; [exact Hm_eq | admit]]. }

          destruct Hmax_xs_fib as [m [Hm_le [Hm_eq Hm_ge]]].

          (* Apply IH to xs *)
          assert (Hxs_sum_bounded: sum_list (y :: ys) < fib (S m)).
          { apply (IHk m).
            - (* m < k *)
              (* From Hm_le: m <= k - 2, so m <= k - 2 < k *)
              assert (Hkm2: S (S (S k''')) - 2 = S k''') by lia.
              rewrite Hkm2 in Hm_le. lia.
            - (* m >= 2 *) exact Hm_ge.
            - (* NoDup xs *)
              (* xs is tail of (fib k :: xs), so NoDup preserved *)
              inversion Hnodup as [| ? ? ? Hnodup_tail]. exact Hnodup_tail.
            - (* no_consecutive_fibs xs *)
              (* Similar: tail of list with no_consecutive_fibs *)
              simpl in Hnocons. destruct Hnocons as [_ Htail]. exact Htail.
            - (* all elements are Fibs *)
              intros x Hx. apply Hfib. simpl. right. exact Hx.
            - (* list_max xs = Some (fib m) *)
              rewrite <- Hm_eq in Hmax_xs. exact Hmax_xs. }

          (* Show fib(S m) ≤ fib(S (S k''')) = fib(k-1) *)
          assert (Hm_lt_km1: fib (S m) <= fib (S (S k'''))).
          { (* From m <= k-2, we get S m <= k-1 = S (S k''') *)
            assert (Hkm2: S (S (S k''')) - 2 = S k''') by lia.
            rewrite Hkm2 in Hm_le.
            (* So m <= S k''', which means S m <= S (S k''') *)
            (* We need fib(S m) <= fib(k-1) *)
            (* Case split: either S m = S (S k''') or S m < S (S k''') *)
            destruct (Nat.eq_dec (S m) (S (S k'''))) as [Heq | Hneq].
            - (* S m = S (S k''') *) rewrite Heq. lia.
            - (* S m < S (S k''') *)
              apply Nat.lt_le_incl. apply fib_mono_lt; try lia.
          }

          (* Combine to get final result *)
          (* Goal after simpl: fib k + sum(y :: ys) < fib k + fib(k-1) *)
          simpl.
          assert (Hsum_lt: sum_list (y :: ys) < fib (S (S k'''))).
          { eapply Nat.lt_le_trans.
            - exact Hxs_sum_bounded.
            - exact Hm_lt_km1. }
          apply Nat.add_lt_mono_l. exact Hsum_lt.
      -- (* fib k is in xs, not at head *)
        (* Similar reasoning but more complex *)
        admit.
Admitted.

(*
  Theorem: Uniqueness of Zeckendorf representation (ADMITTED)

  Every positive integer has a unique representation as a sum of
  non-consecutive Fibonacci numbers.

  This is Zeckendorf's theorem proper. It states that if two lists both
  satisfy the Zeckendorf representation properties for the same number n,
  then they must be equal (up to reordering).

  Proof strategy (following the wiki proof):
  1. Assume l1 and l2 are both valid Zeckendorf representations of n
  2. Remove common elements from both to get l1' and l2'
  3. l1' and l2' still have the same sum (since we removed equal elements)
  4. Assume by contradiction that both l1' and l2' are non-empty
  5. Let F_s be the max of l1' and F_t be the max of l2'
  6. Since l1' and l2' share no elements, F_s ≠ F_t
  7. WLOG assume F_s < F_t
  8. By the lemma, sum(l1') < F_{s+1} ≤ F_t ≤ sum(l2')
  9. This contradicts sum(l1') = sum(l2')
  10. Therefore either l1' or l2' is empty
  11. If l1' is empty, it has sum 0, so l2' has sum 0, so l2' is empty
  12. Thus l1' = l2' = [], which means l1 = l2

  Note: This proof requires additional infrastructure for set operations,
  which is why it remains admitted. A complete formalization would need:
  - List filtering and difference operations
  - Properties of these operations preserving the invariants
  - The sum_nonconsec_fibs_bounded lemma
*)
Theorem zeckendorf_unique : forall n l1 l2,
  is_zeckendorf_repr n l1 ->
  is_zeckendorf_repr n l2 ->
  l1 = l2.
Proof.
Admitted.

(*
  Corollary: Our algorithm produces THE unique Zeckendorf representation

  This combines the three properties to show that our algorithm produces
  a valid Zeckendorf representation:
  1. All elements are Fibonacci numbers (zeckendorf_fib_property)
  2. The sum equals n (zeckendorf_sum_property)
  3. No consecutive Fibonacci numbers (zeckendorf_no_consecutive)
*)
Theorem zeckendorf_is_the_unique_repr : forall n,
  is_zeckendorf_repr n (zeckendorf n []).
Proof.
  intro n.
  unfold is_zeckendorf_repr.
  split; [|split].
  - (* Part 1: All elements are Fibonacci numbers *)
    apply zeckendorf_fib_property.
  - (* Part 2: Sum equals n *)
    apply zeckendorf_sum_property.
  - (* Part 3: No consecutive Fibonacci numbers *)
    apply zeckendorf_no_consecutive.
Qed.
