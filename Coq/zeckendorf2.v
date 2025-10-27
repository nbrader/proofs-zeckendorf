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

Require Import Zeckendorf.zeckendorf.

Fixpoint zeck_lists (n : nat) : list (list nat) :=
  match n with
  | 0 => [[]]
  | S n1 =>
      (* n1 = n - 1 *)
      match n1 with
      | 0 => [ []; [1] ]
      | S n2 =>
          (* n2 = n - 2 *)
          let part1 := zeck_lists n1 in    (* recursive on n-1 *)
          let part2 := map (fun xs => fib (n2 + 3) :: xs) (zeck_lists n2) in
          part1 ++ part2
      end
  end.

(*
  It should be very easy to prove the zeckendorf theorem using zeck which is implemented with zeck_lists.

  1.
  The zeckendorf representation only includes fibonacci numbers because zeck_lists only adds fibonacci numbers.

  2.
  The zeckendorf representation only includes non-consecutive fibonacci numbers because:
  - The largest fibonacci number is only consed on to lists that themselves are non-consecutive and
  - The fibonacci number consed is the fibonacci number after the next fibonacci number after the largest fibonacci number in the list being consed onto.
       - This can be seen in the line: let part2 := map (fun xs => fib (n2 + 3) :: xs) (zeck_lists n2) in
  
  3.
  Every integer has a zeckendorf representation because every iteration simply re-adds the representations from two iterations ago plus exactly the least number required to not repeat an existing total.
*)

Fixpoint find_fib_index_aux (n k b : nat) : nat :=
  match b with
  | 0 => k
  | S b' =>
      if (fib (S k) <=? n)
      then find_fib_index_aux n (S k) b'
      else k
  end.

Definition min_level_for_index (n : nat) : nat :=
  (* use budget S n: more than enough because fib grows and index ≤ n always *)
  find_fib_index_aux n 0 (S n).

Definition zeck (n : nat) : list nat :=
  let m := min_level_for_index n in
  let all := zeck_lists (m-1) in
  nth n all [].

(* =============================================================================
   PROOF OF ZECKENDORF'S THEOREM USING zeck_lists
   =============================================================================

   The key insight of this proof is that zeck_lists constructs all valid
   Zeckendorf representations by a recursive combinatorial construction:

   - zeck_lists(n) includes all representations from zeck_lists(n-1)
   - Plus: fib(n+2) consed onto each representation from zeck_lists(n-2)

   This ensures non-consecutiveness because we skip exactly one Fibonacci number.
*)

(* -----------------------------------------------------------------------------
   Helper Lemmas and Definitions
   -------------------------------------------------------------------------- *)

(* Sum of a list *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

(* All elements in list are Fibonacci numbers *)
Definition all_fibs (l : list nat) : Prop :=
  forall x, In x l -> exists k, k >= 1 /\ fib k = x.

(* Predicate: two Fibonacci indices are consecutive *)
Definition fib_consecutive (k1 k2 : nat) : Prop :=
  k2 = S k1 \/ k1 = S k2.

(* List contains no consecutive Fibonacci numbers *)
Fixpoint no_consecutive_fibs (l : list nat) : Prop :=
  match l with
  | [] => True
  | x :: xs =>
    (forall y, In y xs ->
      forall i j, fib i = x -> fib j = y -> ~fib_consecutive i j) /\
    no_consecutive_fibs xs
  end.

(* -----------------------------------------------------------------------------
   Properties of zeck_lists
   -------------------------------------------------------------------------- *)

(* Lemma: All lists in zeck_lists n contain only Fibonacci numbers *)
Lemma zeck_lists_all_fibs : forall n l,
  In l (zeck_lists n) ->
  all_fibs l.
Proof.
  induction n as [|n1 IHn1]; intros l Hin.
  - (* n = 0: zeck_lists 0 = [[]] *)
    simpl in Hin. destruct Hin as [Heq | Hfalse].
    + (* l = [] *)
      subst. unfold all_fibs. intros x Hin_x. inversion Hin_x.
    + (* impossible *)
      inversion Hfalse.
  - (* n = S n1 *)
    destruct n1 as [|n2].
    + (* n1 = 0, so n = 1: zeck_lists 1 = [[], [1]] *)
      simpl in Hin. destruct Hin as [Heq | [Heq | Hfalse]].
      * (* l = [] *)
        subst. unfold all_fibs. intros x Hin_x. inversion Hin_x.
      * (* l = [1] *)
        subst. unfold all_fibs. intros x Hin_x.
        simpl in Hin_x. destruct Hin_x as [Heq | Hfalse].
        -- subst x. exists 1. split. lia. reflexivity.
        -- inversion Hfalse.
      * inversion Hfalse.
    + (* n = S (S n2), general case *)
      simpl in Hin.
      apply in_app_or in Hin. destruct Hin as [Hin1 | Hin2].
      * (* l is from part1 = zeck_lists (S n2) *)
        apply IHn1. exact Hin1.
      * (* l is from part2 = map (fun xs => fib (n2 + 3) :: xs) (zeck_lists n2) *)
        apply in_map_iff in Hin2.
        destruct Hin2 as [xs [Heq Hin_xs]].
        subst l. unfold all_fibs. intros x Hin_x.
        simpl in Hin_x. destruct Hin_x as [Heq | Hin_xs'].
        -- (* x = fib (n2 + 3) *)
          subst x. exists (n2 + 3). split. lia. reflexivity.
        -- (* x is in xs *)
          apply IHn1 in Hin_xs.
          unfold all_fibs in Hin_xs.
          apply Hin_xs. exact Hin_xs'.
Qed.

(* Lemma: All lists in zeck_lists n have non-consecutive Fibonacci numbers *)
Lemma zeck_lists_no_consecutive : forall n l,
  In l (zeck_lists n) ->
  no_consecutive_fibs l.
Proof.
  induction n as [|n1 IHn1]; intros l Hin.
  - (* n = 0: zeck_lists 0 = [[]] *)
    simpl in Hin. destruct Hin as [Heq | Hfalse].
    + subst. simpl. trivial.
    + inversion Hfalse.
  - (* n = S n1 *)
    destruct n1 as [|n2].
    + (* n = 1: zeck_lists 1 = [[], [1]] *)
      simpl in Hin. destruct Hin as [Heq | [Heq | Hfalse]].
      * subst. simpl. trivial.
      * subst. simpl. split; [|trivial].
        intros y Hin_y. inversion Hin_y.
      * inversion Hfalse.
    + (* n = S (S n2), general case *)
      simpl in Hin.
      apply in_app_or in Hin. destruct Hin as [Hin1 | Hin2].
      * (* l from part1 *)
        apply IHn1. exact Hin1.
      * (* l from part2: fib(n2+3) :: xs where xs from zeck_lists n2 *)
        apply in_map_iff in Hin2.
        destruct Hin2 as [xs [Heq Hin_xs]].
        subst l.
        (* Need to show: no_consecutive_fibs (fib(n2+3) :: xs) *)
        simpl. split.
        -- (* Show fib(n2+3) is not consecutive with any element in xs *)
          intros y Hin_y i j Heq_i Heq_j Hcons.
          (* Key: elements in xs come from zeck_lists n2, which have max index n2+2 *)
          (* But we're adding fib(n2+3), which is separated by a gap *)
          (* We need a helper lemma about max indices in zeck_lists *)
          admit.
        -- (* xs itself has no consecutive fibs *)
          apply IHn1. exact Hin_xs.
Admitted.

(* Lemma: Count how many lists are in zeck_lists n *)
Lemma zeck_lists_length : forall n,
  length (zeck_lists n) = fib (n + 2).
Proof.
  induction n as [|n1 IHn1].
  - (* n = 0: length [[]] = 1 = fib 2 *)
    simpl. reflexivity.
  - destruct n1 as [|n2].
    + (* n = 1: length [[], [1]] = 2 = fib 3 *)
      simpl. reflexivity.
    + (* n = S (S n2) *)
      simpl. rewrite app_length. rewrite map_length.
      (* length(part1) + length(part2) = length(zeck_lists(S n2)) + length(zeck_lists n2) *)
      rewrite IHn1.
      (* Need IH for n2 *)
      assert (IHn2: length (zeck_lists n2) = fib (n2 + 2)).
      { (* This should follow from IHn1 applied to n2, but we need n2 < S (S n2) *)
        admit.
      }
      rewrite IHn2.
      (* Goal: fib(S n2 + 2) + fib(n2 + 2) = fib(S (S n2) + 2) *)
      replace (S n2 + 2) with (S (S (n2 + 1))) by lia.
      replace (S (S n2) + 2) with (S (S (S (n2 + 1)))) by lia.
      replace (n2 + 2) with (S (n2 + 1)) by lia.
      (* Now we need: fib(n+2) + fib(n+1) = fib(n+3) *)
      (* This is just the Fibonacci recurrence *)
      rewrite <- fib_SS.
      replace (S (S (n2 + 1))) with (S (n2 + 2)) by lia.
      replace (S (S (S (n2 + 1)))) with (S (S (n2 + 2))) by lia.
      reflexivity.
Admitted.

(* Lemma: The sum of the nth list in zeck_lists equals... *)
(* This needs more thought about the indexing scheme *)

(* -----------------------------------------------------------------------------
   Main Theorem
   -------------------------------------------------------------------------- *)

(* For now, let's state what we want to prove *)
Theorem zeckendorf_representation_exists : forall n,
  exists l,
    all_fibs l /\
    no_consecutive_fibs l /\
    sum_list l = n.
Proof.
  intro n.
  (* The idea: use zeck n to get the representation *)
  exists (zeck n).
  admit.
Admitted.
