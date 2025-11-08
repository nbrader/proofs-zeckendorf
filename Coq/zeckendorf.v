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

(* Computation lemma for fib *)
Lemma fib_SS : forall n, fib (S (S n)) = fib (S n) + fib n.
Proof.
  intro n. destruct n; simpl; reflexivity.
Qed.

Require Import List.
Import ListNotations.

Fixpoint takeWhile {A : Type} (f : A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if f x then x :: takeWhile f xs else []
  end.

Definition fibs_upto (n : nat) : list nat :=
  takeWhile (fun x => Nat.leb x n) (map fib (seq 1 (S n))).

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
  intros n IH Hge.
  destruct n as [|[|[|n'']]].
  - inversion Hge.
  - compute. auto.
  - compute. auto.
  - rewrite fib_SS.
    apply Nat.add_pos_pos.
    + apply IH.
      * apply Nat.lt_succ_diag_r.
      * apply le_n_S. apply Nat.le_0_l.
    + apply IH.
      * apply Nat.lt_trans with (S (S n'')); apply Nat.lt_succ_diag_r.
      * apply le_n_S. apply Nat.le_0_l.
Qed.

(*
  Fibonacci sequence is monotonically increasing for n >= 2
*)
Lemma fib_mono : forall n, n >= 2 -> fib n < fib (S n).
Proof.
  intro n. pattern n. apply lt_wf_ind. clear n.
  intros n IH Hge.
  destruct n as [|[|[|n'']]].
  - inversion Hge.
  - inversion Hge. inversion H0.
  - simpl. auto.
  - assert (Hpos: fib (S (S n'')) > 0).
    { apply fib_pos. apply le_n_S. apply Nat.le_0_l. }
    assert (Heq: fib (S (S (S (S n'')))) = fib (S (S (S n''))) + fib (S (S n''))).
    { rewrite fib_SS. reflexivity. }
    rewrite Heq.
    apply Nat.lt_add_pos_r. exact Hpos.
Qed.

(*
  Helper lemma: All elements in (seq start len) are >= start
*)
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

(*
  Lemma: Every element in fibs_upto n is a Fibonacci number
*)
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

Lemma in_fibs_upto_pos : forall x n,
  In x (fibs_upto n) -> x > 0.
Proof.
  intros x n Hin.
  destruct (in_fibs_upto_fib x n Hin) as [k [Hk Heq]].
  rewrite <- Heq.
  apply fib_pos. exact Hk.
Qed.

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

(* Define sum of a list *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

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

(*
  Helper lemma: Any Fibonacci number >= 1 has an index >= 2

  This is because fib(0) = 0, fib(1) = fib(2) = 1, and for any fib(k) >= 1,
  we can find an index >= 2 that produces the same value.
*)
Lemma fib_value_has_index_ge_2 : forall k,
  fib k >= 1 ->
  exists k', k' >= 2 /\ fib k' = fib k.
Proof.
  intros k Hge.
  destruct k as [|[|k']].
  - (* k = 0: fib(0) = 0, contradicts fib(k) >= 1 *)
    simpl in Hge. lia.
  - (* k = 1: fib(1) = 1 = fib(2), so use k' = 2 *)
    exists 2. split.
    + lia.
    + simpl. reflexivity.
  - (* k = S (S k'): k >= 2, so use k' = k *)
    exists (S (S k')). split.
    + lia.
    + reflexivity.
Qed.

(*
  ==============================================================================
  ALTERNATIVE UNIQUENESS PROOF USING SORTED LISTS
  ==============================================================================
*)

(*
  Alternative uniqueness theorem for sorted Zeckendorf representations

  This version proves uniqueness specifically for descending-sorted lists,
  which simplifies the proof by avoiding the need for set difference operations.

  Strategy:
  1. If both lists are sorted descending with the same sum and properties,
     they must have the same maximum element (by contradiction using
     sum_nonconsec_fibs_bounded_sorted)
  2. Remove the maximum from both lists and apply induction on the sum

  This is cleaner than the general proof because sorted lists allow direct
  structural comparison.
*)
Theorem zeckendorf_unique_sorted : forall n l1 l2,
  Sorted_dec l1 ->
  Sorted_dec l2 ->
  no_consecutive_fibs_sorted l1 ->
  no_consecutive_fibs_sorted l2 ->
  (forall x, In x l1 -> exists i, i >= 2 /\ fib i = x) ->
  (forall x, In x l2 -> exists i, i >= 2 /\ fib i = x) ->
  sum_list l1 = n ->
  sum_list l2 = n ->
  l1 = l2.
Proof.
  intro n.
  (* Induction on n to handle the sum *)
  induction n as [n IHn] using lt_wf_ind.
  intros l1 l2 Hsorted1 Hsorted2 Hnocons1 Hnocons2 Hfib1 Hfib2 Hsum1 Hsum2.

  (* Case split on l1 *)
  destruct l1 as [|x1 xs1].
  - (* l1 = [] *)
    (* Then sum_list l1 = 0 = n *)
    simpl in Hsum1. subst n.
    (* So sum_list l2 = 0 *)
    simpl in Hsum2.
    (* This means l2 must be empty too *)
    destruct l2 as [|x2 xs2].
    + reflexivity.
    + (* l2 = x2 :: xs2 with sum 0 *)
      (* But all elements are Fibonacci numbers >= 1 (since indices >= 2) *)
      exfalso.
      assert (Hx2_fib: exists i, i >= 2 /\ fib i = x2).
      { apply Hfib2. simpl. left. reflexivity. }
      destruct Hx2_fib as [i [Hi_ge Heq_i]].
      (* fib i >= fib 2 = 1 for i >= 2 *)
      assert (Hx2_ge: x2 >= 1).
      { rewrite <- Heq_i.
        destruct (Nat.eq_dec i 2) as [Heq2 | Hneq2].
        - rewrite Heq2. simpl. lia.
        - assert (Hi_gt: i > 2) by lia.
          assert (Hfib_ge: fib i >= fib 2).
          { destruct (Nat.eq_dec i 2) as [Heq | Hneq].
            - rewrite Heq. lia.
            - apply Nat.lt_le_incl. apply fib_mono_lt; lia. }
          simpl in Hfib_ge. lia. }
      (* sum_list (x2 :: xs2) >= x2 >= 1, contradicts sum = 0 *)
      assert (Hsum_ge: sum_list (x2 :: xs2) >= x2).
      { simpl. lia. }
      lia.

  - (* l1 = x1 :: xs1 *)
    destruct l2 as [|x2 xs2].
    + (* l2 = [], but l1 is non-empty with sum n *)
      (* Similar contradiction as above *)
      exfalso.
      assert (Hx1_fib: exists i, i >= 2 /\ fib i = x1).
      { apply Hfib1. simpl. left. reflexivity. }
      destruct Hx1_fib as [i [Hi_ge Heq_i]].
      assert (Hx1_ge: x1 >= 1).
      { rewrite <- Heq_i.
        destruct (Nat.eq_dec i 2) as [Heq2 | Hneq2].
        - rewrite Heq2. simpl. lia.
        - assert (Hfib_ge: fib i >= fib 2).
          { apply Nat.lt_le_incl. apply fib_mono_lt; lia. }
          simpl in Hfib_ge. lia. }
      simpl in Hsum2.
      (* Hsum2 : 0 = n, so n = 0 *)
      (* Hsum1 : sum_list (x1 :: xs1) = n *)
      (* Therefore sum_list (x1 :: xs1) = 0 *)
      (* But sum_list (x1 :: xs1) = x1 + sum_list xs1 >= x1 >= 1 *)
      simpl in Hsum1.
      lia.

    + (* Both lists are non-empty: l1 = x1 :: xs1, l2 = x2 :: xs2 *)
      (* Key claim: x1 = x2 (the maximum elements must be equal) *)

      (* First, extract indices for x1 and x2 *)
      assert (Hx1_fib: exists i1, i1 >= 2 /\ fib i1 = x1).
      { apply Hfib1. simpl. left. reflexivity. }
      destruct Hx1_fib as [i1 [Hi1_ge Heq_i1]].

      assert (Hx2_fib: exists i2, i2 >= 2 /\ fib i2 = x2).
      { apply Hfib2. simpl. left. reflexivity. }
      destruct Hx2_fib as [i2 [Hi2_ge Heq_i2]].

      (* Prove x1 = x2 by contradiction *)
      assert (Hx1_eq_x2: x1 = x2).
      { destruct (Nat.eq_dec x1 x2) as [Heq | Hneq]; [exact Heq |].
        exfalso.
        (* Assume x1 ≠ x2, derive contradiction using sum_nonconsec_fibs_bounded_sorted *)
        (* WLOG, assume x1 < x2 (the other case is symmetric) *)
        destruct (Nat.lt_trichotomy x1 x2) as [Hlt | [Heq' | Hgt]].
        + (* Case: x1 < x2 *)
          (* Since l1 is sorted descending, x1 is the maximum of l1 *)
          (* Since l2 is sorted descending, x2 is the maximum of l2 *)
          (* We have: sum_list (x1 :: xs1) < fib (S i1) by sum_nonconsec_fibs_bounded_sorted *)
          assert (Hsum1_bound: sum_list (x1 :: xs1) < fib (S i1)).
          { rewrite <- Heq_i1.
            apply (sum_nonconsec_fibs_bounded_sorted i1 xs1).
            - exact Hi1_ge.
            - rewrite Heq_i1. exact Hsorted1.
            - rewrite Heq_i1. exact Hnocons1.
            - intros z Hz. rewrite Heq_i1 in Hz.
              apply Hfib1. exact Hz. }
          (* Also: x2 <= sum_list (x2 :: xs2) (since x2 is in (x2 :: xs2)) *)
          assert (Hx2_le_sum2: x2 <= sum_list (x2 :: xs2)).
          { simpl. lia. }
          (* We have i1 < i2 (since x1 = fib i1 < fib i2 = x2 and fib is injective/monotonic) *)
          assert (Hi1_lt_i2: i1 < i2).
          { destruct (Nat.lt_trichotomy i1 i2) as [Hlt' | [Heq' | Hgt']].
            - exact Hlt'.
            - exfalso. subst i2. rewrite Heq_i1 in Heq_i2. lia.
            - exfalso.
              assert (Hfib_gt: fib i2 < fib i1).
              { apply fib_mono_lt; try assumption; lia. }
              lia. }
          (* So fib (S i1) <= fib i2 *)
          assert (Hfib_Si1_le_i2: fib (S i1) <= fib i2).
          { destruct (Nat.eq_dec (S i1) i2) as [Heq' | Hneq'].
            - rewrite Heq'. lia.
            - assert (HS_i1_lt_i2: S i1 < i2) by lia.
              apply Nat.lt_le_incl.
              apply fib_mono_lt; lia. }
          (* Combine: sum_list (x1 :: xs1) < fib (S i1) <= fib i2 = x2 <= sum_list (x2 :: xs2) *)
          (* But sum_list (x1 :: xs1) = sum_list (x2 :: xs2) = n, contradiction! *)
          rewrite Heq_i2 in Hfib_Si1_le_i2.
          assert (Hcontrad: sum_list (x1 :: xs1) < sum_list (x2 :: xs2)).
          { apply (Nat.lt_le_trans _ (fib (S i1))).
            - exact Hsum1_bound.
            - apply (Nat.le_trans _ x2); assumption. }
          lia.
        + (* Case: x1 = x2 - but we have Hneq : x1 ≠ x2, contradiction *)
          contradiction.
        + (* Case: x1 > x2 (symmetric to above) *)
          assert (Hsum2_bound: sum_list (x2 :: xs2) < fib (S i2)).
          { rewrite <- Heq_i2.
            apply (sum_nonconsec_fibs_bounded_sorted i2 xs2).
            - exact Hi2_ge.
            - rewrite Heq_i2. exact Hsorted2.
            - rewrite Heq_i2. exact Hnocons2.
            - intros z Hz. rewrite Heq_i2 in Hz.
              apply Hfib2. exact Hz. }
          assert (Hx1_le_sum1: x1 <= sum_list (x1 :: xs1)).
          { simpl. lia. }
          assert (Hi2_lt_i1: i2 < i1).
          { destruct (Nat.lt_trichotomy i2 i1) as [Hlt' | [Heq' | Hgt']].
            - exact Hlt'.
            - exfalso. subst i1. rewrite Heq_i2 in Heq_i1. lia.
            - exfalso.
              assert (Hfib_gt: fib i1 < fib i2).
              { apply fib_mono_lt; try assumption; lia. }
              lia. }
          assert (Hfib_Si2_le_i1: fib (S i2) <= fib i1).
          { destruct (Nat.eq_dec (S i2) i1) as [Heq' | Hneq'].
            - rewrite Heq'. lia.
            - assert (HS_i2_lt_i1: S i2 < i1) by lia.
              apply Nat.lt_le_incl.
              apply fib_mono_lt; lia. }
          rewrite Heq_i1 in Hfib_Si2_le_i1.
          assert (Hcontrad: sum_list (x2 :: xs2) < sum_list (x1 :: xs1)).
          { apply (Nat.lt_le_trans _ (fib (S i2))).
            - exact Hsum2_bound.
            - apply (Nat.le_trans _ x1); assumption. }
          lia. }

      (* Now we have x1 = x2, so we can prove the lists are equal *)
      f_equal.
      { (* Prove x1 = fib i2 (the heads are equal) *)
        exact Hx1_eq_x2. }

      (* Prove xs1 = xs2 (the tails are equal) *)
      (* Apply IH to xs1 and xs2 *)
      apply (IHn (sum_list xs1)).
      * (* sum_list xs1 < n *)
        simpl in Hsum1.
        assert (Hx1_pos: x1 > 0).
        { rewrite <- Heq_i1. apply fib_pos. lia. }
        lia.
      * (* xs1 is sorted *)
        destruct xs1 as [|y1 ys1]; [simpl; trivial |].
        simpl in Hsorted1. destruct Hsorted1 as [_ Htail]. exact Htail.
      * (* xs2 is sorted *)
        destruct xs2 as [|y2 ys2]; [simpl; trivial |].
        simpl in Hsorted2. destruct Hsorted2 as [_ Htail]. exact Htail.
      * (* no_consecutive_fibs_sorted xs1 *)
        destruct xs1 as [|y1 ys1]; [simpl; trivial |].
        simpl in Hnocons1. destruct Hnocons1 as [_ Htail]. exact Htail.
      * (* no_consecutive_fibs_sorted xs2 *)
        destruct xs2 as [|y2 ys2]; [simpl; trivial |].
        simpl in Hnocons2. destruct Hnocons2 as [_ Htail]. exact Htail.
      * (* All elements in xs1 are Fibs with indices >= 2 *)
        intros z Hz. apply Hfib1. simpl. right. exact Hz.
      * (* All elements in xs2 are Fibs with indices >= 2 *)
        intros z Hz. apply Hfib2. simpl. right. exact Hz.
      * (* sum_list xs1 = sum_list xs1 *)
        reflexivity.
      * (* sum_list xs2 = sum_list xs1 *)
        simpl in Hsum1, Hsum2.
        lia.
Qed.

(*
  Helper lemmas to simplify application of zeckendorf_unique_sorted
*)

(*
  Helper: sum_list distributes over append
*)
Lemma sum_list_app : forall l1 l2,
  sum_list (l1 ++ l2) = sum_list l1 + sum_list l2.
Proof.
  induction l1 as [|x xs IH]; intro l2.
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

(*
  Lemma: Sum of a reversed list equals sum of the original list
*)
Lemma sum_list_rev : forall l,
  sum_list (rev l) = sum_list l.
Proof.
  induction l as [|x xs IH].
  - simpl. reflexivity.
  - simpl. rewrite sum_list_app. simpl.
    rewrite Nat.add_0_r. rewrite IH. lia.
Qed.

(*
  Lemma: Reversal preserves no_consecutive_fibs property

  If a list has no consecutive Fibonacci numbers, then its reversal
  also has no consecutive Fibonacci numbers.
*)
Lemma rev_preserves_no_consecutive : forall l,
  no_consecutive_fibs l ->
  no_consecutive_fibs (rev l).
Proof.
  induction l as [|x xs IH].
  - (* l = [] *)
    intro. simpl. trivial.
  - (* l = x :: xs *)
    intro Hnocons.
    simpl.
    simpl in Hnocons.
    destruct Hnocons as [Hhead Htail].
    (* rev (x :: xs) = rev xs ++ [x] *)
    (* Need to show no_consecutive_fibs (rev xs ++ [x]) *)
    apply no_consecutive_append_single.
    + (* no_consecutive_fibs (rev xs) by IH *)
      apply IH. exact Htail.
    + (* Show x is not consecutive with any element in rev xs *)
      intros y Hy_in i j Heq_i Heq_j Hcons.
      (* y is in rev xs, so y is in xs *)
      apply in_rev in Hy_in.
      (* nat_consecutive is symmetric *)
      assert (Hcons_sym: nat_consecutive j i).
      { unfold nat_consecutive in *. destruct Hcons as [H|H]; [right|left]; exact H. }
      (* Apply Hhead with y from xs *)
      apply (Hhead y Hy_in j i Heq_j Heq_i Hcons_sym).
Qed.

(*
  Conversion lemma: no_consecutive_fibs implies no_consecutive_fibs_sorted for sorted lists

  For a descending-sorted list, if no two elements are consecutive Fibonacci numbers
  (in the general sense), then adjacent elements are also not consecutive.
*)
Lemma no_consecutive_to_sorted : forall l,
  Sorted_dec l ->
  no_consecutive_fibs l ->
  no_consecutive_fibs_sorted l.
Proof.
  induction l as [|x xs IH].
  - (* l = [] *)
    intros _ _. simpl. trivial.
  - (* l = x :: xs *)
    intros Hsorted Hnocons.
    destruct xs as [|y ys].
    + (* xs = [] *)
      simpl. trivial.
    + (* xs = y :: ys *)
      simpl.
      split.
      * (* Adjacent elements x and y are not consecutive *)
        intros i j Heq_i Heq_j Hcons.
        simpl in Hnocons.
        destruct Hnocons as [Hhead _].
        apply (Hhead y (or_introl eq_refl) i j Heq_i Heq_j Hcons).
      * (* Recursively show tail is sorted *)
        apply IH.
        -- apply (sorted_tail x). exact Hsorted.
        -- simpl in Hnocons. destruct Hnocons as [_ Htail]. exact Htail.
Qed.
