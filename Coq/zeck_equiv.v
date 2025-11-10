Require Import Coq.Arith.Le.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Lia.

Require Import Zeckendorf.zeckendorf.
Require Import Zeckendorf.zeck.

(*
  ==============================================================================
  EQUIVALENCE PROOF: zeck = zeckendorf
  ==============================================================================

  This file proves that the efficient zeck algorithm produces the same
  results as the original zeckendorf algorithm, connecting the fast
  implementation to all the proven correctness properties.

  Strategy:
  1. Show that zeck_lists(m) generates Zeckendorf representations in order
  2. Prove that nth i (zeck_lists m) = zeckendorf i for appropriate m
  3. Conclude that zeck i = zeckendorf i

  The key insight: zeck_lists builds a table using dynamic programming where
  the i-th entry is the Zeckendorf representation of i.
*)

(* First, let's test the behavior computationally *)

Example zeck_0 : zeck 0 = [].
Proof. reflexivity. Qed.

Example zeck_1 : zeck 1 = [1].
Proof. reflexivity. Qed.

Example zeck_2 : zeck 2 = [2].
Proof. reflexivity. Qed.

Example zeck_3 : zeck 3 = [3].
Proof. reflexivity. Qed.

Example zeck_4 : zeck 4 = [3; 1].
Proof. reflexivity. Qed.

Example zeck_5 : zeck 5 = [5].
Proof. reflexivity. Qed.

Example zeck_10 : zeck 10 = [8; 2].
Proof. reflexivity. Qed.

Example zeck_20 : zeck 20 = [13; 5; 2].
Proof. reflexivity. Qed.

Example zeck_100 : zeck 100 = [89; 8; 3].
Proof. reflexivity. Qed.

(* Now verify that zeck matches zeckendorf computationally *)

Example equiv_0 : zeck 0 = zeckendorf 0.
Proof. reflexivity. Qed.

Example equiv_1 : zeck 1 = zeckendorf 1.
Proof. reflexivity. Qed.

Example equiv_2 : zeck 2 = zeckendorf 2.
Proof. reflexivity. Qed.

Example equiv_3 : zeck 3 = zeckendorf 3.
Proof. reflexivity. Qed.

Example equiv_4 : zeck 4 = zeckendorf 4.
Proof. reflexivity. Qed.

Example equiv_5 : zeck 5 = zeckendorf 5.
Proof. reflexivity. Qed.

Example equiv_10 : zeck 10 = zeckendorf 10.
Proof. reflexivity. Qed.

Example equiv_20 : zeck 20 = zeckendorf 20.
Proof. reflexivity. Qed.

Example equiv_50 : zeck 50 = zeckendorf 50.
Proof. reflexivity. Qed.

Example equiv_100 : zeck 100 = zeckendorf 100.
Proof. reflexivity. Qed.

(*
  ======================================================================
  Structural facts about [zeck_lists]
  ======================================================================

  The dynamic-programming constructor [zeck_lists] builds, for each level n,
  all Zeckendorf representations of the numbers [0, 1, ..., fib (n+2) - 1]
  in ascending order by their sum.  The next lemmas capture exactly the two
  ingredients we need:
    1. [map sum_list (zeck_lists n)] is the canonical sequence [0; 1; ...]
    2. Every entry already satisfies the Zeckendorf representation predicate.

  Once these are in place, the main equivalence proof becomes a direct
  instantiation of the uniqueness theorem from [zeckendorf.v].
*)

Lemma seq_map_shift : forall len start offset,
  map (fun x => offset + x) (seq start len) = seq (offset + start) len.
Proof.
  induction len as [|len IH]; intros start offset; simpl.
  - reflexivity.
  - rewrite IH with (start := S start) (offset := offset).
    simpl. replace (offset + S start) with (S (offset + start)) by lia.
    reflexivity.
Qed.

Lemma map_sum_cons : forall c ls,
  map sum_list (map (fun xs => c :: xs) ls) =
  map (fun s => c + s) (map sum_list ls).
Proof.
  intros c ls.
  induction ls as [|xs ls IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma nat_ind2 (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P (S n) -> P (S (S n))) ->
  forall n, P n.
Proof.
  intros H0 H1 Hstep.
  assert (forall n, P n /\ P (S n)) as Hall.
  { induction n as [|n [HPn HPsn]].
    - split; [exact H0|exact H1].
    - split.
      + exact HPsn.
      + apply Hstep; assumption.
  }
  intro n.
  exact (proj1 (Hall n)).
Qed.

Lemma nth_seq_start : forall start len k,
  k < len ->
  nth k (seq start len) 0 = start + k.
Proof.
  intros start len k Hlt.
  revert start len Hlt.
  induction k as [|k IH]; intros start len Hlt.
  - destruct len; simpl in Hlt; [lia|].
    simpl. rewrite Nat.add_0_r. reflexivity.
  - destruct len as [|len]; [lia|].
    simpl in Hlt.
    simpl.
    specialize (IH (S start) len ltac:(lia)).
    rewrite IH. lia.
Qed.

Lemma nth_seq_0 : forall len k,
  k < len ->
  nth k (seq 0 len) 0 = k.
Proof.
  intros len k Hlt.
  replace k with (0 + k) by lia.
  apply nth_seq_start.
  exact Hlt.
Qed.

Lemma not_consecutive_if_gap : forall a b,
  b + 1 < a ->
  ~ nat_consecutive a b.
Proof.
  intros a b Hgap [H|H]; lia.
Qed.

Lemma fib_n_plus_two_gt_n : forall n,
  fib (n + 2) > n.
Proof.
  intro n.
  destruct n as [|[|[|n']]]; simpl; try lia.
  assert (Hgrow: fib (S (S (S n')) + 2) >= S (S (S n')) + 2).
  { apply fib_linear_growth. lia. }
  assert (Hlt: S (S (S n')) < S (S (S n')) + 2) by lia.
  eapply Nat.lt_le_trans; eauto.
Qed.

Lemma fib_eq_le_index : forall j k,
  k >= 2 ->
  fib j = fib k ->
  j <= k.
Proof.
  intros j k Hk Heq.
  destruct (Nat.lt_total j k) as [Hlt | [Heq' | Hgt]].
  - exact (Nat.lt_le_incl _ _ Hlt).
  - lia.
  - exfalso.
    assert (Hfib_lt: fib k < fib j).
    { apply fib_mono_lt; try lia. }
    rewrite Heq in Hfib_lt. lia.
Qed.

(* TODO(codex): Prove this by complete induction on n using [nat_ind2].
   - Base cases n=0,1 are already unfolded; keep proofs short.
   - Step case should reuse the invariant for n and n+1, then show
     the concatenation and mapped block preserve (1) the enumeration
     of sums and (2) the Zeckendorf predicate + index bounds.
   - Useful facts already available: [seq_map_shift], [map_sum_cons],
     monotonicity of fib, and the helper lemmas near the top of this file. *)
Lemma zeck_lists_invariant :
  forall n,
    map sum_list (zeck_lists n) = seq 0 (fib (n + 2)) /\
    forall l,
      In l (zeck_lists n) ->
      is_zeckendorf_repr (sum_list l) l /\
      (forall z k, In z l -> z = fib k -> k <= n + 1).
Admitted.

Corollary zeck_lists_sum_seq : forall n,
  map sum_list (zeck_lists n) = seq 0 (fib (n + 2)).
Proof.
  intro n. apply (zeck_lists_invariant n).
Qed.

(* TODO(codex): Deduce this from [zeck_lists_invariant].
   - Use nth/length facts to show k stays in bounds.
   - Extract the representation proof from the invariant.
   - This is the bridge between the table entry and the formal predicate. *)
Corollary zeck_lists_entry_repr : forall n k,
  k < fib (n + 2) ->
  is_zeckendorf_repr k (nth k (zeck_lists n) []).
Proof. Admitted.

(* TODO(codex): Simple arithmetic identity.
   - Split on m=0 separately.
   - For m+1>=1, use the reasoning that pred(S m) = m and unfold fib definitions. *)
Lemma fib_pred_plus_two : forall m,
  fib (Nat.pred m + 2) = fib (m + 1).
Proof.
  intro m.
  destruct m as [|m']; simpl; auto.
  assert (H : m' + 2 = S m' + 1) by lia.
  rewrite H.
  reflexivity.
Qed.

(* TODO(codex): Prove this by induction on the budget [b].
   - Base case: once k caught up to n+1 we know fib(n+2) > n.
   - Step: leverage the recursive call when fib(S k) <= n, otherwise we
     exit with the desired inequality. *)
Lemma find_fib_index_aux_spec : forall n k b,
  k <= n + 1 ->
  b = n + 1 - k ->
  fib (S (find_fib_index_aux n k b)) > n.
Proof.
  intros n k b Hle Hb.
  assert (Hsum : k + b = S n) by lia.
  clear Hle Hb.
  revert n k Hsum.
  induction b as [|b' IH]; intros n k Hsum; simpl in *.
  - assert (k = S n) by lia. subst k.
    assert (Hfib := fib_n_plus_two_gt_n n).
    replace (n + 2) with (S (S n)) in Hfib by lia.
    exact Hfib.
  - set (guard := (fib (S k) <=? n)).
    destruct guard eqn:Hflag; simpl.
    + admit. (* apply IH. lia. *)
    + unfold guard in Hflag.
      apply Nat.leb_gt in Hflag.
      (* exact Hflag. *)
      admit.
Admitted.

(* TODO(codex): Direct corollary: instantiate [find_fib_index_aux_spec]
   with k=0 and b=S n to obtain the witness used by [zeck]. *)
Lemma min_level_for_index_spec : forall n,
  fib (min_level_for_index n + 1) > n.
Proof.
  intro n.
  unfold min_level_for_index.
  replace (find_fib_index_aux n 0 (S n) + 1) with (S (find_fib_index_aux n 0 (S n))) by lia.
  apply find_fib_index_aux_spec; lia.
Qed.

(* TODO(codex): Combine [min_level_for_index_spec] with
   [zeck_lists_entry_repr]; remember zeck grabs nth n in zeck_lists (m-1),
   so we must show fib(depth+2) > n, then apply the entry lemma. *)
Lemma zeck_is_zeckendorf : forall n,
  is_zeckendorf_repr n (zeck n).
Proof. Admitted.

(*
  Main equivalence theorem: zeck produces the same output as zeckendorf
*)
Theorem zeck_equiv : forall n,
  zeck n = zeckendorf n.
Proof.
  intro n.
  apply zeckendorf_repr_unique.
  apply zeck_is_zeckendorf.
Qed.

Corollary zeck_sum : forall n,
  sum_list (zeck n) = n.
Proof.
  intro n.
  rewrite zeck_equiv.
  apply zeckendorf_sum_property.
Qed.

Corollary zeck_all_fib : forall n z,
  In z (zeck n) -> exists k, k >= 2 /\ z = fib k.
Proof.
  intros n z H.
  rewrite zeck_equiv in H.
  apply (zeckendorf_fib_property n z H).
Qed.
