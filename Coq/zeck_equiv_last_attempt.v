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

Lemma zeck_lists_invariant :
  forall n,
    map sum_list (zeck_lists n) = seq 0 (fib (n + 2)) /\
    forall l,
      In l (zeck_lists n) ->
      is_zeckendorf_repr (sum_list l) l /\
      (forall z k, In z l -> z = fib k -> k <= n + 1).
Proof.
  apply nat_ind2; simpl.
  - split.
    + reflexivity.
    + intros l Hl. destruct Hl as [Hl|[]]; subst l.
      split.
      * repeat split; simpl; auto.
        intros z Hz. inversion Hz.
      * intros z k Hz _. inversion Hz.
  - split.
    + reflexivity.
    + intros l Hl.
      destruct Hl as [Hl|Hl']; [subst l|].
      { split.
        { split.
          { intros z Hz. inversion Hz. }
          split; [simpl; reflexivity|split; [simpl; split; auto|simpl; auto]]. }
        { intros z k Hz _. inversion Hz. } }
      { destruct Hl' as [Hl|[]]; [subst l|inversion Hl].
        - split.
          { split.
            { intros z Hz. inversion Hz. }
            split; [simpl; reflexivity|split; [simpl; split; auto|simpl; auto]]. }
          { intros z k Hz _. inversion Hz. }
        - split.
          { split.
            { intros z Hz.
              simpl in Hz. destruct Hz as [Hz|[]]. subst z.
              exists 2. split; [lia|reflexivity]. }
            split; [simpl; reflexivity|split; [simpl; split; auto|simpl; auto]]. }
          { intros z k Hz Hfib.
            simpl in Hz. destruct Hz as [Hz|[]]; subst z.
            + destruct k as [|k1]; simpl in Hfib; try lia.
              destruct k1 as [|k2]; simpl in Hfib; try lia.
              destruct k2 as [|k3]; simpl in Hfib; try lia.
              simpl in Hfib.
              assert (Hpos1 : fib (S (S k3)) > 0) by (apply fib_pos; lia).
              assert (Hpos2 : fib (S k3) > 0) by (apply fib_pos; lia).
              assert (Hge1 : fib (S (S k3)) >= 1) by lia.
              assert (Hge2 : fib (S k3) >= 1) by lia.
              assert (Hsum_ge : fib (S (S k3)) + fib (S k3) >= 2) by lia.
              exfalso.
              rewrite Hfib in Hsum_ge. inversion Hsum_ge.
            + inversion Hz. } }
  - intros n [Hsum_n Hinv_n] [Hsum_Sn Hinv_Sn].
    split.
    + simpl.
      rewrite map_app, Hsum_Sn, map_sum_cons, Hsum_n.
      rewrite seq_map_shift with (len := fib (n + 2)) (start := 0) (offset := fib (n + 3)).
      rewrite (seq_app 0 (fib (n + 3)) (fib (n + 2))).
      replace (fib (n + 3) + fib (n + 2)) with (fib (n + 4)).
      * reflexivity.
      * replace (n + 4)%nat with (S (S n) + 2)%nat by lia.
        replace (n + 3)%nat with (S (n + 2)) by lia.
        rewrite fib_SS. reflexivity.
    + intros l Hl.
      simpl in Hl.
      apply in_app_or in Hl.
      destruct Hl as [Hin1 | Hin2].
      * specialize (Hinv_Sn _ Hin1) as [Hrepr Hbnd].
        split; [exact Hrepr|].
        intros z k Hz Hzfib.
        apply Hbnd; assumption.
      * apply in_map_iff in Hin2.
        destruct Hin2 as [xs [-> Hxs]].
        specialize (Hinv_n _ Hxs) as [Hrepr_xs Hbnd_xs].
        destruct Hrepr_xs as [Hfib_xs [Hsum_xs [Hnocons_xs Hsorted_xs]]].
        split.
        -- (* is_zeckendorf_repr for fib (n+3) :: xs *)
           split.
           { (* Fib property *)
             intros z Hz.
             simpl in Hz. destruct Hz as [Hz|Hz].
             - subst z. exists (n + 3). split; lia.
             - apply Hfib_xs in Hz.
               destruct Hz as [k [Hk_ge Hk_eq]].
               exists k. split; assumption.
           }
           split.
           { (* Sum property *)
             simpl. reflexivity.
           }
           split.
           { (* No consecutive property *)
             simpl. split.
             - intros y Hy i j Hi Hj Hcons.
               subst.
               specialize (Hfib_xs y Hy) as [k [Hk_ge Hk_eq]].
               pose proof (Hbnd_xs _ _ Hy Hk_eq) as Hk_bound.
               assert (Hj_le: j <= k).
               { apply fib_eq_le_index; try assumption.
                 rewrite Hj, Hk_eq. reflexivity. }
               apply not_consecutive_if_gap with (a := n + 3) (b := j); lia.
             - exact Hnocons_xs.
           }
           { (* Sorted property *)
             simpl.
             destruct xs as [|y ys]; simpl; auto.
             split.
             - specialize (Hfib_xs y (or_introl eq_refl)) as [k [Hk_ge Hk_eq]].
               pose proof (Hbnd_xs _ _ (or_introl eq_refl) Hk_eq) as Hk_le.
               rewrite <- Hk_eq.
               apply fib_mono_lt; try lia.
             - exact Hsorted_xs.
           }
        -- (* Index bound for new list *)
           intros z k Hz Hk_eq.
           simpl in Hz. destruct Hz as [Hz|Hz].
           { subst z. rewrite Hk_eq. lia. }
           { pose proof (Hbnd_xs _ _ Hz Hk_eq) as Hbound.
             lia. }
Qed.

Corollary zeck_lists_sum_seq : forall n,
  map sum_list (zeck_lists n) = seq 0 (fib (n + 2)).
Proof.
  intro n. apply (zeck_lists_invariant n).
Qed.

Corollary zeck_lists_entry_repr : forall n k,
  k < fib (n + 2) ->
  is_zeckendorf_repr k (nth k (zeck_lists n) []).
Proof.
  intros n k Hlt.
  destruct (zeck_lists_invariant n) as [Hsum Hinvar].
  assert (Hlen: k < length (zeck_lists n)).
  { rewrite <- (map_length sum_list (zeck_lists n)).
    rewrite Hsum. simpl. lia. }
  assert (Hsum_k: sum_list (nth k (zeck_lists n) []) = k).
  { rewrite <- (nth_map sum_list (zeck_lists n) [] 0) by assumption.
    rewrite Hsum.
    apply nth_seq_0. lia. }
  assert (Hin: In (nth k (zeck_lists n) []) (zeck_lists n)).
  { apply nth_In. assumption. }
  specialize (Hinvar _ Hin) as [[Hfib [Hsum_prop [Hnocons Hsorted]]] Hbnd].
  rewrite Hsum_k in Hsum_prop.
  repeat split; try assumption.
Qed.

Lemma fib_pred_plus_two : forall m,
  fib (Nat.pred m + 2) = fib (m + 1).
Proof.
  intro m.
  destruct m; simpl; auto.
  replace (Nat.pred (S m) + 2)%nat with (m + 1)%nat by lia.
  reflexivity.
Qed.

Lemma find_fib_index_aux_spec : forall n k b,
  k <= n + 1 ->
  b = n + 1 - k ->
  fib (S (find_fib_index_aux n k b)) > n.
Proof.
  intros n k b Hk Hb.
  revert k Hk Hb.
  induction b as [|b IH]; intros k Hk Hb.
  - simpl in Hb.
    assert (k = n + 1) by lia. subst k.
    simpl. replace (S (n + 1)) with (n + 2) by lia.
    apply fib_n_plus_two_gt_n.
  - simpl in Hb.
    destruct (Nat.leb_spec0 (fib (S k)) n) as [Hle | Hgt].
    + eapply IH with (k := S k).
      * lia.
      * lia.
    + exact Hgt.
Qed.

Lemma min_level_for_index_spec : forall n,
  fib (min_level_for_index n + 1) > n.
Proof.
  intro n.
  unfold min_level_for_index.
  apply find_fib_index_aux_spec; lia.
Qed.

Lemma zeck_is_zeckendorf : forall n,
  is_zeckendorf_repr n (zeck n).
Proof.
  intro n.
  unfold zeck.
  set (m := min_level_for_index n).
  set (depth := Nat.pred m).
  assert (Hbound: n < fib (depth + 2)).
  { subst depth.
    rewrite fib_pred_plus_two.
    apply min_level_for_index_spec.
  }
  apply (zeck_lists_entry_repr depth n).
  exact Hbound.
Qed.

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
