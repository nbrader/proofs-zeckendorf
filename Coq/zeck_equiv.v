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

Lemma seq_app : forall start len1 len2,
  seq start len1 ++ seq (start + len1) len2 = seq start (len1 + len2).
Proof.
  intros start len1 len2.
  revert start.
  induction len1 as [|len1 IH]; intros start.
  - simpl. replace (start + 0) with start by lia. reflexivity.
  - simpl. f_equal.
    rewrite <- IH.
    replace (S start + len1) with (start + S len1) by lia.
    reflexivity.
Qed.

(* Small Fibonacci algebra facts used to keep the main proof readable. *)
Lemma fib_plus_three : forall n,
  fib (n + 3) = fib (n + 2) + fib (n + 1).
Proof.
  intro n.
  replace (n + 3) with (S (S (n + 1))) by lia.
  replace (n + 2) with (S (n + 1)) by lia.
  apply fib_SS.
Qed.

Lemma fib_sum_succ : forall n,
  fib (n + 3) + fib (n + 2) = fib (n + 4).
Proof.
  intro n.
  replace (n + 4)%nat with ((n + 1) + 3)%nat by lia.
  replace (n + 3)%nat with ((n + 1) + 2)%nat by lia.
  replace (n + 2)%nat with ((n + 1) + 1)%nat by lia.
  symmetry.
  apply fib_plus_three.
Qed.

(* Program Fixpoint introduces a nested match when unfolding fib indices.
   This lemma massaging that pattern back into [fib (n+3)] keeps the
   invariant proof manageable. *)
Lemma simplify_nested_fib_match : forall n,
  match n + 2 with
  | 0 => 1
  | S _ =>
      match n + 2 with
      | 0 => 1
      | S n'' => fib (n + 2) + fib n''
      end
  end = fib (n + 3).
Proof.
  intro n.
  assert (Haux : forall k,
            k >= 2 ->
            match k with
            | 0 => 1
            | S _ =>
                match k with
                | 0 => 1
                | S m => fib k + fib m
                end
            end = fib k + fib (k - 1)).
  { intros k Hk.
    destruct k as [|[|k']]; try lia; simpl.
    replace (k' + 1) with (S k') by lia.
    reflexivity. }
  assert (Hge : n + 2 >= 2) by lia.
  rewrite (Haux (n + 2) Hge).
  replace (n + 2 - 1) with (n + 1) by lia.
  symmetry.
  apply fib_plus_three.
Qed.

Lemma fib_n_plus_three_ge_two : forall n,
  fib (n + 3) >= 2.
Proof.
  intro n.
  induction n as [|n IH].
  - simpl. lia.
  - replace (S n + 3)%nat with (S (S (n + 2))) by lia.
    rewrite fib_SS.
    replace (S (n + 2)) with (n + 3) by lia.
    specialize (IH).
    lia.
Qed.

Lemma seq_concat_with_shift : forall a b,
  seq 0 a ++ map (fun x => a + x) (seq 0 b) = seq 0 (a + b).
Proof.
  intros a b.
  rewrite seq_map_shift with (len := b) (start := 0) (offset := a).
  replace (a + 0) with (0 + a) by lia.
  rewrite (seq_app 0 a b).
  reflexivity.
Qed.

Lemma seq_app_start0_r : forall len1 len2,
  seq 0 len1 ++ seq (len1 + 0) len2 = seq 0 (len1 + len2).
Proof.
  intros len1 len2.
  replace (len1 + 0) with (0 + len1) by lia.
  apply seq_app.
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
      simpl in Hl.
      destruct Hl as [Hl|[Hl|[]]]; subst l.
      * split.
        { repeat split; simpl; auto.
          intros z Hz. inversion Hz. }
        { intros z k Hz _. inversion Hz. }
      * split.
        { split.
          { intros z Hz.
            simpl in Hz.
            destruct Hz as [Hz|[]].
            symmetry in Hz. subst z.
            exists 2. split; [lia|reflexivity]. }
          split; [simpl; reflexivity|split; [simpl; split; auto|simpl; auto]]. }
        { intros z k Hz Hfib.
          simpl in Hz.
          destruct Hz as [Hz|[]].
          symmetry in Hz. subst z.
          destruct k as [|[|[|k3]]]; try (simpl in Hfib; lia).
          exfalso.
          destruct k3 as [|k4]; simpl in Hfib; lia. }
  - intros n [Hsum_n Hinv_n] [Hsum_Sn Hinv_Sn].
    split.
    + simpl.
      rewrite map_app, Hsum_Sn, map_sum_cons, Hsum_n.
      rewrite simplify_nested_fib_match.
      replace (S n + 2)%nat with (n + 3)%nat by lia.
      rewrite seq_concat_with_shift with (a := fib (n + 3)) (b := fib (n + 2)).
      remember (fib (n + 3) + fib (n + 2)) as total eqn:Htotal.
      assert (Htotal_eq : total = fib (n + 4)).
      { subst total.
        replace (n + 3)%nat with (S (n + 2)) by lia.
        replace (n + 4)%nat with (S (S (n + 2))) by lia.
        rewrite fib_SS.
        reflexivity. }
      rewrite Htotal_eq.
      reflexivity.
    + intros l Hl.
      simpl in Hl.
      apply in_app_or in Hl.
      destruct Hl as [Hin1 | Hin2].
      * specialize (Hinv_Sn _ Hin1) as [Hrepr Hbnd].
        split; [exact Hrepr|].
        intros z k Hz Hzfib.
        specialize (Hbnd _ _ Hz Hzfib).
        lia.
      * apply in_map_iff in Hin2.
        destruct Hin2 as [xs [Hhead Hxs]].
        symmetry in Hhead. subst l.
        specialize (Hinv_n _ Hxs) as [Hrepr_xs Hbnd_xs].
        destruct Hrepr_xs as [Hfib_xs [Hsum_xs [Hnocons_xs Hsorted_xs]]].
        split.
        -- (* is_zeckendorf_repr for fib (n+3) :: xs *)
           split.
           { (* Fib property *)
             intros z Hz.
             simpl in Hz. destruct Hz as [Hz|Hz].
             - symmetry in Hz. subst z. exists (n + 3). split; lia.
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
                 assert (Hi_ge2 : i >= 2).
                 { destruct i as [|[|i']]; simpl in Hi.
                   - pose proof (fib_n_plus_three_ge_two n) as Hfib.
                     rewrite <- Hi in Hfib. lia.
                   - pose proof (fib_n_plus_three_ge_two n) as Hfib.
                     rewrite <- Hi in Hfib. lia.
                   - lia. }
                 assert (Hi_le : i <= n + 3).
                 { apply fib_eq_le_index; try lia. }
                 assert (Hi_ge : n + 3 <= i).
                 { apply fib_eq_le_index with (j := n + 3) (k := i); try lia. }
                 assert (Hi_eq : i = n + 3) by lia.
                 subst i.
                 specialize (Hfib_xs y Hy) as [k [Hk_ge Hk_eq]].
                 pose proof (Hbnd_xs _ _ Hy Hk_eq) as Hk_bound.
                 set (Hk_eq_sym := eq_sym Hk_eq).
                 assert (Hj_le: j <= k).
                 { apply fib_eq_le_index; try assumption.
                   rewrite Hj, Hk_eq_sym. reflexivity. }
                 assert (Hgap : j + 1 < n + 3) by lia.
                 destruct Hcons as [H|H]; lia.
             - exact Hnocons_xs.
           }
           { (* Sorted property *)
             simpl.
             destruct xs as [|y ys]; simpl; auto.
             split.
             - specialize (Hfib_xs y (or_introl eq_refl)) as [k [Hk_ge Hk_eq]].
               pose proof (Hbnd_xs _ _ (or_introl eq_refl) Hk_eq) as Hk_le.
               rewrite Hk_eq.
               apply fib_mono_lt; try lia.
             - exact Hsorted_xs.
           }
        -- (* Index bound for new list *)
           intros z k Hz Hk_eq.
           simpl in Hz. destruct Hz as [Hz|Hz].
           { symmetry in Hz. subst z.
             symmetry in Hk_eq.
             enough (k <= n + 3) by lia.
             apply fib_eq_le_index; try lia. }
           { pose proof (Hbnd_xs _ _ Hz Hk_eq) as Hbound.
             lia. }
Qed.

Corollary zeck_lists_sum_seq : forall n,
  map sum_list (zeck_lists n) = seq 0 (fib (n + 2)).
Proof.
  intro n. apply (zeck_lists_invariant n).
Qed.

(* Each table entry inherits the full Zeckendorf predicate from
   [zeck_lists_invariant]; this corollary packages the bookkeeping. *)
Corollary zeck_lists_entry_repr : forall n k,
  k < fib (n + 2) ->
  is_zeckendorf_repr k (nth k (zeck_lists n) []).
Proof.
  intros n k Hlt.
  destruct (zeck_lists_invariant n) as [Hsum Hinvar].
  assert (Hlen: k < length (zeck_lists n)).
  { rewrite <- (map_length sum_list (zeck_lists n)).
    rewrite Hsum. rewrite seq_length. exact Hlt. }
  assert (Hsum_k: sum_list (nth k (zeck_lists n) []) = k).
  { rewrite <- (map_nth sum_list) by assumption.
    rewrite Hsum.
    apply nth_seq_0. assumption. }
  assert (Hin: In (nth k (zeck_lists n) []) (zeck_lists n)).
  { apply nth_In. assumption. }
  specialize (Hinvar _ Hin) as [[Hfib [Hsum_prop [Hnocons Hsorted]]] Hbnd].
  rewrite Hsum_k in Hsum_prop.
  repeat split; try assumption.
Qed.

(* Simple arithmetic fact about shifting indices inside a predecessor. *)
Lemma fib_pred_plus_two : forall m,
  fib (Nat.pred m + 2) = fib (m + 1).
Proof.
  intro m.
  destruct m as [|m']; simpl; auto.
  assert (H : m' + 2 = S m' + 1) by lia.
  rewrite H.
  reflexivity.
Qed.

(* The auxiliary search used by [min_level_for_index] always stops at a
   Fibonacci strictly larger than [n]; proved by induction on the fuel. *)
Lemma find_fib_index_aux_spec : forall n k b,
  k <= n + 1 ->
  b = n + 1 - k ->
  fib (S (find_fib_index_aux n k b)) > n.
Proof.
  intros n k b Hk Hb.
  revert k Hk Hb.
  induction b as [|b IH]; intros k Hk Hb.
  - assert (k = n + 1) by lia. subst k.
    unfold find_fib_index_aux.
    replace (S (n + 1)) with (n + 2) by lia.
    apply fib_n_plus_two_gt_n.
  - simpl in Hb.
    unfold find_fib_index_aux; fold find_fib_index_aux.
    destruct (Nat.leb_spec (fib (S k)) n) as [Hle | Hgt].
    + eapply IH with (k := S k); lia.
    + exact Hgt.
Qed.

(* Direct corollary for the specific initial parameters of
   [min_level_for_index]. *)
Lemma min_level_for_index_spec : forall n,
  fib (min_level_for_index n + 1) > n.
Proof.
  intro n.
  unfold min_level_for_index.
  replace (find_fib_index_aux n 0 (S n) + 1) with (S (find_fib_index_aux n 0 (S n))) by lia.
  apply find_fib_index_aux_spec; lia.
Qed.

(* The fast [zeck] algorithm reuses the table entry and therefore inherits
   the Zeckendorf predicate established above. *)
Lemma zeck_is_zeckendorf : forall n,
  is_zeckendorf_repr n (zeck n).
Proof.
  intro n.
  unfold zeck.
  set (m := min_level_for_index n).
  assert (Hbound: n < fib (m - 1 + 2)).
  { replace (m - 1 + 2) with (Nat.pred m + 2) by lia.
    rewrite fib_pred_plus_two.
    apply min_level_for_index_spec.
  }
  apply (zeck_lists_entry_repr (m - 1) n).
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
