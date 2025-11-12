Require Import Coq.Arith.Le.
Require Import Coq.Lists.List.
Import ListNotations.

From Coq Require Import Extraction ExtrHaskellBasic ExtrHaskellNatInteger.

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

Extraction Language Haskell.
Extraction "../Haskell/extracted_zeck.hs" zeck.
