Require Import Coq.Arith.Le.
Require Import Coq.Lists.List.
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
