# Proof Status: zeckendorf_produces_sorted_asc

This document used to track the in-progress proof that the greedy algorithm
produces sorted output. The work now lives in the pair of lemmas
`zeckendorf_fuel_sorted_empty` (`Coq/zeckendorf.v:1633-1694`) and
`zeckendorf_sorted` (`Coq/zeckendorf.v:1695-1702`), both of which are proven
with `Qed`.

## Current State

- ✅ `zeckendorf_fuel_sorted_empty` shows that the fuel-bounded greedy recursion
  returns a strictly descending list when started from an empty accumulator.
- ✅ `zeckendorf_sorted` instantiates the lemma above for the public-facing
  `zeckendorf` function.
- ✅ `zeckendorf_repr_exists`/`zeckendorf_repr_unique` consume the sorting,
  no-consecutive, and sum properties to deliver the final theorem.

There are no remaining admits tied to this effort; this file now serves as a
historical note explaining which lemmas correspond to the earlier
`zeckendorf_produces_sorted_asc` placeholder.

## How the Proof Works

1. **Fuel-based recursion**  
   `zeckendorf_fuel` decreases both `fuel` and the remaining sum. The sorted
   lemma performs induction on `fuel`, mirroring the execution of the greedy
   algorithm.

2. **Bounding arguments**  
   Lemmas such as `zeckendorf_fuel_elements_bounded_empty` ensure recursive
   calls never reintroduce elements larger than the current head, which makes
   the sorted proof straightforward.

3. **Combining invariants**  
   Alongside sorting, the project proves:
   - `zeckendorf_fib_property` – every element is a Fibonacci number
   - `zeckendorf_sum_property` – the list sums to the original `n`
   - `zeckendorf_no_consecutive` – no adjacent Fibonacci indices are consecutive  
   These feed directly into `is_zeckendorf_repr`.

## Optional Enhancements

While the lemma is complete, these ideas could be explored in future work:

1. **Stronger accumulator invariants** – generalize the sorted lemma to handle
   arbitrary accumulators satisfying `Sorted_dec` and a “greater-than” guard.
2. **Automation** – package the sorted/no-consecutive proofs into reusable
   tactics for other greedy algorithms.
3. **Documentation** – keep the SVG/PNG plots in `docs/images/` up-to-date if
   the algorithm is extended to visualize additional invariants.

The Coq build (`cd Coq && ./build_coq.sh`) currently succeeds without manual
intervention, so no immediate proof work is required.
