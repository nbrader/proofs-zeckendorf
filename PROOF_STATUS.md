# Zeckendorf Proof Status

This note summarizes the current shape of the `main` branch. The Coq
development compiles on Coq 8.18.0 with no remaining admits.

## Highlights

1. **Greedy algorithm infrastructure**
   - `zeckendorf_fuel` is a structurally recursive `Fixpoint` that decreases both
     the remaining sum and a fuel parameter.
   - Wrapper lemmas `zeckendorf_acc_fib`, `zeckendorf_acc_sum`,
     `zeckendorf_no_consecutive`, and `zeckendorf_sorted` assemble the four
     components of `is_zeckendorf_repr`.

2. **Sorted-list uniqueness pipeline**
   - `sum_nonconsec_fibs_bounded_sorted` (`Coq/zeckendorf.v:1926-2071`) captures
     the “sum of non-consecutive Fibonacci numbers stays below the next Fib”
     lemma from the wiki proof.
   - `zeckendorf_unique_sorted` and `zeckendorf_repr_unique` use it to derive
     uniqueness without permutation reasoning.

3. **Optimized implementation equivalence**
   - `Coq/zeck_equiv.v` proves that the table-driven function `zeck` returns the
     same list as `zeckendorf`, so downstream code can reuse the fast version
     while inheriting the proven properties.

4. **Supporting assets**
   - `docs/images/` holds illustrative diagrams and plots.
   - `docs/notes/wiki-proof*.txt` records the informal proof and the mapping to
     the mechanized development.
   - `Python/` contains regression scripts that mirror the Coq definitions and
     exercise the same invariants over finite ranges.

## Potential Enhancements

These ideas are optional; the proof is already complete.

- **Generalized sorted lemmas** – extend `zeckendorf_fuel_sorted_empty` to cover
  arbitrary accumulators that satisfy a monotonicity invariant.
- **Automation** – package recurring reasoning patterns (bounding Fibonacci
  indices, transfer through `rev`, etc.) into custom tactics.
- **Executable examples** – turn the Haskell scripts into a small cabal/stack
  project to make experimentation easier.

Run `cd Coq && ./build_coq.sh` after edits; it regenerates the `Makefile` via
`coq_makefile` and rebuilds all `.v` files.
