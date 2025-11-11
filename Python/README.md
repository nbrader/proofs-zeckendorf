# Python Test Scripts for Zeckendorf Proof

This directory contains Python scripts that empirically test the key invariants from the Coq proof of Zeckendorf's theorem. They were originally written while a few lemmas were still admitted and now serve as lightweight regression tests.

## Scripts

### test_admitted_goals.py

The main test script that verifies the invariants that were once left admitted (now formally proven) in the Coq proof.

**Tests included:**

1. **fib_in_fibs_upto** (Line 931-943 in zeckendorf.v)
   - **Claim:** If k ≥ 1 and fib(k) ≤ n, then fib(k) ∈ fibs_upto(n)
   - **Tests:** 1,514 test cases
   - **Result:** ✓ All pass

2. **largest_fib_in_fibs_upto** (Line 897-922 in zeckendorf.v)
   - **Claim:** If x is the largest Fibonacci number ≤ n (where fib(i) = x, i ≥ 2) and x < n, then n < fib(i+1)
   - **Tests:** 985 test cases
   - **Result:** ✓ All pass

3. **zeckendorf_fuel_no_consecutive_empty** (Line 1020-1159 in zeckendorf.v)
   - **Claim:** The Zeckendorf representation contains no consecutive Fibonacci numbers
   - **Tests:** 1,000 test cases
   - **Result:** ✓ All pass

4. **Sanity checks:**
   - Sum correctness: Σ(zeckendorf(n)) = n
   - All elements are Fibonacci numbers
   - **Tests:** 2,000 additional test cases
   - **Result:** ✓ All pass

**Usage:**
```bash
python3 test_admitted_goals.py
```

**Total:** 5,499 tests, 100% pass rate

### test_edge_cases.py

Extended test suite for edge cases, stress testing, and advanced properties.

**Tests included:**

1. **Basic Fibonacci Properties**
   - Recurrence relation: fib(n) = fib(n-1) + fib(n-2)
   - Monotonicity for n ≥ 2
   - Base cases

2. **fibs_upto Edge Cases**
   - Small values (0, 1, 2, 3)
   - Exact Fibonacci values
   - Values just below Fibonacci numbers

3. **Zeckendorf Edge Cases**
   - Fibonacci numbers themselves
   - Powers of 2
   - Known test cases

4. **Consecutive Fibonacci Detection**
   - Correctness of consecutive detection
   - Verification that no Zeckendorf representation has consecutives

5. **Stress Tests**
   - Large values: 1,000 to 100,000
   - Verification at scale

6. **Remainder Property**
   - **Key proof property:** If fib(k) is the largest Fib ≤ n and n > fib(k), then (n - fib(k)) < fib(k-1)
   - This is the core property that ensures no consecutive Fibonacci numbers

7. **Uniqueness Property**
   - Partial verification that representations are unique
   - Comparison with exhaustive search for small values

**Usage:**
```bash
python3 test_edge_cases.py
```

## Key Findings

The scripts cover the same statements proved in Coq and continue to pass:

- ✅ **fib_in_fibs_upto**: Verified for 1,514 cases
- ✅ **largest_fib_in_fibs_upto**: Verified for 985 cases
- ✅ **zeckendorf_fuel_no_consecutive_empty**: Verified for 1,000 cases
- ✅ **Remainder property**: Verified for 1,000 cases (core proof property)

All tests pass with 100% success rate, providing an extra sanity check alongside the formal development.

## Implementation Notes

The Python implementation mirrors the Coq definitions:

- **fib(n)**: Matches the Coq Fixpoint definition exactly
- **fibs_upto(n)**: Implements `takeWhile (≤n) (map fib (seq 1 (S n)))`
- **zeckendorf(n)**: Greedy algorithm matching the Coq `Fixpoint` definition

The algorithms are tested up to n=100,000 to provide confidence in the correctness of the targeted properties.

## What This Means for the Proof

These tests provide empirical evidence that:

1. The critical lemmas behave exactly as specified
2. The proof strategy is sound
3. Future refactors can rely on executable examples for quick feedback

They function as sanity checks alongside the formally verified Coq development.
