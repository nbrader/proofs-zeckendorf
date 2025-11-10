#!/usr/bin/env python3
"""
Test script for verifying the admitted goals in the Coq proof of Zeckendorf's theorem.

This script empirically tests the properties that are admitted in the Coq proof
to build confidence that they are actually true.
"""

from typing import List, Optional, Tuple
import sys


# ============================================================================
# Helper Functions
# ============================================================================

def fib(n: int) -> int:
    """Compute the nth Fibonacci number (matching Coq definition)."""
    if n == 0:
        return 0
    elif n == 1:
        return 1
    else:
        a, b = 0, 1
        for _ in range(2, n + 1):
            a, b = b, a + b
        return b


def fibs_upto(n: int) -> List[int]:
    """
    Generate list of Fibonacci numbers <= n.
    Matches Coq definition: takeWhile (fun x => Nat.leb x n) (map fib (seq 1 (S n)))
    """
    result = []
    for i in range(1, n + 2):  # seq 1 (S n) in Coq
        f = fib(i)
        if f <= n:
            result.append(f)
        else:
            break
    return result


def zeckendorf(n: int) -> List[int]:
    """
    Greedy algorithm for Zeckendorf representation.
    Returns list of non-consecutive Fibonacci numbers that sum to n.
    """
    if n == 0:
        return []

    result = []
    while n > 0:
        # Find largest Fibonacci number <= n
        fibs = fibs_upto(n)
        if not fibs:
            break
        largest = fibs[-1]
        result.append(largest)
        n -= largest

    return result


def is_consecutive_fibs(i: int, j: int) -> bool:
    """Check if i and j are consecutive indices (nat_consecutive in Coq)."""
    return abs(i - j) == 1


def fib_index(value: int) -> Optional[int]:
    """Find the index i such that fib(i) = value, or None if not found."""
    for i in range(100):  # Check first 100 Fibonacci numbers
        if fib(i) == value:
            return i
        if fib(i) > value:
            return None
    return None


def has_consecutive_fibs(zeck_repr: List[int]) -> bool:
    """Check if the Zeckendorf representation has consecutive Fibonacci numbers."""
    indices = []
    for val in zeck_repr:
        idx = fib_index(val)
        if idx is None:
            print(f"Warning: {val} is not a Fibonacci number!")
            return True
        indices.append(idx)

    # Check if any pair of indices are consecutive
    for i in range(len(indices)):
        for j in range(i + 1, len(indices)):
            if is_consecutive_fibs(indices[i], indices[j]):
                return True
    return False


# ============================================================================
# Test 1: fib_in_fibs_upto
# ============================================================================

def test_fib_in_fibs_upto(max_k: int = 20, max_n: int = 1000) -> Tuple[int, int]:
    """
    Test the admitted lemma: fib_in_fibs_upto

    Claim: forall k n, k >= 1 -> fib k <= n -> In (fib k) (fibs_upto n)

    Translation: If k >= 1 and fib(k) <= n, then fib(k) is in fibs_upto(n).

    Returns: (passed, total) test count
    """
    print("\n" + "="*70)
    print("TEST 1: fib_in_fibs_upto")
    print("="*70)
    print("Claim: If k >= 1 and fib(k) <= n, then fib(k) is in fibs_upto(n)")
    print()

    passed = 0
    total = 0
    failures = []

    for k in range(1, max_k + 1):
        fib_k = fib(k)

        # Only test for n values where fib(k) <= n
        for n in range(fib_k, min(fib_k + 100, max_n + 1)):
            total += 1
            fibs = fibs_upto(n)

            if fib_k in fibs:
                passed += 1
            else:
                failures.append((k, n, fib_k, fibs))
                if len(failures) <= 5:  # Only print first 5 failures
                    print(f"FAIL: k={k}, n={n}, fib({k})={fib_k}, fibs_upto({n})={fibs}")

    print(f"\nResult: {passed}/{total} tests passed")
    if failures:
        print(f"WARNING: {len(failures)} failures detected!")
    else:
        print("✓ All tests passed!")

    return passed, total


# ============================================================================
# Test 2: largest_fib_in_fibs_upto
# ============================================================================

def test_largest_fib_in_fibs_upto(max_n: int = 1000) -> Tuple[int, int]:
    """
    Test the admitted lemma: largest_fib_in_fibs_upto

    Claim: forall x i n xs,
      i >= 2 ->
      fib i = x ->
      rev (fibs_upto n) = x :: xs ->
      x < n ->
      n < fib (S i)

    Translation: If x is the largest Fibonacci number <= n (i.e., the head of
    rev(fibs_upto n)), where fib(i) = x, and x < n, then n < fib(i+1).

    Returns: (passed, total) test count
    """
    print("\n" + "="*70)
    print("TEST 2: largest_fib_in_fibs_upto")
    print("="*70)
    print("Claim: If x is the largest Fib <= n (where fib(i) = x, i >= 2)")
    print("       and x < n, then n < fib(i+1)")
    print()

    passed = 0
    total = 0
    failures = []

    for n in range(2, max_n + 1):
        fibs = fibs_upto(n)

        if not fibs:
            continue

        # x is the largest (last element of fibs_upto)
        x = fibs[-1]

        # Find i such that fib(i) = x
        i = fib_index(x)

        if i is None:
            print(f"ERROR: Could not find index for {x}")
            continue

        # Only test when i >= 2 and x < n
        if i >= 2 and x < n:
            total += 1

            # Check if n < fib(i+1)
            fib_next = fib(i + 1)

            if n < fib_next:
                passed += 1
            else:
                failures.append((n, x, i, fib_next))
                if len(failures) <= 5:
                    print(f"FAIL: n={n}, x={x}, i={i}, fib({i+1})={fib_next}")
                    print(f"      Expected: {n} < {fib_next}, but {n} >= {fib_next}")

    print(f"\nResult: {passed}/{total} tests passed")
    if failures:
        print(f"WARNING: {len(failures)} failures detected!")
    else:
        print("✓ All tests passed!")

    return passed, total


# ============================================================================
# Test 3: zeckendorf_no_consecutive
# ============================================================================

def test_zeckendorf_no_consecutive(max_n: int = 1000) -> Tuple[int, int]:
    """
    Test the admitted lemma: zeckendorf_fuel_no_consecutive_empty

    Claim: forall fuel n, no_consecutive_fibs (zeckendorf_fuel fuel n [])

    Translation: The Zeckendorf representation of any number n contains no
    consecutive Fibonacci numbers.

    Returns: (passed, total) test count
    """
    print("\n" + "="*70)
    print("TEST 3: zeckendorf_no_consecutive")
    print("="*70)
    print("Claim: The Zeckendorf representation contains no consecutive Fibonacci numbers")
    print()

    passed = 0
    total = 0
    failures = []

    for n in range(1, max_n + 1):
        total += 1
        zeck = zeckendorf(n)

        if not has_consecutive_fibs(zeck):
            passed += 1
        else:
            failures.append((n, zeck))
            if len(failures) <= 10:
                indices = [fib_index(v) for v in zeck]
                print(f"FAIL: n={n}, zeckendorf={zeck}, indices={indices}")

    print(f"\nResult: {passed}/{total} tests passed")
    if failures:
        print(f"WARNING: {len(failures)} failures detected!")
    else:
        print("✓ All tests passed!")

    return passed, total


# ============================================================================
# Test 4: Additional Property Tests
# ============================================================================

def test_zeckendorf_sum_correctness(max_n: int = 1000) -> Tuple[int, int]:
    """
    Sanity check: Verify that the Zeckendorf representation sums to n.
    """
    print("\n" + "="*70)
    print("TEST 4: zeckendorf_sum_correctness (sanity check)")
    print("="*70)
    print("Claim: sum(zeckendorf(n)) = n")
    print()

    passed = 0
    total = 0
    failures = []

    for n in range(1, max_n + 1):
        total += 1
        zeck = zeckendorf(n)
        zeck_sum = sum(zeck)

        if zeck_sum == n:
            passed += 1
        else:
            failures.append((n, zeck, zeck_sum))
            if len(failures) <= 5:
                print(f"FAIL: n={n}, zeckendorf={zeck}, sum={zeck_sum}")

    print(f"\nResult: {passed}/{total} tests passed")
    if failures:
        print(f"WARNING: {len(failures)} failures detected!")
    else:
        print("✓ All tests passed!")

    return passed, total


def test_zeckendorf_all_fibs(max_n: int = 1000) -> Tuple[int, int]:
    """
    Sanity check: Verify that all elements in Zeckendorf representation are Fibonacci numbers.
    """
    print("\n" + "="*70)
    print("TEST 5: zeckendorf_all_fibs (sanity check)")
    print("="*70)
    print("Claim: All elements in zeckendorf(n) are Fibonacci numbers")
    print()

    passed = 0
    total = 0
    failures = []

    for n in range(1, max_n + 1):
        total += 1
        zeck = zeckendorf(n)
        all_fibs = all(fib_index(val) is not None for val in zeck)

        if all_fibs:
            passed += 1
        else:
            failures.append((n, zeck))
            if len(failures) <= 5:
                print(f"FAIL: n={n}, zeckendorf={zeck}")
                for val in zeck:
                    if fib_index(val) is None:
                        print(f"      {val} is not a Fibonacci number")

    print(f"\nResult: {passed}/{total} tests passed")
    if failures:
        print(f"WARNING: {len(failures)} failures detected!")
    else:
        print("✓ All tests passed!")

    return passed, total


# ============================================================================
# Main Test Runner
# ============================================================================

def main():
    """Run all tests and print summary."""
    print("="*70)
    print("TESTING ADMITTED GOALS IN ZECKENDORF COQPROOF")
    print("="*70)
    print()
    print("This script empirically tests the properties that are admitted")
    print("in the Coq proof to build confidence that they are true.")
    print()

    # Run all tests
    results = []
    results.append(test_fib_in_fibs_upto(max_k=20, max_n=1000))
    results.append(test_largest_fib_in_fibs_upto(max_n=1000))
    results.append(test_zeckendorf_no_consecutive(max_n=1000))
    results.append(test_zeckendorf_sum_correctness(max_n=1000))
    results.append(test_zeckendorf_all_fibs(max_n=1000))

    # Print summary
    print("\n" + "="*70)
    print("SUMMARY")
    print("="*70)

    total_passed = sum(r[0] for r in results)
    total_tests = sum(r[1] for r in results)

    print(f"Total: {total_passed}/{total_tests} tests passed")
    print(f"Success rate: {100 * total_passed / total_tests:.2f}%")

    if total_passed == total_tests:
        print("\n✓ All admitted goals appear to be correct!")
        return 0
    else:
        print(f"\n✗ {total_tests - total_passed} test(s) failed!")
        return 1


if __name__ == "__main__":
    sys.exit(main())
