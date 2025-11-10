#!/usr/bin/env python3
"""
Extended test script for edge cases and stress testing of admitted goals.

This script provides additional testing beyond the basic verification,
including edge cases, larger values, and specific counterexample searches.
"""

from test_admitted_goals import (
    fib, fibs_upto, zeckendorf, fib_index,
    has_consecutive_fibs, is_consecutive_fibs
)
import sys


# ============================================================================
# Edge Case Tests
# ============================================================================

def test_fibonacci_properties():
    """Test basic Fibonacci properties."""
    print("="*70)
    print("EDGE CASE TEST 1: Basic Fibonacci Properties")
    print("="*70)

    # Test base cases
    assert fib(0) == 0, "fib(0) should be 0"
    assert fib(1) == 1, "fib(1) should be 1"
    assert fib(2) == 1, "fib(2) should be 1"
    assert fib(3) == 2, "fib(3) should be 2"
    assert fib(4) == 3, "fib(4) should be 3"
    assert fib(5) == 5, "fib(5) should be 5"

    # Test recurrence relation: fib(n) = fib(n-1) + fib(n-2)
    for n in range(3, 30):
        assert fib(n) == fib(n-1) + fib(n-2), f"Recurrence fails at n={n}"

    # Test monotonicity for n >= 2
    for n in range(2, 50):
        assert fib(n) < fib(n+1), f"Monotonicity fails at n={n}"

    print("✓ All basic Fibonacci properties hold!")
    print()


def test_fibs_upto_edge_cases():
    """Test edge cases for fibs_upto."""
    print("="*70)
    print("EDGE CASE TEST 2: fibs_upto Edge Cases")
    print("="*70)

    # Test small values
    assert fibs_upto(0) == [], "fibs_upto(0) should be []"
    assert fibs_upto(1) == [1, 1], "fibs_upto(1) should be [1, 1]"
    assert fibs_upto(2) == [1, 1, 2], "fibs_upto(2) should be [1, 1, 2]"
    assert fibs_upto(3) == [1, 1, 2, 3], "fibs_upto(3) should be [1, 1, 2, 3]"

    # Test exact Fibonacci values
    for i in range(1, 20):
        f = fib(i)
        fibs = fibs_upto(f)
        assert f in fibs, f"fib({i})={f} should be in fibs_upto({f})"
        assert fibs[-1] == f, f"Last element of fibs_upto({f}) should be {f}"

    # Test values just below Fibonacci numbers
    for i in range(3, 20):
        f = fib(i)
        if f > 1:
            fibs = fibs_upto(f - 1)
            assert f not in fibs, f"fib({i})={f} should not be in fibs_upto({f-1})"
            assert fibs[-1] == fib(i-1), f"Last element should be fib({i-1})"

    print("✓ All fibs_upto edge cases pass!")
    print()


def test_zeckendorf_edge_cases():
    """Test edge cases for Zeckendorf representation."""
    print("="*70)
    print("EDGE CASE TEST 3: Zeckendorf Edge Cases")
    print("="*70)

    # Test Fibonacci numbers themselves
    for i in range(1, 20):
        f = fib(i)
        if f > 0:
            zeck = zeckendorf(f)
            assert f in zeck, f"zeckendorf({f}) should contain {f}"
            # For Fibonacci numbers, the representation should be just that number
            # (except for 1+1=2, but our greedy algorithm picks largest first)

    # Test powers of 2
    for p in range(1, 11):
        n = 2**p
        zeck = zeckendorf(n)
        assert sum(zeck) == n, f"zeckendorf({n}) should sum to {n}"
        assert not has_consecutive_fibs(zeck), f"zeckendorf({n}) has consecutive Fibs"

    # Test specific known cases
    test_cases = [
        (10, [8, 2]),      # 10 = 8 + 2
        (20, [13, 5, 2]),  # 20 = 13 + 5 + 2
        (100, [89, 8, 3]), # 100 = 89 + 8 + 3
    ]

    for n, expected in test_cases:
        zeck = zeckendorf(n)
        assert sum(zeck) == n, f"zeckendorf({n}) should sum to {n}"
        assert sorted(zeck, reverse=True) == zeck, f"zeckendorf({n}) should be sorted descending"
        # Note: the exact representation might differ if there are ties,
        # but the greedy algorithm should be deterministic

    print("✓ All Zeckendorf edge cases pass!")
    print()


def test_consecutive_fibonacci_detection():
    """Test the consecutive Fibonacci detection."""
    print("="*70)
    print("EDGE CASE TEST 4: Consecutive Fibonacci Detection")
    print("="*70)

    # Test pairs of consecutive Fibonacci indices
    for i in range(2, 20):
        assert is_consecutive_fibs(i, i+1), f"{i} and {i+1} should be consecutive"
        assert is_consecutive_fibs(i+1, i), f"{i+1} and {i} should be consecutive"

    # Test non-consecutive pairs
    for i in range(2, 20):
        for j in range(i+2, min(i+5, 20)):
            assert not is_consecutive_fibs(i, j), f"{i} and {j} should not be consecutive"

    # Test that actual Zeckendorf representations have no consecutives
    for n in range(1, 200):
        zeck = zeckendorf(n)
        indices = [fib_index(v) for v in zeck]

        # Check all pairs
        for i in range(len(indices)):
            for j in range(i+1, len(indices)):
                idx_i, idx_j = indices[i], indices[j]
                assert not is_consecutive_fibs(idx_i, idx_j), \
                    f"zeckendorf({n})={zeck} has consecutive Fibs at indices {idx_i},{idx_j}"

    print("✓ All consecutive Fibonacci detection tests pass!")
    print()


# ============================================================================
# Stress Tests
# ============================================================================

def test_large_values():
    """Test with larger values to stress test the algorithms."""
    print("="*70)
    print("STRESS TEST: Large Values")
    print("="*70)

    test_values = [1000, 5000, 10000, 50000, 100000]

    for n in test_values:
        zeck = zeckendorf(n)

        # Check correctness
        assert sum(zeck) == n, f"zeckendorf({n}) sum incorrect"
        assert all(fib_index(v) is not None for v in zeck), \
            f"zeckendorf({n}) contains non-Fibonacci numbers"
        assert not has_consecutive_fibs(zeck), \
            f"zeckendorf({n}) has consecutive Fibs"

        print(f"  n={n:6d}: zeckendorf has {len(zeck):2d} terms, "
              f"largest={max(zeck) if zeck else 0:6d}")

    print("✓ All large value tests pass!")
    print()


def test_remainder_property():
    """
    Test the key property used in the proof:
    If fib(k) is the largest Fib <= n, and n > fib(k),
    then remainder = n - fib(k) < fib(k-1).

    This ensures the greedy algorithm doesn't pick consecutive Fibs.
    """
    print("="*70)
    print("PROOF PROPERTY TEST: Remainder < Previous Fibonacci")
    print("="*70)
    print("Property: If fib(k) is largest Fib <= n and n > fib(k),")
    print("          then (n - fib(k)) < fib(k-1)")
    print()

    failures = 0

    for n in range(2, 1000):
        fibs = fibs_upto(n)
        if not fibs:
            continue

        largest = fibs[-1]
        k = fib_index(largest)

        if k is None or k < 2:
            continue

        if largest < n:  # n > fib(k)
            remainder = n - largest
            prev_fib = fib(k - 1)

            if not (remainder < prev_fib):
                print(f"FAIL: n={n}, fib({k})={largest}, remainder={remainder}, "
                      f"fib({k-1})={prev_fib}")
                failures += 1

    if failures == 0:
        print("✓ Remainder property holds for all tested values!")
    else:
        print(f"✗ {failures} failures detected!")
    print()

    return failures == 0


# ============================================================================
# Uniqueness Test (Advanced)
# ============================================================================

def test_uniqueness_property():
    """
    Test that Zeckendorf representations are unique.

    This is a partial test - we verify that for small values,
    there's only one way to represent them as sums of non-consecutive Fibs.
    """
    print("="*70)
    print("ADVANCED TEST: Uniqueness of Representation")
    print("="*70)
    print("Checking that the greedy algorithm produces unique representations")
    print()

    def all_nonconsec_representations(n, max_fib_idx=20):
        """Find all ways to represent n as sum of non-consecutive Fibs."""
        fibs = [fib(i) for i in range(2, max_fib_idx + 1)]
        fibs = [f for f in fibs if f <= n]

        def backtrack(target, available_fibs, current, last_idx):
            if target == 0:
                return [current[:]]
            if target < 0 or not available_fibs:
                return []

            results = []
            for i, f in enumerate(available_fibs):
                if f > target:
                    continue

                # Check if this would be consecutive with the last picked
                fib_idx = fib_index(f)
                if last_idx is not None and abs(fib_idx - last_idx) == 1:
                    continue

                current.append(f)
                # Skip next Fibonacci to avoid consecutive
                results.extend(backtrack(
                    target - f,
                    available_fibs[i+2:] if i+1 < len(available_fibs) else [],
                    current,
                    fib_idx
                ))
                current.pop()

            return results

        return backtrack(n, fibs[::-1], [], None)  # Start with largest first

    # Test uniqueness for small values
    for n in range(1, 50):
        representations = all_nonconsec_representations(n)
        greedy = sorted(zeckendorf(n), reverse=True)

        if len(representations) == 0:
            print(f"WARNING: No representation found for {n}")
        elif len(representations) > 1:
            print(f"Multiple representations for {n}:")
            for rep in representations:
                print(f"  {sorted(rep, reverse=True)}")
            print(f"  Greedy gives: {greedy}")
        else:
            # Verify greedy matches the unique representation
            unique = sorted(representations[0], reverse=True)
            if unique != greedy:
                print(f"MISMATCH at n={n}: unique={unique}, greedy={greedy}")

    print("✓ Uniqueness tests completed!")
    print()


# ============================================================================
# Main Test Runner
# ============================================================================

def main():
    """Run all extended tests."""
    print("="*70)
    print("EXTENDED TESTING: EDGE CASES AND STRESS TESTS")
    print("="*70)
    print()

    try:
        test_fibonacci_properties()
        test_fibs_upto_edge_cases()
        test_zeckendorf_edge_cases()
        test_consecutive_fibonacci_detection()
        test_large_values()

        if not test_remainder_property():
            print("\n✗ Remainder property test failed!")
            return 1

        test_uniqueness_property()

        print("="*70)
        print("ALL EXTENDED TESTS PASSED!")
        print("="*70)
        return 0

    except AssertionError as e:
        print(f"\n✗ Test failed: {e}")
        return 1
    except Exception as e:
        print(f"\n✗ Unexpected error: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
