#!/usr/bin/env python3
"""
Test script to verify the admitted axioms in zeckendorf.v are true.
This gives us confidence that the axioms are correct before attempting to prove them.
"""

def fib(n):
    """Fibonacci function matching the Coq definition"""
    if n == 0:
        return 0
    elif n == 1:
        return 1
    else:
        a, b = 0, 1
        for _ in range(n - 1):
            a, b = b, a + b
        return b

def fibs_upto(n):
    """
    Generate list of Fibonacci numbers <= n, starting from fib(2).
    Matches: takeWhile (fun x => Nat.leb x n) (map fib (seq 2 (S n)))
    """
    result = []
    k = 2
    while True:
        f = fib(k)
        if f <= n:
            result.append(f)
            k += 1
        else:
            break
    return result

def zeckendorf(n, acc=None):
    """
    Greedy Zeckendorf algorithm matching the Coq implementation.
    Returns list of Fibonacci numbers in descending order.
    """
    if acc is None:
        acc = []

    if n == 0:
        return acc

    fibs = fibs_upto(n)
    if not fibs:
        return acc

    # Get largest (last in list)
    x = fibs[-1]

    if x <= n:
        # Cons x onto recursive result (builds descending order)
        return [x] + zeckendorf(n - x, acc)
    else:
        return acc

def nat_consecutive(i, j):
    """Check if two natural numbers are consecutive"""
    return i + 1 == j or j + 1 == i

# ============================================================================
# Test 1: largest_fib_in_fibs_upto
# ============================================================================

def test_largest_fib_in_fibs_upto():
    """
    Test: If fib(i) is the largest in fibs_upto(n), then n < fib(i+1)

    This is the property that the greedy algorithm always picks a Fibonacci
    number such that the next Fibonacci is too large.
    """
    print("=" * 70)
    print("TEST 1: largest_fib_in_fibs_upto")
    print("=" * 70)

    failures = []

    for n in range(1, 1000):
        fibs = fibs_upto(n)
        if not fibs:
            continue

        x = fibs[-1]  # largest

        # Find i such that fib(i) = x
        i = None
        for k in range(2, 100):
            if fib(k) == x:
                i = k
                break

        if i is None:
            failures.append(f"n={n}: Could not find index for x={x}")
            continue

        # Check: n < fib(i+1)
        if not (n < fib(i + 1)):
            failures.append(f"n={n}: x=fib({i})={x}, but n={n} >= fib({i+1})={fib(i+1)}")

    if failures:
        print(f"❌ FAILED: {len(failures)} cases")
        for f in failures[:10]:  # Show first 10
            print(f"  {f}")
    else:
        print(f"✅ PASSED: All 999 test cases")

    return len(failures) == 0

# ============================================================================
# Test 2: fib_in_fibs_upto
# ============================================================================

def test_fib_in_fibs_upto():
    """
    Test: If fib(k) <= n and k >= 2, then fib(k) is in fibs_upto(n)

    This ensures that fibs_upto correctly includes all Fibonacci numbers
    satisfying the predicate.
    """
    print("\n" + "=" * 70)
    print("TEST 2: fib_in_fibs_upto")
    print("=" * 70)

    failures = []

    for n in range(1, 500):
        fibs = fibs_upto(n)

        # Check all k >= 2 where fib(k) <= n
        for k in range(2, 50):
            fk = fib(k)
            if fk > n:
                break

            if fk not in fibs:
                failures.append(f"n={n}, k={k}: fib({k})={fk} <= {n} but not in fibs_upto")

    if failures:
        print(f"❌ FAILED: {len(failures)} cases")
        for f in failures[:10]:
            print(f"  {f}")
    else:
        print(f"✅ PASSED: All test cases")

    return len(failures) == 0

# ============================================================================
# Test 3: zeckendorf_fuel_no_consecutive_empty
# ============================================================================

def test_no_consecutive_fibs():
    """
    Test: zeckendorf(n) produces lists with no consecutive Fibonacci numbers

    For each adjacent pair of numbers in the result, their Fibonacci indices
    should not be consecutive.
    """
    print("\n" + "=" * 70)
    print("TEST 3: zeckendorf produces no consecutive Fibs")
    print("=" * 70)

    failures = []

    for n in range(1, 500):
        result = zeckendorf(n)

        # Find indices for each element
        indices = []
        for x in result:
            for k in range(2, 100):
                if fib(k) == x:
                    indices.append(k)
                    break

        # Check no consecutive indices
        for i in range(len(indices) - 1):
            if nat_consecutive(indices[i], indices[i+1]):
                failures.append(f"n={n}: result={result}, indices={indices}, "
                              f"fib({indices[i]}) and fib({indices[i+1]}) are consecutive")

    if failures:
        print(f"❌ FAILED: {len(failures)} cases")
        for f in failures[:10]:
            print(f"  {f}")
    else:
        print(f"✅ PASSED: All 499 test cases")

    return len(failures) == 0

# ============================================================================
# Test 4: zeckendorf_fuel_sorted_empty
# ============================================================================

def test_zeckendorf_sorted():
    """
    Test: zeckendorf(n) produces descending sorted lists

    Each element should be greater than the next.
    """
    print("\n" + "=" * 70)
    print("TEST 4: zeckendorf produces sorted (descending) lists")
    print("=" * 70)

    failures = []

    for n in range(1, 500):
        result = zeckendorf(n)

        # Check descending order
        for i in range(len(result) - 1):
            if not (result[i] > result[i+1]):
                failures.append(f"n={n}: result={result} not sorted: "
                              f"{result[i]} <= {result[i+1]} at index {i}")

    if failures:
        print(f"❌ FAILED: {len(failures)} cases")
        for f in failures[:10]:
            print(f"  {f}")
    else:
        print(f"✅ PASSED: All 499 test cases")

    return len(failures) == 0

# ============================================================================
# Additional Tests: Correctness of zeckendorf
# ============================================================================

def test_zeckendorf_correctness():
    """
    Test that zeckendorf correctly computes representations:
    1. All elements are Fibonacci numbers with index >= 2
    2. Sum equals n
    """
    print("\n" + "=" * 70)
    print("BONUS TEST: zeckendorf correctness")
    print("=" * 70)

    failures = []

    for n in range(1, 500):
        result = zeckendorf(n)

        # Check all elements are Fibonacci numbers >= 2
        for x in result:
            is_fib = False
            for k in range(2, 100):
                if fib(k) == x:
                    is_fib = True
                    break
            if not is_fib:
                failures.append(f"n={n}: {x} in result but not a Fibonacci number >= fib(2)")

        # Check sum equals n
        if sum(result) != n:
            failures.append(f"n={n}: sum({result}) = {sum(result)} != {n}")

    if failures:
        print(f"❌ FAILED: {len(failures)} cases")
        for f in failures[:10]:
            print(f"  {f}")
    else:
        print(f"✅ PASSED: All 499 test cases")

    return len(failures) == 0

# ============================================================================
# Main
# ============================================================================

def main():
    print("Testing all admitted axioms from zeckendorf.v\n")

    results = []

    results.append(("largest_fib_in_fibs_upto", test_largest_fib_in_fibs_upto()))
    results.append(("fib_in_fibs_upto", test_fib_in_fibs_upto()))
    results.append(("no_consecutive_fibs", test_no_consecutive_fibs()))
    results.append(("zeckendorf_sorted", test_zeckendorf_sorted()))
    results.append(("zeckendorf_correctness", test_zeckendorf_correctness()))

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    for name, passed in results:
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"{status}: {name}")

    all_passed = all(passed for _, passed in results)

    if all_passed:
        print("\n🎉 All axioms verified! They are true for n in [1, 500)")
    else:
        print("\n⚠️  Some axioms failed - review the output above")

    return 0 if all_passed else 1

if __name__ == "__main__":
    exit(main())
