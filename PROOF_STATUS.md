# Zeckendorf Theorem Proof Status

## Branch: `claude/sorted-lists-011CUYYXjhnTQmurLvAS6v4Z`

This branch implements a **sorted list approach** to the Zeckendorf theorem proofs, dramatically simplifying the proof structure by eliminating complex case analysis about element positions.

## Key Innovation: Sorted Lists

The user requested:
> "rework the existing proofs to use sorted lists throughout (which is closer to the wikipedia proof that uses sets to avoid worrying about permutations and difficulty finding the max and proving things about monotonicity."

### Benefits of Sorted List Approach

1. **Maximum finding is trivial**: For descending sorted lists, `max l = head l`
2. **NoDup automatic**: Sorted lists with strictly decreasing elements are automatically distinct
3. **Adjacent-only checking**: For non-consecutive property, only need to check adjacent pairs
4. **No position case analysis**: Eliminate complex reasoning about where elements appear in list
5. **Cleaner proofs**: Much shorter, more direct proofs

## Completed Work

### ✅ Sorted List Infrastructure (lines 615-709)

Added complete infrastructure for working with sorted lists:

1. **`Sorted_dec` predicate** (line 621):
   - Defines descending sorted lists (strictly decreasing)
   - `Fixpoint` with pattern matching on list structure

2. **`sorted_head_max` lemma** (line 630):
   - Proves that in sorted list, head is greater than all tail elements
   - **Completed proof** using induction

3. **`sorted_NoDup` lemma** (line 647):
   - Proves sorted lists automatically have no duplicates
   - **Completed proof** using sorted_head_max

4. **`sorted_max` definition** (line 668):
   - Trivial maximum function for sorted lists (just return head)
   - Much simpler than general `list_max`

5. **`no_consecutive_fibs_sorted` predicate** (line 681):
   - Simplified predicate checking only adjacent pairs
   - For sorted Fibonacci lists, this is equivalent to checking all pairs

6. **Helper lemmas**:
   - `sorted_tail_lt` (line 694): All tail elements less than head
   - `sorted_tail` (line 703): Tail of sorted list is sorted

### ✅ Simplified Bounded Sum Lemma (lines 1352-1494)

Created **`sum_nonconsec_fibs_bounded_sorted`** - dramatically simpler version of the main lemma:

```coq
Lemma sum_nonconsec_fibs_bounded_sorted : forall k xs,
  k >= 2 ->
  Sorted_dec (fib k :: xs) ->
  no_consecutive_fibs_sorted (fib k :: xs) ->
  (forall x, In x (fib k :: xs) -> exists i, fib i = x) ->
  sum_list (fib k :: xs) < fib (S k).
```

**Key simplifications compared to original version**:
- Pattern match directly on `fib k :: xs` (no need to search for max)
- No `NoDup` precondition (follows from `Sorted_dec`)
- Use `no_consecutive_fibs_sorted` for adjacent-only checking
- Much cleaner proof structure

**Proof structure**:
- ✅ Base case k=2: Completed with sorted list reasoning
- ✅ Inductive case k≥3:
  - Shows fib(k-1) NOT in xs by checking adjacent pair
  - Empty list case: Completed using monotonicity
  - Non-empty list case: **2 admits remain** (same conceptual issues as original proof)

**Admits in sorted version** (lines 1480, 1503):
1. When fib(k-1) is deeper in tail (not adjacent): Need stronger property about sorted lists
2. Showing y ≤ fib(k-2) when y < fib k, y ≠ fib(k-1): Needs Fibonacci gap lemma

## Comparison with Original Version

| Aspect | Original (unsorted) | Sorted Version |
|--------|-------------------|---------------|
| **Lines of proof** | ~430 lines (1315-1744) | ~140 lines (1352-1494) |
| **Max finding** | Complex `list_max` reasoning | Trivial (head element) |
| **NoDup proof** | Explicit precondition required | Automatic from sorting |
| **Case analysis** | 8+ nested cases for element positions | 2-3 simple cases |
| **Non-consecutive check** | All pairs (n² checks) | Adjacent pairs only (n checks) |
| **Proof clarity** | Heavy case analysis | Direct, intuitive |

**Estimated complexity reduction**: ~60-70% fewer lines, much simpler reasoning

## Original Version (kept for reference)

The original `sum_nonconsec_fibs_bounded` (lines 1528-1898) is kept for reference, labeled as:
```coq
(*
  ==============================================================================
  ORIGINAL UNSORTED VERSION (for reference)
  ==============================================================================
*)
```

It still has the same admits as before, but now we have a cleaner sorted version to work with.

## Build Status

✅ **File compiles successfully** (as of 2025-11-06)

```bash
coqc -Q Coq Zeckendorf Coq/zeckendorf.v
```

All infrastructure compiles cleanly. The sorted version lemma compiles with 2 admits.

## Next Steps

### Immediate (This Branch)

1. **Complete the 2 admits in `sum_nonconsec_fibs_bounded_sorted`**:
   - Admit at line 1480: Prove that in sorted non-consecutive Fibonacci list, fib(k-1) cannot appear anywhere (not just adjacent to fib k)
   - Admit at line 1503: Prove that if y < fib k, y ≠ fib(k-1), and y is Fibonacci, then y ≤ fib(k-2)

2. **Add helper lemmas**:
   - Fibonacci gap lemma: Between fib k and fib(k-2), only fib(k-1) exists
   - Sorted implies strong non-consecutive: For sorted Fibonacci lists, adjacent-only checking suffices

3. **Update other lemmas** to use sorted list versions

### Future Work

Once sorted version is complete:

1. **Refactor greedy algorithm** to produce sorted output
2. **Update zeckendorf_fuel_no_consecutive** to use sorted lists
3. **Update zeckendorf_unique** to use sorted lists
4. **Prove equivalence**: Sorted version ↔ Original version (for compatibility)

## Key Insights

The sorted list approach demonstrates that the **Wikipedia proof strategy** (using sets) translates well to Coq by using **sorted lists as canonical representatives** of sets. This avoids:
- Permutation reasoning
- Complex element position case analysis
- Explicit distinctness proofs
- Maximum finding complexity

The result is **significantly simpler and more maintainable code**.

## Key Files

- `Coq/zeckendorf.v` - Main file with both sorted and unsorted versions
- `Coq/build_coq.sh` - Build script
- `PROOF_STATUS.md` - This file

Generated: 2025-11-06
Branch: `claude/sorted-lists-011CUYYXjhnTQmurLvAS6v4Z`
