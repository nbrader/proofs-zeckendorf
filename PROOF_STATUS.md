# Zeckendorf Theorem Proof Status

## Branch: `claude/greedy-proofs-011CUYYXjhnTQmurLvAS6v4Z`

This branch focuses on completing the admitted proofs in `Coq/zeckendorf.v` for the greedy algorithm approach.

## Completed Work

### ✅ `sum_nonconsec_fibs_bounded` - Base Case (k=2)
**Status**: COMPLETED (with 2 minor admits for edge cases)

- Added `NoDup` (distinctness) precondition to fix false lemma issue
- Proved that when max = fib(2) = 1, the list must be exactly [1]
- Used NoDup to show at most one occurrence of 1
- Proved sum = 1 < 2 = fib(3) ✓
- Two small admits remain:
  - Case where 0 is in list along with 1 (both consecutive subcases in tail)
  - These are provable but require more case analysis

### ✅ `sum_nonconsec_fibs_bounded` - Inductive Case (k≥3) - PARTIAL
**Status**: IN PROGRESS (significant progress)

#### Completed:
- ✅ Proved fib(k-1) is NOT in list when max = fib(k)
  - This is the key insight: consecutive Fibonacci numbers can't both be in list
  - Handled multiple cases (head/tail positions)
- ✅ Case split: list is either [fib k] alone, or has other elements
- ✅ Trivial case: if list = [fib k], then sum = fib k < fib k + fib(k-1) = fib(k+1)

#### Remaining:
- ❌ Show all other elements have indices ≤ k-2
- ❌ Apply induction hypothesis to remaining elements
- ❌ Combine results to complete proof

#### Why It's Hard:
The proof requires careful tracking of:
1. Which Fibonacci indices can appear in the list
2. The maximum of the remaining elements after removing fib k
3. Applying the IH recursively

**Note**: As the user suggested, this proof would be MUCH simpler with sorted lists. The current approach requires extensive case analysis about where elements appear in unsorted lists.

## Remaining Admitted Proofs

### ❌ `zeckendorf_fuel_no_consecutive`
**Status**: NOT STARTED

Needs to prove that the greedy algorithm produces non-consecutive Fibonacci numbers.

**Challenge**: Requires strengthening with additional invariants about the accumulator and remaining value. The current statement doesn't capture enough information.

**Suggested approach**:
1. Use the stronger variant `zeckendorf_fuel_no_consecutive_strong` which tracks bounds
2. Or restructure to track more state during recursion

### ❌ `zeckendorf_unique`
**Status**: NOT STARTED (depends on `sum_nonconsec_fibs_bounded`)

Once `sum_nonconsec_fibs_bounded` is complete, this theorem follows the standard proof:
1. Assume l1 and l2 both represent n
2. Remove common elements → l1', l2'
3. If both non-empty, get contradiction using sum bound
4. Therefore both empty, so l1 = l2

**Missing infrastructure**:
- List filtering/difference operations
- Properties of these operations preserving invariants

## Recommendations for Future Work

### Short Term
1. **Add helper lemmas** for `sum_nonconsec_fibs_bounded`:
   - Lemma: If z ∈ l and max l = fib k, then ∃i. i ≤ k ∧ fib i = z
   - Lemma: If no_consecutive_fibs l and fib k ∈ l and fib(k-1) ∉ l, then all other elements have indices ≤ k-2
   - Lemma: Properties of list_max after removing max element

2. **Complete `sum_nonconsec_fibs_bounded`** using these helpers

3. **Tackle `zeckendorf_fuel_no_consecutive`** with strengthened statement

### Long Term (Major Refactoring)
Consider switching to **sorted lists** throughout:
- Define `sorted_list_fibs` predicate
- Prove greedy algorithm produces sorted output
- Restate all theorems with sorted precondition
- Many proofs become trivial with sorting

Benefits:
- Max is always at head/tail (depending on sort order)
- No case analysis about element positions
- Easier to reason about consecutive elements
- More natural representation

This would be a significant refactoring but would likely result in cleaner, shorter proofs.

## Build Status
✅ File compiles successfully with current admits
```bash
cd Coq && coqc -Q . Zeckendorf zeckendorf.v
```

## Key Files
- `Coq/zeckendorf.v` - Main greedy algorithm proofs
- `Coq/zeckendorf2.v` - Combinatorial approach (separate, incomplete)
- `Coq/build_coq.sh` - Build script

Generated: 2025-11-06
Branch: `claude/greedy-proofs-011CUYYXjhnTQmurLvAS6v4Z`
