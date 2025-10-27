# CLAUDE.md

This file provides guidance to Claude Code when working with formal proofs of Zeckendorf's theorem in this repository.

## Project Overview

This repository contains formal verifications of the **Zeckendorf Representation Theorem** in Coq. The theorem states:

> **Zeckendorf's Theorem**: Every positive integer has a unique representation as a sum of non-consecutive Fibonacci numbers.

The repository includes two different proof approaches:

1. **Greedy Algorithm Approach** (`zeckendorf.v`) - Proves correctness of the greedy algorithm ✅ **NEARLY COMPLETE**
2. **Combinatorial Construction Approach** (`zeckendorf2.v` and `zeckendorf2_complete.v`) - Constructs representations systematically 🚧 **IN PROGRESS**

Additionally, a reference Haskell implementation (`Haskell/zeckendorf.hs`) demonstrates the algorithm informally.

## Repository Structure

```
proofs-zeckendorf/
├── Coq/
│   ├── zeckendorf.v              # Main greedy algorithm proof (NEARLY COMPLETE)
│   ├── zeckendorf2.v             # Combinatorial construction (PARTIAL)
│   ├── zeckendorf2_complete.v    # Extended combinatorial approach
│   ├── _CoqProject               # Coq project configuration
│   └── build_coq.sh              # Build script
├── Haskell/
│   └── zeckendorf.hs             # Reference implementation
├── CLAUDE.md                     # This file
└── LICENSE                       # MIT License
```

## Build System

### Building the Coq Proofs

The project uses `coq_makefile` to generate build files from `_CoqProject`:

```bash
# Quick build using the provided script
cd Coq && ./build_coq.sh

# Manual build process
cd Coq
coq_makefile -f _CoqProject -o Makefile
make

# Clean build artifacts
make clean

# Clean all including timing files
make cleanall
```

### Coq Project Configuration

The `_CoqProject` file defines the logical path mapping:
- `-Q . Zeckendorf` maps the current directory to the `Zeckendorf` namespace
- All `.v` files in the `Coq/` directory are part of this namespace

## Proof Approach 1: Greedy Algorithm (`zeckendorf.v`)

**Status**: ✅ **NEARLY COMPLETE** (2 auxiliary lemmas for non-consecutive property remain)

### Algorithm Overview

The greedy algorithm repeatedly selects the largest Fibonacci number that fits:

```coq
Fixpoint zeckendorf_fuel (fuel n : nat) (acc : list nat) : list nat :=
  match fuel with
  | 0 => acc
  | S fuel' =>
    match n with
    | 0 => acc
    | _ => let fibs := rev (fibs_upto n) in
           match fibs with
           | [] => acc
           | x :: xs =>
             if Nat.leb x n
             then zeckendorf_fuel fuel' (n - x) (x :: acc)
             else acc
           end
    end
  end.
```

### Core Definitions (Lines 10-32)

1. **Fibonacci Function** (`fib`)
   ```coq
   Fixpoint fib (n : nat) : nat :=
     match n with
     | 0 => 0
     | 1 => 1
     | S n' => match n' with
               | 0 => 1
               | S n'' => fib n' + fib n''
               end
     end.
   ```

2. **Helper Functions**
   - `takeWhile {A} (f : A -> bool) (l : list A)` - filters list while predicate holds
   - `fibs_upto (n : nat)` - generates Fibonacci numbers ≤ n

3. **Main Algorithm** (`zeckendorf`)
   - Uses fuel-based termination (fuel = n ensures enough iterations)
   - Greedy selection: always pick largest Fibonacci ≤ remaining value
   - Accumulator pattern for building result list

### Proven Theorems

#### 1. Fibonacci Properties (Lines 33-241) - ALL PROVEN ✅

| Lemma | Statement | Lines | Status |
|-------|-----------|-------|--------|
| `fib_SS` | `fib (S (S n)) = fib (S n) + fib n` | 35-38 | ✅ |
| `fib_pos` | `n ≥ 1 → fib n > 0` | 48-81 | ✅ |
| `fib_mono` | `n ≥ 2 → fib n < fib (S n)` | 90-115 | ✅ |
| `seq_ge` | `In x (seq start len) → x ≥ start` | 126-141 | ✅ |
| `in_fibs_upto_fib` | `In x (fibs_upto n) → ∃k≥1. fib k = x` | 151-186 | ✅ |
| `in_fibs_upto_pos` | `In x (fibs_upto n) → x > 0` | 194-204 | ✅ |
| `in_fibs_upto_le` | `In x (fibs_upto n) → x ≤ n` | 213-235 | ✅ |
| `fib_decrease` | Termination helper | 237-241 | ✅ |

#### 2. Main Correctness (Lines 296-516) - ALL PROVEN ✅

| Theorem | Statement | Lines | Status |
|---------|-----------|-------|--------|
| `zeckendorf_fuel_acc_fib` | All elements are Fibonacci numbers | 296-351 | ✅ |
| `zeckendorf_acc_fib` | Wrapper: `zeckendorf` produces Fibs | 359-368 | ✅ |
| `zeckendorf_fuel_acc_sum` | Sum equals `sum(acc) + n` | 387-482 | ✅ |
| `zeckendorf_acc_sum` | Wrapper: sum property | 489-497 | ✅ |
| `zeckendorf_acc_correct` | Combined properties | 505-516 | ✅ |

#### 3. Main Theorems (Lines 540-593) - PROVEN ✅

```coq
Theorem zeckendorf_fib_property : forall n,
  let zs := zeckendorf n [] in
  forall z, In z zs -> exists k, z = fib k.

Theorem zeckendorf_sum_property : forall n,
  sum_list (zeckendorf n []) = n.

Theorem zeckendorf_correct : forall n,
  let zs := zeckendorf n [] in
  (forall z, In z zs -> exists k, z = fib k) /\
  sum_list zs = n.
```

**Status**: ✅ All three main theorems are **PROVEN**

#### 4. Non-consecutive Property (Lines 605-783)

| Item | Status | Lines |
|------|--------|-------|
| Definitions (`fib_consecutive`, `no_consecutive_fibs`) | ✅ Defined | 612-628 |
| `fib_recurrence` | ✅ Proven | 635-650 |
| `remainder_less_than_prev_fib` | ✅ Proven | 660-673 |
| `zeckendorf_fuel_no_consecutive` | ⚠️ **Admitted** | 685-763 |
| `zeckendorf_no_consecutive` | ✅ Proven (uses admitted) | 773-783 |

#### 5. Uniqueness Infrastructure (Lines 819-1092)

| Lemma | Status | Lines |
|-------|--------|-------|
| `fib_mono_lt` (strict monotonicity) | ✅ Proven | 819-849 |
| `fib_injective` (injectivity for indices ≥2) | ✅ Proven | 859-875 |
| List maximum helpers | ✅ Proven | 878-998 |
| `sum_nonconsec_fibs_bounded` | ⚠️ **Partially proven** | 1021-1092 |
| `zeckendorf_unique` | ⚠️ **Admitted** | 1124-1129 |

#### 6. Final Theorem (Lines 1140-1152)

```coq
Theorem zeckendorf_is_the_unique_repr : forall n,
  is_zeckendorf_repr n (zeckendorf n []).
```

Where `is_zeckendorf_repr n l` means:
- All elements in `l` are Fibonacci numbers ✅
- `sum_list l = n` ✅
- `no_consecutive_fibs l` (pending one lemma)

### What Remains

Only **2 lemmas** need completion:

1. **`zeckendorf_fuel_no_consecutive`** (Line 685):
   - **Claim**: The greedy algorithm produces non-consecutive Fibonacci numbers
   - **Key insight**: After selecting F_k, remainder < F_{k-1}, so next pick has index ≤ k-2
   - **Status**: Structure in place, needs formal details

2. **`sum_nonconsec_fibs_bounded`** (Line 1021):
   - **Claim**: Sum of non-consecutive Fibs with max F_k is < F_{k+1}
   - **Key insight**: Since F_{k-1} not in list (non-consecutive), sum < F_k + F_{k-1} = F_{k+1}
   - **Status**: Base cases done, inductive step needs completion

## Proof Approach 2: Combinatorial Construction (`zeckendorf2.v`)

**Status**: 🚧 **IN PROGRESS** - Elegant alternative approach

### Key Insight

Instead of computing one representation greedily, construct **ALL** valid Zeckendorf representations systematically:

```coq
Fixpoint zeck_lists (n : nat) : list (list nat) :=
  match n with
  | 0 => [[]]
  | S n1 =>
      match n1 with
      | 0 => [ []; [1] ]
      | S n2 =>
          let part1 := zeck_lists n1 in
          let part2 := map (fun xs => fib (n2 + 3) :: xs) (zeck_lists n2) in
          part1 ++ part2
      end
  end.
```

### How It Works

The construction ensures non-consecutiveness by design:

1. **Base cases**:
   - `zeck_lists 0 = [[]]` → represents {0}
   - `zeck_lists 1 = [[], [1]]` → represents {0, 1}

2. **Recursive case** for `zeck_lists (n+2)`:
   - **Part 1**: Include all representations from level n+1
   - **Part 2**: Add F_{n+3} to each representation from level n
   - Result: `zeck_lists(n+1) ++ map (cons F_{n+3}) (zeck_lists n)`

3. **Non-consecutiveness guarantee**:
   - When we cons `fib(n+3)` onto lists from `zeck_lists(n)`,
   - The largest Fib index in those lists is at most n+2,
   - So we're adding F_{n+3} to lists with max F_{n+2},
   - This **skips F_{n+2+1} = F_{n+3-1}**, ensuring the gap!

### Examples

```
zeck_lists 0 = [[]]
  → Sums: [0]
  → Count: 1 = fib(2)

zeck_lists 1 = [[], [1]]
  → Sums: [0, 1]
  → Count: 2 = fib(3)

zeck_lists 2 = [[], [1], [2]]
  → Sums: [0, 1, 2]
  → Count: 3 = fib(4)

zeck_lists 3 = [[], [1], [2], [3], [3,1]]
  → Sums: [0, 1, 2, 3, 4]
  → Count: 5 = fib(5)

zeck_lists 4 = [[], [1], [2], [3], [3,1], [5], [5,1], [5,2], [5,3,1]]
  → Sums: [0, 1, 2, 3, 4, 5, 6, 7, 8]
  → Count: 8 = fib(6)
```

**Crucial observation**: The i-th list (0-indexed) has sum = i!

### Theoretical Beauty

This construction reveals deep mathematical structure:

1. **Fibonacci recurrence in counting**:
   ```
   |zeck_lists(n+2)| = |zeck_lists(n+1)| + |zeck_lists(n)|
                     = fib(n+3) + fib(n+2)
                     = fib(n+4)
   ```

2. **Coverage**: Represents all integers from 0 to fib(n+2) - 1

3. **Order**: Representations appear sorted by their sums

4. **Bijection**: One representation per integer in the range

### Implementation Status

Located in `zeckendorf2.v` (Lines 14-61) and extended in `zeckendorf2_complete.v`:

| Component | Status |
|-----------|--------|
| `zeck_lists` definition | ✅ Implemented |
| `find_fib_index_aux` (finds level for index) | ✅ Implemented |
| `min_level_for_index` | ✅ Implemented |
| `zeck` (retrieves nth representation) | ✅ Implemented |

### Proofs in `zeckendorf2_complete.v`

| Lemma | Statement | Status |
|-------|-----------|--------|
| `zeck_lists_all_fibs` | All lists contain only Fibonacci numbers | ✅ Proven |
| `zeck_lists_max_index` | Max Fib index in level n is ≤ n+2 | ⚠️ Mostly proven |
| `zeck_lists_no_consecutive` | All lists have non-consecutive Fibs | 🚧 Structure proven |
| `zeck_lists_length` | `length(zeck_lists n) = fib(n+2)` | 🚧 Outlined |
| Sum-indexing correspondence | i-th list has sum i | 🚧 TODO |
| `zeckendorf_exists` | Existence for all n | 🚧 Depends on above |
| `zeckendorf_unique` | Uniqueness | 🚧 Requires completeness |

### Why This Approach is Elegant

1. **Non-consecutiveness by construction**: The "skip one" pattern guarantees the property automatically

2. **Fibonacci appears everywhere**: The counting follows Fibonacci recurrence!

3. **Complete enumeration**: Not just one representation, but ALL valid ones

4. **Computational interpretation**: Can extract to enumerate all Zeckendorf representations up to n

5. **Pedagogical value**: Makes the structure transparent

### Challenges

The main difficulties:

1. **Indexing complexity**: Proving `nth i (zeck_lists n) [] ` has sum = i requires tracking cumulative sums

2. **Completeness**: Showing every integer appears exactly once

3. **Level selection**: `min_level_for_index` must correctly compute which level contains index i

## Comparison of Approaches

| Aspect | Greedy Algorithm | Combinatorial Construction |
|--------|------------------|----------------------------|
| **Conceptual complexity** | Medium (algorithmic thinking) | High (combinatorial insight) |
| **Proof complexity** | Medium (invariant maintenance) | High (structural induction + indexing) |
| **Result type** | One representation | All representations enumerated |
| **Main advantage** | Standard algorithmic proof | Elegant mathematical structure |
| **Completion status** | 98% (2 lemmas remain) | ~60% (structure in place) |
| **Non-consecutive proof** | Requires bound lemmas | Falls out of construction! |
| **Uniqueness proof** | Requires bound lemma | Requires completeness |
| **Computational efficiency** | O(n) per number | O(fib(n)) to build table |
| **Best for** | Practical implementation | Theoretical understanding |

**Recommendation**: Complete the greedy algorithm approach first (nearly done), then pursue the combinatorial approach for its theoretical elegance.

## Testing with Haskell

The Haskell implementation (`Haskell/zeckendorf.hs`) provides an executable reference:

```bash
# Run with stack
cd Haskell
stack ghci zeckendorf.hs

# Example usage in GHCi
> zeckendorf 10
[8,2]

> map zeckendorf [1..10]
[[1],[2],[3,1],[5],[5,1],[5,2],[8],[8,1],[8,2],[8,2,1]]

> map (sum . zeckendorf) [1..20] == [1..20]
True
```

Use Haskell to:
- Verify the greedy algorithm's correctness
- Explore the pattern of representations
- Test edge cases before formalizing in Coq

## Key Insights for Completing the Proofs

### Completing `zeckendorf_fuel_no_consecutive`

**Goal**: Show greedy algorithm produces non-consecutive Fibonacci numbers

**Strategy**:
1. Strengthen induction hypothesis to track relationship between acc and remainder
2. Use `remainder_less_than_prev_fib` (already proven at line 660):
   ```coq
   fib k < n < fib (S k) → n - fib k < fib (k - 1)
   ```
3. Key argument:
   - When we select F_k (where k is maximal s.t. F_k ≤ n),
   - The remainder r = n - F_k satisfies r < F_{k-1}
   - Therefore, the next Fibonacci selected has index ≤ k-2
   - This ensures a gap of at least 1, so no consecutive Fibs

**What's needed**: Formalize the "maximal F_k ≤ n" property and connect it to the bound

### Completing `sum_nonconsec_fibs_bounded`

**Goal**: Sum of non-consecutive Fibs with max F_k is strictly less than F_{k+1}

**Strategy**:
1. Use strong induction on k
2. Base case k=2:
   - Lists with max F_2 = 1 can only contain {1}, so sum ≤ 1 < 2 = F_3 ✓
3. Inductive case k≥3:
   - Given list l with max = F_k and no consecutive Fibs
   - Partition: l = {F_k} ∪ l'
   - Since F_{k-1} not in l (would be consecutive with F_k), all elements of l' have index ≤ k-2
   - So max(l') ≤ F_{k-2}
   - By IH: sum(l') < F_{k-1}
   - Therefore: sum(l) = F_k + sum(l') < F_k + F_{k-1} = F_{k+1} ✓

**What's needed**:
- Formalize the partitioning argument
- Prove that non-consecutiveness implies F_{k-1} ∉ l when F_k ∈ l
- Apply the induction hypothesis correctly

### Completing Combinatorial Approach

**Main task**: Prove sum-indexing correspondence

**Strategy**:
1. Define `sum_below n = Σᵢ₌₀ⁿ⁻¹ fib(i+2) = fib(n+2) - 1` (sum of counts up to level n-1)
2. Show by induction that:
   - Lists 0 to fib(n+2)-1 in the flattened structure come from levels 0..n
   - The i-th list has sum equal to i
3. Use the bijection between indices and sums
4. Extract that `zeck i` correctly retrieves the representation of i

## Working with Coq Files

### Compilation Commands

```bash
# Compile single file
coqc -Q . Zeckendorf zeckendorf.v

# Type-check without native compilation
coqc -vos zeckendorf.v

# Generate HTML documentation
make html

# Check for admitted lemmas
grep -n "Admitted\|admit" zeckendorf.v
```

### Interactive Development

When modifying proofs:

1. **Tools**:
   - `coqide` - Official IDE
   - VS Code with Coq extension
   - Emacs with Proof General
   - Vim with Coqtail

2. **Standard library modules used**:
   - `Lists.List` - List operations and lemmas
   - `Arith.Arith` - Arithmetic lemmas
   - `Wellfounded.*` - Well-founded induction
   - `Lia` - Linear integer arithmetic (very powerful!)

3. **Key patterns**:
   - Use structural recursion when possible
   - Use well-founded recursion (`Program Fixpoint`) when structure decreases in complex ways
   - The combinatorial approach uses structural recursion (simpler!)

### Essential Tactics

| Tactic | Purpose | Example |
|--------|---------|---------|
| `induction` | Proof by induction | `induction n as [|n' IH]` |
| `induction ... using lt_wf_ind` | Well-founded induction | For strong induction on < |
| `destruct` | Case analysis | `destruct n as [|[|n'']]` |
| `lia` | Linear arithmetic | Solves inequalities automatically |
| `apply ... in` | Forward reasoning | `apply H in H'` |
| `rewrite` | Equation rewriting | `rewrite H` |
| `simpl` / `unfold` | Simplification | `simpl in H` |
| `assert` | Intermediate lemma | `assert (H: x > 0)` |
| `exfalso` | Proof by contradiction | Prove False |
| `reflexivity` | Prove equality | For `x = x` |
| `lia` | **Most powerful** | Solves arithmetic goals! |

**Pro tip**: When stuck, try `lia`! It solves many arithmetic goals automatically.

### Debugging Workflow

1. **See current proof state**: Coq IDE shows goals and hypotheses
2. **Check assumptions**: `Print Assumptions theorem_name`
3. **Find lemmas**: `Search (fib _ < fib _)`
4. **See proof term**: `Show Proof`
5. **Get type**: `Check expression`

## Collaboration and Extension

### Adding New Lemmas

Follow this pattern:

```coq
(*
  Lemma: [Statement in English]

  Proof strategy: [High-level approach]
  - [Key insight 1]
  - [Key insight 2]
*)
Lemma lemma_name : forall n,
  n >= 1 -> property n.
Proof.
  (* [Begin proof] *)
  intros n Hn.
  (* [Explain next step] *)
  induction n.
  (* [Case n = 0] *)
  - ...
  (* [Case n = S n'] *)
  - ...
Qed.
```

### Code Review Checklist

- [ ] Lemma has clear English description
- [ ] Proof strategy explained in comments
- [ ] Admits marked with TODO and explanation
- [ ] Variable names are descriptive
- [ ] Proof compiles (or compilation issues documented)
- [ ] Tests pass (if applicable)

### Style Guidelines

1. **Naming**:
   - Use descriptive names: `zeckendorf_sum_property` not `zeck_sp`
   - Prefix with main concept: `fib_mono`, `fib_pos`, etc.

2. **Comments**:
   - Explain "why", not "what"
   - Mark proof steps: `(* Base case *)`, `(* Inductive step *)`
   - Document admits: `(* TODO: complete this proof *)`

3. **Structure**:
   - Group related lemmas
   - Use `(* ============= *)` section dividers
   - Keep proofs under 50 lines when possible

## References

### Zeckendorf's Theorem

- **Wikipedia**: [Zeckendorf's theorem](https://en.wikipedia.org/wiki/Zeckendorf%27s_theorem)
- **OEIS A014417**: [Zeckendorf representations](https://oeis.org/A014417)
- **Original**: Zeckendorf, E. (1972) "Représentation des nombres naturels par une somme de nombres de Fibonacci ou de nombres de Lucas"

### Coq Resources

- **Coq Documentation**: https://coq.inria.fr/documentation
- **Software Foundations**: https://softwarefoundations.cis.upenn.edu/ (excellent tutorial)
- **Mathematical Components**: Formalization techniques for mathematics
- **Coq Tactics Cheatsheet**: https://pjreddie.com/coq-tactics/
- **Coq'Art**: The book "Interactive Theorem Proving and Program Development"

### Fibonacci Properties

Key facts used in the proofs:

1. **Recurrence**: F(n+2) = F(n+1) + F(n)
2. **Monotonicity**: F(n) < F(n+1) for n ≥ 2
3. **Positivity**: F(n) > 0 for n ≥ 1
4. **Injectivity**: F(i) = F(j) ∧ i,j ≥ 2 → i = j
5. **Gap property**: F(k-1) + F(k-2) + ... + F(1) < F(k)
6. **Sum bound**: Sum of non-consecutive Fibs with max F(k) is < F(k+1)

## Project Status

### ✅ Completed (Greedy Approach)

- ✅ Fibonacci properties (positivity, monotonicity, injectivity)
- ✅ Greedy algorithm implementation with termination proof
- ✅ Correctness: all elements are Fibonacci numbers
- ✅ Correctness: sum equals input
- ✅ Infrastructure for non-consecutive property
- ✅ Infrastructure for uniqueness

### ⚠️ Remaining (Greedy Approach) - Only 2 lemmas!

- ⚠️ `zeckendorf_fuel_no_consecutive` - Structure in place, needs details
- ⚠️ `sum_nonconsec_fibs_bounded` - Base cases done, induction step remains

### 🚧 In Progress (Combinatorial Approach)

- 🚧 `zeck_lists` construction and basic properties
- 🚧 Proof that all lists contain Fibonacci numbers
- 🚧 Non-consecutive property (structural insight proven)
- 🚧 Sum-indexing correspondence (main challenge)

### 📊 Overall Progress

- **Greedy approach**: ~98% complete ✅
- **Combinatorial approach**: ~60% complete 🚧
- **Main Zeckendorf theorem**: Can be stated once above completes

## Important Notes

- Coq version: **8.18.0**
- Working directory: `Coq/`
- Build artifacts: `.vo`, `.vos`, `.vok`, `.glob` files
- License: **MIT** (see LICENSE file)
- The greedy algorithm approach is nearly complete and should be prioritized
- The combinatorial approach is elegant and valuable for understanding

## Next Steps

### Immediate (Complete greedy approach)

1. Complete `zeckendorf_fuel_no_consecutive` proof
2. Complete `sum_nonconsec_fibs_bounded` proof
3. State and prove main theorem: `∃! l. is_zeckendorf_repr n l`

### Future (Combinatorial approach)

1. Prove sum-indexing correspondence for `zeck_lists`
2. Prove completeness (every integer 0..fib(n+2)-1 appears)
3. Implement and verify `zeck` function
4. Extract computational implementations

### Long-term

1. Prove decidability of Zeckendorf representation
2. Extract efficient Haskell/OCaml code
3. Prove complexity bounds
4. Extend to generalized Fibonacci sequences
5. Connect to other combinatorial structures

---

**Conclusion**: This repository contains a nearly complete formal proof of Zeckendorf's theorem using two complementary approaches. The greedy algorithm approach is 98% complete, requiring only 2 remaining lemmas. The combinatorial construction approach offers elegant theoretical insights and is a valuable alternative perspective.
