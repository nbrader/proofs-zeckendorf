# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This repository contains a formal verification of the Zeckendorf representation theorem in Coq. The theorem states that every positive integer can be represented as a sum of non-consecutive Fibonacci numbers. The main proof is located in `Coq/zeckendorf.v`.

The project also includes a reference Haskell implementation in `Haskell/zeckendorf.hs` that demonstrates the algorithm informally.

## Build System

### Building the Coq Proof

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

## Code Architecture

### Core Definitions (Coq/zeckendorf.v)

1. **Fibonacci Function** (`fib`, lines 10-18)
   - Structurally recursive definition of Fibonacci numbers
   - Base cases: fib(0) = 0, fib(1) = 1

2. **Helper Functions** (lines 23-30)
   - `takeWhile`: filters list elements while predicate holds
   - `fibs_upto n`: generates Fibonacci numbers ≤ n

3. **Main Algorithm** (`zeckendorf`, lines 141-167)
   - Uses `Program Fixpoint` with measure-based termination
   - Greedy algorithm: repeatedly selects largest Fibonacci number ≤ remaining value
   - Accumulator pattern for building result list
   - Well-founded recursion proof in `Next Obligation` (lines 154-167)

### Proof Structure

The correctness proof has two main components:

1. **Fibonacci Property Lemmas** (lines 33-132)
   - `fib_pos`: Fibonacci numbers are positive for n ≥ 1
   - `fib_mono`: Fibonacci sequence is monotonically increasing for n ≥ 2
   - `in_fibs_upto_fib`: elements in `fibs_upto` are Fibonacci numbers
   - `fib_decrease`: termination helper for the main recursion

2. **Correctness Theorems** (lines 177-252)
   - `zeckendorf_acc_fib`: all elements in result are Fibonacci numbers (ADMITTED)
   - `zeckendorf_acc_sum`: sum of result equals input (ADMITTED)
   - `zeckendorf_correct`: combines both properties (lines 243-252)

**Current Status**: The main correctness lemmas (`zeckendorf_acc_fib` and `zeckendorf_acc_sum`) are admitted due to difficulties with Program Fixpoint's internal representation. The infrastructure is in place, but the proofs require functional induction schemes or rewriting using explicit well-founded recursion.

### Key Challenges

The proofs at lines 181-210 are admitted because `Program Fixpoint` generates complex dependent types (using `existT`) that don't match the expected pattern for straightforward unfolding. To complete these proofs, you would need to either:
- Use functional induction schemes for Program Fixpoint
- Rewrite using `Function` with explicit well-founded recursion
- Extract Program-generated equations for the function

## Testing with Haskell

The Haskell implementation (`Haskell/zeckendorf.hs`) provides an executable reference:

```bash
# Run with stack
cd Haskell
stack ghci zeckendorf.hs

# Example usage in GHCi
> zeckendorf 10  -- [8,2]
> map zeckendorf [1..10]
```

## Working with Coq Files

### Compilation Commands

```bash
# Compile single file
coqc -Q . Zeckendorf zeckendorf.v

# Type-check without native compilation
coqc -vos zeckendorf.v

# Generate HTML documentation
make html
```

### Interactive Development

When modifying proofs:
1. Use `coqtop` or `coqide` for interactive proof development
2. The file uses standard library modules: `Lists.List`, `Arith.Arith`, `Wellfounded.*`
3. Rely on `Program Fixpoint` for measure-based recursion

## Important Notes

- The Coq version is 8.18.0 (see Makefile line 281)
- Working directory for Coq files is `Coq/`
- Build artifacts (`.vo`, `.vos`, `.vok`, `.glob` files) are generated in the `Coq/` directory
- The project is under MIT License (see LICENSE file)
- Rough Working\wiki proof.txt shows an example of a plain english proof in full that this proof Coq proof can borrow from.

## Latest Updates (2025-02-14)

- `fib_consecutive` has been renamed to the more general `nat_consecutive`; all callers in `Coq/zeckendorf.v` have been updated and `make` passes.
- No admitted proofs have been discharged yet. The open obligations remain at:
  - `zeckendorf_fuel_no_consecutive` (`Coq/zeckendorf.v:790`)
  - `sum_nonconsec_fibs_bounded` (`Coq/zeckendorf.v:1119`)
  - `zeckendorf_unique` (`Coq/zeckendorf.v:1156`)
- Recommended next steps:
  1. Strengthen the accumulator invariant for the greedy algorithm so the non-consecutive lemma can be completed.
  2. Finish the inductive argument for `sum_nonconsec_fibs_bounded`, then use it to prove `zeckendorf_unique`.
  3. Once admits are resolved, rerun `make` (or `coqc`) to ensure the entire development stays closed.
