# agents.md

This file provides guidance to any AI coding agent working in this repository (Claude Code, GPT‑based tools, etc.).

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

### Core Definitions (`Coq/zeckendorf.v`)

1. **Fibonacci Function** (`fib`, lines 10-18)
   - Structurally recursive definition of Fibonacci numbers
   - Base cases: fib(0) = 0, fib(1) = 1

2. **Helper Functions** (lines 23-30)
   - `takeWhile`: filters list elements while predicate holds
   - `fibs_upto n`: generates Fibonacci numbers ≤ n

3. **Main Algorithm** (`zeckendorf`, lines 141-167)
   - Implemented as a structurally recursive `Fixpoint` with an explicit fuel argument
   - Greedy algorithm: repeatedly selects largest Fibonacci number ≤ remaining value
   - Accumulator pattern for building result list
   - Termination is justified by decreasing both the `fuel` and the remaining sum

### Proof Structure

The correctness proof has two main components:

1. **Fibonacci Property Lemmas** (lines 33-132)
   - `fib_pos`: Fibonacci numbers are positive for n ≥ 1
   - `fib_mono`: Fibonacci sequence is monotonically increasing for n ≥ 2
   - `in_fibs_upto_fib`: elements in `fibs_upto` are Fibonacci numbers
   - `fib_decrease`: termination helper for the main recursion

2. **Correctness Theorems** (lines 177-252)
   - `zeckendorf_acc_fib`: all elements in the accumulated result are Fibonacci numbers (proven via `zeckendorf_fuel_acc_fib`)
   - `zeckendorf_acc_sum`: the sum of the list equals the input (proven via `zeckendorf_fuel_acc_sum`)
   - `zeckendorf_correct`: packages the existence/uniqueness properties (combining the lemmas above)

The modern file works entirely in Coq 8.18 without any remaining admits; the explicit fuel argument in `zeckendorf_fuel` provides the structural decrease, while helper lemmas such as `zeckendorf_fuel_acc_fib`, `zeckendorf_fuel_acc_sum`, `zeckendorf_no_consecutive`, and `zeckendorf_sorted` discharge the main invariants.

## Testing with Haskell

The Haskell implementation (`Haskell/zeckendorf.hs`) provides an executable reference:

```bash
# Run with stack or cabal (requires a system-wide GHC/Stack install)
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
3. Remember that `zeckendorf_fuel` is a structurally recursive `Fixpoint` with explicit fuel decreasing at each step
4. **IMPORTANT**: Always test compile after making changes using `cd Coq && make` to ensure the entire development remains valid

## Important Notes

- The Coq version is 8.18.0 (see Makefile line 281)
- Working directory for Coq files is `Coq/`
- Build artifacts (`.vo`, `.vos`, `.vok`, `.glob` files) are generated in the `Coq/` directory
- The project is under MIT License (see LICENSE file)
- `docs/notes/wiki-proof*.txt` contains the original plain-English proof and an annotated mapping to the Coq development.

## Current Highlights

- `sum_nonconsec_fibs_bounded_sorted` (`Coq/zeckendorf.v:1926-2071`) captures the key lemma from the uniqueness proof using sorted lists and is fully proven.
- `zeckendorf_sorted` (`Coq/zeckendorf.v:1695-1702`) shows that the greedy algorithm outputs a strictly descending list, which feeds into `zeckendorf_repr_exists` and `zeckendorf_repr_unique`.
- `zeck_equiv.v` bridges the optimized table-driven algorithm `zeck` with the proven `zeckendorf` function so that downstream code can reuse the faster version while inheriting all correctness theorems.
