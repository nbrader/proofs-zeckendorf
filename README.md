# proofs-zeckendorf

Formal verification of Zeckendorf’s theorem in Coq together with a small
reference implementation in Haskell. Zeckendorf’s theorem states that every
positive integer can be expressed uniquely as a sum of non-consecutive Fibonacci
numbers. The repository provides both the mechanically checked proof and an
executable model of the greedy algorithm.

## Repository layout

- `Coq/` – the formal development. Notable files:
  - `zeckendorf.v`: definitions of Fibonacci numbers, helper lemmas, the greedy
    algorithm, and the main correctness statements.
  - `zeck_equiv.v`: proves the optimized `zeck` implementation matches the
    original `zeckendorf` function.
  - `_CoqProject`: logical load paths (`-Q . Zeckendorf`) and file list.
  - `build_coq.sh`: convenience wrapper around `coq_makefile` + `make`.
- `Haskell/` – informal reference implementation (`zeckendorf.hs`) that mirrors
  the greedy algorithm for experimentation in GHCi/Stack.
- `Python/`, `Rough Working/` – scratch material, plain-English proofs, and
  exploratory scripts used while developing the formal proof.
- Documentation helpers:
  - `NEXT_STEPS.md`, `PROOF_STATUS*.md`: describe remaining admits and current
    milestones.
  - `agents.md`: quick brief for AI/code assistants.

## Building the Coq proofs

```bash
cd Coq
./build_coq.sh          # quick build (generates Makefile + make)
# or run the steps manually:
coq_makefile -f _CoqProject -o Makefile
make                    # compiles all .v files
make clean              # remove artifacts
make cleanall           # remove artifacts + timing files
```

The project targets Coq 8.18.0 (see `Coq/Makefile`). All files live under the
`Zeckendorf` namespace as configured in `_CoqProject`.

## Haskell quick start

```bash
cd Haskell
stack ghci zeckendorf.hs
> zeckendorf 10        -- [8,2]
> map zeckendorf [1..10]
```

This implementation is not formally verified but is useful for experimenting
with the greedy algorithm and generating example sequences.

## Current status

- Core correctness lemmas for `zeckendorf` are in place, though a few admits
  remain (see `PROOF_STATUS*.md` for the exact list).
- `zeck_equiv.v` establishes that the optimized `zeck` function reuses the
  precomputed tables from `zeck_lists` and therefore agrees with `zeckendorf`.
- `zeckendorf_produces_sorted_asc` and supporting lemmas (added 2025‑11‑08)
  prove the greedy output is sorted when starting from an empty accumulator.

To work on the development interactively, use your preferred Coq IDE (CoqIDE,
VS Code + VsCoq, Proof General, etc.), reload `Coq/zeckendorf.v`, and re-run
`make` after edits to ensure the whole project still compiles.
