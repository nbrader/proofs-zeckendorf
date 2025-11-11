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
- `Haskell/` – informal reference implementation (`zeckendorf.hs` and
  `zeck.hs`) that mirrors the greedy algorithm for experimentation in
  GHCi/Stack.
- `Python/` – quick-running sanity checks that mirror the Coq definitions and
  empirically test the main invariants.
- `docs/` – curated assets (plots, diagrams, annotated wiki proof) that used
  to live in the ad-hoc “Rough Working” directory.
- Documentation helpers:
  - `PROOF_STATUS*.md`: document milestones, historical
    planning notes, and any follow-up work items.
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
ghci zeckendorf.hs     # or `runghc zeck.hs` for the table builder demo
Prelude> zeckendorf 10   -- [8,2]
Prelude> map zeckendorf [1..10]
```

This implementation is not formally verified but is useful for experimenting
with the greedy algorithm and generating example sequences. A working GHC or
Stack installation is required (not vendored in this repository).

## Python sanity checks

The scripts in `Python/` provide executable mirrors of the Coq definitions and
stress the originally-admitted lemmas. Typical usage:

```bash
cd Python
python3 test_admitted_goals.py
python3 test_edge_cases.py
python3 test_axioms.py
```

They are lightweight (pure `python3`, no extra dependencies) and help regression
test the greedy algorithm alongside the formal proofs.

## Current status

- `Coq/zeckendorf.v` closes every goal (no remaining admits) and provides the
  full existence/uniqueness package for Zeckendorf representations.
- `zeck_equiv.v` establishes that the optimized `zeck` function reuses the
  precomputed tables from `zeck_lists` and therefore agrees with `zeckendorf`.
- Historical planning notes in `PROOF_STATUS*.md` capture
  how the project reached the current state; they remain as documentation only.

To work on the development interactively, use your preferred Coq IDE (CoqIDE,
VS Code + VsCoq, Proof General, etc.), reload `Coq/zeckendorf.v`, and re-run
`make` after edits to ensure the whole project still compiles.
