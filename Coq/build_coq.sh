#!/bin/bash

# Ensure we use the same opam switch as the IDE (rocq-8.18.0)
eval $(opam env --switch=rocq-8.18.0)

# Clean up old build artifacts
make clean

# Generate Makefile from _CoqProject
coq_makefile -f _CoqProject -o Makefile

# Build the project using the generated Makefile
make