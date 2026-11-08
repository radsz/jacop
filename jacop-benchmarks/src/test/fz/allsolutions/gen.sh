#!/bin/sh
# Flattens every model of models/ twice: with JaCoP's MiniZinc library (<m>/<m>.fzn) and with
# MiniZinc's standard library plus shims/ for the predicates only JaCoP has (<m>/<m>.std.fzn).
# AllSolutionsSuite compares the solutions of the two. Needs MZN (minizinc binary) and
# MZN_SOLVER_PATH with a solver org.jacop (mznlib = JaCoP's library) and a solver org.std
# (mznlib = an empty directory).
set -e
cd "$(dirname "$0")"
MZN=${MZN:-minizinc}
for m in models/*.mzn; do
  name=$(basename "$m" .mzn)
  case "$1" in ""|"$name") ;; *) continue ;; esac
  mkdir -p "$name"
  "$MZN" -c --solver org.jacop "$m" --fzn "$name/$name.fzn" --no-output-ozn
  "$MZN" -c --solver org.std -I shims "$m" --fzn "$name/$name.std.fzn" --no-output-ozn
  sed -i '/^% Command line invocation/d; /^% Solver library/d' "$name/$name.fzn" "$name/$name.std.fzn"
done
