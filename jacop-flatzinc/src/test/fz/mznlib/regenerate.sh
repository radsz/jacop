#!/usr/bin/env bash
# Regenerates the FlatZinc files used by MznlibGlobalsTest.
#
# For every model X.mzn it writes
#   X.fzn         compiled with JaCoP's MiniZinc library (native propagators), and
#   X-decomp.fzn  compiled with the MiniZinc standard library only (standard decompositions),
#                 from decomp/X-decomp.mzn instead when the standard library has no decomposition for X.
# The test checks that JaCoP finds the same solutions for both.
#
# Usage: MINIZINC=/path/to/minizinc ./regenerate.sh [model.mzn ...]
set -euo pipefail
cd "$(dirname "$0")"
MINIZINC=${MINIZINC:-minizinc}
MZNLIB=$(cd ../../../main/minizinc/org/jacop/minizinc && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
mkdir "$TMP/empty"
for lib in jacop std; do
  if [[ "$lib" = jacop ]]; then dir=$MZNLIB; else dir=$TMP/empty; fi
  cat > "$TMP/$lib.msc" <<MSC
{"id": "org.jacop.test.$lib", "name": "$lib", "version": "1.0", "mznlib": "$dir",
 "executable": "/bin/true", "inputType": "FZN", "stdFlags": ["-a"]}
MSC
done
models=("$@")
[[ ${#models[@]} -eq 0 ]] && models=(*.mzn)
for m in "${models[@]}"; do
  base=${m%.mzn}
  "$MINIZINC" -c --solver "$TMP/jacop.msc" "$m" -o "$base.fzn" --no-output-ozn
  decomp=$m
  [[ -f "decomp/$base-decomp.mzn" ]] && decomp=decomp/$base-decomp.mzn
  "$MINIZINC" -c --solver "$TMP/std.msc" "$decomp" -o "$base-decomp.fzn" --no-output-ozn
  # Drop the header lines that record local paths.
  sed -i '/^% Solver library:/d; /^% Command line invocation:/d' "$base.fzn" "$base-decomp.fzn"
done
