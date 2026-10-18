# JaCoP and MiniZinc: current support level (checked 2026-10-18)

Tested: JaCoP `develop-5.0` (commit 8972bf26, built with JDK 25) against MiniZinc **2.10.1** (latest, 31 Aug 2026), with MiniZinc **2.8.7** as a baseline for anything that failed.

## How JaCoP plugs into MiniZinc

| Piece | Where | Notes |
|---|---|---|
| FlatZinc front end | `jacop-flatzinc/src/main/java/org/jacop/fz/` | JavaCC parser (`Parser.jj` → `Parser.java`), `Fz2jacop` entry point. Constraints are dispatched by reflection: each FlatZinc predicate name maps to a method in `constraints/ConstraintFncs.java` (224 predicates). Unknown name → `RuntimeException "constraint X is not supported"`. |
| Solver library (mznlib) | `jacop-flatzinc/src/main/minizinc/org/jacop/minizinc/` | ~100 files: `fzn_*.mzn` overrides that map globals to `jacop_*` native constraints, plus `redefinitions.mzn`, `redefinitions-2.0.mzn`, `-2.2.1.mzn`, `-2.7.1.mzn`. Legacy `minizinc_upTo2.3` library was dropped in develop-5.0. |
| Solver config | `jacop-flatzinc/src/main/minizinc/org.jacop.msc` (template, filtered into `jacop-all/target/org.jacop.msc`) | Text-FlatZinc only (`inputType: FZN`), std flags `-a -n -s -t -v -f -r`, extra flags for `-b`, `-sat`, restarts, etc. |
| Launcher | `jacop-all/src/main/resources/scripts/fzn-jacop.template` → `jacop-all/target/fzn-jacop` | Bash wrapper around `org.jacop.fz.Fz2jacop`. |

## Is "JaCoP doesn't work with the latest MiniZinc" (issue #79) true?

**Mostly no.** Issue #79 has only a title, no body or error. With correct paths in the `.msc`, MiniZinc 2.10.1 compiles and runs JaCoP models fine:

- MiniZinc's own unit suite at tag 2.10.1 (1,093 models), JaCoP vs Gecode 6.4.0, 20 s limit each: **1,072 identical outcomes** (759 SAT, 66 optimal, 28 UNSAT, 219 identical compiler errors from tests that are meant to error, 3 UNKNOWN on both).
- Every JaCoP failure that is not an on_restart abort fails the same way under MiniZinc 2.8.7 too, so **none of them is a 2.9/2.10 regression**.
- There are **no new `redefinitions-2.x.mzn` files** after 2.7.1 (2.10.1 still ships 2.0 … 2.7.1), and JaCoP already provides `redefinitions-2.7.1.mzn` (`float_ceil/floor/round`), as the 2.9.3 changelog requires.
- FlatZinc changes since 2.8 (header comments with the command line, removal of non-array RHS on var decls, two-arg `bool_xor` removed from builtins) all parse fine.

What actually breaks for a user out of the box is the **packaging**: `org.jacop.msc` hard-codes `/Users/kris/jacop-mzn/...` for `mznlib` and `executable` and says version `4.10`. Dropped into any MiniZinc install it fails immediately with `Cannot access include directory /Users/kris/jacop-mzn/jacop` (reproduced). That matches #74/#75 and is the most likely cause of #79.

## Concrete differences / work list

### A. Breaks today (fix first)
1. **`org.jacop.msc` paths and version.** *Fixed (see "Using JaCoP from MiniZinc" below).* The file hard-coded `/Users/kris/...` and `"version": "4.10"`. It is now a template filtered at build time with the pom version and paths relative to the `.msc` file; `jacop-all` packages it next to `fzn-jacop` and a copy of the mznlib. The executable must be written as `./fzn-jacop`: MiniZinc 2.8.7 resolves a bare `fzn-jacop` relative to the `.msc`, but 2.10.1 looks it up on `PATH`. The deprecated `supportsFzn`/`supportsMzn` flags were replaced by `"inputType": "FZN"` (2.8.0), and a duplicate `name` key was removed.
2. **`set_superset` / `set_superset_reif` not implemented.** They are FlatZinc builtins and MiniZinc emits them for `s superset t` (also in 2.8.7). JaCoP throws `constraint set_superset is not supported`. Fix: add two methods to `ConstraintFncs` that call the `set_subset` generators with swapped arguments.
3. **`bool_or_imp` declared native but not implemented.** `redefinitions.mzn:44` declares it with no body; `ConstraintFncs` has no `bool_or_imp`. Any half-reified `bool_or` that survives to FlatZinc would crash. Implement it or give it a body.

### B. New in 2.8–2.10 that JaCoP doesn't support (MiniZinc falls back or aborts)
4. **`on_restart` meta-search (2.8, experimental).** All 9 `on_restart` tests abort at compile time with "experimental on_restart feature ... not supported by target solver"; Gecode runs them. Needs `mzn_opt_on_restart`-style support in the mznlib (`complete`, `status`, `sol_*`, `last_val_*`, `uniform_on_restart`) and handling in `fz/Solve.java`. JaCoP's own restart flags and `relax_and_reconstruct` still work.
5. **New global hooks JaCoP could implement natively but currently gets decomposed:** `fzn_count_*_bool/float/set` (2.9.6), `fzn_sliding_among_int/bool` (2.9.5), `fzn_cumulatives(_opt)` (2.8.0), `fzn_bin_packing*_opt` (2.9.4), reified `regular` (2.10.0), `fzn_assume` (2.10.0), `blackbox` propagators (2.10.0). Not failures, only weaker propagation.
6. **FlatZinc JSON input** (2.8.0, `--fzn-format`). Optional; JaCoP reads text FlatZinc only. Not needed for normal use.
7. **Parameter names in mznlib (2.10.0 named arguments).** `--warn-non-authoritative-names` reports ≥20 mismatches, e.g. JaCoP's `fzn_circuit(x)` vs std `fzn_circuit_reif(xs, …)`, `fzn_disjunctive(s,d)` vs `(start,duration)`, `fzn_lex_less_int(x,y)` vs `(xs,ys)`, `int_ne_imp(a,b,…)` vs `int_ne(x,y)`. Today it is only a warning and reified globals still resolve correctly (tested). MiniZinc says native names stay positional-only "for now", so renaming parameters to the canonical std names is cheap future-proofing.
8. **FlatZinc predicate items with defaults** (`predicate foo(var int: x, var int: y = 5);`, 2.10 named args). JaCoP's parser fails on `=`. Gecode's parser fails too, and it only appears for user-declared native predicates, so it is low priority.

### C. JaCoP bugs found by the suite (not version-related, same on 2.8.7)
9. `regression/test_bug53`: nested `seq_search` of an ignored annotation → NPE in `Solve.getLastSearch` (`Solve.java:1284`). Gecode solves it.
10. `types/tuple_if_then_else`: tiny model with `jacop_if_then_else_bool(..., true)` → JVM stack overflow, UNKNOWN. Gecode finds both solutions.
11. `regression/bug284`: a 2-column `table` with a few hundred tuples over unbounded `var int` → out of memory (default `-Xmx12G` script). Gecode solves it.
12. `general/multidim_array_concat`: MiniZinc 2.10.1 emits FlatZinc referencing an undeclared array (`X_INTRODUCED_43_`) when JaCoP's `jacop_strictly_increasing` is used. This looks like a MiniZinc compiler bug triggered by JaCoP's library; worth a minimal repro upstream.

(One more difference, `general/test_set_lt_3`: JaCoP returns the expected `{1,4}` and Gecode wrongly says UNSAT, so JaCoP is right there.)

## Using JaCoP from MiniZinc

`mvn -DskipTests install` produces a self-contained solver bundle in `jacop-all/target`:

```
jacop-all/target/
  org.jacop.msc             solver configuration (version from the pom, relative paths)
  fzn-jacop                 launcher script
  jacop-all-<version>.jar
  lib/                      runtime dependencies
  mznlib/                   JaCoP's MiniZinc library
```

Use it in place:

```
MZN_SOLVER_PATH=/path/to/jacop/jacop-all/target minizinc --solver org.jacop model.mzn
```

or copy those files into one directory and put that directory on `MZN_SOLVER_PATH`, or copy them into MiniZinc's `share/minizinc/solvers/` directory. Checked with MiniZinc 2.10.1 and 2.8.7.

## How to reproduce
- MiniZinc bundle: `MiniZincIDE-2.10.1-x86_64-linux-gnu.tgz` from GitHub releases; JaCoP built with `mvn -DskipTests install -pl jacop-all -am` on JDK 25 (the pom hard-codes `<release>25</release>`, so JDK 21 cannot build develop-5.0).
- Point `MZN_SOLVER_PATH` at `jacop-all/target` (see below).
- The test models are `tests/spec/unit/**.mzn` from `MiniZinc/libminizinc` at tag `2.10.1`; run each with `minizinc --solver org.jacop --time-limit 20000` and compare with `--solver gecode`. This is a good candidate for the "test bench" for MiniZinc support.
