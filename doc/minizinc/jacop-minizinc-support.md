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

**Status:** fixed in `develop-5.0` (PR #82, see A1). #74, #75 and #79 are resolved there.

## Concrete differences / work list

### A. Breaks today (fix first)
1. **`org.jacop.msc` paths and version.** *Fixed (see "Using JaCoP from MiniZinc" below).* The file hard-coded `/Users/kris/...` and `"version": "4.10"`. It is now a template filtered at build time with the pom version and paths relative to the `.msc` file; `jacop-all` packages it next to `fzn-jacop` and a copy of the mznlib. The executable must be written as `./fzn-jacop`: MiniZinc 2.8.7 resolves a bare `fzn-jacop` relative to the `.msc`, but 2.10.1 looks it up on `PATH`. The deprecated `supportsFzn`/`supportsMzn` flags were replaced by `"inputType": "FZN"` (2.8.0), and a duplicate `name` key was removed.
2. **`set_superset` / `set_superset_reif` not implemented.** *Fixed (PR #84): both are dispatched to `AinB` with swapped arguments, `_reif` through `Reified`.* They are FlatZinc builtins and MiniZinc emits them for `s superset t` (also in 2.8.7). JaCoP throws `constraint set_superset is not supported`. Fix: add two methods to `ConstraintFncs` that call the `set_subset` generators with swapped arguments.
3. **`bool_or_imp` declared native but not implemented.** *Fixed (PR #83): posted as `SumBool([a, b], ">=", r)`.* `redefinitions.mzn:44` declares it with no body; `ConstraintFncs` has no `bool_or_imp`. Any half-reified `bool_or` that survives to FlatZinc would crash. Implement it or give it a body.

### B. New in 2.8–2.10 that JaCoP doesn't support (MiniZinc falls back or aborts)
4. **`on_restart` meta-search (2.8, experimental).** All 9 `on_restart` tests abort at compile time with "experimental on_restart feature ... not supported by target solver"; Gecode runs them. Needs `mzn_opt_on_restart`-style support in the mznlib (`complete`, `status`, `sol_*`, `last_val_*`, `uniform_on_restart`) and handling in `fz/Solve.java`. JaCoP's own restart flags and `relax_and_reconstruct` still work.
5. **New global hooks JaCoP could implement natively but currently gets decomposed:** `fzn_count_*_bool/float/set` (2.9.6), `fzn_sliding_among_int/bool` (2.9.5), `fzn_cumulatives(_opt)` (2.8.0), `fzn_bin_packing*_opt` (2.9.4), reified `regular` (2.10.0), `fzn_assume` (2.10.0), `blackbox` propagators (2.10.0). Not failures, only weaker propagation.
   *Mostly done.* Native now: `fzn_cumulatives(_opt)` (one `CumulativeOptional` per machine, a task is present on machine k iff it runs there), `fzn_sliding_among_int/bool` (`Sequence`), and `fzn_count_*_bool` with all `_par`/`_reif` forms (counted on the 0/1 view by JaCoP's `Count`/`CountVar`). `fzn_bin_packing*_opt` and reified `regular` needed no override: MiniZinc's default bodies rewrite them to `bin_packing_capa`/`bin_packing_load` and `regular`, which JaCoP already posts natively. `fzn_count_*_float/set` are left to MiniZinc: JaCoP has no float or set count propagator that would prune more than the decomposition. `fzn_assume` and `blackbox` are experimental in MiniZinc and not addressed. Each hook is checked by `MznlibGlobalsTest`, which compares JaCoP's solutions with its library against the pure MiniZinc decomposition (`jacop-flatzinc/src/test/fz/mznlib`, regenerated by `regenerate.sh`).
6. **FlatZinc JSON input** (2.8.0, `--fzn-format`). Optional; JaCoP reads text FlatZinc only. Not needed for normal use.
7. **Parameter names in mznlib (2.10.0 named arguments).** `--warn-non-authoritative-names` reports ≥20 mismatches, e.g. JaCoP's `fzn_circuit(x)` vs std `fzn_circuit_reif(xs, …)`, `fzn_disjunctive(s,d)` vs `(start,duration)`, `fzn_lex_less_int(x,y)` vs `(xs,ys)`, `int_ne_imp(a,b,…)` vs `int_ne(x,y)`. Today it is only a warning and reified globals still resolve correctly (tested). MiniZinc says native names stay positional-only "for now", so renaming parameters to the canonical std names is cheap future-proofing.
8. **FlatZinc predicate items with defaults** (`predicate foo(var int: x, var int: y = 5);`, 2.10 named args). JaCoP's parser fails on `=`. Gecode's parser fails too, and it only appears for user-declared native predicates, so it is low priority.

### C. JaCoP bugs found by the suite (not version-related, same on 2.8.7)
9. *Fixed (PR #105): a `seq_search` whose annotations were all ignored now falls back to the default search; test `FlatzincFrontEndTest#seqSearchOfIgnoredAnnotationsFallsBackToDefaultSearch`.* `regression/test_bug53`: nested `seq_search` of an ignored annotation → NPE in `Solve.getLastSearch` (`Solve.java:1284`). Gecode solves it.
10. *Fixed (PR #105): the default search bisects integer variables instead of trying one value after another; test `FlatzincFrontEndTest#defaultSearchReachesValuesOfUnboundedVariables`.* `types/tuple_if_then_else`: tiny model with `jacop_if_then_else_bool(..., true)` → JVM stack overflow, UNKNOWN. Gecode finds both solutions.
11. *Fixed.* `regression/bug284`: a 2-column `table` with 250,164 tuples → out of memory (default `-Xmx12G` script). Cause: `GlobalConstraints.deduplicateTableRows` allocates each row as `new ArrayList<>(t.length)`, which is quadratic in the number of tuples (see `globals-and-extensional.md`). With the capacity fixed, JaCoP solves it in about a second.
12. `general/multidim_array_concat`: MiniZinc 2.10.1 emits FlatZinc referencing an undeclared array (`X_INTRODUCED_43_`) when JaCoP's `jacop_strictly_increasing` is used. This looks like a MiniZinc compiler bug triggered by JaCoP's library; worth a minimal repro upstream.

Bugs found and fixed while wiring the hooks in B5 (all with regression tests):

13. *Fixed.* FlatZinc front end dropped `bool_eq_reif(x, false, r)` (and other equality reifications with a constant) when the 0/1 view of `x` also had collected `int_eq_reif`s, leaving `r` free and producing wrong solutions (`ChannelMap`, `ComparisonConstraints`).
14. *Fixed.* The `fzn_bin_packing_capa` override numbered bins from `lb_array(bin)` instead of the capacity array's index set, shifting capacities and losing solutions; this also broke `bin_packing*_opt`.
15. *Fixed.* `jacop_sequence` (used by `sliding_among`) crashed on value sets with gaps.
16. *Fixed.* `CumulativeOptional` failed on every propagation, and its profile made feasible optional tasks absent; `Cumulative` edge finding lost solutions (a capacity map built for the original task order was used after reordering).

(One more difference, `general/test_set_lt_3`: JaCoP returns the expected `{1,4}` and Gecode wrongly says UNSAT, so JaCoP is right there.)

## Using JaCoP from MiniZinc

`mvn -DskipTests install` produces a self-contained solver bundle in `jacop-all/target`:

```
jacop-all/target/
  org.jacop.msc             solver configuration (version from the pom, relative paths)
  fzn-jacop                 launcher script
  fzn-jacop-aot             makes jacop.aot, the optional start-up cache (see below)
  aot-training/             FlatZinc models fzn-jacop-aot trains the cache on
  jacop-all-<version>.jar
  lib/                      runtime dependencies
  mznlib/                   JaCoP's MiniZinc library
```

Use it in place:

```
MZN_SOLVER_PATH=/path/to/jacop/jacop-all/target minizinc --solver org.jacop model.mzn
```

or copy those files into one directory and put that directory on `MZN_SOLVER_PATH`, or copy them into MiniZinc's `share/minizinc/solvers/` directory. Checked with MiniZinc 2.10.1 and 2.8.7.

### Faster start-up with an AOT cache (optional)

Every run starts a JVM, which loads and links JaCoP's classes and runs them in the interpreter before the JIT compiles them; on a small instance this is most of the time. Java 25's ahead-of-time cache (JEP 483, 514 and 515) records the loaded and linked classes and the method profiles of a training run, and a later JVM starts from them. Make the cache once after building:

```
jacop-all/target/fzn-jacop-aot            # or: mvn -Paot -DskipTests install
```

It solves the FlatZinc models in `target/aot-training/` (or the `.fzn` files given as arguments) with default search, `-f` and `--lcg -f`, about 10 s, and writes `target/jacop.aot` (about 26 MB). `fzn-jacop` uses the cache when it is there and newer than the jar; without it, or with a cache made for another build, it runs as before. The cache holds no solver state: answers, solutions and search are the same. Make it again after rebuilding the jar or changing the JDK; the JVM must be the `java` on the `PATH` in both cases, and copied bundles need the cache, the jar and `lib/` together. `fzn-jacop` sends JVM warnings, such as a rejected cache, to stderr, so they never mix with the FlatZinc output.

Measured on 54 mznbench instances that `--lcg -f` solves in under 4 s (Java 25, 4-core cloud machine, 3 runs each, `-t 20000`): with the same search, the median run is 30 % shorter (0.21 s less) with `--lcg -f` and 31 % shorter (0.19 s) with the model's own search; runs under 1 s take a median 0.35 s instead of 0.56 s. JaCoP's `initTime` falls from 0.15 to 0.09 s. Runs of several seconds stay within noise. On an empty model `fzn-jacop` takes 0.12 s instead of 0.25 s.

JaCoP's search can depend on identity hash codes (variables and constraints in hash sets), which shift with any change of the JVM's start-up, the cache included. So on some instances the cache leads to another, equally valid search path with a different node count and time, as other JVM flags do; the answers are the same.

## Free search (`-f`)

With `-f` (MiniZinc's "free search" flag) JaCoP ignores the search annotations as the only search and runs its free search engine, `org.jacop.search.free.FreeSearch`, which is also available to Java models through `FreeSearch.withDefaults(store, vars)`. By default it branches with dom/wdeg, last conflict (k = 1) and solution-based phase saving, restarts geometrically (for satisfaction from 100 failures, growing by 1.5; for optimisation, as Choco does, from 10 failures growing by 1.05, started again after each solution, with the dom/wdeg weights forgotten every 32 restarts), restarts after each solution, learns nogoods from restarts, and interleaves the model's annotation with free search, one restart each. For `-a` on a satisfaction model it runs one complete search without restarts and reports each assignment of the output variables once. `-n`, `-t`, `-s` and `-v` work as without `-f`; `-r` has no effect, since the engine makes no random choices.

`--free-engine legacy` selects the previous implementation. `--free-config key=value,...` changes the settings of the new engine, mainly for experiments:

| Key | Values | Default |
|---|---|---|
| `heuristic` | `domwdeg`, `cacd` (wdeg^ca.cd), `chs` (conflict history search), `afc` | `domwdeg` |
| `lc` | last conflict size, 0 is off | 1 |
| `phase` | solution-based phase saving, 0 or 1 | 1 |
| `restarts`, `scale`, `base` | `geometric`, `luby` or `none`; failures of the first run; growth of geometric restarts | `geometric`; 100, 1.5 for satisfaction; 10, 1.05 for optimisation |
| `restart-on-solution` | 0 or 1 | 1 |
| `objective-last` | branch on the objective after the other variables, 0 or 1 | 1 |
| `interleave` | `restart`, `solution` (annotation until the first solution) or `none` | `restart` |
| `nogoods` | nogoods from restarts, 0 or 1 | 1 |
| `impact`, `impact-until` | bound-impact values for optimisation on domains up to n values (0 is off); `first` or `always` | 0, `first` |
| `impact-every` | with `impact`, probe in the first run and then every k-th run only (0 is every run) | 0 |
| `restart-reset` | start the restart limits again after each solution, 0 or 1 | 0 for satisfaction, 1 for optimisation |
| `flush` | forget the dom/wdeg weights every k restarts (0 is never) | 0 for satisfaction, 32 for optimisation |

`--restart` (with `--restart-scale` and `--restart-base`), when given, replaces the restart policy of the free search.

## Several objectives (`goal_hierarchy`, `pareto`)

A solve item with `satisfy` can carry MiniZinc's `goal_hierarchy` annotation (declared in `std/experimental.mzn`) for the lexicographic optimum of its goals, or JaCoP's `pareto` annotation (declared in `jacop.mzn`, which includes `experimental.mzn`) for the Pareto front:

```minizinc
include "jacop.mzn";
solve :: goal_hierarchy([int_min_goal(cost), max_goal(quality), sat_goal(on_time)]) satisfy;
solve :: pareto([min_goal(cost), min_goal(delay)]) satisfy;
```

Goals are `min_goal`, `int_min_goal`, `max_goal` and `int_max_goal` of an integer, and `sat_goal` of a Boolean (true is better); float goals are not supported (the annotation is then ignored with a warning on stderr). JaCoP solves a sequence of single-objective subproblems (`org.jacop.search.MultiObjective`), each the FlatZinc model with its bounds as constraints and `minimize` or `maximize` of one goal, with the options given (`-f`, `--lcg`, `--presolve`, `-p` all apply to each subproblem); `-t` limits them all together.

- `goal_hierarchy` prints what an optimisation prints: the best solution (with `-a` each solution lexicographically better than the one before) and `==========` when it is the lexicographic optimum.
- `pareto` prints each point of the front as soon as it is proven Pareto optimal (one solution per vector of goal values, not in a particular order) and `==========` when the front is complete. At a time-out the last solution found, not dominated by the points printed but not proven optimal, is printed last.
- `-s` adds `goalSubproblems`, `paretoPoints` (Pareto) or `objective` (the first goal, lexicographic), and the nodes, failures, propagations and restarts of all subproblems.

In the MiniZinc 2.9.4 bundle, Gecode and OR-Tools CP-SAT ignored `goal_hierarchy` on our test model and returned the first solution of the satisfaction problem.

## How to reproduce
- MiniZinc bundle: `MiniZincIDE-2.10.1-x86_64-linux-gnu.tgz` from GitHub releases; JaCoP built with `mvn -DskipTests install -pl jacop-all -am` on JDK 25 (the pom hard-codes `<release>25</release>`, so JDK 21 cannot build develop-5.0).
- Point `MZN_SOLVER_PATH` at `jacop-all/target` (see below).
- The test models are `tests/spec/unit/**.mzn` from `MiniZinc/libminizinc` at tag `2.10.1`; run each with `minizinc --solver org.jacop --time-limit 20000` and compare with `--solver gecode`. This is a good candidate for the "test bench" for MiniZinc support.
