# Checking global constraints against their decompositions

`org.jacop.decomposition.DecompositionCheck` (in `jacop-benchmarks/src/test/java`) tests JaCoP's
global constraints on the FlatZinc problems of a time category. For every problem it

1. counts the solutions with JaCoP's own constraints (the reference run);
2. for each `jacop_*` global constraint in the problem, replaces every occurrence of it with the
   decomposition that the MiniZinc 2.10.1 standard library (`share/minizinc/std/fzn_*.mzn`) posts
   when the solver has no native version, written with FlatZinc built-ins only;
3. counts the solutions again and compares them with the reference run.

The decomposed model is equivalent, so its search tree differs but its solutions must not.

## Running it

It is a tool, not part of the build:

```
mvn -Pmin -pl jacop-benchmarks test -Dtest=DecompositionCheck -Dsurefire.rerunFailingTestsCount=0 \
    -Ddecomp.threads=3
```

| Property | Default | Meaning |
|---|---|---|
| `decomp.category` | `upTo5sec` | problems listed in `src/test/fz/<category>/list.txt` |
| `decomp.state` | `src/test/fz/decomposition/state-<category>.tsv` | results of earlier runs |
| `decomp.timeout` | 30 | seconds per solver run |
| `decomp.solutions` | 200000 | solution limit per counting run |
| `decomp.constraints` | all | comma-separated constraint names, e.g. `jacop_cumulative,jacop_regular` |
| `decomp.problems` | all | regular expression on problem names |
| `decomp.maxProblems` | no limit | stop after this many problems were worked on |
| `decomp.retry` | none | verdicts to check again, e.g. `DIFF,ERROR`; `EMPTY` re-checks `PARTIAL` results that compared no solution |
| `decomp.threads` | 1 | problems checked in parallel |
| `decomp.out` | `target/decomposition-check` | decomposed models of differences |

Each solver run is a separate JVM (`Fz2jacop -a -s --default-search input`), killed 30 seconds after
its time limit.

## Resuming

Every result is appended to the state file as soon as it is known. A new run skips every problem
and constraint that already has a result for the same FlatZinc file (the file's SHA-256 is part of
the key, so a changed file is checked again), and continues with the next one. Commit the state
file with the work so that the next run, on any machine, continues from there. To check something
again, delete its lines or use `decomp.retry`.

Line format (tab-separated):

- `B problem hash kind objective status solutions distinct digest nodes millis date`: the
  reference run.
- `C problem hash constraint occurrences verdict status solutions distinct digest nodes millis date
  note`: the check of one constraint with all its occurrences decomposed.
- `N problem hash reason date`: nothing to check (no global constraint, or an objective that is
  not an integer variable).

## How solutions are compared

- An optimisation problem is first solved to its best objective value `v` (within the time limit);
  the counting model is then the satisfaction problem with `objective <= v` (`>= v` for
  maximisation), so the decomposition must keep exactly the same optimal solutions and must not
  allow better ones.
- The counting models replace dynamic search heuristics (`first_fail`, `dom_w_deg`,
  `indomain_median`, ...) with `input_order` and `indomain_min`. With a static search the
  solutions come in the same order whatever the propagation, so two runs are compared solution by
  solution, even when a run stops at the time or solution limit.
- The digest is an order-independent hash of the set of printed solutions; `solutions` counts
  printed solutions and `distinct` the different ones.

Verdicts:

| Verdict | Meaning |
|---|---|
| `PASS` | Both searches finished with the same solutions. |
| `PARTIAL` | A search stopped at a limit; the solutions both runs found are the same sequence. |
| `DIFF` | The solutions differ. |
| `ERROR` | The decomposed model failed to solve (exception, `=====ERROR=====`). |
| `UNSUPPORTED` | The decomposition does not handle this use of the constraint (for example an unbounded variable where MiniZinc needs bounds). |
| `NO_DECOMPOSITION` | No decomposition is written for this constraint yet. |

A `DIFF` or `ERROR` writes the decomposed model and the first solutions that only one model has
to `decomp.out`, and, when the constraint occurs several times, looks for one occurrence that
alone reproduces the difference. Every difference must be investigated, its cause explained and
fixed (in JaCoP or in the decomposition), with a regression test.

## The decompositions

`StdDecompositions` maps each `jacop_*` constraint back to the MiniZinc global that JaCoP's
library (`jacop-flatzinc/src/main/minizinc`) rewrites into it, and posts that global's standard
decomposition. Globals that a standard decomposition calls (such as `count` inside `at_least`,
`all_different` inside `circuit`, or `minimum` inside `subcircuit`) are decomposed as well, so a
decomposed model uses built-ins only. `StdDecompositionsTest` (in the build) checks every
decomposition against JaCoP's constraint on a small model.

Globals without a decomposition yet (reported as `NO_DECOMPOSITION`): `jacop_geost`,
`jacop_geost_bb` and the graph constraints (`jacop_wst`, `jacop_tree`, `jacop_steiner`,
`jacop_path`, `jacop_dpath`, `jacop_dreachable`, `jacop_connected`).
