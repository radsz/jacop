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
decomposed model uses built-ins only. `StdDecompositionsTest` checks every
decomposition against JaCoP's constraint on a small model. It takes about two hours and is not
in any Maven profile; run it on demand with
`mvn -Pmin -pl jacop-benchmarks test -Dtest=StdDecompositionsTest -Dsurefire.rerunFailingTestsCount=0`.

Globals without a decomposition yet (reported as `NO_DECOMPOSITION`): `jacop_geost`,
`jacop_geost_bb` and the graph constraints (`jacop_wst`, `jacop_tree`, `jacop_steiner`,
`jacop_path`, `jacop_dpath`, `jacop_dreachable`, `jacop_connected`).

# The all-solutions suite

`org.jacop.decomposition.AllSolutionsSuite` builds a growing suite of small problems whose
solutions JaCoP enumerates completely within 5 minutes, and checks that every other way of solving
them gives exactly the same solutions. A propagator, explanation or search bug that removes a
solution, or lets a wrong one through, shows as a difference. Like `DecompositionCheck` it is a
tool, not part of the build:

```
mvn -Pmin -pl jacop-benchmarks test -Dtest=AllSolutionsSuite -Dsurefire.rerunFailingTestsCount=0 \
    -Dsuite.threads=3 \
    -Dsuite.roots=jacop=src/test/fz,hakank=../../osolpro/hakank-suite/fz,mznc=../../minizinc-competition/fz
```

For each problem, smallest FlatZinc file first, an optimisation problem is solved to its best value
`v` and becomes the satisfaction problem `objective <= v` (`>=` for maximisation). The problem
joins the suite when the reference run, JaCoP's own constraints with a static search
(`input_order`, `indomain_min`), finishes within `suite.timeout` (300 s). Every variable that no
constraint defines is printed, so two solutions that differ only in unprinted variables are told
apart. Then:

| Check | What must hold |
|---|---|
| `all:f` | `-a -f` prints the same set of solutions. |
| `decomp:C` | With every occurrence of global `C` replaced by MiniZinc's standard decomposition (`StdDecompositions`), the same set. |
| `std`, `std:f` | When `<inst>.std.fzn` exists (the same model flattened with MiniZinc's standard library), the same set of solutions projected on the variables both files print, with static and with free search. |
| `objK:MODE` | LCG cannot enumerate solutions, so the sets are compared through random linear objectives over the printed variables. Their minimum over the reference solutions is known; the native model minimised with `MODE` (`plain`, `f`, `lcg`, `lcg-f`), each decomposed model (`obj0:lcg:decomp:C`) and the standard-library twin (`objstd:lcg`) must prove the same minimum, and every solution they print must be a reference solution. |

Verdicts: `PASS`; `PARTIAL` (a run stopped at the limit, and what it printed is correct);
`WRONG` (a printed solution is not a reference solution); `MISSED` (a finished run lacks reference
solutions or proves a worse minimum); `DUPLICATES`; `ERROR`; `UNSUPPORTED` and `NO_DECOMPOSITION`
(nothing checked). Failed checks keep their model in `target/all-solutions-suite/`.

The next problem is picked to keep the suite balanced across constraints: the smallest file that
contains the global constraint with the fewest suite problems so far, at most `suite.familyCap` (3)
problems per model directory and `suite.cap` (30) per constraint; a model directory is given up
once one of its instances was too slow. Results are appended to `suite-state.tsv` as they come
(a new run continues from there; `suite.retry=WRONG,ERROR` checks again), and `suite-coverage.md`
is the per-constraint table of the suite. Runs over generated variants (`allsolutions/gen_variants.py`)
write one state file per batch of seeds, `gen-state/sFFFF-LLLL.tsv`, gzipped once the batch ends,
and read the others with `suite.stateRead=src/test/fz/decomposition/suite-state.tsv,src/test/fz/decomposition/gen-state`;
a single growing file passed 50 MB after 700 seeds.

`allsolutions/` holds small models written for the constraints that no benchmark problem uses:
`models/*.mzn`, flattened by `allsolutions/gen.sh` with JaCoP's library (`<m>/<m>.fzn`) and with
MiniZinc's standard library (`<m>/<m>.std.fzn`), where `allsolutions/shims/` decomposes the
predicates that only JaCoP has. Model names start with `m_` so that a model never shadows a
library file of the same name (`lex_chain_less_bool.mzn` did). `models/<m>.jacop-flags` adds
flags to the JaCoP flattening and `models/<m>.no-std` skips the standard one.
`AllSolutionsModelsTest` (in the build) runs every model that has both flattenings.

`allsolutions/gen_variants.py SEED COUNT OUTDIR` writes random variants of these models (every
`var lo..hi` domain gets a new upper bound) with both flattenings, for an endless supply of
problems: run the suite on them with `-Dsuite.roots=gen=OUTDIR -Dsuite.familyCap=100
-Dsuite.cap=1000`. A variant may break a documented precondition (the first did: the variable
based softgcc requires `sum(soft_counters) <= length(x)`); the decompositions and shims must
state such preconditions too.

A reference run that prints solutions and then `=====UNSATISFIABLE=====` is an error, not a
complete run: JaCoP did that at the time limit before the fix of the timed-out child search
(KidneyExchange-4-041_c23), and the suite then reported false `WRONG` verdicts.

Other properties: `suite.solutions` (solution limit, 2000000), `suite.maxBytes` (largest FlatZinc
file, 1000000), `suite.objectives` (2), `suite.allOutput` (true), `suite.problems` (regular
expression on names such as `jacop:upTo5sec/...`), `suite.maxProblems`, `suite.hours`,
`suite.state`, `suite.report`, `suite.out`.
