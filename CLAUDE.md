# CLAUDE.md

@AGENTS.md

The rules below take precedence over anything in AGENTS.md that conflicts with them.

## Pull request workflow

Every pull request triggers the GitHub Actions build (`.github/workflows/ci.yml`), which runs
`mvn spotless:check` and `mvn -B -Pcommit verify`. That suite is long, so a PR is opened only once
the work is truly done.

- Every pull request targets `develop-5.0` directly; never stack a PR on another PR's branch.
  Extend an existing PR or open a new one against `develop-5.0`.
- Do not open a pull request (draft or ready) until the work is complete.
- Pushing work in progress to a remote branch is fine and encouraged; just do not open the PR yet.
- Before opening a PR, run locally and make sure all of these pass:
  1. The regression tests for the change (a test that fails before the fix and passes after it).
  2. `mvn spotless:check`
  3. `mvn -B -Pmin verify`
- Do not run `-Pcommit` locally; CI runs it. The `min` profile runs every test class the `commit`
  profile runs, with fewer random instances (`globals.bruteforce.trials`,
  `cumulative.bruteforce.trials`, `grounding.trials`) and, instead of the whole upTo30sec FlatZinc
  category, the sample in `jacop-benchmarks/src/test/fz/upTo30sec/list-min.txt`.
- Build with `mvn clean ...` before trusting a local result: an incremental `mvn install` re-packs
  the previous all-in-one jar in `jacop-all`, so stale classes can hide or fake a failure.
- Open the PR only after those pass. Do not use the PR's CI as a substitute for running them locally.
- Each new commit pushed to an open PR re-runs the whole suite, so batch follow-up changes and
  verify them locally first.

## Bug fixes

- Base bug-fix branches on `develop-5.0`. Group fixes into pull requests the way the maintainer
  asks (for example all open correctness fixes in one PR), with one commit per bug.
- Every fix comes with a regression test that reproduces the bug and fails without the fix.
- Put the regression test in a test class that the `commit` profile runs (for constraint bugs,
  `jacop-core/src/test/java/org/jacop/SingleConstraintTest.java`), or add the new test class to the
  `min`, `commit` and `push` profile includes in the parent `pom.xml`. Otherwise CI never runs it.
  A slow new class gets a system property for its instance count, lowered in the `min` profile.
- When a new upTo30sec FlatZinc instance uses a built-in that no upTo5sec instance uses, add its
  fastest instance to `upTo30sec/list-min.txt`.
- Prefer comparing solution counts against a brute-force or decomposition reference over checking
  a single expected output.

## Checking propagator strength (consistency checker)

`jacop-core/src/test/java/org/jacop/ConsistencyChecker.java` measures the consistency a propagator
actually reaches. It is a tool for improving constraints, not part of the build: no Maven profile
includes it, so run it on demand with `-Dtest`.

```
mvn -Pmin -pl jacop-core test -Dtest=ConsistencyChecker -Dsurefire.rerunFailingTestsCount=0
mvn -Pmin -pl jacop-core test -Dtest=ConsistencyChecker -Dsurefire.rerunFailingTestsCount=0 \
    -Dconsistency.cases=XmulYeqZ,GCC -Dconsistency.instances=5000
```

- `consistency.cases`: comma-separated parts of case names to run (default: all cases).
- `consistency.instances`: random instances per case (default 1000; 5000 gives about 2 million nodes
  over all cases).

How it works: each case posts one constraint on small random variables with holes in their domains
and makes random dives of decisions (`x = v`, `x != v`, `x <= v`, `x >= v`). After propagation at
every node it enumerates the box of current intervals and tests a plain-Java relation on each tuple,
then reports the strongest level held at every node:

- bounds(R): each min and max has a support over the real intervals (only for cases that supply a
  real check, currently linear and multiplication);
- bounds(Z): each min and max has a support with the other variables in their integer intervals;
- bounds(D): the same with the other variables in their domains;
- domain (GAC): every value has a support in the domains.

It also fails a case that removes a solution or fails while a solution exists (wrong pruning), and
counts nodes where a missing support would be pruned by running the constraint again (not at
fixpoint). Each case prints its level, the node count and the first counterexample of the next
level, with the instance and the decision path that reproduces it.

Using it to improve a propagator:

1. Run the checker for the constraint and read the counterexample.
2. Fix the propagator; put the counterexample in a regression test in `SingleConstraintTest` (that
   class is in the build).
3. Re-run the checker with a high `consistency.instances` and raise the case's level in
   `ConsistencyChecker.cases()` to what it now reaches, so a later weakening is caught when the
   checker is run.

To check another propagator, add a `Case` to `cases()`: a name, the level it reaches, and a
generator returning a `Model` (the constraint, the relation as a `Predicate<int[]>` on complete
assignments, and the variables in the relation's order). Keep the instances small, since every node
enumerates the whole box (nodes above 200,000 tuples are skipped).

## Checking wake-up events (fresh fixpoint)

`jacop-core/src/test/java/org/jacop/WakeUpFixpointTest.java` (in the build, `wakeup.trials`, 1000 in
`min` and 3000 otherwise) makes random dives over primitive constraints, constraints composed of them
(Reified, Implies, Not, Xor, Eq, And, Or, IfThen, IfThenElse, Conditional) and globals, and at every
node imposes the same constraint in a fresh store over the current domains. Any value the fresh store
prunes is a missed wake-up event or a constraint that does not propagate its own pruning. After
changing a pruning event or a composed constraint, run it at volume:

```
mvn -Pmin -pl jacop-core test -Dtest=WakeUpFixpointTest -Dsurefire.rerunFailingTestsCount=0 \
    -Dwakeup.trials=100000
```

## Checking globals against their decompositions

`jacop-benchmarks/src/test/java/org/jacop/decomposition/DecompositionCheck.java` replaces each
`jacop_*` global of the FlatZinc test problems with the MiniZinc standard library decomposition and
checks that the solutions stay the same. Like the consistency checker it is run on demand:

```
mvn -Pmin -pl jacop-benchmarks test -Dtest=DecompositionCheck -Dsurefire.rerunFailingTestsCount=0 \
    -Ddecomp.threads=3
```

Results go to `jacop-benchmarks/src/test/fz/decomposition/state-<category>.tsv` and a run resumes
where the last one stopped; commit the state file with the work. Every `DIFF` or `ERROR` must be
investigated, explained and fixed with a regression test. Details: `src/test/fz/decomposition/README.md`.

`StdDecompositionsTest` checks each of those decompositions against JaCoP's constraint on a small
model. It enumerates every solution of several scheduling models and takes about two hours, so it
is not in any profile either; run it on demand after changing `StdDecompositions` or a global it
covers:

```
mvn -Pmin -pl jacop-benchmarks test -Dtest=StdDecompositionsTest -Dsurefire.rerunFailingTestsCount=0
```

## Fuzzing the SAT core

`jacop-sat/src/test/java/org/jacop/jasat/cdcl/CdclFuzzTest.java` fuzzes the CDCL core in process.
Like the consistency checker it is not in any profile; run it on demand:

```
mvn -Pmin -pl jacop-sat test -Dtest=CdclFuzzTest -Dsurefire.rerunFailingTestsCount=0 \
    -Dfuzz.runs=1000000 -Dfuzz.seed=1
```

Every answer is checked without a reference solver: a SAT answer by its model, an UNSAT answer by
checking its DRAT proof with `RupChecker`, and an UNSAT answer under assumptions by re-solving with
the failed assumptions as units. A failure prints the seed and, for small formulas, the CNF. Run
it after any change to `org.jacop.jasat.cdcl`; 10⁶ runs take about 45 minutes on one core (split
them over seeds to use more).

## Checking lazy clause generation

`LcgSolver` checks every explanation when `jacop.lcg.check=true` (the LCG tests switch it on with
`setChecking(true)`): the constraint is copied into a scratch store over the root domains, the
reason is imposed with the negated atom, and propagation or a bounded search must find no solution.
A wrong explanation throws `IllegalStateException("wrong explanation: ...")` with a counterexample.

`jacop-sat/src/test/java/org/jacop/jasat/lcg/LcgFuzzTest.java` solves random small models over a
broad pool of constraints with LCG (checker on) and with depth-first search, and fails on any
difference in satisfiability or optimum, or on an LCG solution that is not one. It is in the build
(`lcg.fuzz.runs`, 300 in `min`, 2000 otherwise); run it at volume after a change to `LcgSolver`,
`AtomicTrail` or an explanation:

```
mvn -Pmin -pl jacop-sat test -Dtest=LcgFuzzTest -Dsurefire.rerunFailingTestsCount=0 \
    -Dlcg.fuzz.runs=100000 -Dlcg.fuzz.seed=1000000
```

A failure names the seed; the model of a seed is rebuilt with `-Dlcg.fuzz.runs=1 -Dlcg.fuzz.seed=N`.
A constraint whose pruning depends on a variable that is not among its arguments (such as an
internal counter) needs that variable in its scope, or the generic reason is unsound.
