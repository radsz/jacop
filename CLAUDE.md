# CLAUDE.md

@AGENTS.md

The rules below take precedence over anything in AGENTS.md that conflicts with them.

## Pull request workflow

Every pull request triggers the GitHub Actions build (`.github/workflows/ci.yml`), which runs
`mvn spotless:check` and `mvn -B -Pcommit verify`. That suite is long, so a PR is opened only once
the work is truly done.

- Do not open a pull request (draft or ready) until the work is complete.
- Pushing work in progress to a remote branch is fine and encouraged; just do not open the PR yet.
- Before opening a PR, run locally and make sure all of these pass:
  1. The regression tests for the change (a test that fails before the fix and passes after it).
  2. `mvn spotless:check`
  3. `mvn -B -Pcommit verify`
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
  `commit` and `push` profile includes in the parent `pom.xml`. Otherwise CI never runs it.
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
