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
