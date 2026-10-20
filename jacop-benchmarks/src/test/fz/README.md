This test suite uses problems in Minizinc/Flatzinc format to test JaCoP. We have divided the
problems into seven time categories. Each category is stored in a separate directory
and has its own test file. For example, directory upTo5sec contains problems that JaCoP can solve
within 5 seconds. This test category is executed by test file MinizincBasedTestUpTo5Seconds.
In case of upTo5seconds category is a solving a problem takes more than three times five seconds then
it is considered a failed tests. The test problems are stored in test/fz directory. The test programs
executing problems within a given category is stored within test/java/org/jacop directory.

Minizinc problems (*.mzn) were transformed into Flatzinc (*.fzn) problems using JaCoP minizinc library.
Moreover, the first time the problem was solved by JaCoP the result was stored within output file (*.out).
This output file is used by test runner to check if the problems was solved in the same fashion later.
If there is any difference in the output for the consecutive problem solving attempt then it is considered
as a failed test.

The list of all time categories of the minizinc based test suite :

- MinizincBasedTestAbove1Hours (java.org.jacop.MinizincBasedTestAbove1Hours)
- MinizincBasedTestUpTo1Hours (java.org.jacop.MinizincBasedTestUpTo1Hours)
- MinizincBasedTestUpTo1Minutes (org.jacop.MinizincBasedTestUpTo1Minutesa)
- MinizincBasedTestUpTo5Minutes (org.jacop.MinizincBasedTestUpTo5Minutes)
- MinizincBasedTestUpTo5Seconds (org.jacop.MinizincBasedTestUpTo5Seconds)
- MinizincBasedTestUpTo10Minutes (org.jacop.MinizincBasedTestUpTo10Minutes)
- MinizincBasedTestUpTo30Seconds (org.jacop.MinizincBasedTestUpTo30Seconds)

Each test category contains a script that will regenerate list.txt file that contains all the files
that are used by the test runner for a given category. It is possible to manualy adapt this list.

There are additional directories within this test suite. First, directory flakyTests contains problems
that output different result when the problem is being solved. Sometimes, it is for trivial reason like
float variables precision makes solution differ in actual values of the variables. Sometimes, the search
finds a different solution since more than one is available. Those problems/solution approach needs to
be adapted to make sure the output is the same each time the problem is being solved.

There is an extra script listchoosegenerator.sh that makes it possible to search for problems that contain
a particular keyword. The resulting list.txt file will be placed inside minizincbasedchosen directory.
This test suite can be run by executing the test MinizincBasedChosen. This test can be useful if one
for examples has improved a table constraint within JaCoP then it is possible to run this script provide
table word as a parameter and all problems contains this keyword will be stored within minizincbasedchosen
directory.

It is encouraged to run time categories upTo5sec and upTo30sec each time you push a branch to remote host.
It is encourated to run additional categories upTo1min and upTo5min when you merge a branch to develop branch.
It is encourated to run all tests before release, merging to a master branch.

Directory test contains problems that have not been categorized yet and are awaiting categorization.
Therefore, this minizinc based test suite will always be work in progress as one can continuously add
new tests to improve the test coverage of this test suite.

## Constraint-Based Test Selection

In addition to time-based categorization, each benchmark directory contains a `metadata.json` file
that records which FlatZinc builtins and JaCoP constraint families the benchmark exercises. This
enables targeted test runs when a specific constraint implementation changes.

### Running benchmarks by constraint family

Use `MinizincByConstraintTest` with the `-DconstraintFilter` system property:

    mvn -pl jacop-benchmarks -Dtest=MinizincByConstraintTest -DconstraintFilter=alldifferent test

This runs all benchmarks (in the default time range upTo30sec) that use any constraint from the
`alldifferent` family (Alldiff, Alldistinct, AlldifferentExceptZero, etc.).

Multiple families can be combined (OR semantics, deduplicated):

    mvn -pl jacop-benchmarks -Dtest=MinizincByConstraintTest -DconstraintFilter=cumulative,diffn test

### Controlling the time range

The `-DtimeFilter` property controls which time categories are included (cumulative). It defaults
to `upTo30sec`.

    mvn -pl jacop-benchmarks -Dtest=MinizincByConstraintTest -DconstraintFilter=alldifferent -DtimeFilter=upTo5sec test
    mvn -pl jacop-benchmarks -Dtest=MinizincByConstraintTest -DconstraintFilter=alldifferent -DtimeFilter=upTo5min test
    mvn -pl jacop-benchmarks -Dtest=MinizincByConstraintTest -DconstraintFilter=alldifferent -DtimeFilter=all test

Each individual test gets a timeout matching its own time category (e.g. 20s for upTo5sec benchmarks).

### Available constraint families

The mapping from FlatZinc builtins to families is defined in `constraint-families.json`:

    alldifferent, gcc, cumulative, circuit, element, table, regular, knapsack, binpacking,
    diffn, linear, comparison, boolean, arithmetic, counting, ordering, networkflow, geost,
    sequence, assignment, member, set, float, graph, channel, minmax

### Generating or regenerating metadata

Run the metadata generator to (re)populate all `metadata.json` files:

    mvn -pl jacop-benchmarks -am -Dtest=BenchmarkMetadataGenerator#generateAllMetadata -Dsurefire.failIfNoSpecifiedTests=false test

### Adding a new benchmark

Use `BenchmarkAdder` to add a new MiniZinc problem:

    java -cp <classpath> org.jacop.BenchmarkAdder model.mzn [data1.dzn data2.dzn ...]

This compiles the model to FlatZinc using `minizinc --compile --solver org.jacop`, solves it with
JaCoP to produce the golden output, categorizes by execution time, generates `metadata.json`, and
updates `list.txt`. Requires MiniZinc to be installed and JaCoP registered as a solver (see the
`run-minizinc-jacop` skill).

Cross-checked tests. Directories upTo5sec/hakank_* hold models from Hakan Kjellerstrand's MiniZinc
collection (https://github.com/radsz/hakank), chosen because they use FlatZinc builtins and JaCoP
globals that the rest of the suite rarely reaches. Some are variants that call a MiniZinc global
where the original model spells it out. Their golden outputs are not simply JaCoP's first answer:
script scripts/minizinc-crosscheck.py checks each one against Gecode and Chuffed before it is added.
Models with few solutions enumerate all of them (options.opt passes -n 1000000), and the solution
set must be the same for all three solvers. Larger models get a search annotation that is
input_order/indomain_min on every decision variable, so that all solvers reach the same first (or
optimal) solution. Each directory keeps the model it was flattened from (*.mzn) and a crosscheck.txt
that says what was verified; "scripts/minizinc-crosscheck.py verify <dir>" repeats the check, for
example after a change to the JaCoP MiniZinc library.

Directories upTo5sec/shortest_path_flow_* hold instances of shortest_path from
https://github.com/MiniZinc/minizinc-benchmarks, rewritten with network_flow_cost and checked the same
way. Only instances that finish well within the time limit with JaCoP's internal checks enabled are kept,
because the network simplex checks make each node much slower.

## Extensional constraint benchmarks

The problem directories `table_*` and `mdd_random` hold generated instances for table, negative
table, short table, Boolean table and MDD constraints (random tables, Dubois parity, crosswords,
kakuro, TSP with a distance table). They come from `scripts/extensional-benchmarks.py` with the
parameters in `scripts/extensional-benchmarks-grid.txt`. Directories ending in `_all` enumerate all
solutions (`options.opt` passes `-n 100000`). Together with `circular_except_0`, `nonogram_gchq`,
`peacable_queens`, `pentominoes-zayenz`, `rotating-workforce` and `rotating-workforce-scheduling`
(MiniZinc Challenge and hakank models) they cover `table_int`, `table_bool`, `not table`, `regular`
and `mdd`. Run them alone with `-DconstraintFilter=table` or `-DconstraintFilter=regular`.
