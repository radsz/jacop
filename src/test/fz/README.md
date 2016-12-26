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
