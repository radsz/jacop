JaCoP
=====

Java Constraint Programming (JaCoP) solver

JaCoP solver is Java-based open source solver developed and maintained mainly by two people
- Krzysztof Kuchcinski, Dept. of Computer Science, Lund University, Sweden.
- Radoslaw Szymanek - Crossing-Tech, Switzerland.

Moreover a number of students have contributed to the solver by programming first versions of different global
constraints and set constraints. The solver is being used in academia for research and teaching as well as in
industry for commercial purposes. The most successful use of the solver is within Electronic Design Automation
community, since both main authors come from that community.

JaCoP provides a significant number of constraints to facilitate modeling as well as modular design of search.
This allows to tailor search to characteristics of the problem being addressed. It has currently more than 90,000 lines
of code, not including examples and testing code. The examples which are the preferred way to document the abilities of
JaCoP have more than 20.000 lines of code. The core developers have been working on JaCoP for past 10 years during their
free time as a hobby activity. It has been refactored, transformed, and improved many times. Initial versions of JaCoP
were even 3 orders of magnitude slower than the current version. JaCoP implementation has been influenced heavily by
more than 20 research articles. Moreover, JaCoP was used as a tool to conduct experiments for CP publications.
JaCoP supports finite domains of integers and sets of integers.

The major focus of JaCoP are its constraints. These constraints include rich set of primitive, logical, and
conditional constraints as well as many global constraints. The most important global constraints are as follows.

- diff2,
- cumulative,
- alldifferent,
- gcc,
- extensional support (with three different state-of-the-art approaches)and extensional conflict,
- among,
- element,
- circuit,
- knapsack,
- regular,
- netflow, and
- geost.

JaCoP solver contains also front-end for FlatZinc language that makes it possible to execute MiniZinc models. It allows
us to perform extensive testing with the help of other solvers as we can compare results from different solvers.

JaCoP is an ongoing activity. We are working on it in our free time. The most recent addition is Scala based DSL so
you can create your own constraint programs more intuitively.

Getting started
---------------

The easiest way to make jar file for JaCoP is to use maven. First, install maven on your computer and then write

    mvn install -DskipTests

The jar file will be generated into the `target` directory.

One can test the setup by running:

    java -jar target/jacop-x.x.x.jar fd.Sudoku

Where `fd` stands for 'finite domain'. See the `src/main/java/org/jacop/examples/` directory for more examples.

Compilation
-----------

Compilation of JaCoP can be easily done by issuing the following command

    mvn compile

Documentation
-------------

Generation of Java API documentation

    mvn javadoc:javadoc

Generation of Scala formatted API documentation for Java and Scala

    mvn scala:doc

Installation using Maven
------------------------

To use JaCoP with maven you can just include it as a dependency in your `pom.xml`

    <dependency>
        <groupId>org.jacop</groupId>
        <artifactId>jacop</artifactId>
        <version>4.5.0</version>
    </dependency>

From the version 4.4.0, JaCoP is uploaded to Maven Central so the above is the only thing you need to do.

For older versions of JaCoP (4.3 and older) you also need to add the following information 
about CSLTH Maven repository to your `pom.xml` as well

    <repositories>
		<repository>
			<id>CSLTH</id>
			<name>CS LTH maven repo</name>
			<releases>
				<enabled>true</enabled>
			</releases>
			<snapshots>
				<enabled>true</enabled>
				<updatePolicy>always</updatePolicy>
			</snapshots>
			<url>http://maven.cs.lth.se/content/repositories/public/</url>
		</repository>
	</repositories>

