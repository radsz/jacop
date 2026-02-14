# AGENTS.md

Guidance for agentic coding assistants working in this repository.

## Scope and priorities
- This is a multi-module Maven project for JaCoP (Java Constraint Programming solver).
- Main language is Java; Scala DSL lives in `jacop-scala` and `jacop-examples-scala`.
- Prefer small, module-scoped changes over repository-wide rewrites.
- Keep behavior stable unless the task explicitly asks for semantic changes.
- Constraint propagation correctness is critical; avoid changes that could break solver semantics.

## Core architecture concepts
Understanding these concepts is essential for working with JaCoP:

- **Store**: Central registry holding all variables and constraints. Manages backtracking levels.
- **Var/IntVar**: Decision variables with domains. IntVar has an IntDomain representing possible values.
- **Domain types**:
  - `IntervalDomain`: Stores values as intervals (e.g., 1..5, 10..20). Default for large ranges.
  - `SmallDenseDomain`: Bit-vector representation for domains spanning ≤64 values. Used automatically for small ranges.
  - `BoundDomain`: Only tracks min/max bounds, not holes.
- **Constraint**: Defines relationships between variables. Key methods:
  - `impose()`: Attaches constraint to store
  - `consistency()`: Propagates constraint, pruning variable domains
  - `satisfied()`: Returns true if constraint is definitely satisfied
- **Backtracking**: The solver uses trail-based backtracking via `BacktrackableManager`. Variables record domain changes per level.
- **Search**: `DepthFirstSearch` with variable/value selection heuristics (`SelectChoicePoint`, `Indomain`).
- **Propagation events**: `GROUND` (singleton), `BOUND` (min/max changed), `ANY` (any change), `NONE` (no notification needed).

## Repository layout
- Parent POM: `pom.xml`
- Core modules:
  - `jacop-core`
  - `jacop-floats`
  - `jacop-sets`
  - `jacop-sat`
  - `jacop-flatzinc`
  - `jacop-examples-java`
  - `jacop-benchmarks`
  - `jacop-scala`
  - `jacop-examples-scala`
  - `jacop-all`
- Style and static analysis configuration:
  - `doc/checkstyle.xml`
  - `doc/suppression.xml`

## Build commands
- Build all modules (skip tests):
  - `mvn -DskipTests install`
- Compile all modules:
  - `mvn compile`
- Clean and compile everything:
  - `mvn clean compile`
- Build a single module and dependencies:
  - `mvn -pl jacop-core -am compile`
  - Replace `jacop-core` with the module you are editing.
- Fast local iteration without Checkstyle (profile disables checkstyle execution):
  - `mvn -Pnocs -pl jacop-core -am test`

## Lint and formatting commands
- Checkstyle (configured in validate phase by default):
  - `mvn checkstyle:check`
- Spotless format Java sources (configured with google-java-format):
  - `mvn spotless:apply`
- Spotless verify formatting:
  - `mvn spotless:check`
- SpotBugs report:
  - `mvn spotbugs:spotbugs`
- PMD report:
  - `mvn pmd:pmd`
  - Report output: `target/pmd.xml` (per module)
- PMD check (fails build on violations):
  - `mvn pmd:check`
- Common PMD violations to watch for:
  - `UselessParentheses`: Remove unnecessary parentheses, especially in assert statements
  - `UnnecessaryFullyQualifiedName`: Use simple names when class is already accessible (e.g., in subclasses use `GROUND` not `IntDomain.GROUND`)

## Test commands
- Always run tests with `-Pmin` unless explicitly instructed otherwise.
- Run default test set from parent Surefire config:
  - `mvn -Pmin test`
- Run tests in one module:
  - `mvn -Pmin -pl jacop-core test`
- Run one test class (important):
  - `mvn -Pmin -pl jacop-core -Dtest=IntDomainTest test`
- Run one test method (important):
  - `mvn -Pmin -pl jacop-core -Dtest=IntDomainTest#testContains test`
- Run multiple methods:
  - `mvn -Pmin -pl jacop-core -Dtest=IntDomainTest#testContains+testComplement test`
- Run a class in another module:
  - `mvn -Pmin -pl jacop-flatzinc -Dtest=ExampleBasedTest test`

## Test profiles and CI-like subsets
- The parent POM defines test profiles with increasing coverage:
  - `min`
  - `commit`
  - `push`
  - `release`
- Use when you need broader FlatZinc benchmark coverage:
  - `mvn -Pmin test`
  - `mvn -Pcommit test`
  - `mvn -Ppush test`
  - `mvn -Prelease test`

## Writing tests
- Use JUnit 5 (`@Test`, `@BeforeEach`, `@ParameterizedTest`).
- Test domain operations thoroughly: intersection, union, subtraction, complement.
- For constraint tests, verify:
  - Correct pruning behavior
  - Failure detection (empty domain)
  - Backtracking correctness (state restoration)
- Use `Store.consistency()` to run propagation after imposing constraints.
- Common test pattern:
  ```java
  Store store = new Store();
  IntVar x = new IntVar(store, "x", 1, 10);
  store.impose(constraint);
  assertTrue(store.consistency());
  assertEquals(expectedDomain, x.dom());
  ```

## Notes about Surefire behavior
- Parent Surefire includes only selected classes by default:
  - `**/IntDomainTest.java`
  - `**/ExampleBasedTest.java`
  - `**/SingleConstraintTest.java`
- For newly added test classes, use `-Dtest=...` while iterating.
- If needed, align new tests with existing naming/placement patterns.

## Java version and toolchain
- Maven compiler target/release is Java 25 (`<release>25</release>`).
- Do not introduce APIs incompatible with Java 25 baseline.
- Use Maven commands from repository root unless task says otherwise.

## Code style: source of truth
- Primary style rules are enforced by:
  - Checkstyle config: `doc/checkstyle.xml`
  - Spotless with `google-java-format` style
- If this file conflicts with tooling, follow tooling.

## Code style: formatting and structure
- Use spaces, not tabs.
- Keep Java line length within 150 chars (imports/packages are exempt by rule).
- Always use braces for `if`, `else`, `for`, `while`, and `do` blocks.
- Keep one top-level class per file.
- Add a newline at end of file.
- Do not rely on manual alignment; let formatter decide.

## Code style: imports
- Do not use wildcard imports in Java.
- Keep imports unwrapped (no line wraps in import/package lines).
- Import order follows Checkstyle custom rule:
  - static imports first
  - then non-static third-party/project imports
  - keep groups alphabetized and separated by a blank line
- Remove unused imports (Spotless is configured to do this).

## Code style: naming
- Packages: lowercase dot-separated.
- Types (classes/interfaces/enums/records): UpperCamelCase.
- Methods: lowerCamelCase.
- Parameters and lambda parameters: lowerCamelCase.
- Prefer meaningful names over abbreviations; Checkstyle is strict about acronyms.
- Keep existing public API names intact unless explicitly requested.

## Code style: types and API design
- Prefer explicit types in public APIs.
- Keep generic bounds explicit when required by solver abstractions.
- Avoid raw types.
- Preserve serialization/compatibility-sensitive signatures.
- Follow existing Lombok usage patterns (`@Getter`, `@Setter`, `@Slf4j`) where present.

## Code style: Javadoc and comments
- Public/protected APIs are expected to have Javadoc in this codebase.
- Keep Javadoc summaries as proper sentences.
- For TODOs, format exactly as `TODO:` (all caps + colon).
- Do not add noisy comments; explain non-obvious reasoning only.

## Error handling and logging
- Use domain-specific exceptions consistently:
  - `FailException`: Propagation failure (empty domain). Use `throw Store.failException;` (singleton instance).
  - `IllegalArgumentException`: Invalid constraint parameters at construction time.
- Do not swallow exceptions silently.
- If intentionally ignoring an exception, keep it explicit and safe.
- Prefer structured logging through existing SLF4J/Lombok patterns (`@Slf4j` annotation).
- Preserve existing failure semantics in search/constraint propagation code.
- The `DEBUG` flag pattern is common: `if (DEBUG) { log.debug(...); }` for expensive debug output.

## Constraint categories
Constraints are organized by type in `org.jacop.constraints`:

- **Primitive**: `XeqC`, `XltY`, `XplusYeqZ` - basic arithmetic/comparison
- **Reified**: `Reified`, `IfThen`, `IfThenElse` - constraint as boolean variable
- **Global**: `Alldifferent`, `GCC`, `Cumulative`, `Element` - complex constraints with specialized propagation
- **Regular**: `Regular`, `ExtensionalSupport` - table/automaton-based constraints
- **Decomposed**: Constraints that decompose into simpler primitives
- **Network flow**: `NetworkFlow` and related in `org.jacop.constraints.netflow`

Key constraint interfaces:
- `Constraint`: Base class for all constraints
- `PrimitiveConstraint`: Constraints that can be negated (used in reification)
- `DecomposedConstraint`: Constraints that generate auxiliary variables/constraints

## Common code patterns

### Assert statements
- Use assertions for invariant checks, not for validation
- Do not wrap assert conditions in parentheses: `assert condition;` not `assert (condition);`
- Include descriptive messages: `assert min <= max : "min must be <= max";`

### Domain operations
- Always check `checkInvariants()` in debug assertions after domain modifications
- Use domain ID checks for type-specific optimizations:
  ```java
  if (domain.domainId() == SMALL_DENSE_DOMAIN_ID) {
      // optimized path for SmallDenseDomain
  }
  ```
- Subclasses of `IntDomain` can access constants directly: `GROUND`, `BOUND`, `ANY`, `NONE`, `MIN_INT`, `MAX_INT`

### Constraint implementation
- Call `store.addChanged(var, event, ...)` when a variable's domain changes
- Use `Store.failException` to signal propagation failure
- Implement `consistency()` to be idempotent; it may be called multiple times

### Backtracking
- Record changes via `BacktrackableManager.addChanged(index)`
- Implement `remove(int level)` to restore state when backtracking
- Domain stamps track the level at which changes were made

### Performance considerations
- Prefer `SmallDenseDomain` for variables with small ranges (≤64 values)
- Use sparse iteration (`ValueEnumeration`) instead of dense loops over large domains
- Avoid allocating objects in hot paths; reuse arrays where possible

## Module-specific tips
- `jacop-flatzinc` uses JavaCC/JJTree generation.
- If parser-generated classes get stale in IDE builds, run:
  - `mvn -Pmin -pl jacop-flatzinc clean test`
- Scala modules use `scala-maven-plugin`; do not assume Java-only build paths.

## Agent workflow checklist
1. **Understand scope**: Identify which module(s) and classes are affected.
2. **Read before editing**: Always read a file before modifying it; understand existing patterns.
3. **Compile early**: Run `mvn -pl <module> -am compile` after initial changes.
4. **Test incrementally**: Use `-Pmin -Dtest=ClassName#methodName` for fast iteration.
5. **Fix formatting**: Run `mvn spotless:apply` to auto-format code.
6. **Check style**: Run `mvn checkstyle:check` and `mvn pmd:check` before finalizing.
7. **Verify tests pass**: Run `mvn -Pmin -pl <module> test` for the affected module.
8. **Document changes**: Report exact commands executed and any skipped verification.

### Common fix patterns
- **PMD UselessParentheses**: `assert (x)` → `assert x`
- **PMD UnnecessaryFullyQualifiedName**: `IntDomain.GROUND` → `GROUND` (in subclass)
- **Checkstyle import order**: Let `spotless:apply` fix import ordering
- **Missing Javadoc**: Add for public/protected members; keep summaries as sentences

## AI assistant configuration files
- `AGENTS.md` (this file): Primary guidance for AI coding assistants
- `CLAUDE.md`: Claude-specific instructions (if present)
- `.cursorrules`: Cursor IDE rules (not present)
- `.cursor/rules/`: Cursor rule directory (not present)
- `.github/copilot-instructions.md`: GitHub Copilot instructions (not present)

Priority order: Tool-specific files > AGENTS.md > inferred patterns from codebase.
