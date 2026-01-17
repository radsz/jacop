---
name: Multi-module Maven Migration
overview: Migrate JaCoP from a single-module Maven project to a multi-module structure with 9 core modules plus optional aggregator module, preserving all functionality, build profiles, and test infrastructure.
todos: []
---

# Multi-Module Maven Migration Plan for JaCoP

This plan migrates the single-module JaCoP project (`jacop/pom.xml`) to a multi-module structure as specified in `MODULE_STRUCTURE_PROPOSAL.md`.

## Phase 1:

Already done, go to phase 2.

### Phase 2: Create Parent POM Structure

### 2.1 Restructure root directory

- Move current `jacop/pom.xml` to `jacop/pom.xml.old` (backup)
- Create new parent POM at `jacop/pom.xml`:
  - Change `<packaging>` from `jar` to `pom`
  - Change `<artifactId>` from `jacop` to `jacop-parent`
  - Move all `<pluginManagement>`, `<properties>`, `<profiles>`, `<build>` configuration to parent
  - Move `<dependencies>` (JUnit, Mockito, SLF4J) to parent with appropriate scopes
  - Add `<modules>` section listing all 9 modules
  - Keep `<developers>`, `<licenses>`, `<scm>`, `<distributionManagement>` in parent

### 2.2 Update properties and profiles

- Preserve all existing profiles: `nocs`, `min`, `commit`, `push`, `release`, `logging`, `ossrh`
- Update surefire plugin excludes/includes in profiles to reference new module paths
- Keep Scala version, AspectJ version, and other properties in parent

## Phase 3: Create Module Directories and POMs

### 3.1 Create module directory structure

Create directories for each module:

```
jacop/
├── jacop-core/
├── jacop-floats/
├── jacop-sets/
├── jacop-sat/
├── jacop-flatzinc/
├── jacop-scala/
├── jacop-examples-java/
├── jacop-examples-scala/
├── jacop-benchmarks/
└── jacop-all/ (optional)
```

### 3.2 Create individual module POMs

**For each module**, create `pom.xml` with:

- Parent reference to `jacop-parent`
- Module-specific `<artifactId>` and `<packaging>jar</packaging>`
- Module-specific dependencies
- Module-specific plugin configurations (e.g., Scala plugin only in `jacop-scala`, JJTree only in `jacop-flatzinc`)

**Key module POM configurations:**

- **jacop-core**: Minimal dependencies (SLF4J only), no special plugins
- **jacop-floats/sets/sat**: Depend on `jacop-core`
- **jacop-flatzinc**: Depend on `jacop-core`, `jacop-floats`, `jacop-sets`; includes JJTree/Javacc plugin
- **jacop-scala**: Depend on `jacop-core`; includes Scala Maven plugin
- **jacop-examples-***: Depend on relevant modules
- **jacop-benchmarks**: Test scope dependencies on all modules; includes benchmark files

## Phase 4: Move Source Code Files

Make sure to use git rename command for every file move so git diff is minimal.

### 4.1 Move core module files (`jacop-core`)

**Source files to move:**

- `src/main/java/org/jacop/core/` → `jacop-core/src/main/java/org/jacop/core/`
- `src/main/java/org/jacop/constraints/` → `jacop-core/src/main/java/org/jacop/constraints/`
- `src/main/java/org/jacop/search/` → `jacop-core/src/main/java/org/jacop/search/`
- `src/main/java/org/jacop/util/` → `jacop-core/src/main/java/org/jacop/util/`
- `src/main/java/org/jacop/api/` → `jacop-core/src/main/java/org/jacop/api/`

**Test files to move:**

- `src/test/java/org/jacop/IntDomainTest.java` → `jacop-core/src/test/java/org/jacop/IntDomainTest.java`
- `src/test/java/org/jacop/SingleConstraintTest.java` → `jacop-core/src/test/java/org/jacop/SingleConstraintTest.java`
- `src/test/java/org/jacop/QueueForwardTest.java` → `jacop-core/src/test/java/org/jacop/QueueForwardTest.java`
- `src/test/java/org/jacop/SmallDenseDomainTest.java` → `jacop-core/src/test/java/org/jacop/SmallDenseDomainTest.java`
- `src/test/java/org/jacop/ConstraintStatusKnownAtImposition.java` → `jacop-core/src/test/java/org/jacop/ConstraintStatusKnownAtImposition.java`
- `src/test/java/org/jacop/TestHelper.java` → `jacop-core/src/test/java/org/jacop/TestHelper.java` (if used by core tests)

### 4.2 Move floats module files (`jacop-floats`)

- `src/main/java/org/jacop/floats/` → `jacop-floats/src/main/java/org/jacop/floats/`
- Move any floats-specific test files

### 4.3 Move sets module files (`jacop-sets`)

- `src/main/java/org/jacop/set/` → `jacop-sets/src/main/java/org/jacop/set/`
- Move any sets-specific test files

### 4.4 Move SAT module files (`jacop-sat`)

- `src/main/java/org/jacop/jasat/` → `jacop-sat/src/main/java/org/jacop/jasat/`
- `src/main/java/org/jacop/satwrapper/` → `jacop-sat/src/main/java/org/jacop/satwrapper/`
- Move any SAT-specific test files

### 4.5 Move FlatZinc module files (`jacop-flatzinc`)

- `src/main/java/org/jacop/fz/` → `jacop-flatzinc/src/main/java/org/jacop/fz/`
- `src/main/jjtree/org/jacop/fz/` → `jacop-flatzinc/src/main/jjtree/org/jacop/fz/`
- `src/main/minizinc/` → `jacop-flatzinc/src/main/minizinc/`
- Update build-helper-maven-plugin to only add jjtree and minizinc sources
- Ensure javacc-maven-plugin runs in this module only
- Move FlatZinc-specific unit tests (if any)

### 4.6 Move Scala module files (`jacop-scala`)

- `src/main/scala/org/jacop/scala/` → `jacop-scala/src/main/scala/org/jacop/scala/`
- Remove `src/main/scala` source addition from parent build-helper plugin
- Configure scala-maven-plugin only in `jacop-scala` POM
- Move Scala DSL tests (if any)

### 4.7 Move Java examples (`jacop-examples-java`)

- `src/main/java/org/jacop/examples/*.java` (excluding `examples/scala/`) → `jacop-examples-java/src/main/java/org/jacop/examples/`
- `src/main/java/org/jacop/examples/fd/` → `jacop-examples-java/src/main/java/org/jacop/examples/fd/`
- `src/main/java/org/jacop/examples/floats/` → `jacop-examples-java/src/main/java/org/jacop/examples/floats/`
- `src/main/java/org/jacop/examples/flatzinc/` → `jacop-examples-java/src/main/java/org/jacop/examples/flatzinc/`
- `src/main/java/org/jacop/examples/set/` → `jacop-examples-java/src/main/java/org/jacop/examples/set/`
- `src/main/java/org/jacop/examples/minizinc/` → `jacop-examples-java/src/main/java/org/jacop/examples/minizinc/`
- `src/main/java/org/jacop/examples/graph/` → `jacop-examples-java/src/main/java/org/jacop/examples/graph/`
- `src/main/java/org/jacop/examples/cpviz/` → `jacop-examples-java/src/main/java/org/jacop/examples/cpviz/`
- `src/main/java/org/jacop/ui/` → `jacop-examples-java/src/main/java/org/jacop/ui/`
- Update maven-jar-plugin mainClass to `org.jacop.examples.RunExample` in this module

### 4.8 Move Scala examples (`jacop-examples-scala`)

- `src/main/scala/org/jacop/examples/scala/` → `jacop-examples-scala/src/main/scala/org/jacop/examples/scala/`

### 4.9 Move benchmarks (`jacop-benchmarks`)

- `src/test/fz/` → `jacop-benchmarks/src/test/fz/`
- `src/test/java/org/jacop/MinizincBasedTest*.java` → `jacop-benchmarks/src/test/java/org/jacop/`
- `src/test/java/org/jacop/MinizincBasedTestsHelper.java` → `jacop-benchmarks/src/test/java/org/jacop/`
- `src/test/java/org/jacop/ExampleBasedTest.java` → `jacop-benchmarks/src/test/java/org/jacop/`
- `src/test/java/org/jacop/FilterBenchmarkTest.java` → `jacop-benchmarks/src/test/java/org/jacop/`
- `src/test/java/org/jacop/PerformanceTest.java` → `jacop-benchmarks/src/test/java/org/jacop/`
- `src/test/java/org/jacop/MinTestSuite.java` → `jacop-benchmarks/src/test/java/org/jacop/`
- `src/test/java/org/jacop/MizincBasedChosen.java` → `jacop-benchmarks/src/test/java/org/jacop/`
- Preserve all `.fzn`, `.mzn`, `.dzn`, `.out` files in `src/test/fz/`

## Phase 5: Update Dependencies and Imports

### 5.1 Module dependencies

**In each module POM**, add dependencies:

- `jacop-core`: None (only SLF4J in parent)
- `jacop-floats`: `jacop-core`
- `jacop-sets`: `jacop-core`
- `jacop-sat`: `jacop-core`
- `jacop-flatzinc`: `jacop-core`, `jacop-floats`, `jacop-sets`
- `jacop-scala`: `jacop-core`
- `jacop-examples-java`: `jacop-core`, `jacop-floats`, `jacop-sets`, `jacop-flatzinc`
- `jacop-examples-scala`: `jacop-core`, `jacop-scala`
- `jacop-benchmarks`: All above modules (test scope)

### 5.2 Test dependencies

- Use `test-jar` type dependencies if tests need access to internal classes from other modules
- Keep JUnit and Mockito in parent with test scope
- Ensure TestHelper utilities are accessible where needed

### 5.3 Verify import statements

- Java import statements should remain unchanged (packages don't change)
- Only module boundaries affect compilation, not package structure

## Phase 6: Plugin Configuration Updates

### 6.1 Parent POM plugins

- Keep plugin management in parent
- Remove module-specific plugin executions from parent
- Keep profiles with module-agnostic configurations

### 6.2 Module-specific plugins

**jacop-flatzinc:**

- Configure `javacc-maven-plugin` to process `src/main/jjtree/org/jacop/fz/Parser.jjt`
- Configure `build-helper-maven-plugin` to add `src/main/jjtree` and `src/main/minizinc` as sources
- Update generated sources path references

**jacop-scala:**

- Configure `scala-maven-plugin` with sourceDir `src/main/scala`
- Ensure `sendJavaToScalac=false` for compatibility

**jacop-examples-java:**

- Configure `maven-jar-plugin` with `mainClass=org.jacop.examples.RunExample`

**jacop-benchmarks:**

- Configure surefire plugin with excludes for long-running tests (preserve existing profile logic)

### 6.3 Javadoc plugin

- Update `sourcepath` exclusions to reference new module structure
- Keep exclusions for generated parser files (`**/fz/Parser.java`, etc.)

### 6.4 JaCoCo plugin

- Update excludes to reference new module paths:
  - `org/jacop/examples/scala/**/*.class` → in `jacop-examples-scala`
  - `org/jacop/scala/**/*.class` → in `jacop-scala`

### 6.5 Checkstyle plugin

- Update `configLocation` path to `../doc/checkstyle.xml` (relative from modules) or keep in parent
- Ensure PMD exclusions still work for generated parser files

## Phase 7: Update Build Profiles

### 7.1 Preserve all profiles in parent

- `nocs`, `min`, `commit`, `push`, `release`, `logging`, `ossrh`
- Update surefire includes/excludes to work with multi-module structure
- Profile paths may need wildcards: `**/IntDomainTest.java` instead of specific module paths

### 7.2 Test execution profiles

- Ensure profiles can selectively run tests across modules
- Consider using module-specific profiles if needed

## Phase 8: Root-Level Files and Resources

### 8.1 Preserve root files

- Keep in `jacop/` root: `.gitignore`, `.travis.yml`, `CHANGELOG`, `LICENSE.md`, `README.md`, `GITWORKFLOW.md`, `change.bash`, `properties.txt`
- Keep `doc/` directory in root (shared documentation)

### 8.2 Update CI/CD

- Update `.travis.yml` or CI scripts if they reference specific paths
- Ensure CI builds all modules: `mvn clean install`

### 8.3 IDE configuration

- Update `.idea/` paths if needed (IntelliJ will auto-detect multi-module structure)
- Module `.iml` files may be regenerated

## Phase 9: Aggregator Module

### 9.1 Create jacop-all

- Create `jacop-all/pom.xml` with packaging `pom`
- Add all modules as dependencies
- Configure `maven-shade-plugin` to create fat JAR
- Or use `maven-assembly-plugin` for custom packaging

## Phase 10: Verification and Testing

### 10.1 Build verification

- Run `mvn clean install` from parent directory (it should run as currently mvn clean install -Pmin)
- Verify all modules compile successfully
- Check generated JARs in each `target/` directory

### 10.2 Test execution (use current profile min)

- Run `mvn test` to execute all unit tests
- Verify core tests: `mvn test -pl jacop-core`
- Verify benchmark tests: `mvn test -pl jacop-benchmarks`
- Test with profiles: `mvn test -Pmin`, `mvn test -Pcommit`, etc.

### 10.3 Example execution

- Verify examples compile: `mvn compile -pl jacop-examples-java`
- Test RunExample: `java -cp ... org.jacop.examples.RunExample`

### 10.4 FlatZinc/MiniZinc verification

- Test FlatZinc parser compilation
- Verify generated parser sources are created correctly
- Test MiniZinc executable scripts (if applicable)

### 10.5 Documentation generation

- Test javadoc generation: `mvn javadoc:javadoc`
- Verify site generation: `mvn site` (if used)

## Phase 11: Cleanup

### 11.1 Remove old structure

- After verification, remove `pom.xml.old`
- Remove empty `src/` directories if any remain in root
- Clean up any temporary migration files

### 11.2 Update documentation

- Update `README.md` with new module structure
- Document how to build individual modules

## Risk Mitigation

### Potential Issues:

1. **Circular dependencies**: Verify no circular module dependencies (shouldn't occur based on proposal)
2. **Test access to internals**: Use `test-jar` dependencies or make test utilities available
3. **Generated code paths**: Ensure JJTree/Javacc generated code paths are correct
4. **Classpath issues**: Verify all examples can find their dependencies
5. **Build performance**: Multi-module builds may be slower initially; optimize later if needed