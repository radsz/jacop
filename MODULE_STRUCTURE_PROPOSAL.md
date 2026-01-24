# Proposed Multi-Module Maven Structure for JaCoP

Based on the current codebase analysis, here is a proposed multi-module structure:

## Root Module: `jacop-parent`

- Parent POM managing common dependencies and plugin configurations
- Defines version properties, build profiles, and shared configurations

## Core Modules

### 1. `jacop-core`

**Purpose**: Core constraint programming solver engine

**Contains**:

- `org.jacop.core` - Core domain, variables, store, backtracking
- `org.jacop.constraints` - All constraint implementations (207+ files)
- `org.jacop.search` - Search strategies and implementations
- `org.jacop.util` - Utility classes (SparseSet, QueueForward, MDD, etc.)
- `org.jacop.api` - Core interfaces and APIs
- `src/test/java/org/jacop/*` - Unit tests for core functionality:
    - `IntDomainTest.java`
    - `SingleConstraintTest.java`
    - `QueueForwardTest.java`
    - `SmallDenseDomainTest.java`
    - `ConstraintStatusKnownAtImposition.java`

**Dependencies**: None (or minimal, like SLF4J for logging)

---

### 2. `jacop-floats`

**Purpose**: Floating-point constraint support

**Contains**:

- `org.jacop.floats.*` - All floating-point domain and constraints (73 files)

**Dependencies**: `jacop-core`

---

### 3. `jacop-sets`

**Purpose**: Set variable and constraint support

**Contains**:

- `org.jacop.set.core` - Set variables and domains
- `org.jacop.set.constraints` - Set constraints (24 files)
- `org.jacop.set.search` - Set variable search heuristics

**Dependencies**: `jacop-core`

---

### 4. `jacop-sat`

**Purpose**: SAT solver integration

**Contains**:

- `org.jacop.jasat.*` - JaCoP SAT solver implementation (48 files)
- `org.jacop.satwrapper.*` - SAT wrapper for boolean constraints (10 files)

**Dependencies**: `jacop-core`

---

## Integration/Support Modules

### 5. `jacop-flatzinc`

**Purpose**: FlatZinc/MiniZinc format support

**Contains**:

- `org.jacop.fz.*` - FlatZinc parser and loader
- `src/main/jjtree/org/jacop/fz/` - Parser grammar (JJTree/Javacc)
- `src/main/minizinc/org/jacop/minizinc/` - MiniZinc library files (.mzn)
- MiniZinc executable scripts and configuration

**Dependencies**: `jacop-core`, `jacop-floats`, `jacop-sets`

---

### 6. `jacop-scala`

**Purpose**: Scala DSL for JaCoP

**Contains**:

- `org.jacop.scala.*` - Scala DSL definitions
- `package.scala`, `jacop.scala`

**Dependencies**: `jacop-core`, Scala libraries

---

### 7. `jacop-examples-java`

**Purpose**: Java examples and demonstrations

**Contains**:

- `org.jacop.examples.*` (Java examples only)
    - `org.jacop.examples.fd.*` - Finite domain examples
    - `org.jacop.examples.floats.*` - Floating-point examples
    - `org.jacop.examples.flatzinc.*` - FlatZinc examples
    - `org.jacop.examples.set.*` - Set constraint examples
    - `org.jacop.examples.minizinc.*` - MiniZinc model files
    - `org.jacop.examples.graph.*` - Graph constraint examples
    - `org.jacop.examples.cpviz.*` - CP visualization examples
    - `org.jacop.ui.*` - UI utilities (e.g., `PrintSchedule.java` - part of examples)
- `org.jacop.examples.RunExample.java`

**Dependencies**: `jacop-core`, `jacop-floats`, `jacop-sets`, `jacop-flatzinc`

---

### 8. `jacop-examples-scala`

**Purpose**: Scala examples and demonstrations

**Contains**:

- `org.jacop.examples.scala.*` - All Scala example files (30 files)

**Dependencies**: `jacop-core`, `jacop-scala`

---

### 9. `jacop-benchmarks`

**Purpose**: FlatZinc benchmark test suite and integration tests

**Contains**:

- `src/test/fz/*` - All FlatZinc benchmark files (.fzn, .mzn, .dzn)
    - `upTo5sec/` - Problems solvable in <5 seconds
    - `upTo30sec/` - Problems solvable in <30 seconds
    - `upTo1min/`, `upTo5min/`, `upTo10min/`, `upTo1hour/`, `above1hour/`
    - `flakyTests/`, `errors/`, `scriptTest/`, `scriptGolden/`
- `src/test/java/org/jacop/MinizincBasedTest*.java` - Test runners for benchmarks
- `src/test/java/org/jacop/ExampleBasedTest.java` - Cross-module example tests
- `src/test/java/org/jacop/FilterBenchmarkTest.java` - Benchmark infrastructure tests
- `src/test/java/org/jacop/PerformanceTest.java` - Performance tests
- `*.out` files with expected outputs

**Dependencies**: `jacop-core`, `jacop-floats`, `jacop-sets`, `jacop-flatzinc` (test scope)

---

## Optional/Additional Modules

### 10. `jacop-all` (Optional)

**Purpose**: Aggregator module - single JAR with all dependencies

**Contains**:

- Maven shade plugin to create fat JAR
- Useful for distribution and standalone usage

**Dependencies**: All other modules

---

## Module Dependency Graph

```
jacop-core (foundation)
    ├── jacop-floats
    ├── jacop-sets
    ├── jacop-sat
    ├── jacop-flatzinc ──┐
    ├── jacop-scala      │
    │                    ├── jacop-examples-java
    │                    ├── jacop-examples-scala
    │                    │
    │                    └── jacop-benchmarks
```

---

## Benefits of This Structure

1. **Clear Separation of Concerns**: Each module has a well-defined purpose
2. **Selective Dependencies**: Users can depend only on modules they need
3. **Independent Development**: Modules can be developed/tested independently
4. **Better Build Performance**: Only changed modules need to be rebuilt
5. **Easier Maintenance**: Clear boundaries make refactoring safer
6. **Smaller Artifacts**: Users don't need to include examples/benchmarks in production

---

## Testing Strategy

**Unit Tests**: Each module contains its own unit tests in `src/test/java`:

- `jacop-core` - Tests core functionality (domains, variables, constraints)
- `jacop-floats` - Tests floating-point constraints
- `jacop-sets` - Tests set constraints
- `jacop-sat` - Tests SAT solver integration
- `jacop-flatzinc` - Tests FlatZinc parser and loader

**Integration Tests**: Cross-module integration tests and benchmarks:

- `jacop-benchmarks` - Contains FlatZinc benchmark suite and integration tests that span multiple modules
- These tests verify that modules work together correctly

This approach follows Maven best practices where each module is self-contained with its own tests.

---

## Migration Considerations

1. **Package Structure**: Current packages should remain mostly unchanged
2. **Test Dependencies**: Tests may need access to internal classes - use test-jar dependencies
3. **Examples**: Some examples might cross module boundaries - move to appropriate module or create shared example
   utilities
4. **Build Profiles**: Current Maven profiles can be preserved in parent POM
5. **Generated Code**: JJTree/Javacc generated code remains in `jacop-flatzinc`
6. **Test Organization**: Move unit tests to their respective modules; keep integration/benchmark tests in
   `jacop-benchmarks`

---

## Additional Notes

- The `jacop-benchmarks` module contains a large number of files (8500+), which makes it a good candidate for separation
- Scala support is self-contained and makes sense as a separate module
- FlatZinc/MiniZinc support is substantial enough to warrant its own module
- Examples are already partially separated (Java vs Scala), making this split natural
- UI utilities like `PrintSchedule` are part of the examples and stay in `jacop-examples-java`