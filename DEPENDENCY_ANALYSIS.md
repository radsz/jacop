# JaCoP Dependency Analysis - Phase 1

**Date:** 2026-01-17  
**Purpose:** Complete dependency graph for gradual multi-module refactoring

## Executive Summary

This document identifies all circular dependencies between `jacop-core`, `jacop-floats`, and `jacop-sets` modules that must be resolved before the multi-module migration can succeed.

## Dependency Matrix

| From Module | To Module | Type | Severity | Files Affected |
|------------|----------|------|----------|---------------|
| jacop-core (search) | jacop-floats | Import | **HIGH** | 4 files |
| jacop-core (search) | jacop-sets | Import | **HIGH** | 2 files |
| jacop-core (util) | jacop-floats | Import | **MEDIUM** | 1 file |
| jacop-floats (search) | jacop-core (search) | Import | **HIGH** | 1 file |
| jacop-floats (search) | jacop-core (core) | Import | OK | Multiple (expected) |
| jacop-sets (search) | jacop-core (search) | Import | **MEDIUM** | Multiple (interfaces only) |

## Detailed Dependencies

### 1. jacop-core → jacop-floats

#### 1.1 Search Package Dependencies

**File:** `org.jacop.search.DepthFirstSearch`
- **Imports:**
  - `org.jacop.floats.constraints.PlteqC`
  - `org.jacop.floats.core.FloatDomain`
  - `org.jacop.floats.core.FloatVar`
- **Usage Patterns:**
  - Line 525: `instanceof FloatVar` check
  - Line 526-528: Direct FloatVar domain operations
  - Line 641-655: FloatVar cost handling in child searches
  - Line 665-669: FloatVar cost constraint creation
  - Line 706-708: FloatVar cost domain updates
  - Line 921-922: FloatVar cost value printing
  - Line 1152-1153: FloatVar cost value display
  - Line 1299-1300: FloatVar cost value in toString
- **Impact:** **CRITICAL** - Core search algorithm depends on float types

**File:** `org.jacop.search.PrioritySearch`
- **Imports:**
  - `org.jacop.floats.core.FloatVar`
  - `org.jacop.floats.core.FloatDomain`
  - `org.jacop.floats.constraints.PlteqC`
- **Usage:** Similar to DepthFirstSearch (needs analysis)

**File:** `org.jacop.search.SimpleSolutionListener`
- **Imports:**
  - `org.jacop.floats.core.FloatVar`
  - `org.jacop.set.core.SetVar`
- **Usage:** Type checking for solution listeners

**File:** `org.jacop.search.restart.RestartSearch`
- **Imports:**
  - `org.jacop.floats.core.FloatVar`
  - `org.jacop.floats.core.FloatDomain`
  - `org.jacop.floats.constraints.PlteqC`
- **Usage:** Restart search with float support

#### 1.2 Util Package Dependencies

**File:** `org.jacop.util.Matrix`
- **Imports:**
  - `org.jacop.floats.core.FloatDomain`
  - `org.jacop.floats.core.FloatInterval`
  - `org.jacop.floats.core.FloatIntervalDomain`
- **Usage:**
  - Line 159: `mult(FloatInterval[][], double[][])` method returns `FloatIntervalDomain[][]`
  - Line 178-179: Uses `FloatDomain.mulBounds()` and `FloatDomain.addBounds()`
- **Impact:** **MEDIUM** - Only used in `IntervalGaussSeidel` (float-specific constraint)
- **Recommendation:** **MOVE TO jacop-floats** (only used in floats module)

### 2. jacop-core → jacop-sets

#### 2.1 Search Package Dependencies

**File:** `org.jacop.search.DepthFirstSearch`
- **Imports:**
  - `org.jacop.set.core.SetDomain`
  - `org.jacop.set.core.SetVar`
- **Usage Patterns:**
  - Line 585-589: `instanceof SetVar` check and SetVar domain operations
  - Line 810-814: SetVar complement operations
  - Line 577: Comment mentions SetVar-specific search behavior
- **Impact:** **CRITICAL** - Core search algorithm depends on set types

**File:** `org.jacop.search.TraceGenerator`
- **Imports:**
  - `org.jacop.set.core.SetDomain`
  - `org.jacop.set.core.SetVar`
- **Usage:** Trace generation for set variables

**File:** `org.jacop.search.SimpleSolutionListener`
- **Imports:**
  - `org.jacop.set.core.SetVar`
- **Usage:** Type checking for solution listeners

### 3. jacop-floats → jacop-core

#### 3.1 Search Package Dependencies

**File:** `org.jacop.floats.search.Optimize`
- **Imports:**
  - `org.jacop.search.DepthFirstSearch` ⚠️ **CONCRETE CLASS**
  - `org.jacop.search.Search` ✓ (interface - OK)
  - `org.jacop.search.SelectChoicePoint` ✓ (interface - OK)
  - `org.jacop.search.SimpleSolutionListener` ⚠️ **CONCRETE CLASS**
- **Usage:**
  - Line 55: `DepthFirstSearch<T> search;` - field declaration
  - Line 67: Constructor parameter `DepthFirstSearch<T> search`
  - Line 70: Direct assignment `this.search = search;`
  - Line 74-75: Direct method calls on `search` object
  - Line 82: Uses `SimpleSolutionListener` directly
  - Line 100: Calls `search.labeling(store, select)`
- **Impact:** **HIGH** - Float optimization depends on concrete search class

**All Float Search Classes:**
- **Imports:**
  - `org.jacop.core.Store` ✓ (core class - OK)
  - `org.jacop.core.Var` ✓ (core class - OK)
  - `org.jacop.core.TimeStamp` ✓ (core class - OK)
  - `org.jacop.constraints.PrimitiveConstraint` ✓ (core class - OK)
  - `org.jacop.search.ComparatorVariable` ✓ (interface - OK)
  - `org.jacop.search.SimpleSelect` ✓ (interface - OK)
- **Status:** Most dependencies are on interfaces/core classes - **OK**

### 4. jacop-sets → jacop-core

#### 4.1 Search Package Dependencies

**All Set Search Classes:**
- **Imports:**
  - `org.jacop.core.IntDomain` ✓ (core class - OK)
  - `org.jacop.core.Store` ✓ (core class - OK)
  - `org.jacop.search.ComparatorVariable` ✓ (interface - OK)
  - `org.jacop.search.Indomain` ✓ (interface - OK)
- **Status:** All dependencies are on interfaces/core classes - **OK**

## Circular Dependency Chains

### Chain 1: Search ↔ Floats
```
jacop-core.search.DepthFirstSearch
    ↓ (imports FloatVar, FloatDomain, PlteqC)
jacop-floats.core.FloatVar
    ↓ (extends Var)
jacop-core.core.Var
    ↓ (used by)
jacop-floats.search.Optimize
    ↓ (imports DepthFirstSearch)
jacop-core.search.DepthFirstSearch
```
**Type:** Import-based circular dependency  
**Severity:** **CRITICAL**

### Chain 2: Search ↔ Sets
```
jacop-core.search.DepthFirstSearch
    ↓ (imports SetVar, SetDomain)
jacop-sets.core.SetVar
    ↓ (extends Var)
jacop-core.core.Var
    ↓ (used by)
jacop-sets.search.*
    ↓ (imports search interfaces)
jacop-core.search.*
```
**Type:** Import-based circular dependency  
**Severity:** **CRITICAL**

## Hot Spots (Classes with Most Cross-Dependencies)

1. **DepthFirstSearch** - 7 cross-module imports
   - 3 from floats (FloatVar, FloatDomain, PlteqC)
   - 2 from sets (SetVar, SetDomain)
   - Used by floats.search.Optimize

2. **Optimize** (floats) - 2 concrete class imports from core.search
   - DepthFirstSearch (concrete)
   - SimpleSolutionListener (concrete)

3. **PrioritySearch** - 3 imports from floats
   - Similar pattern to DepthFirstSearch

4. **SimpleSolutionListener** - 2 cross-module imports
   - FloatVar, SetVar

## Usage Pattern Analysis

### Pattern 1: Type Checking with instanceof
**Location:** `DepthFirstSearch.label()`
```java
if (costVariable instanceof FloatVar) {
    // FloatVar-specific operations
}
if (fdv instanceof SetVar) {
    // SetVar-specific operations
}
```
**Frequency:** Multiple locations in DepthFirstSearch  
**Solution:** Extract to handler pattern

### Pattern 2: Direct Type Casting
**Location:** `DepthFirstSearch.label()`
```java
((FloatVar) costVariable).domain.in(...)
((SetVar) fdv).domain.inGLB(...)
```
**Frequency:** High  
**Solution:** Use handler pattern with type-specific implementations

### Pattern 3: Constraint Creation
**Location:** `DepthFirstSearch.label()`
```java
cost = new PlteqC((FloatVar) costVariable, ...);
```
**Frequency:** Multiple locations  
**Solution:** Factory pattern or handler pattern

### Pattern 4: Concrete Class Dependency
**Location:** `Optimize.java`
```java
DepthFirstSearch<T> search;  // Concrete class, not interface
```
**Frequency:** 1 file  
**Solution:** Use `Search<T>` interface instead

## Recommendations

### Priority 1 (Critical - Blocks Migration)

1. **Refactor DepthFirstSearch**
   - Extract FloatVar/SetVar handling to handler interfaces
   - Remove direct imports of FloatVar, SetVar, FloatDomain, SetDomain
   - Use handler registry pattern

2. **Refactor Optimize**
   - Change `DepthFirstSearch<T>` to `Search<T>` interface
   - Remove dependency on `SimpleSolutionListener` concrete class

3. **Refactor PrioritySearch**
   - Similar to DepthFirstSearch refactoring

### Priority 2 (High - Should Fix)

4. **Refactor SimpleSolutionListener**
   - Extract type checking to handlers
   - Remove FloatVar/SetVar imports

5. **Refactor RestartSearch**
   - Similar pattern to DepthFirstSearch

### Priority 3 (Medium - Nice to Have)

6. **Move Matrix to jacop-floats**
   - Only used in IntervalGaussSeidel
   - Has float-specific dependencies
   - Simple move operation

7. **Refactor TraceGenerator**
   - Extract SetVar handling to handler

## Next Steps

1. ✅ **Phase 1 Complete:** Dependency analysis documented
2. **Phase 2:** Extract handler interfaces in jacop-core
3. **Phase 3:** Refactor DepthFirstSearch to use handlers
4. **Phase 4:** Refactor Optimize to use interfaces
5. **Phase 5:** Move Matrix to jacop-floats
6. **Phase 6:** Test module isolation
7. **Phase 7:** Execute final migration

## Files Requiring Refactoring

### jacop-core
- `src/main/java/org/jacop/search/DepthFirstSearch.java` ⚠️ **CRITICAL**
- `src/main/java/org/jacop/search/PrioritySearch.java` ⚠️ **HIGH**
- `src/main/java/org/jacop/search/SimpleSolutionListener.java` ⚠️ **HIGH**
- `src/main/java/org/jacop/search/TraceGenerator.java` ⚠️ **MEDIUM**
- `src/main/java/org/jacop/search/restart/RestartSearch.java` ⚠️ **MEDIUM**
- `src/main/java/org/jacop/util/Matrix.java` → **MOVE TO floats**

### jacop-floats
- `src/main/java/org/jacop/floats/search/Optimize.java` ⚠️ **HIGH**

### jacop-sets
- No files require refactoring (all use interfaces correctly)

---

**Analysis completed:** 2026-01-17  
**Next phase:** Extract handler interfaces
