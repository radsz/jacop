---
name: run-minizinc-jacop
description: Compile MiniZinc (.mzn) models to FlatZinc (.fzn) using JaCoP solver configuration and execute them with JaCoP. Use when the user provides a .mzn file to run, asks to solve a MiniZinc model with JaCoP, or needs to generate and execute FlatZinc files.
---

# Run MiniZinc Models with JaCoP

Compiles `.mzn` files to `.fzn` using JaCoP's MiniZinc library, then executes the `.fzn` with JaCoP's FlatZinc solver.

## Prerequisites

- Java 25+ on PATH
- MiniZinc installed (default: `C:\Program Files\MiniZinc`)
- JaCoP built: `mvn -DskipTests install` from repo root

## Workflow

### Phase A: One-time setup (idempotent)

Check if JaCoP is already registered:

```powershell
& "C:\Program Files\MiniZinc\minizinc.exe" --solvers 2>&1 | Select-String "org.jacop"
```

If `org.jacop` appears, skip to Phase B. Otherwise run the setup script:

```powershell
powershell -ExecutionPolicy Bypass -File ".cursor/skills/run-minizinc-jacop/scripts/setup-minizinc-jacop.ps1"
```

The script auto-elevates to admin (needed to write to `C:\Program Files\MiniZinc`). It:
1. Reads the JaCoP version from `pom.xml` (`<revision>` property)
2. Copies JaCoP's MiniZinc library from `jacop-flatzinc/src/main/minizinc/org/jacop/minizinc/` into `<MiniZinc>/share/minizinc/jacop/`
3. Creates `fzn-jacop.bat` in the MiniZinc directory with the correct classpath pointing to JaCoP module JARs
4. Creates `org.jacop.msc` in `<MiniZinc>/share/minizinc/solvers/`

If JaCoP has not been built yet, run first:

```powershell
mvn -DskipTests install
```

### Phase B: Compile and execute

Set the MiniZinc executable path:

```powershell
$mzn = "C:\Program Files\MiniZinc\minizinc.exe"
```

**Without data file:**

```powershell
# Compile .mzn to .fzn
& $mzn --compile --solver org.jacop model.mzn

# Execute .fzn with JaCoP
& "C:\Program Files\MiniZinc\fzn-jacop.bat" model.fzn
```

**With data file (.dzn):**

```powershell
# Compile .mzn + .dzn to .fzn
& $mzn --compile --solver org.jacop model.mzn -d data.dzn

# Execute .fzn with JaCoP
& "C:\Program Files\MiniZinc\fzn-jacop.bat" model.fzn
```

**Or run directly (MiniZinc handles compile + solve + output formatting):**

```powershell
# Without data
& $mzn --solver org.jacop model.mzn

# With data
& $mzn --solver org.jacop model.mzn -d data.dzn
```

### Common Fz2jacop flags

| Flag | Description |
|------|-------------|
| `-a` | Find all solutions |
| `-n N` | Find N solutions |
| `-t MS` | Timeout in milliseconds |
| `-s` | Print search statistics |
| `-f` | Free search (ignore annotations) |
| `-b` | Prefer bounds consistency |
| `-sat` | Use SAT solver for booleans |
| `-cs` | Complementary search |
| `--restart luby` | Restart search (none/constant/linear/luby/geometric) |

Pass these to `fzn-jacop.bat` or via `minizinc --solver org.jacop -a model.mzn`.

## Key paths

| Item | Path |
|------|------|
| MiniZinc executable | `C:\Program Files\MiniZinc\minizinc.exe` |
| JaCoP MiniZinc library (source) | `jacop-flatzinc/src/main/minizinc/org/jacop/minizinc/` |
| JaCoP MiniZinc library (installed) | `C:\Program Files\MiniZinc\share\minizinc\jacop\` |
| Solver config | `C:\Program Files\MiniZinc\share\minizinc\solvers\org.jacop.msc` |
| fzn-jacop wrapper | `C:\Program Files\MiniZinc\fzn-jacop.bat` |
| FlatZinc entry point class | `org.jacop.fz.Fz2jacop` |

## Verification

After setup, run these checks to confirm the skill works.

### Level 1: Setup check

```powershell
& "C:\Program Files\MiniZinc\minizinc.exe" --solvers 2>&1 | Select-String "org.jacop"
```

Expect: a line containing `org.jacop`.

### Level 2: FZN-only execution

Run JaCoP directly on a pre-compiled `.fzn` from the repo:

```powershell
& "C:\Program Files\MiniZinc\fzn-jacop.bat" jacop-benchmarks/src/test/fz/upTo5sec/alpha/alpha.fzn
```

Expect: 26 variable assignments (a=5, b=13, ... z=18) followed by `----------`.
Compare against `jacop-benchmarks/src/test/fz/upTo5sec/alpha/alpha.out`.

### Level 3: Full pipeline, no data file

```powershell
$mzn = "C:\Program Files\MiniZinc\minizinc.exe"
$testDir = ".cursor/skills/run-minizinc-jacop/tests"

& $mzn --solver org.jacop "$testDir/alpha.mzn"
```

Expect output containing: a = 5, b = 13, c = 9, d = 16, e = 20, f = 4, g = 24, h = 21, i = 25, j = 17, k = 23, l = 2, m = 8, n = 12, o = 10, p = 19, q = 7, r = 11, s = 15, t = 3, u = 1, v = 26, w = 6, x = 22, y = 14, z = 18.

Compare values against `tests/alpha.expected`.

### Level 4: Full pipeline, with data file

```powershell
& $mzn --solver org.jacop "$testDir/fastfood.mzn" -d "$testDir/ff4.dzn"
```

Expect output containing the optimal depot positions:
`[23, 40, 50, 54, 61, 100, 105, 116, 124, 129, 175, 180, 198, 205, 225, 237, 263, 270, 313, 337, 352, 373, 397, 469]`
and `==========` indicating optimality was proven.

Compare against `tests/ff4.expected`.
