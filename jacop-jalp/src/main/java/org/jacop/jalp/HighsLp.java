/*
 * HighsLp.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.jalp;

import static java.lang.foreign.ValueLayout.ADDRESS;
import static java.lang.foreign.ValueLayout.JAVA_DOUBLE;
import static java.lang.foreign.ValueLayout.JAVA_INT;

import java.lang.foreign.Arena;
import java.lang.foreign.FunctionDescriptor;
import java.lang.foreign.Linker;
import java.lang.foreign.MemorySegment;
import java.lang.foreign.SymbolLookup;
import java.lang.invoke.MethodHandle;
import java.lang.ref.Cleaner;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;

/**
 * The dual simplex of HiGHS (MIT licence, highs.dev) through Java's foreign function API, with the
 * interface of {@link RevisedDualSimplex}: {@code min c x} subject to {@code lo_i <= a_i x <= hi_i}
 * and {@code lo_j <= x_j <= hi_j}, the slack of row i being column {@code n + i} of the system
 * {@code [A -I] (x, s) = 0}. HiGHS keeps its basis and factorization between calls, so a change of
 * bounds or added rows is solved from the last basis.
 *
 * <p>The native library is not shipped with JaCoP. It is looked up, in this order, at the path of
 * the system property {@code org.jacop.jalp.highs}, at the path of the environment variable {@code
 * JACOP_HIGHS}, and by its name ({@code libhighs.so}, {@code libhighs.dylib}, {@code highs.dll}) on
 * the library path of the system. {@link #available()} says whether it was found; the JVM needs
 * {@code --enable-native-access=ALL-UNNAMED} to call it without a warning. HiGHS 1.15 with 32-bit
 * {@code HighsInt} (its default build) is the version this was written for.
 *
 * <p>Each instance owns one HiGHS object, single-threaded (option {@code threads=1}), with presolve
 * off and the dual simplex. It is freed when the instance is collected.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class HighsLp {

  /** The status of an optimal solve. */
  public static final int OPTIMAL = RevisedDualSimplex.OPTIMAL;

  /** The status of a solve that proved the problem infeasible. */
  public static final int INFEASIBLE = RevisedDualSimplex.INFEASIBLE;

  /** The status of a solve that stopped at its limit of pivots, or for another reason. */
  public static final int LIMIT = RevisedDualSimplex.LIMIT;

  /** The status of a solve whose objective is unbounded. */
  public static final int UNBOUNDED = RevisedDualSimplex.UNBOUNDED;

  // HiGHS's constants (highs_c_api.h)
  private static final int MODEL_OPTIMAL = 7;
  private static final int MODEL_INFEASIBLE = 8;
  private static final int MODEL_UNBOUNDED_OR_INFEASIBLE = 9;
  private static final int MODEL_UNBOUNDED = 10;
  private static final int MODEL_EMPTY = 6;
  private static final int BASIS_BASIC = 1;
  private static final int ROW_WISE = 2;
  private static final int MINIMIZE = 1;
  private static final int STATUS_ERROR = -1;

  // a sparse operation against an update of a dense tableau entry, as RevisedDualSimplex counts
  private static final long OP_COST = 3;

  private static final Cleaner CLEANER = Cleaner.create();

  /** The native functions, bound when the class is first used. */
  private static final class Native {

    static final Throwable ERROR;
    static final String VERSION;
    static MethodHandle create;
    static MethodHandle destroy;
    static MethodHandle passLp;
    static MethodHandle setBool;
    static MethodHandle setInt;
    static MethodHandle setString;
    static MethodHandle run;
    static MethodHandle modelStatus;
    static MethodHandle solution;
    static MethodHandle getBasis;
    static MethodHandle setBasis;
    static MethodHandle dualRay;
    static MethodHandle basicVariables;
    static MethodHandle inverseRow;
    static MethodHandle colBounds;
    static MethodHandle rowBounds;
    static MethodHandle addRows;
    static MethodHandle deleteRows;
    static MethodHandle intInfo;
    static MethodHandle objective;
    static MemorySegment optOutput;
    static MemorySegment optPresolve;
    static MemorySegment optSolver;
    static MemorySegment optStrategy;
    static MemorySegment optThreads;
    static MemorySegment optLimit;
    static MemorySegment infoIterations;
    static MemorySegment valueOff;
    static MemorySegment valueSimplex;

    private Native() {}

    static {
      Throwable error = null;
      String version = null;
      try {
        Linker linker = Linker.nativeLinker();
        SymbolLookup lib = lookup();
        create = handle(linker, lib, "Highs_create", FunctionDescriptor.of(ADDRESS));
        destroy = handle(linker, lib, "Highs_destroy", FunctionDescriptor.ofVoid(ADDRESS));
        passLp =
            handle(
                linker,
                lib,
                "Highs_passLp",
                FunctionDescriptor.of(
                    JAVA_INT,
                    ADDRESS,
                    JAVA_INT,
                    JAVA_INT,
                    JAVA_INT,
                    JAVA_INT,
                    JAVA_INT,
                    JAVA_DOUBLE,
                    ADDRESS,
                    ADDRESS,
                    ADDRESS,
                    ADDRESS,
                    ADDRESS,
                    ADDRESS,
                    ADDRESS,
                    ADDRESS));
        setBool = handle(linker, lib, "Highs_setBoolOptionValue", fn(ADDRESS, ADDRESS, JAVA_INT));
        setInt = handle(linker, lib, "Highs_setIntOptionValue", fn(ADDRESS, ADDRESS, JAVA_INT));
        setString =
            handle(linker, lib, "Highs_setStringOptionValue", fn(ADDRESS, ADDRESS, ADDRESS));
        run = handle(linker, lib, "Highs_run", fn(ADDRESS));
        modelStatus = handle(linker, lib, "Highs_getModelStatus", fn(ADDRESS));
        solution =
            handle(
                linker, lib, "Highs_getSolution", fn(ADDRESS, ADDRESS, ADDRESS, ADDRESS, ADDRESS));
        getBasis = handle(linker, lib, "Highs_getBasis", fn(ADDRESS, ADDRESS, ADDRESS));
        setBasis = handle(linker, lib, "Highs_setBasis", fn(ADDRESS, ADDRESS, ADDRESS));
        dualRay = handle(linker, lib, "Highs_getDualRay", fn(ADDRESS, ADDRESS, ADDRESS));
        basicVariables = handle(linker, lib, "Highs_getBasicVariables", fn(ADDRESS, ADDRESS));
        inverseRow =
            handle(
                linker,
                lib,
                "Highs_getBasisInverseRow",
                fn(ADDRESS, JAVA_INT, ADDRESS, ADDRESS, ADDRESS));
        colBounds =
            handle(
                linker,
                lib,
                "Highs_changeColsBoundsBySet",
                fn(ADDRESS, JAVA_INT, ADDRESS, ADDRESS, ADDRESS));
        rowBounds =
            handle(
                linker,
                lib,
                "Highs_changeRowsBoundsBySet",
                fn(ADDRESS, JAVA_INT, ADDRESS, ADDRESS, ADDRESS));
        addRows =
            handle(
                linker,
                lib,
                "Highs_addRows",
                fn(ADDRESS, JAVA_INT, ADDRESS, ADDRESS, JAVA_INT, ADDRESS, ADDRESS, ADDRESS));
        deleteRows = handle(linker, lib, "Highs_deleteRowsBySet", fn(ADDRESS, JAVA_INT, ADDRESS));
        intInfo = handle(linker, lib, "Highs_getIntInfoValue", fn(ADDRESS, ADDRESS, ADDRESS));
        objective =
            handle(
                linker,
                lib,
                "Highs_getObjectiveValue",
                FunctionDescriptor.of(JAVA_DOUBLE, ADDRESS));
        MethodHandle sizeof =
            handle(
                linker, lib, "Highs_getSizeofHighsInt", FunctionDescriptor.of(JAVA_INT, ADDRESS));
        MethodHandle ver = handle(linker, lib, "Highs_version", FunctionDescriptor.of(ADDRESS));
        Arena g = Arena.global();
        optOutput = g.allocateFrom("output_flag");
        optPresolve = g.allocateFrom("presolve");
        optSolver = g.allocateFrom("solver");
        optStrategy = g.allocateFrom("simplex_strategy");
        optThreads = g.allocateFrom("threads");
        optLimit = g.allocateFrom("simplex_iteration_limit");
        infoIterations = g.allocateFrom("simplex_iteration_count");
        valueOff = g.allocateFrom("off");
        valueSimplex = g.allocateFrom("simplex");
        MemorySegment h = (MemorySegment) create.invokeExact();
        int size = (int) sizeof.invokeExact(h);
        destroy.invokeExact(h);
        if (size != Integer.BYTES) {
          throw new UnsupportedOperationException(
              "HiGHS built with " + (8 * size) + "-bit HighsInt; 32-bit expected");
        }
        version = ((MemorySegment) ver.invokeExact()).reinterpret(64).getString(0);
      } catch (Throwable t) {
        error = t;
      }
      ERROR = error;
      VERSION = version;
    }

    private static FunctionDescriptor fn(java.lang.foreign.MemoryLayout... args) {
      return FunctionDescriptor.of(JAVA_INT, args);
    }

    private static SymbolLookup lookup() {
      String path = System.getProperty("org.jacop.jalp.highs");
      if (path == null || path.isEmpty()) {
        path = System.getenv("JACOP_HIGHS");
      }
      if (path != null && !path.isEmpty()) {
        Path p = Path.of(path);
        if (Files.isDirectory(p)) {
          p = p.resolve(System.mapLibraryName("highs"));
        }
        return SymbolLookup.libraryLookup(p, Arena.global());
      }
      return SymbolLookup.libraryLookup(System.mapLibraryName("highs"), Arena.global());
    }

    private static MethodHandle handle(
        Linker linker, SymbolLookup lib, String name, FunctionDescriptor d) {
      MemorySegment f =
          lib.find(name).orElseThrow(() -> new UnsatisfiedLinkError("no symbol " + name));
      return linker.downcallHandle(f, d);
    }
  }

  /**
   * Returns whether the HiGHS library was found and bound.
   *
   * @return true when instances can be made
   */
  public static boolean available() {
    return Native.ERROR == null;
  }

  /**
   * Returns why the HiGHS library could not be bound, or null when it was.
   *
   * @return the error
   */
  public static Throwable loadError() {
    return Native.ERROR;
  }

  /**
   * Returns the version string of the HiGHS library, or null when it is not available.
   *
   * @return the version
   */
  public static String version() {
    return Native.VERSION;
  }

  // the HiGHS object, freed by the cleaner
  private final MemorySegment highs;
  private final Arena arena = Arena.ofAuto();

  private final int n;
  private int m;
  // the model as given, for copies and for the scaling of rows of the basis inverse
  private int[][] rowIdx;
  private double[][] rowVal;
  private double[] rowLo;
  private double[] rowHi;
  private final double[] cost;
  private final double[] colLo;
  private final double[] colHi;

  // columns whose bounds changed since the last solve
  private int[] changed;
  private int changedCount;
  private final boolean[] isChanged;
  private int[] changedRows = new int[0];
  private int changedRowCount;
  private boolean[] isChangedRow;

  private int limitSet = -1;
  private long totalPivots;
  private int status = LIMIT;

  // the answers of the last solve, fetched when first asked for
  private boolean solutionValid;
  private double[] colValue;
  private double[] rowValue;
  private double[] rowDual;
  private boolean basisValid;
  private int[] basic;
  private int[] rowOf;

  // native buffers, grown when needed
  private MemorySegment dbuf1 = MemorySegment.NULL;
  private MemorySegment dbuf2 = MemorySegment.NULL;
  private MemorySegment dbuf3 = MemorySegment.NULL;
  private MemorySegment dbuf4 = MemorySegment.NULL;
  private MemorySegment ibuf1 = MemorySegment.NULL;
  private MemorySegment ibuf2 = MemorySegment.NULL;
  private final MemorySegment one;

  /**
   * Creates the problem. The columns are bounded by [0, +inf) until {@link #setBounds} says
   * otherwise, as in {@link RevisedDualSimplex}.
   *
   * @param columns the columns of each row
   * @param weights the weights of each row, matching its columns
   * @param rowLo the lower bounds of the rows, or negative infinity
   * @param rowHi the upper bounds of the rows, or positive infinity
   * @param cost the objective over the n columns, minimized
   * @throws IllegalStateException when the HiGHS library is not available
   */
  public HighsLp(
      int[][] columns, double[][] weights, double[] rowLo, double[] rowHi, double[] cost) {
    this(
        columns,
        weights,
        rowLo,
        rowHi,
        cost,
        new double[cost.length],
        filled(cost.length, Double.POSITIVE_INFINITY));
  }

  private HighsLp(
      int[][] columns,
      double[][] weights,
      double[] rowLo,
      double[] rowHi,
      double[] cost,
      double[] colLo,
      double[] colHi) {
    if (!available()) {
      throw new IllegalStateException("HiGHS is not available", Native.ERROR);
    }
    n = cost.length;
    m = columns.length;
    rowIdx = columns.clone();
    rowVal = weights.clone();
    this.rowLo = rowLo.clone();
    this.rowHi = rowHi.clone();
    this.cost = cost.clone();
    this.colLo = colLo.clone();
    this.colHi = colHi.clone();
    changed = new int[n];
    isChanged = new boolean[n];
    isChangedRow = new boolean[m];
    one = arena.allocate(JAVA_INT);
    try {
      highs = (MemorySegment) Native.create.invokeExact();
      MemorySegment h = highs;
      CLEANER.register(this, () -> free(h));
      int ok = (int) Native.setBool.invokeExact(highs, Native.optOutput, 0);
      ok |= (int) Native.setString.invokeExact(highs, Native.optPresolve, Native.valueOff);
      ok |= (int) Native.setString.invokeExact(highs, Native.optSolver, Native.valueSimplex);
      ok |= (int) Native.setInt.invokeExact(highs, Native.optStrategy, 1);
      ok |= (int) Native.setInt.invokeExact(highs, Native.optThreads, 1);
      check(ok, "options");
      pass();
    } catch (RuntimeException e) {
      throw e;
    } catch (Throwable t) {
      throw new IllegalStateException(t);
    }
  }

  // whether the rows have no nonzero
  private boolean unconstrained() {
    for (int[] r : rowIdx) {
      if (r.length > 0) {
        return false;
      }
    }
    return true;
  }

  private static double[] filled(int k, double v) {
    double[] a = new double[k];
    Arrays.fill(a, v);
    return a;
  }

  private static void free(MemorySegment h) {
    try {
      Native.destroy.invokeExact(h);
    } catch (Throwable t) {
      // nothing to do: the object is gone either way
    }
  }

  private static void check(int status, String what) {
    if (status == STATUS_ERROR) {
      throw new IllegalStateException("HiGHS " + what + " failed");
    }
  }

  // hands the model as it is now to HiGHS
  private void pass() throws Throwable {
    int nz = 0;
    for (int[] r : rowIdx) {
      nz += r.length;
    }
    MemorySegment start = arena.allocate(JAVA_INT, m + 1L);
    MemorySegment index = arena.allocate(JAVA_INT, Math.max(1, nz));
    MemorySegment value = arena.allocate(JAVA_DOUBLE, Math.max(1, nz));
    int k = 0;
    for (int i = 0; i < m; i++) {
      start.setAtIndex(JAVA_INT, i, k);
      for (int q = 0; q < rowIdx[i].length; q++) {
        index.setAtIndex(JAVA_INT, k, rowIdx[i][q]);
        value.setAtIndex(JAVA_DOUBLE, k++, rowVal[i][q]);
      }
    }
    start.setAtIndex(JAVA_INT, m, k);
    int ok =
        (int)
            Native.passLp.invokeExact(
                highs,
                n,
                m,
                nz,
                ROW_WISE,
                MINIMIZE,
                0.0,
                doubles(cost),
                doubles(colLo),
                doubles(colHi),
                doubles(rowLo),
                doubles(rowHi),
                start,
                index,
                value);
    check(ok, "passLp");
  }

  private MemorySegment doubles(double[] a) {
    return a.length == 0 ? arena.allocate(JAVA_DOUBLE) : arena.allocateFrom(JAVA_DOUBLE, a);
  }

  private MemorySegment grow(MemorySegment s, long count, java.lang.foreign.ValueLayout l) {
    long bytes = Math.max(1, count) * l.byteSize();
    return s.byteSize() >= bytes ? s : arena.allocate(bytes * 3 / 2, 8);
  }

  /**
   * Returns the number of rows.
   *
   * @return the rows
   */
  public int rows() {
    return m;
  }

  /**
   * Returns the number of structural columns.
   *
   * @return the columns
   */
  public int columns() {
    return n;
  }

  /**
   * Returns the simplex iterations HiGHS made so far.
   *
   * @return the pivots
   */
  public long pivots() {
    return totalPivots;
  }

  /**
   * Returns an estimate of the work of one pivot, in updates of a dense tableau entry, counted as
   * {@link RevisedDualSimplex#pivotWork()} counts its base.
   *
   * @return the work of a pivot
   */
  public long pivotWork() {
    return OP_COST * (2L * m + n);
  }

  /**
   * Returns an estimate of the work done so far.
   *
   * @return the work
   */
  public long work() {
    return totalPivots * pivotWork();
  }

  /**
   * Sets the bounds of a column, structural ({@code j < n}) or slack ({@code n + i}).
   *
   * @param j the column
   * @param min its lower bound, or negative infinity
   * @param max its upper bound, or positive infinity
   */
  public void setBounds(int j, double min, double max) {
    if (j < n) {
      if (colLo[j] != min || colHi[j] != max) {
        colLo[j] = min;
        colHi[j] = max;
        if (!isChanged[j]) {
          isChanged[j] = true;
          changed[changedCount++] = j;
        }
      }
    } else {
      int i = j - n;
      if (rowLo[i] != min || rowHi[i] != max) {
        rowLo[i] = min;
        rowHi[i] = max;
        if (!isChangedRow[i]) {
          isChangedRow[i] = true;
          if (changedRowCount == changedRows.length) {
            changedRows = Arrays.copyOf(changedRows, Math.max(4, 2 * changedRowCount));
          }
          changedRows[changedRowCount++] = i;
        }
      }
    }
  }

  // hands the bounds that changed to HiGHS
  private void pushBounds() throws Throwable {
    if (changedCount > 0) {
      Arrays.sort(changed, 0, changedCount);
      ibuf1 = grow(ibuf1, changedCount, JAVA_INT);
      dbuf1 = grow(dbuf1, changedCount, JAVA_DOUBLE);
      dbuf2 = grow(dbuf2, changedCount, JAVA_DOUBLE);
      for (int k = 0; k < changedCount; k++) {
        int j = changed[k];
        ibuf1.setAtIndex(JAVA_INT, k, j);
        dbuf1.setAtIndex(JAVA_DOUBLE, k, colLo[j]);
        dbuf2.setAtIndex(JAVA_DOUBLE, k, colHi[j]);
        isChanged[j] = false;
      }
      int ok = (int) Native.colBounds.invokeExact(highs, changedCount, ibuf1, dbuf1, dbuf2);
      check(ok, "changeColsBoundsBySet");
      changedCount = 0;
    }
    if (changedRowCount > 0) {
      Arrays.sort(changedRows, 0, changedRowCount);
      ibuf1 = grow(ibuf1, changedRowCount, JAVA_INT);
      dbuf1 = grow(dbuf1, changedRowCount, JAVA_DOUBLE);
      dbuf2 = grow(dbuf2, changedRowCount, JAVA_DOUBLE);
      for (int k = 0; k < changedRowCount; k++) {
        int i = changedRows[k];
        ibuf1.setAtIndex(JAVA_INT, k, i);
        dbuf1.setAtIndex(JAVA_DOUBLE, k, rowLo[i]);
        dbuf2.setAtIndex(JAVA_DOUBLE, k, rowHi[i]);
        isChangedRow[i] = false;
      }
      int ok = (int) Native.rowBounds.invokeExact(highs, changedRowCount, ibuf1, dbuf1, dbuf2);
      check(ok, "changeRowsBoundsBySet");
      changedRowCount = 0;
    }
  }

  /**
   * Solves the problem from the current basis.
   *
   * @param limit the most pivots to make
   * @return {@link #OPTIMAL}, {@link #INFEASIBLE}, {@link #UNBOUNDED} or {@link #LIMIT}
   */
  public int solve(int limit) {
    solutionValid = false;
    basisValid = false;
    try {
      pushBounds();
      if (limit != limitSet) {
        check((int) Native.setInt.invokeExact(highs, Native.optLimit, limit), "iteration limit");
        limitSet = limit;
      }
      int ok = (int) Native.run.invokeExact(highs);
      int iterations = 0;
      if ((int) Native.intInfo.invokeExact(highs, Native.infoIterations, one) != STATUS_ERROR) {
        iterations = one.get(JAVA_INT, 0);
      }
      totalPivots += Math.max(0, iterations);
      if (ok == STATUS_ERROR) {
        return status = LIMIT;
      }
      int model = (int) Native.modelStatus.invokeExact(highs);
      status =
          switch (model) {
            case MODEL_OPTIMAL, MODEL_EMPTY -> OPTIMAL;
            case MODEL_INFEASIBLE -> INFEASIBLE;
            case MODEL_UNBOUNDED, MODEL_UNBOUNDED_OR_INFEASIBLE -> UNBOUNDED;
            default -> LIMIT;
          };
      return status;
    } catch (RuntimeException e) {
      throw e;
    } catch (Throwable t) {
      throw new IllegalStateException(t);
    }
  }

  private void fetchSolution() {
    if (solutionValid) {
      return;
    }
    try {
      dbuf1 = grow(dbuf1, n, JAVA_DOUBLE);
      dbuf2 = grow(dbuf2, n, JAVA_DOUBLE);
      dbuf3 = grow(dbuf3, m, JAVA_DOUBLE);
      dbuf4 = grow(dbuf4, m, JAVA_DOUBLE);
      check((int) Native.solution.invokeExact(highs, dbuf1, dbuf2, dbuf3, dbuf4), "getSolution");
      colValue = dbuf1.asSlice(0, n * JAVA_DOUBLE.byteSize()).toArray(JAVA_DOUBLE);
      rowValue = dbuf3.asSlice(0, m * JAVA_DOUBLE.byteSize()).toArray(JAVA_DOUBLE);
      rowDual = dbuf4.asSlice(0, m * JAVA_DOUBLE.byteSize()).toArray(JAVA_DOUBLE);
      solutionValid = true;
    } catch (RuntimeException e) {
      throw e;
    } catch (Throwable t) {
      throw new IllegalStateException(t);
    }
  }

  private void fetchBasis() {
    if (basisValid) {
      return;
    }
    try {
      if (unconstrained()) {
        // HiGHS solves an LP without nonzeros with no basis matrix (and getBasicVariables would
        // read one): the basis is the slack of each row
        basic = new int[m];
        for (int r = 0; r < m; r++) {
          basic[r] = -1 - r;
        }
      } else {
        ibuf2 = grow(ibuf2, m, JAVA_INT);
        check((int) Native.basicVariables.invokeExact(highs, ibuf2), "getBasicVariables");
        basic = ibuf2.asSlice(0, m * JAVA_INT.byteSize()).toArray(JAVA_INT);
      }
      rowOf = new int[n + m];
      Arrays.fill(rowOf, -1);
      for (int r = 0; r < m; r++) {
        int v = basic[r];
        basic[r] = v >= 0 ? v : n + (-1 - v);
        rowOf[basic[r]] = r;
      }
      basisValid = true;
    } catch (RuntimeException e) {
      throw e;
    } catch (Throwable t) {
      throw new IllegalStateException(t);
    }
  }

  /**
   * Returns a dual ray over the rows that proves the problem infeasible, after a solve returned
   * {@link #INFEASIBLE}, or zeros when HiGHS has none.
   *
   * @return the multipliers of the rows
   */
  public double[] farkas() {
    try {
      dbuf3 = grow(dbuf3, m, JAVA_DOUBLE);
      check((int) Native.dualRay.invokeExact(highs, one, dbuf3), "getDualRay");
      if (one.get(JAVA_INT, 0) == 0) {
        return rowRay();
      }
      return dbuf3.asSlice(0, m * JAVA_DOUBLE.byteSize()).toArray(JAVA_DOUBLE);
    } catch (RuntimeException e) {
      throw e;
    } catch (Throwable t) {
      throw new IllegalStateException(t);
    }
  }

  // without a ray from HiGHS (it finds some infeasibilities before the simplex, such as an empty
  // row that excludes 0): a single row whose activity cannot reach its bounds, or zeros
  private double[] rowRay() {
    double[] y = new double[m];
    for (int i = 0; i < m; i++) {
      double min = 0;
      double max = 0;
      for (int q = 0; q < rowIdx[i].length; q++) {
        int j = rowIdx[i][q];
        double a = rowVal[i][q];
        min += a > 0 ? a * colLo[j] : a * colHi[j];
        max += a > 0 ? a * colHi[j] : a * colLo[j];
      }
      if (min > rowHi[i] || max < rowLo[i]) {
        y[i] = 1;
        return y;
      }
    }
    return y;
  }

  /**
   * Returns a row of the basis inverse, scaled so that the basic column of the row has coefficient
   * one in the combination {@code y (A x - s)}, as {@link RevisedDualSimplex#inverseRow} does.
   *
   * @param r the row of the basis
   * @return the multipliers of the rows
   */
  public double[] inverseRow(int r) {
    fetchBasis();
    if (unconstrained()) {
      double[] y = new double[m];
      y[r] = -1; // the slack of row r, with coefficient -1 in A x - s
      return y;
    }
    try {
      dbuf3 = grow(dbuf3, m, JAVA_DOUBLE);
      ibuf1 = grow(ibuf1, m, JAVA_INT);
      check((int) Native.inverseRow.invokeExact(highs, r, dbuf3, one, ibuf1), "getBasisInverseRow");
      double[] y = dbuf3.asSlice(0, m * JAVA_DOUBLE.byteSize()).toArray(JAVA_DOUBLE);
      int p = basic[r];
      double coefficient = 0;
      if (p >= n) {
        coefficient = -y[p - n];
      } else {
        for (int i = 0; i < m; i++) {
          if (y[i] != 0) {
            int[] c = rowIdx[i];
            for (int q = 0; q < c.length; q++) {
              if (c[q] == p) {
                coefficient += y[i] * rowVal[i][q];
              }
            }
          }
        }
      }
      if (coefficient != 0 && coefficient != 1) {
        for (int i = 0; i < m; i++) {
          y[i] /= coefficient;
        }
      }
      return y;
    } catch (RuntimeException e) {
      throw e;
    } catch (Throwable t) {
      throw new IllegalStateException(t);
    }
  }

  /**
   * Returns the duals of the rows at the last solution, with the signs of {@link
   * RevisedDualSimplex#duals()}.
   *
   * @return the duals by row
   */
  public double[] duals() {
    fetchSolution();
    return rowDual.clone();
  }

  /**
   * Returns the objective of the current solution.
   *
   * @return the objective
   */
  public double objective() {
    try {
      return (double) Native.objective.invokeExact(highs);
    } catch (Throwable t) {
      throw new IllegalStateException(t);
    }
  }

  /**
   * Returns the value of a column, structural ({@code j < n}) or slack ({@code n + i}).
   *
   * @param j the column
   * @return its value
   */
  public double value(int j) {
    fetchSolution();
    return j < n ? colValue[j] : rowValue[j - n];
  }

  /**
   * Returns the row of the basis a column is basic in, or -1.
   *
   * @param j the column
   * @return its row, or -1 when it is nonbasic
   */
  public int basicRow(int j) {
    fetchBasis();
    return rowOf[j];
  }

  /**
   * Adds rows, with basic slacks.
   *
   * @param columns the columns of each row
   * @param weights the weights of each row
   * @param lo the lower bounds of the rows
   * @param hi the upper bounds of the rows
   */
  public void addRows(int[][] columns, double[][] weights, double[] lo, double[] hi) {
    int k = columns.length;
    if (k == 0) {
      return;
    }
    try {
      pushBounds();
      int nz = 0;
      for (int[] c : columns) {
        nz += c.length;
      }
      MemorySegment start = arena.allocate(JAVA_INT, k);
      MemorySegment index = arena.allocate(JAVA_INT, Math.max(1, nz));
      MemorySegment value = arena.allocate(JAVA_DOUBLE, Math.max(1, nz));
      int e = 0;
      for (int q = 0; q < k; q++) {
        start.setAtIndex(JAVA_INT, q, e);
        for (int t = 0; t < columns[q].length; t++) {
          index.setAtIndex(JAVA_INT, e, columns[q][t]);
          value.setAtIndex(JAVA_DOUBLE, e++, weights[q][t]);
        }
      }
      int ok =
          (int)
              Native.addRows.invokeExact(
                  highs, k, doubles(lo), doubles(hi), nz, start, index, value);
      check(ok, "addRows");
    } catch (RuntimeException e) {
      throw e;
    } catch (Throwable t) {
      throw new IllegalStateException(t);
    }
    rowIdx = Arrays.copyOf(rowIdx, m + k);
    rowVal = Arrays.copyOf(rowVal, m + k);
    rowLo = Arrays.copyOf(rowLo, m + k);
    rowHi = Arrays.copyOf(rowHi, m + k);
    for (int q = 0; q < k; q++) {
      rowIdx[m + q] = columns[q].clone();
      rowVal[m + q] = weights[q].clone();
      rowLo[m + q] = lo[q];
      rowHi[m + q] = hi[q];
    }
    m += k;
    isChangedRow = Arrays.copyOf(isChangedRow, m);
    solutionValid = false;
    basisValid = false;
  }

  /**
   * Removes rows whose slacks are basic; a row whose slack is nonbasic is kept.
   *
   * @param rows the rows to remove
   * @return the old row of each new row, or null when no row was removed
   */
  public int[] removeRows(int[] rows) {
    int[] status = rowStatus();
    boolean[] gone = new boolean[m];
    int count = 0;
    for (int i : rows) {
      if (i >= 0 && i < m && !gone[i] && status[i] == BASIS_BASIC) {
        gone[i] = true;
        count++;
      }
    }
    if (count == 0) {
      return null;
    }
    try {
      pushBounds();
      MemorySegment set = arena.allocate(JAVA_INT, count);
      int k = 0;
      for (int i = 0; i < m; i++) {
        if (gone[i]) {
          set.setAtIndex(JAVA_INT, k++, i);
        }
      }
      check((int) Native.deleteRows.invokeExact(highs, count, set), "deleteRowsBySet");
    } catch (RuntimeException e) {
      throw e;
    } catch (Throwable t) {
      throw new IllegalStateException(t);
    }
    int[] old = new int[m - count];
    int k = 0;
    for (int i = 0; i < m; i++) {
      if (!gone[i]) {
        rowIdx[k] = rowIdx[i];
        rowVal[k] = rowVal[i];
        rowLo[k] = rowLo[i];
        rowHi[k] = rowHi[i];
        old[k++] = i;
      }
    }
    m = k;
    rowIdx = Arrays.copyOf(rowIdx, m);
    rowVal = Arrays.copyOf(rowVal, m);
    rowLo = Arrays.copyOf(rowLo, m);
    rowHi = Arrays.copyOf(rowHi, m);
    isChangedRow = new boolean[m];
    solutionValid = false;
    basisValid = false;
    return old;
  }

  // the basis status of the rows, and of the columns in colStatus when asked for
  private int[] rowStatus() {
    return basis()[1];
  }

  private int[][] basis() {
    try {
      MemorySegment cs = arena.allocate(JAVA_INT, Math.max(1, n));
      MemorySegment rs = arena.allocate(JAVA_INT, Math.max(1, m));
      check((int) Native.getBasis.invokeExact(highs, cs, rs), "getBasis");
      return new int[][] {
        cs.asSlice(0, n * JAVA_INT.byteSize()).toArray(JAVA_INT),
        rs.asSlice(0, m * JAVA_INT.byteSize()).toArray(JAVA_INT)
      };
    } catch (RuntimeException e) {
      throw e;
    } catch (Throwable t) {
      throw new IllegalStateException(t);
    }
  }

  /**
   * Returns a deep copy with the same basis, a new HiGHS object that factorizes it when it is first
   * solved.
   *
   * @return the copy
   */
  public HighsLp copy() {
    int[][] b = basis();
    HighsLp c = new HighsLp(rowIdx, rowVal, rowLo, rowHi, cost, colLo, colHi);
    // bounds not yet handed to this HiGHS object are in colLo/colHi, so the copy has them
    c.totalPivots = totalPivots;
    try {
      MemorySegment cs = c.arena.allocateFrom(JAVA_INT, b[0].length == 0 ? new int[1] : b[0]);
      MemorySegment rs = c.arena.allocateFrom(JAVA_INT, b[1].length == 0 ? new int[1] : b[1]);
      int ok = (int) Native.setBasis.invokeExact(c.highs, cs, rs);
      check(ok, "setBasis");
    } catch (RuntimeException e) {
      throw e;
    } catch (Throwable t) {
      throw new IllegalStateException(t);
    }
    return c;
  }
}
