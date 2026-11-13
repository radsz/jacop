/*
 * CardinalityMatrix.java
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
package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Cardinality matrix (colored_matrix of the Global Constraint Catalog): in a matrix x of n rows and
 * m columns, value values[k] occurs rowCount[r][k] times in row r and colCount[c][k] times in
 * column c. Values that are not listed are not counted. Rostering models have it: the rows are
 * persons, the columns days and the values shifts, with a count of each shift per person and per
 * day.
 *
 * <p>It is the cardinality matrix constraint of J.-C. Régin and C. Gomes, "The cardinality matrix
 * constraint", CP 2004, LNCS 3258, 572-587. For each value, the cells that hold it form a 0/1
 * matrix whose row and column sums are the counts of that value, and this constraint propagates
 * each of those matrices with the flow network of the symmetric cardinality constraint ({@link
 * SymmetricGCC}): a value is removed from a cell when the cell is 0 in every matrix within the
 * bounds of the counts, a cell is fixed to a value when it is 1 in all of them, and the counts get
 * the least and largest flows on their arcs. One flow per value links the rows and the columns,
 * which separate cardinality constraints on rows and on columns do not. Régin and Gomes also post a
 * global cardinality constraint on every row and every column, which link the values of a row; in
 * JaCoP those are separate constraints (GCC, CountValues), and models usually have them already.
 *
 * <p>The computations repeat until no domain changes, since fixing a cell to one value removes the
 * others.
 *
 * <p>For lazy clause generation an atom is explained by a cut of the network of one value, built
 * over the domains before the atom with the atom negated (G. Downing, T. Feydy and P. J. Stuckey,
 * "Explaining flow-based propagation", CPAIOR 2012; see {@link FlowReason}): an atom of a count is
 * explained by the network of its value, an atom of a cell by the first network that its negation
 * makes infeasible.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class CardinalityMatrix extends Constraint
    implements SatisfiedPresent, Copyable<CardinalityMatrix>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The matrix. */
  final IntVar[][] x;

  /** The counted values. */
  final int[] values;

  /** rowCount[r][k] is the number of occurrences of values[k] in row r. */
  final IntVar[][] rowCount;

  /** colCount[c][k] is the number of occurrences of values[k] in column c. */
  final IntVar[][] colCount;

  private final int n;
  private final int m;
  private final DegreeFlow network = new DegreeFlow();
  private final int[] cells;
  private final int[] rowMin;
  private final int[] rowMax;
  private final int[] colMin;
  private final int[] colMax;
  private final CardinalityExplanation.Budget budget = new CardinalityExplanation.Budget();

  /**
   * It constructs a cardinality matrix constraint.
   *
   * @param x the matrix, n rows of m variables
   * @param values the counted values, distinct
   * @param rowCount for every row, the count of each value
   * @param colCount for every column, the count of each value
   */
  public CardinalityMatrix(IntVar[][] x, int[] values, IntVar[][] rowCount, IntVar[][] colCount) {
    checkInputForNullness(new String[] {"x", "rowCount", "colCount"}, x, rowCount, colCount);
    checkInputForNullness("values", values);
    this.n = x.length;
    this.m = colCount.length;
    int k = values.length;
    if (Arrays.stream(values).distinct().count() != k) {
      throw new IllegalArgumentException("CardinalityMatrix: values must be distinct");
    }
    if (rowCount.length != n) {
      throw new IllegalArgumentException("CardinalityMatrix: rowCount needs one array per row");
    }
    this.x = new IntVar[n][];
    for (int r = 0; r < n; r++) {
      checkInputForNullness("x", x[r]);
      checkInputForNullness("rowCount", rowCount[r]);
      if (x[r].length != m || rowCount[r].length != k) {
        throw new IllegalArgumentException(
            "CardinalityMatrix: every row needs m variables and one count per value");
      }
      this.x[r] = Arrays.copyOf(x[r], m);
    }
    for (IntVar[] counts : colCount) {
      checkInputForNullness("colCount", counts);
      if (counts.length != k) {
        throw new IllegalArgumentException("CardinalityMatrix: one count per value per column");
      }
    }
    this.numberId = idNumber.incrementAndGet();
    this.values = Arrays.copyOf(values, k);
    this.rowCount = new IntVar[n][];
    for (int r = 0; r < n; r++) {
      this.rowCount[r] = Arrays.copyOf(rowCount[r], k);
    }
    this.colCount = new IntVar[m][];
    for (int c = 0; c < m; c++) {
      this.colCount[c] = Arrays.copyOf(colCount[c], k);
    }
    this.cells = new int[n * m];
    this.rowMin = new int[n];
    this.rowMax = new int[n];
    this.colMin = new int[m];
    this.colMax = new int[m];
    this.queueIndex = 3;
    List<IntVar> scope = new ArrayList<>();
    for (IntVar[] row : this.x) {
      scope.addAll(Arrays.asList(row));
    }
    for (IntVar[] row : this.rowCount) {
      scope.addAll(Arrays.asList(row));
    }
    for (IntVar[] row : this.colCount) {
      scope.addAll(Arrays.asList(row));
    }
    setScope(scope.toArray(new IntVar[0]));
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void consistency(Store store) {
    boolean changed = true;
    while (changed) {
      changed = false;
      for (int k = 0; k < values.length; k++) {
        changed |= propagate(store, k);
      }
    }
  }

  // one value's 0/1 matrix; true if a domain changed in a way that may concern other values
  private boolean propagate(Store store, int k) {
    int value = values[k];
    boolean changed = false;
    for (int r = 0; r < n; r++) {
      for (int c = 0; c < m; c++) {
        IntDomain d = x[r][c].domain;
        cells[r * m + c] =
            !d.contains(value) ? DegreeFlow.ZERO : d.singleton() ? DegreeFlow.ONE : DegreeFlow.FREE;
      }
      IntVar count = rowCount[r][k];
      count.domain.in(store.level, count, 0, m);
      rowMin[r] = count.min();
      rowMax[r] = count.max();
    }
    for (int c = 0; c < m; c++) {
      IntVar count = colCount[c][k];
      count.domain.in(store.level, count, 0, n);
      colMin[c] = count.min();
      colMax[c] = count.max();
    }
    if (!network.solve(n, m, cells, rowMin, rowMax, colMin, colMax, true)) {
      throw Store.failException;
    }
    for (int i = 0; i < n * m; i++) {
      if (cells[i] == DegreeFlow.FREE && network.cell[i] != DegreeFlow.FREE) {
        IntVar v = x[i / m][i % m];
        if (network.cell[i] == DegreeFlow.ONE) {
          v.domain.in(store.level, v, value, value);
        } else {
          v.domain.inComplement(store.level, v, value);
        }
        changed = true;
      }
    }
    for (int r = 0; r < n; r++) {
      changed |= SymmetricGCC.narrow(store, rowCount[r][k], network.rowLo[r], network.rowUp[r]);
    }
    for (int c = 0; c < m; c++) {
      changed |= SymmetricGCC.narrow(store, colCount[c][k], network.colLo[c], network.colUp[c]);
    }
    return changed;
  }

  @Override
  public boolean satisfied() {
    for (IntVar[] row : x) {
      for (IntVar v : row) {
        if (!v.singleton()) {
          return false;
        }
      }
    }
    for (int k = 0; k < values.length; k++) {
      for (int r = 0; r < n; r++) {
        int count = 0;
        for (int c = 0; c < m; c++) {
          count += x[r][c].value() == values[k] ? 1 : 0;
        }
        if (!rowCount[r][k].singleton(count)) {
          return false;
        }
      }
      for (int c = 0; c < m; c++) {
        int count = 0;
        for (int r = 0; r < n; r++) {
          count += x[r][c].value() == values[k] ? 1 : 0;
        }
        if (!colCount[c][k].singleton(count)) {
          return false;
        }
      }
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : CardinalityMatrix([");
    appendMatrix(result, x);
    result.append("], ").append(Arrays.toString(values)).append(", [");
    appendMatrix(result, rowCount);
    result.append("], [");
    appendMatrix(result, colCount);
    result.append("])");
    return result.toString();
  }

  private static void appendMatrix(StringBuilder result, IntVar[][] matrix) {
    for (int r = 0; r < matrix.length; r++) {
      result.append(r == 0 ? "[" : ", [");
      appendArrayToString(result, matrix[r]);
      result.append(']');
    }
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar z = trail.variable(entry);
    FlowReason reason = FlowReason.ofEntry(trail, entry, out);
    for (int k = 0; k < values.length; k++) {
      for (int r = 0; r < n; r++) {
        if (rowCount[r][k] == z) {
          return explain(reason, k);
        }
      }
      for (int c = 0; c < m; c++) {
        if (colCount[c][k] == z) {
          return explain(reason, k);
        }
      }
    }
    if (!isCell(z)) {
      return false;
    }
    // x != a is most likely the network of a, which its negation x = a fills
    int first = -1;
    if (trail.kind(entry) == AtomicTrail.NE) {
      for (int k = 0; k < values.length; k++) {
        first = values[k] == trail.value(entry) ? k : first;
      }
    }
    if (first >= 0 && explain(reason, first)) {
      return true;
    }
    for (int k = 0; k < values.length; k++) {
      reason.clear();
      if (k != first && explain(reason, k)) {
        return true;
      }
    }
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    FlowReason reason = new FlowReason(trail, trail.size(), out);
    for (int k = 0; k < values.length; k++) {
      reason.clear();
      if (explain(reason, k)) {
        return true;
      }
    }
    return false;
  }

  @Override
  public boolean checksReasons() {
    return true;
  }

  private boolean isCell(IntVar z) {
    for (IntVar[] row : x) {
      for (IntVar v : row) {
        if (v == z) {
          return true;
        }
      }
    }
    return false;
  }

  // the network of value k over the domains before the reason's position, with its atom negated
  private boolean explain(FlowReason reason, int k) {
    long started = System.nanoTime();
    if (!budget.allows(started)) {
      return false;
    }
    try {
      int value = values[k];
      int[] status = new int[n * m];
      for (int i = 0; i < n * m; i++) {
        IntVar v = x[i / m][i % m];
        if (!reason.contains(v, value)) {
          status[i] = DegreeFlow.ZERO;
        } else {
          boolean fixed = reason.min(v) == value && reason.max(v) == value;
          status[i] = fixed ? DegreeFlow.ONE : DegreeFlow.FREE;
        }
      }
      IntVar[] rows = new IntVar[n];
      int[] rLo = new int[n];
      int[] rUp = new int[n];
      for (int r = 0; r < n; r++) {
        rows[r] = rowCount[r][k];
        rLo[r] = Math.max(reason.min(rows[r]), 0);
        rUp[r] = Math.min(reason.max(rows[r]), m);
      }
      IntVar[] cols = new IntVar[m];
      int[] cLo = new int[m];
      int[] cUp = new int[m];
      for (int c = 0; c < m; c++) {
        cols[c] = colCount[c][k];
        cLo[c] = Math.max(reason.min(cols[c]), 0);
        cUp[c] = Math.min(reason.max(cols[c]), n);
      }
      DegreeFlow.CellReason cells =
          new DegreeFlow.CellReason() {
            @Override
            public void zero(int i) {
              reason.exclude(x[i / m][i % m], value);
            }

            @Override
            public void one(int i) {
              reason.needLower(x[i / m][i % m], value);
              reason.needUpper(x[i / m][i % m], value);
            }
          };
      return network.explain(n, m, status, rLo, rUp, cLo, cUp, rows, cols, reason, cells)
          && reason.finish();
    } finally {
      budget.spend(started);
    }
  }

  @Override
  public CardinalityMatrix copy(VarMap map) {
    return new CardinalityMatrix(
        copyOf(map, x), values, copyOf(map, rowCount), copyOf(map, colCount));
  }

  private static IntVar[][] copyOf(VarMap map, IntVar[][] matrix) {
    IntVar[][] copied = new IntVar[matrix.length][];
    for (int r = 0; r < matrix.length; r++) {
      copied[r] = map.get(matrix[r]);
    }
    return copied;
  }
}
