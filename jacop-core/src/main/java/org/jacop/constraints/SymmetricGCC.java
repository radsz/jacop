/*
 * SymmetricGCC.java
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
 * Symmetric cardinality (symmetric_gcc of the Global Constraint Catalog): a many-to-many assignment
 * between n items and m resources given as a 0/1 matrix, x[i][j] = 1 when item i uses resource j,
 * where item i uses rowCount[i] resources and resource j is used by colCount[j] items.
 *
 * <p>The constraint is the symmetric cardinality constraint of W. Kocjan and P. Kreuger, "Filtering
 * methods for symmetric cardinality constraint", CPAIOR 2004, LNCS 3011, 200-208, written over the
 * 0/1 matrix of the assignment instead of set variables. It is propagated with their flow network:
 * a source, a node per item, a node per resource and a sink, with the row sums on the arcs from the
 * source, a 0..1 arc for every free cell and the column sums on the arcs to the sink. Matrices
 * within the bounds and feasible flows correspond one to one, so a cell is fixed exactly when its
 * arc has the same flow in all feasible flows, which the strongly connected components of the
 * residual graph tell (J.-C. Régin, "Generalized arc consistency for global cardinality
 * constraint", AAAI 1996). The matrix is thus domain consistent, and the counters are bounds
 * consistent: their new bounds are the least and largest flows on their arcs.
 *
 * <p>For lazy clause generation an atom is explained by a cut of the same network built over the
 * domains before it, with the atom negated: the bounds of the counters and the cells fixed to 0 or
 * 1 that keep a set of nodes from passing the flow it must (G. Downing, T. Feydy and P. J. Stuckey,
 * "Explaining flow-based propagation", CPAIOR 2012; see {@link FlowReason}).
 *
 * <p>Separate sums on the rows and on the columns only see one side at a time; the network sees,
 * for example, that two items needing two resources each cannot share three resources that one
 * other item needs as well.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class SymmetricGCC extends Constraint
    implements SatisfiedPresent, Copyable<SymmetricGCC>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The assignment matrix, rows are items and columns resources. */
  final IntVar[][] x;

  /** The number of resources each item uses. */
  final IntVar[] rowCount;

  /** The number of items each resource is used by. */
  final IntVar[] colCount;

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
   * It constructs a symmetric cardinality constraint.
   *
   * @param x the 0/1 assignment matrix, n rows of m variables
   * @param rowCount the number of ones of each row, n variables
   * @param colCount the number of ones of each column, m variables
   */
  public SymmetricGCC(IntVar[][] x, IntVar[] rowCount, IntVar[] colCount) {
    checkInputForNullness(new String[] {"x", "rowCount", "colCount"}, x, rowCount, colCount);
    this.n = x.length;
    this.m = colCount.length;
    if (rowCount.length != n) {
      throw new IllegalArgumentException("SymmetricGCC: rowCount needs one variable per row");
    }
    for (IntVar[] row : x) {
      checkInputForNullness("x", row);
      if (row.length != m) {
        throw new IllegalArgumentException("SymmetricGCC: every row needs one variable per column");
      }
    }
    this.numberId = idNumber.incrementAndGet();
    this.x = new IntVar[n][];
    for (int i = 0; i < n; i++) {
      this.x[i] = Arrays.copyOf(x[i], m);
    }
    this.rowCount = Arrays.copyOf(rowCount, n);
    this.colCount = Arrays.copyOf(colCount, m);
    this.cells = new int[n * m];
    this.rowMin = new int[n];
    this.rowMax = new int[n];
    this.colMin = new int[m];
    this.colMax = new int[m];
    this.queueIndex = 2;
    List<IntVar> scope = new ArrayList<>(n * m + n + m);
    for (IntVar[] row : this.x) {
      scope.addAll(Arrays.asList(row));
    }
    scope.addAll(Arrays.asList(this.rowCount));
    scope.addAll(Arrays.asList(this.colCount));
    setScope(scope.toArray(new IntVar[0]));
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void consistency(Store store) {
    for (IntVar[] row : x) {
      for (IntVar v : row) {
        v.domain.in(store.level, v, 0, 1);
      }
    }
    for (int r = 0; r < n; r++) {
      rowCount[r].domain.inMin(store.level, rowCount[r], 0);
      rowCount[r].domain.inMax(store.level, rowCount[r], m);
    }
    for (int c = 0; c < m; c++) {
      colCount[c].domain.inMin(store.level, colCount[c], 0);
      colCount[c].domain.inMax(store.level, colCount[c], n);
    }
    boolean changed = true;
    while (changed) {
      changed = false;
      for (int r = 0; r < n; r++) {
        for (int c = 0; c < m; c++) {
          IntVar v = x[r][c];
          cells[r * m + c] =
              v.min() >= 1 ? DegreeFlow.ONE : v.max() <= 0 ? DegreeFlow.ZERO : DegreeFlow.FREE;
        }
        rowMin[r] = rowCount[r].min();
        rowMax[r] = rowCount[r].max();
      }
      for (int c = 0; c < m; c++) {
        colMin[c] = colCount[c].min();
        colMax[c] = colCount[c].max();
      }
      if (!network.solve(n, m, cells, rowMin, rowMax, colMin, colMax, true)) {
        throw Store.failException;
      }
      for (int k = 0; k < n * m; k++) {
        if (cells[k] == DegreeFlow.FREE && network.cell[k] != DegreeFlow.FREE) {
          IntVar v = x[k / m][k % m];
          v.domain.in(store.level, v, network.cell[k], network.cell[k]);
        }
      }
      for (int r = 0; r < n; r++) {
        changed |= narrow(store, rowCount[r], network.rowLo[r], network.rowUp[r]);
      }
      for (int c = 0; c < m; c++) {
        changed |= narrow(store, colCount[c], network.colLo[c], network.colUp[c]);
      }
    }
  }

  // narrows a counter to [lo, up]; true if a hole made a bound move past what the flow saw
  static boolean narrow(Store store, IntVar v, int lo, int up) {
    v.domain.in(store.level, v, lo, up);
    return v.min() != lo || v.max() != up;
  }

  @Override
  public boolean satisfied() {
    for (int r = 0; r < n; r++) {
      if (!rowCount[r].singleton()) {
        return false;
      }
      int sum = 0;
      for (int c = 0; c < m; c++) {
        if (!x[r][c].singleton()) {
          return false;
        }
        sum += x[r][c].value();
      }
      if (sum != rowCount[r].value()) {
        return false;
      }
    }
    for (int c = 0; c < m; c++) {
      if (!colCount[c].singleton()) {
        return false;
      }
      int sum = 0;
      for (int r = 0; r < n; r++) {
        sum += x[r][c].value();
      }
      if (sum != colCount[c].value()) {
        return false;
      }
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : SymmetricGCC([");
    for (int r = 0; r < n; r++) {
      result.append(r == 0 ? "[" : ", [");
      appendArrayToString(result, x[r]);
      result.append(']');
    }
    result.append("], [");
    appendArrayToString(result, rowCount);
    result.append("], [");
    appendArrayToString(result, colCount);
    result.append("])");
    return result.toString();
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return inScope(trail.variable(entry)) && explain(FlowReason.ofEntry(trail, entry, out));
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return explain(new FlowReason(trail, trail.size(), out));
  }

  @Override
  public boolean checksReasons() {
    return true;
  }

  private boolean inScope(IntVar z) {
    for (IntVar v : rowCount) {
      if (v == z) {
        return true;
      }
    }
    for (IntVar v : colCount) {
      if (v == z) {
        return true;
      }
    }
    for (IntVar[] row : x) {
      for (IntVar v : row) {
        if (v == z) {
          return true;
        }
      }
    }
    return false;
  }

  // the network of the domains before the reason's position, with its atom negated
  private boolean explain(FlowReason reason) {
    long started = System.nanoTime();
    if (!budget.allows(started)) {
      return false;
    }
    try {
      int[] status = new int[n * m];
      for (int k = 0; k < n * m; k++) {
        IntVar v = x[k / m][k % m];
        int lo = reason.min(v);
        int hi = reason.max(v);
        if (lo > 1 || hi < 0 || lo > hi) {
          return false;
        }
        status[k] = lo >= 1 ? DegreeFlow.ONE : hi <= 0 ? DegreeFlow.ZERO : DegreeFlow.FREE;
      }
      int[] rLo = new int[n];
      int[] rUp = new int[n];
      for (int r = 0; r < n; r++) {
        rLo[r] = Math.max(reason.min(rowCount[r]), 0);
        rUp[r] = Math.min(reason.max(rowCount[r]), m);
      }
      int[] cLo = new int[m];
      int[] cUp = new int[m];
      for (int c = 0; c < m; c++) {
        cLo[c] = Math.max(reason.min(colCount[c]), 0);
        cUp[c] = Math.min(reason.max(colCount[c]), n);
      }
      DegreeFlow.CellReason cells =
          new DegreeFlow.CellReason() {
            @Override
            public void zero(int k) {
              reason.needUpper(x[k / m][k % m], 0);
            }

            @Override
            public void one(int k) {
              reason.needLower(x[k / m][k % m], 1);
            }
          };
      return network.explain(n, m, status, rLo, rUp, cLo, cUp, rowCount, colCount, reason, cells)
          && reason.finish();
    } finally {
      budget.spend(started);
    }
  }

  @Override
  public SymmetricGCC copy(VarMap map) {
    IntVar[][] copied = new IntVar[n][];
    for (int r = 0; r < n; r++) {
      copied[r] = map.get(x[r]);
    }
    return new SymmetricGCC(copied, map.get(rowCount), map.get(colCount));
  }
}
