/*
 * SymmetricGCCDetector.java
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

package org.jacop.fz.constraints;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.SymmetricGCC;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * It finds 0/1 matrices whose row sums and column sums are both bounded, written by hand as linear
 * sums, and posts a redundant {@link SymmetricGCC} on each of them (Kocjan and Kreuger, CPAIOR
 * 2004). The sums are {@code int_lin_eq}, {@code int_lin_le}, {@code bool_lin_eq} and {@code
 * bool_lin_le} with all coefficients 1 (or all -1) over distinct 0/1 variables and a constant
 * right-hand side, and {@code int_lin_eq} with coefficients 1 over 0/1 variables and -1 for one
 * counter variable. Sums over the same variables are merged. A variable in exactly two sums joins
 * them; the sums whose graph is bipartite, where two sums share at most one variable and every sum
 * of each side meets at least two of the other side, are the rows and columns of a matrix. Its
 * other cells are 0. The sums themselves are still posted; the flow links the rows and the columns,
 * which separate sums do not (battleship tallies, degree constraints of routing models, schedules
 * of agents by time).
 *
 * <p>A matrix needs at least {@code org.jacop.fz.symmetricGccLines} rows and as many columns
 * (default 2). The detection is opt-in, with {@code -Dorg.jacop.fz.symmetricGcc=true}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class SymmetricGCCDetector {

  static final int MIN_LINES = Integer.getInteger("org.jacop.fz.symmetricGccLines", 2);

  /** The most cells of a matrix, empty cells included. */
  static final int MAX_CELLS = Integer.getInteger("org.jacop.fz.symmetricGccCells", 40_000);

  private final Support support;

  private final Map<IntVar, Integer> index = new IdentityHashMap<>();
  private final List<IntVar> vars = new ArrayList<>();

  /** A sum over distinct 0/1 variables with bounds, or a counter. */
  private static final class Line {
    final int[] cells;
    int lo;
    int hi;
    IntVar counter;

    Line(int[] cells, int lo, int hi) {
      this.cells = cells;
      this.lo = lo;
      this.hi = hi;
    }
  }

  private final Map<String, Line> lines = new LinkedHashMap<>();

  /** Statistics: the matrices posted. */
  int matrices;

  /** Statistics: the cells of the matrices posted. */
  int cells;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public SymmetricGCCDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return true if the system property org.jacop.fz.symmetricGcc is true.
   */
  public static boolean enabled() {
    return Boolean.getBoolean("org.jacop.fz.symmetricGcc");
  }

  /**
   * It reads the sums of the model and posts the matrices they form.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    List<Line> all = new ArrayList<>(lines.values());
    int count = all.size();
    if (count < 2 * MIN_LINES) {
      return;
    }
    // the lines of each variable
    int[][] of = new int[vars.size()][2];
    int[] degree = new int[vars.size()];
    for (int l = 0; l < count; l++) {
      for (int c : all.get(l).cells) {
        if (degree[c] < 2) {
          of[c][degree[c]] = l;
        }
        degree[c]++;
      }
    }
    // lines joined by the variables in exactly two lines
    List<List<int[]>> adjacent = new ArrayList<>();
    for (int l = 0; l < count; l++) {
      adjacent.add(new ArrayList<>());
    }
    for (int v = 0; v < vars.size(); v++) {
      if (degree[v] == 2) {
        adjacent.get(of[v][0]).add(new int[] {of[v][1], v});
        adjacent.get(of[v][1]).add(new int[] {of[v][0], v});
      }
    }
    int[] side = new int[count];
    Arrays.fill(side, -1);
    for (int start = 0; start < count; start++) {
      if (side[start] >= 0 || adjacent.get(start).isEmpty()) {
        continue;
      }
      List<Integer> component = new ArrayList<>();
      boolean bipartite = true;
      ArrayDeque<Integer> queue = new ArrayDeque<>();
      side[start] = 0;
      queue.add(start);
      while (!queue.isEmpty()) {
        int u = queue.poll();
        component.add(u);
        for (int[] e : adjacent.get(u)) {
          if (side[e[0]] < 0) {
            side[e[0]] = 1 - side[u];
            queue.add(e[0]);
          } else if (side[e[0]] == side[u]) {
            bipartite = false;
          }
        }
      }
      if (bipartite) {
        post(all, component, side, adjacent);
      }
    }
    if (support.options.debug() && matrices > 0) {
      FzConsole.println("% SymmetricGCC: " + matrices + " matrices, " + cells + " cells");
    }
  }

  private void post(List<Line> all, List<Integer> component, int[] side, List<List<int[]>> adj) {
    List<Integer> rows = new ArrayList<>();
    List<Integer> cols = new ArrayList<>();
    for (int l : component) {
      (side[l] == 0 ? rows : cols).add(l);
    }
    if (rows.size() < MIN_LINES || cols.size() < MIN_LINES) {
      return;
    }
    Map<Integer, Integer> rowAt = new HashMap<>();
    Map<Integer, Integer> colAt = new HashMap<>();
    for (int l : rows) {
      rowAt.put(l, rowAt.size());
    }
    for (int l : cols) {
      colAt.put(l, colAt.size());
    }
    for (int l : component) {
      List<Integer> others = new ArrayList<>();
      for (int[] e : adj.get(l)) {
        if (others.contains(e[0])) {
          return; // two lines sharing two variables are not a row and a column
        }
        others.add(e[0]);
      }
      if (others.size() < 2) {
        return;
      }
    }
    int n = rows.size();
    int m = cols.size();
    // variables of a line that are in no line of the other side get a column (or row) of their own
    List<int[]> extraCols = new ArrayList<>();
    List<int[]> extraRows = new ArrayList<>();
    Map<Long, Integer> cell = new HashMap<>();
    for (int l : component) {
      boolean isRow = side[l] == 0;
      for (int c : all.get(l).cells) {
        Integer other = null;
        for (int[] e : adj.get(l)) {
          if (e[1] == c) {
            other = e[0];
          }
        }
        if (other == null) {
          (isRow ? extraCols : extraRows).add(new int[] {isRow ? rowAt.get(l) : colAt.get(l), c});
        } else if (isRow) {
          cell.put((long) rowAt.get(l) * (m + 1) + colAt.get(other), c);
        }
      }
    }
    int rowsTotal = n + extraRows.size();
    int colsTotal = m + extraCols.size();
    if ((long) rowsTotal * colsTotal > MAX_CELLS) {
      return;
    }
    IntVar[][] x = new IntVar[rowsTotal][colsTotal];
    IntVar zero = new IntVar(support.store, 0, 0);
    for (IntVar[] row : x) {
      Arrays.fill(row, zero);
    }
    for (Map.Entry<Long, Integer> e : cell.entrySet()) {
      x[(int) (e.getKey() / (m + 1))][(int) (e.getKey() % (m + 1))] = vars.get(e.getValue());
    }
    IntVar[] rowCount = new IntVar[rowsTotal];
    IntVar[] colCount = new IntVar[colsTotal];
    for (int r = 0; r < n; r++) {
      rowCount[r] = counter(all.get(rows.get(r)));
    }
    for (int c = 0; c < m; c++) {
      colCount[c] = counter(all.get(cols.get(c)));
    }
    for (int k = 0; k < extraCols.size(); k++) {
      int[] e = extraCols.get(k);
      x[e[0]][m + k] = vars.get(e[1]);
      colCount[m + k] = new IntVar(support.store, 0, 1);
    }
    for (int k = 0; k < extraRows.size(); k++) {
      int[] e = extraRows.get(k);
      x[n + k][e[0]] = vars.get(e[1]);
      rowCount[n + k] = new IntVar(support.store, 0, 1);
    }
    SymmetricGCC matrix = new SymmetricGCC(x, rowCount, colCount);
    support.implied(() -> support.pose(matrix));
    matrices++;
    cells += cell.size();
  }

  private IntVar counter(Line line) {
    if (line.counter != null) {
      return line.counter;
    }
    return new IntVar(support.store, Math.max(line.lo, 0), Math.min(line.hi, line.cells.length));
  }

  private void collect(ASTConstElem node) {
    String name = node.getName();
    boolean eq = "int_lin_eq".equals(name) || "bool_lin_eq".equals(name);
    boolean le = "int_lin_le".equals(name) || "bool_lin_le".equals(name);
    if (!eq && !le || node.jjtGetNumChildren() != 3) {
      return;
    }
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    if (a == null || !(node.jjtGetChild(2) instanceof ASTScalarFlatExpr rhs)) {
      return;
    }
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (v == null || v.length != a.length || v.length < 2) {
      return;
    }
    int b;
    try {
      b = support.getInt(rhs);
    } catch (IllegalArgumentException | ClassCastException e) {
      return;
    }
    // a counter: 1 on 0/1 variables and -1 on one other variable, = 0
    // (a counter with domain 0..1 is the single -1 among +1s)
    IntVar counter = null;
    int minus = 0;
    for (int coefficient : a) {
      minus += coefficient == -1 ? 1 : 0;
    }
    boolean counted = eq && b == 0 && minus == 1 && a.length > 2;
    int sign = 0;
    List<IntVar> terms = new ArrayList<>();
    for (int j = 0; j < v.length; j++) {
      boolean binary = v[j].min() >= 0 && v[j].max() <= 1;
      if (counted && a[j] == -1) {
        counter = v[j];
      } else if (binary && (a[j] == 1 || a[j] == -1) && (sign == 0 || sign == a[j])) {
        sign = a[j];
        terms.add(v[j]);
      } else {
        return;
      }
    }
    if (terms.size() < 2 || counter != null && sign != 1) {
      return;
    }
    int[] cols = new int[terms.size()];
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    for (int j = 0; j < cols.length; j++) {
      if (seen.put(terms.get(j), Boolean.TRUE) != null) {
        return;
      }
      cols[j] = node(terms.get(j));
    }
    int[] key = cols.clone();
    Arrays.sort(key);
    // sign * sum rel b: sum <= b, sum >= -b, or sum = sign * b
    int lo = 0;
    int hi = cols.length;
    if (counter == null) {
      if (eq) {
        lo = hi = sign * b;
      } else if (sign == 1) {
        hi = b;
      } else {
        lo = -b;
      }
    }
    Line line = lines.get(Arrays.toString(key));
    if (line == null) {
      line = new Line(key, lo, hi);
      lines.put(Arrays.toString(key), line);
    } else {
      line.lo = Math.max(line.lo, lo);
      line.hi = Math.min(line.hi, hi);
    }
    if (counter != null && line.counter == null) {
      line.counter = counter;
    }
  }

  private int node(IntVar x) {
    return index.computeIfAbsent(
        x,
        v -> {
          vars.add(v);
          return vars.size() - 1;
        });
  }
}
