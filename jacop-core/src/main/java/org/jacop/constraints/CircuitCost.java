/*
 * CircuitCost.java
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

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * CircuitCost constraint assures that the variables build a Hamiltonian circuit and that cost is
 * the sum of the costs of the arcs of that circuit. Value of every variable x[i] points to the next
 * variable in the circuit, and costs[i][j] is the cost of x[i] pointing to the j-th variable
 * (counted from 0). Variables are numbered from 1 by default, as in {@link Circuit}, or from the
 * given offset.
 *
 * <p>The constraint filters the arcs and the cost with two relaxations of the circuit:
 *
 * <ul>
 *   <li>the assignment problem, solved incrementally by the Hungarian method, which bounds the cost
 *       and removes every arc whose reduced cost exceeds the slack between the bound and the cost
 *       (Focacci, Lodi and Milano, CP 1999). The maximum assignment bounds the cost from above in
 *       the same way when the cost has a lower bound of its own;
 *   <li>the Held-Karp 1-tree bound with Lagrangian penalties computed by subgradient optimisation,
 *       which removes every edge whose replacement cost in the 1-tree exceeds the slack (Benchimol
 *       et al., Constraints 2012). It is used by default when the costs are symmetric, where the
 *       assignment bound is weak.
 * </ul>
 *
 * <p>The structure of the circuit is only checked once all variables are ground; post the
 * constraint together with {@link Circuit} on the same variables for the structural propagation.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CircuitCost extends Constraint implements SatisfiedPresent, Copyable<CircuitCost> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The successor variables. */
  public final IntVar[] list;

  /** The cost of each arc: costs[i][j] is the cost of list[i] = offset + j. */
  public final int[][] costs;

  /** The cost of the circuit. */
  public final IntVar cost;

  /** The value that points to list[0]. */
  public final int offset;

  private final int n;

  private final boolean symmetric;

  private boolean useAssignment = true;

  private boolean useOneTree;

  private final Assignment minAssignment;

  private final Assignment maxAssignment;

  private OneTree oneTree;

  // the last 1-tree bound, to tell a lower bound of the cost set by other constraints
  private long oneTreeBound = Long.MIN_VALUE;

  // the sums of the largest and of the smallest arc cost of each row, from the last call
  private final long[] rows = new long[2];

  // the last minimum assignment
  private long assignmentBound = Long.MIN_VALUE;

  // The 1-tree bound is optimised longer the first time, its penalties are kept between calls.
  private int oneTreeIterations = 100;

  private static final int ONE_TREE_NODE_ITERATIONS = 20;

  /**
   * It constructs a circuit constraint with a cost, whose variables are numbered from 1.
   *
   * @param list variables which must form a circuit.
   * @param costs costs[i][j] is the cost of list[i] pointing to list[j].
   * @param cost the sum of the costs of the arcs of the circuit.
   */
  public CircuitCost(IntVar[] list, int[][] costs, IntVar cost) {
    this(list, costs, cost, 1);
  }

  /**
   * It constructs a circuit constraint with a cost, whose variables are numbered from the given
   * offset.
   *
   * @param list variables which must form a circuit.
   * @param costs costs[i][j] is the cost of list[i] = offset + j.
   * @param cost the sum of the costs of the arcs of the circuit.
   * @param offset the value that points to list[0]; list[i] is pointed to by offset + i.
   */
  public CircuitCost(IntVar[] list, int[][] costs, IntVar cost, int offset) {

    checkInputForNullness(new String[] {"list", "costs", "cost"}, list, costs, new Object[] {cost});
    checkInputForDuplication("list", list);
    if ((long) offset < IntDomain.MIN_INT || (long) offset + list.length - 1 > IntDomain.MAX_INT) {
      throw new IllegalArgumentException(
          "CircuitCost has values "
              + offset
              + ".."
              + ((long) offset + list.length - 1)
              + " out of range");
    }
    if (costs.length != list.length) {
      throw new IllegalArgumentException(
          "CircuitCost needs a cost row for each of the " + list.length + " variables");
    }
    for (int[] row : costs) {
      if (row == null || row.length != list.length) {
        throw new IllegalArgumentException(
            "CircuitCost needs " + list.length + " costs in each row of costs");
      }
    }
    for (IntVar v : list) {
      if (v == cost) {
        throw new IllegalArgumentException("CircuitCost cost variable is also in list");
      }
    }

    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.n = list.length;
    this.costs = new int[n][];
    for (int i = 0; i < n; i++) {
      this.costs[i] = Arrays.copyOf(costs[i], n);
    }
    this.cost = cost;
    this.offset = offset;
    this.queueIndex = 2;

    boolean sym = true;
    for (int i = 0; i < n && sym; i++) {
      for (int j = i + 1; j < n; j++) {
        if (costs[i][j] != costs[j][i]) {
          sym = false;
          break;
        }
      }
    }
    this.symmetric = sym;
    this.useOneTree = sym;

    minAssignment = new Assignment(n, this.costs, false);
    maxAssignment = new Assignment(n, this.costs, true);

    setScope(list, new IntVar[] {cost});
  }

  /**
   * It selects the relaxations used for filtering. The 1-tree bound is used by default only when
   * the costs are symmetric.
   *
   * @param assignment true to use the assignment bound and its reduced costs.
   * @param oneTree true to use the Held-Karp 1-tree bound.
   */
  public void setFiltering(boolean assignment, boolean oneTree) {
    this.useAssignment = assignment;
    this.useOneTree = oneTree;
  }

  /**
   * It tells if the costs are symmetric.
   *
   * @return true if costs[i][j] equals costs[j][i] for all i and j.
   */
  public boolean isSymmetric() {
    return symmetric;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    Integer event = getConsistencyPruningEventFromMap(v);
    if (event != null) {
      return event;
    }
    return v == cost ? IntDomain.BOUND : IntDomain.ANY;
  }

  @Override
  public void consistency(Store store) {

    if (n == 1) {
      // a variable cannot point to itself
      throw Store.failException;
    }

    for (int i = 0; i < n; i++) {
      IntVar x = list[i];
      x.domain.in(store.level, x, offset, offset + n - 1);
      x.domain.inComplement(store.level, x, offset + i);
    }

    boolean oneTreePending = useOneTree && n >= 4;
    boolean again;
    do {
      do {
        store.propagationHasOccurred = false;
        upperBoundFromRows(store);
        // Every assignment costs at most the sum of the row maxima, so the minimum assignment
        // can only prune when the cost has a smaller upper bound, and the same for the maximum
        // assignment, which in addition only runs when the lower bound of the cost is not the
        // one this constraint set.
        if (useAssignment) {
          assignmentBound =
              CostBounds.assignments(
                  store,
                  list,
                  offset,
                  cost,
                  minAssignment,
                  maxAssignment,
                  rows,
                  assignmentBound,
                  oneTreeBound);
        }
      } while (store.propagationHasOccurred);

      // the 1-tree runs once per call and only prunes against an upper bound of the cost tighter
      // than the arc costs give, such as the bound of branch and bound after a first solution
      again = false;
      if (oneTreePending && cost.max() < rows[1]) {
        oneTreePending = false;
        if (oneTree == null) {
          oneTree = new OneTree(n, costs);
        }
        store.propagationHasOccurred = false;
        oneTree.propagate(store, this, oneTreeIterations);
        oneTreeIterations = ONE_TREE_NODE_ITERATIONS;
        again = store.propagationHasOccurred;
      }
    } while (again);

    if (cost.singleton() && allGround()) {
      checkCircuit();
    }
  }

  private boolean allGround() {
    for (IntVar x : list) {
      if (!x.singleton()) {
        return false;
      }
    }
    return true;
  }

  private void checkCircuit() {
    int i = 0;
    int no = 0;
    do {
      i = list[i].value() - offset;
      no++;
    } while (no < n && i != 0);
    if (no != n || i != 0) {
      throw Store.failException;
    }
  }

  // cost <= sum of the largest arc cost of each row; exact when all variables are ground
  private void upperBoundFromRows(Store store) {
    CostBounds.rowSums(list, costs, offset, rows);
    setMax(store, rows[1]);
    setMin(store, rows[0]);
  }

  void setMin(Store store, long min) {
    CostBounds.setMin(store, cost, min);
  }

  void setMax(Store store, long max) {
    CostBounds.setMax(store, cost, max);
  }

  void removeArc(Store store, int from, int to) {
    IntVar x = list[from];
    if (x.domain.contains(offset + to)) {
      x.domain.inComplement(store.level, x, offset + to);
    }
  }

  @Override
  public boolean satisfied() {
    if (!cost.singleton()) {
      return false;
    }
    long sum = 0;
    for (int i = 0; i < n; i++) {
      if (!list[i].singleton()) {
        return false;
      }
      int j = list[i].value() - offset;
      if (j < 0 || j >= n || j == i) {
        return false;
      }
      sum += costs[i][j];
    }
    if (sum != cost.value()) {
      return false;
    }
    int i = 0;
    int no = 0;
    do {
      i = list[i].value() - offset;
      no++;
    } while (no < n && i != 0);
    return no == n && i == 0;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : CircuitCost([");
    appendArrayToString(result, list);
    result.append("], ");
    CostBounds.appendCosts(result, costs);
    result.append(", ").append(cost);
    if (offset != 1) {
      result.append(", ").append(offset);
    }
    result.append(')');
    return result.toString();
  }

  /**
   * The assignment relaxation: a minimum cost matching of the variables (rows) to distinct values
   * in their domains (columns), by the Hungarian method with shortest augmenting paths. There are
   * at least as many columns as rows; every row is matched and a column at most once. The matching
   * and the duals are kept between calls and are not trailed: each call restores dual feasibility
   * for the arcs that came back on backtracking and augments only the rows that lost their arc.
   *
   * <p>With more columns than rows the column duals stay at most zero and are zero on the columns
   * that are not matched, so the dual sum is the cost of the matching and every arc's reduced cost
   * still bounds the cost of the matchings that use it.
   */
  static final class Assignment {

    private static final long INF = Long.MAX_VALUE / 4;

    // the duals are reset when they drift this far, long before an overflow
    private static final long DRIFT_LIMIT = 1L << 52;

    private final int n;
    private final int m;
    private final long[][] weight;
    private final long[] u;
    private final long[] v;
    private final int[] rowMate;
    // colMate[m] is the virtual column the augmenting path starts from
    private final int[] colMate;
    private final long[] minv;
    private final int[] way;
    private final boolean[] used;
    private long dualSum;

    // With copies, value j has the columns first[j]..first[j] + open[j] - 1 and column c is a copy
    // of value valueOf[c]; without, column j is value j.
    private final int[] first;
    private final int[] open;
    private final int[] valueOf;

    Assignment(int n, int[][] costs, boolean negate) {
      this(n, n, costs, negate);
    }

    /**
     * It creates the assignment of n rows to m columns, m at least n.
     *
     * @param n the number of rows (variables).
     * @param m the number of columns (values).
     * @param costs costs[i][j] is the cost of row i taking column j.
     * @param negate true to maximise the cost instead.
     */
    Assignment(int n, int m, int[][] costs, boolean negate) {
      this(n, m, costs, negate, null);
    }

    /**
     * It creates the assignment of n rows to the copies of the values: value j has copies[j]
     * columns, of which the first open(j) ones are used, so that at most that many rows take it.
     *
     * @param n the number of rows (variables).
     * @param values the number of values.
     * @param costs costs[i][j] is the cost of row i taking value j.
     * @param negate true to maximise the cost instead.
     * @param copies the most rows that may take each value, or null for one each.
     */
    Assignment(int n, int values, int[][] costs, boolean negate, int[] copies) {
      this.n = n;
      int columns = values;
      if (copies != null) {
        first = new int[values];
        open = new int[values];
        columns = 0;
        for (int j = 0; j < values; j++) {
          first[j] = columns;
          open[j] = copies[j];
          columns += copies[j];
        }
        valueOf = new int[columns];
        for (int j = 0; j < values; j++) {
          Arrays.fill(valueOf, first[j], first[j] + copies[j], j);
        }
      } else {
        assert values >= n : "fewer columns than rows";
        first = null;
        open = null;
        valueOf = null;
      }
      this.m = columns;
      weight = new long[n][m];
      for (int i = 0; i < n; i++) {
        for (int c = 0; c < m; c++) {
          int j = valueOf == null ? c : valueOf[c];
          weight[i][c] = negate ? -(long) costs[i][j] : costs[i][j];
        }
      }
      u = new long[n];
      v = new long[m];
      rowMate = new int[n];
      colMate = new int[m + 1];
      minv = new long[m];
      way = new int[m];
      used = new boolean[m + 1];
      reset();
    }

    /**
     * The weights, which may be changed between two calls of solve: it then repairs the duals.
     *
     * @return the weight matrix, weight[i][j] for successor i pointing to j.
     */
    long[][] weights() {
      return weight;
    }

    /**
     * The value of successor i in the last minimum assignment, less the offset.
     *
     * @param i the successor.
     * @return the column matched to row i.
     */
    int rowMate(int i) {
      return rowMate[i];
    }

    /**
     * It sets how many copies of a value the next solve may use, at most the copies it was created
     * with.
     *
     * @param j the value, less the offset.
     * @param copies the number of rows that may take value j.
     */
    void setOpen(int j, int copies) {
      open[j] = copies;
    }

    // the column of a matched arc is gone from the domain or is a copy that is closed
    private boolean gone(IntVar x, int column, int offset) {
      if (valueOf == null) {
        return !x.domain.contains(column + offset);
      }
      int j = valueOf[column];
      return column - first[j] >= open[j] || !x.domain.contains(j + offset);
    }

    private void reset() {
      Arrays.fill(u, INF);
      Arrays.fill(v, 0);
      Arrays.fill(rowMate, -1);
      Arrays.fill(colMate, -1);
    }

    /**
     * It computes the minimum cost assignment for the current domains.
     *
     * @return the cost of the minimum assignment.
     */
    long solve(IntVar[] list, int offset) {

      for (int i = 0; i < n; i++) {
        if (u[i] != INF && (u[i] > DRIFT_LIMIT || u[i] < -DRIFT_LIMIT)) {
          reset();
          break;
        }
      }

      // restore dual feasibility and drop the matched arcs that are gone or not tight anymore
      boolean freed = repairDuals(list, offset);
      // with more columns than rows, a column left without a row must have a zero dual
      while (freed) {
        freed = false;
        for (int j = 0; j < m; j++) {
          if (colMate[j] < 0 && v[j] != 0) {
            v[j] = 0;
            freed = true;
          }
        }
        freed = freed && repairDuals(list, offset);
      }

      for (int i = 0; i < n; i++) {
        if (rowMate[i] < 0 && !augment(i, list, offset)) {
          throw Store.failException;
        }
      }

      long sum = 0;
      long duals = 0;
      for (int i = 0; i < n; i++) {
        sum += weight[i][rowMate[i]];
        duals += u[i];
      }
      for (int j = 0; j < m; j++) {
        duals += v[j];
      }
      assert sum == duals : "assignment cost " + sum + " differs from dual bound " + duals;
      dualSum = duals;
      return sum;
    }

    // it lowers the row duals to keep the reduced costs non-negative and unmatches the arcs that
    // are gone or not tight; it tells if a column with a non-zero dual lost its row
    private boolean repairDuals(IntVar[] list, int offset) {
      boolean freed = false;
      for (int i = 0; i < n; i++) {
        IntVar x = list[i];
        int mate = rowMate[i];
        if (mate >= 0 && gone(x, mate, offset)) {
          colMate[mate] = -1;
          rowMate[i] = -1;
          freed |= v[mate] != 0;
          mate = -1;
        }
        long[] w = weight[i];
        long min = INF;
        int last = x.max();
        for (int val = x.min(); ; val = x.domain.nextValue(val)) {
          int j = val - offset;
          int end = valueOf == null ? j + 1 : first[j] + open[j];
          for (int c = valueOf == null ? j : first[j]; c < end; c++) {
            long rc = w[c] - v[c];
            if (rc < min) {
              min = rc;
            }
          }
          if (val >= last) {
            break;
          }
        }
        if (u[i] > min) {
          u[i] = min;
        }
        // a matched arc stays only while tight (the duals or the weights may have changed)
        if (mate >= 0 && w[mate] - u[i] - v[mate] != 0) {
          colMate[mate] = -1;
          rowMate[i] = -1;
          freed |= v[mate] != 0;
        }
      }
      return freed && m > n;
    }

    // shortest augmenting path from row r in the reduced costs (Hungarian method, O(n m))
    private boolean augment(int r, IntVar[] list, int offset) {
      Arrays.fill(minv, INF);
      Arrays.fill(used, false);
      colMate[m] = r;
      int j0 = m;
      do {
        used[j0] = true;
        int i0 = colMate[j0];
        IntVar x = list[i0];
        long[] w = weight[i0];
        long ui = u[i0];
        int last = x.max();
        for (int val = x.min(); ; val = x.domain.nextValue(val)) {
          int j = val - offset;
          int end = valueOf == null ? j + 1 : first[j] + open[j];
          for (int c = valueOf == null ? j : first[j]; c < end; c++) {
            if (!used[c]) {
              long cur = w[c] - ui - v[c];
              if (cur < minv[c]) {
                minv[c] = cur;
                way[c] = j0;
              }
            }
          }
          if (val >= last) {
            break;
          }
        }
        long delta = INF;
        int j1 = -1;
        for (int j = 0; j < m; j++) {
          if (!used[j] && minv[j] < delta) {
            delta = minv[j];
            j1 = j;
          }
        }
        if (j1 < 0) {
          // no augmenting path: some variables cannot be matched to different values
          colMate[m] = -1;
          return false;
        }
        for (int j = 0; j < m; j++) {
          if (used[j]) {
            u[colMate[j]] += delta;
            v[j] -= delta;
          } else if (minv[j] != INF) {
            minv[j] -= delta;
          }
        }
        u[r] += delta;
        j0 = j1;
      } while (colMate[j0] != -1);

      while (j0 != m) {
        int j1 = way[j0];
        int row = colMate[j1];
        colMate[j0] = row;
        rowMate[row] = j0;
        j0 = j1;
      }
      colMate[m] = -1;
      return true;
    }

    /**
     * It removes every arc whose reduced cost added to the assignment bound exceeds the given
     * bound, since every assignment with that arc costs at least as much.
     */
    void prune(Store store, IntVar[] list, int offset, long bound) {
      long slack = bound - dualSum;
      for (int i = 0; i < n; i++) {
        IntVar x = list[i];
        if (x.singleton()) {
          continue;
        }
        long[] w = weight[i];
        long ui = u[i];
        int mate = valueOf == null ? rowMate[i] : valueOf[rowMate[i]];
        for (int val = x.min(); ; val = x.domain.nextValue(val)) {
          int j = val - offset;
          if (j != mate && reducedCost(w, ui, j) > slack) {
            x.domain.inComplement(store.level, x, val);
          }
          if (val >= x.max()) {
            break;
          }
        }
      }
    }

    // the smallest reduced cost of row i taking value j, over its open copies
    private long reducedCost(long[] w, long ui, int j) {
      if (valueOf == null) {
        return w[j] - ui - v[j];
      }
      long min = INF;
      for (int c = first[j], end = c + open[j]; c < end; c++) {
        min = Math.min(min, w[c] - ui - v[c]);
      }
      return min;
    }
  }

  /**
   * The Held-Karp relaxation: a minimum 1-tree (a spanning tree of the nodes other than node 0,
   * plus the two cheapest edges of node 0) in the undirected graph of the arcs, with Lagrangian
   * penalties on the node degrees. An edge {i, j} costs the cheaper of the arcs i to j and j to i
   * that are still in the domains, so every circuit costs at least as much as its 1-tree.
   */
  private static final class OneTree {

    private static final double INF = Double.POSITIVE_INFINITY;

    private final int n;
    private final int[][] costs;
    private final double[][] edge;
    private final double[] pi;
    private final double[] bestPi;
    private final int[] degree;
    private final int[] parent;
    private final int[] order;
    private final double[] key;
    private final boolean[] inTree;
    private final double[][] maxOnPath;
    private int first0;
    private int second0;

    OneTree(int n, int[][] costs) {
      this.n = n;
      this.costs = costs;
      edge = new double[n][n];
      pi = new double[n];
      bestPi = new double[n];
      degree = new int[n];
      parent = new int[n];
      order = new int[n];
      key = new double[n];
      inTree = new boolean[n];
      maxOnPath = new double[n][n];
    }

    private void buildEdges(IntVar[] list, int offset) {
      for (double[] row : edge) {
        Arrays.fill(row, INF);
      }
      for (int i = 0; i < n; i++) {
        IntVar x = list[i];
        int[] row = costs[i];
        int last = x.max();
        for (int val = x.min(); ; val = x.domain.nextValue(val)) {
          int j = val - offset;
          double c = row[j];
          if (c < edge[i][j]) {
            edge[i][j] = c;
            edge[j][i] = c;
          }
          if (val >= last) {
            break;
          }
        }
      }
    }

    /**
     * It computes the minimum 1-tree with the penalties p and its degrees.
     *
     * @return the Lagrangian bound, or negative infinity if no 1-tree exists.
     */
    private double solve(double[] p) {
      // Prim's algorithm on nodes 1..n-1
      Arrays.fill(inTree, false);
      Arrays.fill(degree, 0);
      Arrays.fill(key, INF);
      Arrays.fill(parent, -1);
      double total = 0;
      key[1] = 0;
      for (int k = 0; k < n - 1; k++) {
        int best = -1;
        double bestKey = INF;
        for (int j = 1; j < n; j++) {
          if (!inTree[j] && key[j] < bestKey) {
            bestKey = key[j];
            best = j;
          }
        }
        if (best < 0) {
          return Double.NEGATIVE_INFINITY;
        }
        inTree[best] = true;
        order[k] = best;
        total += bestKey;
        if (parent[best] >= 0) {
          degree[best]++;
          degree[parent[best]]++;
        }
        double[] row = edge[best];
        double pb = p[best];
        for (int j = 1; j < n; j++) {
          if (!inTree[j] && row[j] < INF) {
            double c = row[j] + pb + p[j];
            if (c < key[j]) {
              key[j] = c;
              parent[j] = best;
            }
          }
        }
      }
      // the two cheapest edges of node 0
      first0 = -1;
      second0 = -1;
      double c1 = INF;
      double c2 = INF;
      double[] row0 = edge[0];
      for (int j = 1; j < n; j++) {
        if (row0[j] < INF) {
          double c = row0[j] + p[0] + p[j];
          if (c < c1) {
            c2 = c1;
            second0 = first0;
            c1 = c;
            first0 = j;
          } else if (c < c2) {
            c2 = c;
            second0 = j;
          }
        }
      }
      if (second0 < 0) {
        return Double.NEGATIVE_INFINITY;
      }
      degree[0] = 2;
      degree[first0]++;
      degree[second0]++;
      total += c1 + c2;
      double sumPi = 0;
      for (int i = 0; i < n; i++) {
        sumPi += p[i];
      }
      return total - 2 * sumPi;
    }

    private static double tolerance(double value) {
      return 1e-7 * Math.max(1.0, Math.abs(value));
    }

    void propagate(Store store, CircuitCost c, int iterations) {

      buildEdges(c.list, c.offset);
      double ub = c.cost.max();

      double best = Double.NEGATIVE_INFINITY;
      double lambda = 2.0;
      int sinceImproved = 0;
      for (int it = 0; it < iterations; it++) {
        double bound = solve(pi);
        if (Double.isInfinite(bound)) {
          // the graph is not connected or node 0 has fewer than two neighbours
          throw Store.failException;
        }
        if (Double.isInfinite(best) || bound > best + tolerance(best)) {
          best = bound;
          System.arraycopy(pi, 0, bestPi, 0, n);
          sinceImproved = 0;
        } else if (++sinceImproved >= 5) {
          lambda /= 2;
          sinceImproved = 0;
        }
        if (best > ub + tolerance(ub)) {
          throw Store.failException;
        }
        long norm = 0;
        for (int i = 0; i < n; i++) {
          long d = (long) degree[i] - 2;
          norm += d * d;
        }
        if (norm == 0) {
          // the 1-tree is a circuit, so its cost is the optimum for these domains
          break;
        }
        double target = ub < IntDomain.MAX_INT ? ub : bound + Math.max(1.0, Math.abs(bound) * 0.05);
        double step = lambda * Math.max(target - bound, tolerance(bound)) / norm;
        for (int i = 0; i < n; i++) {
          pi[i] += step * (degree[i] - 2);
        }
      }
      System.arraycopy(bestPi, 0, pi, 0, n);

      double bound = solve(pi);
      if (Double.isInfinite(bound)) {
        throw Store.failException;
      }
      long lowerBound = (long) Math.ceil(bound - tolerance(bound));
      c.oneTreeBound = lowerBound;
      c.setMin(store, lowerBound);
      ub = c.cost.max();
      double limit = ub + tolerance(ub);

      // the largest edge on the tree path between every pair of nodes 1..n-1
      for (int k = 0; k < n - 1; k++) {
        int vk = order[k];
        maxOnPath[vk][vk] = Double.NEGATIVE_INFINITY;
        if (k == 0) {
          continue;
        }
        int pk = parent[vk];
        double ce = edge[vk][pk] + pi[vk] + pi[pk];
        for (int l = 0; l < k; l++) {
          int vl = order[l];
          double m = Math.max(maxOnPath[pk][vl], ce);
          maxOnPath[vk][vl] = m;
          maxOnPath[vl][vk] = m;
        }
      }

      double c2 = edge[0][second0] + pi[0] + pi[second0];
      for (int i = 0; i < n; i++) {
        IntVar x = c.list[i];
        if (x.singleton()) {
          continue;
        }
        for (int val = x.min(); ; val = x.domain.nextValue(val)) {
          int j = val - c.offset;
          if (!isTreeEdge(i, j)) {
            double ce = edge[i][j] + pi[i] + pi[j];
            double replaced = i == 0 || j == 0 ? c2 : maxOnPath[i][j];
            if (bound + ce - replaced > limit) {
              // the edge is too expensive in either direction
              c.removeArc(store, i, j);
              c.removeArc(store, j, i);
            }
          }
          if (val >= x.max()) {
            break;
          }
        }
      }
    }

    private boolean isTreeEdge(int i, int j) {
      if (i == 0) {
        return j == first0 || j == second0;
      }
      if (j == 0) {
        return i == first0 || i == second0;
      }
      return parent[i] == j || parent[j] == i;
    }
  }

  @Override
  public CircuitCost copy(VarMap map) {
    CircuitCost c = new CircuitCost(map.get(list), costs, map.get(cost), offset);
    c.useAssignment = useAssignment;
    c.useOneTree = useOneTree;
    return c;
  }
}
