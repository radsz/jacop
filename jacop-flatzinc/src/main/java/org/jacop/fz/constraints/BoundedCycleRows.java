/*
 * BoundedCycleRows.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XeqC;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * The cycle formulation of a permutation whose cycles are at most K long, for the linear
 * relaxation.
 *
 * <p>The cardinality-constrained multi-cycle problem of kidney exchange (2019 MiniZinc Challenge
 * kidney-exchange) states a permutation {@code alldifferent(succ)} with a cost {@code sum(i)(w[i,
 * succ[i]])} found by {@link CircuitCostDetector}, labels every vertex with its cycle, {@code
 * cycle[i] = cycle[succ[i]]}, and bounds the cycle length by {@code bin_packing(K, cycle, [1, ...,
 * 1])}. The assignment relaxation of {@link org.jacop.constraints.CostAlldifferent} ignores the
 * length bound (3_20_0.25_2: bound 1275 for an optimum of 1008), and so do the value columns of the
 * linear relaxation: that is the edge formulation without its path rows. The cycle formulation of
 * Abraham, Blum and Sandholm (Clearing algorithms for barter exchange markets, EC 2007) and Roth,
 * Sönmez and Ünver (Efficient kidney exchange, American Economic Review 97(3), 2007) has a 0/1
 * variable per cycle of at most K arcs and gives a much tighter bound (Mak-Hau, J Comb Optim 33,
 * 2017): every vertex is in at most one chosen cycle, {@code succ[i] = i + sum(c ∋ i)(next_c(i) -
 * i) y_c}, and the cost is {@code sum(i)(w[i, i]) + sum(c)(w_c - sum(i ∈ c)(w[i, i])) y_c}. These
 * rows are implied by the model, since a permutation with cycles of at most K vertices is the union
 * of its cycles. Each y_c also implies the arcs of its cycle.
 *
 * <p>The rows are posted when the cycles of at most K arcs over the successor domains are at most
 * {@value #MAX_CYCLES}, for K up to {@value #MAX_LENGTH}. The system property {@code
 * org.jacop.fz.boundedCycles=false} turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class BoundedCycleRows {

  /** At most this many cycles get a variable. */
  static final int MAX_CYCLES = 20_000;

  /** The longest bound on the cycle length that is expanded. */
  static final int MAX_LENGTH = 4;

  private final Support support;

  // label = labels[index - first] with an array of variables, by index variable
  private static final class LabelElement {
    private final IntVar[] labels;
    private final IntVar value;
    private final int first;

    LabelElement(IntVar[] labels, IntVar value, int first) {
      this.labels = labels;
      this.value = value;
      this.first = first;
    }

    IntVar[] labels() {
      return labels;
    }

    IntVar value() {
      return value;
    }

    int first() {
      return first;
    }
  }

  private final Map<IntVar, List<LabelElement>> labelElements = new IdentityHashMap<>();

  // bin packing of unit items: the bins and the largest capacity
  private static final class UnitPacking {
    private final IntVar[] bins;
    private final int capacity;

    UnitPacking(IntVar[] bins, int capacity) {
      this.bins = bins;
      this.capacity = capacity;
    }

    IntVar[] bins() {
      return bins;
    }

    int capacity() {
      return capacity;
    }
  }

  private final List<UnitPacking> packings = new ArrayList<>();

  BoundedCycleRows(Support support) {
    this.support = support;
  }

  static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.boundedCycles"));
  }

  /**
   * Reads an element over an array of variables or a bin packing.
   *
   * @param node the constraint node
   */
  void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "array_var_int_element" -> labelElement(node, 1);
      case "jacop_array_var_int_element_nonshifted" ->
          labelElement(node, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
      case "jacop_bin_packing_capacity" -> packing(node);
      default -> {
        // not part of a bounded cycle
      }
    }
  }

  boolean hasCandidates() {
    return !labelElements.isEmpty() && !packings.isEmpty();
  }

  private void labelElement(ASTConstElem node, int first) {
    IntVar index = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar[] labels = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar value = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (!index.singleton()) {
      labelElements
          .computeIfAbsent(index, k -> new ArrayList<>())
          .add(new LabelElement(labels, value, first));
    }
  }

  private void packing(ASTConstElem node) {
    IntVar[] bins = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] capacities = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] weights = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    if (capacities == null || weights == null || weights.length != bins.length) {
      return;
    }
    for (int w : weights) {
      if (w != 1) {
        return;
      }
    }
    int capacity = 0;
    for (int c : capacities) {
      capacity = Math.max(capacity, c);
    }
    packings.add(new UnitPacking(bins, capacity));
  }

  /**
   * The bound on the cycle length of the permutation x (x[i] = offset + j: j follows i), or 0 when
   * the model has no labels of its cycles packed into bins.
   */
  private int cycleBound(IntVar[] x, int offset) {
    int n = x.length;
    int best = 0;
    for (UnitPacking p : packings) {
      if (p.bins().length != n || p.capacity() < 2 || best > 0 && p.capacity() >= best) {
        continue;
      }
      boolean all = true;
      for (int i = 0; i < n && all; i++) {
        all = labels(x[i], p.bins(), p.bins()[i], offset);
      }
      if (all) {
        best = p.capacity();
      }
    }
    return best;
  }

  // whether labels[x - offset] = label is in the model
  private boolean labels(IntVar x, IntVar[] labels, IntVar label, int offset) {
    for (LabelElement e : labelElements.getOrDefault(x, List.of())) {
      if (e.value() == label && e.first() == offset && Arrays.equals(e.labels(), labels)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Posts the cycle formulation when the permutation x has a bound on its cycle length.
   *
   * @param x the successors, x[i] = offset + j when j follows i
   * @param offset the value of the first vertex
   * @param costs costs[i][j] the cost of x[i] = offset + j
   * @param cost the sum of the costs of the successors
   * @return the number of cycles posted, 0 when none
   */
  int post(IntVar[] x, int offset, int[][] costs, IntVar cost) {
    int n = x.length;
    int k = cycleBound(x, offset);
    if (k < 2 || k > MAX_LENGTH || costs.length != n) {
      return 0;
    }
    for (int[] row : costs) {
      if (row.length < n) {
        return 0;
      }
    }
    List<int[]> cycles = new ArrayList<>();
    if (!cycles(x, offset, k, cycles)) {
      return 0;
    }
    long selfCost = 0;
    for (int i = 0; i < n; i++) {
      selfCost += costs[i][i];
    }
    // the gain of each cycle over leaving its vertices alone
    long[] gain = new long[cycles.size()];
    long lo = selfCost;
    long hi = selfCost;
    for (int c = 0; c < cycles.size(); c++) {
      int[] cycle = cycles.get(c);
      for (int p = 0; p < cycle.length; p++) {
        int i = cycle[p];
        gain[c] += costs[i][cycle[(p + 1) % cycle.length]] - (long) costs[i][i];
      }
      lo += Math.min(0, gain[c]);
      hi += Math.max(0, gain[c]);
    }
    if (lo < Integer.MIN_VALUE / 2 || hi > Integer.MAX_VALUE / 2) {
      return 0;
    }
    IntVar[] y = new IntVar[cycles.size()];
    List<List<Integer>> through = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      through.add(new ArrayList<>());
    }
    List<Constraint> posted = new ArrayList<>();
    for (int c = 0; c < y.length; c++) {
      y[c] = new IntVar(support.store, "cycle" + c, 0, 1);
      int[] cycle = cycles.get(c);
      for (int p = 0; p < cycle.length; p++) {
        int i = cycle[p];
        through.get(i).add(c);
        posted.add(new Implies(y[c], new XeqC(x[i], offset + cycle[(p + 1) % cycle.length])));
      }
    }
    for (int i = 0; i < n; i++) {
      List<Integer> mine = through.get(i);
      if (mine.isEmpty()) {
        continue;
      }
      IntVar[] vars = new IntVar[mine.size() + 1];
      int[] weights = new int[mine.size() + 1];
      int[] ones = new int[mine.size()];
      IntVar[] ys = new IntVar[mine.size()];
      vars[0] = x[i];
      weights[0] = 1;
      for (int t = 0; t < mine.size(); t++) {
        int c = mine.get(t);
        int[] cycle = cycles.get(c);
        int p = position(cycle, i);
        vars[t + 1] = y[c];
        weights[t + 1] = -(cycle[(p + 1) % cycle.length] - i);
        ys[t] = y[c];
        ones[t] = 1;
      }
      posted.add(new LinearInt(ys, ones, "<=", 1));
      posted.add(new LinearInt(vars, weights, "==", offset + i));
    }
    IntVar[] vars = new IntVar[y.length + 1];
    int[] weights = new int[y.length + 1];
    vars[0] = cost;
    weights[0] = 1;
    for (int c = 0; c < y.length; c++) {
      vars[c + 1] = y[c];
      weights[c + 1] = (int) -gain[c];
    }
    posted.add(new LinearInt(vars, weights, "==", (int) selfCost));
    for (Constraint c : posted) {
      c.setDegreeWeight(0);
      support.delayedConstraints.add(c);
    }
    if (support.options.debug()) {
      FzConsole.println("% bounded cycles: " + y.length + " cycles of at most " + k + " arcs");
    }
    return y.length;
  }

  private static int position(int[] cycle, int i) {
    for (int p = 0; p < cycle.length; p++) {
      if (cycle[p] == i) {
        return p;
      }
    }
    throw new IllegalStateException("vertex " + i + " not on its cycle");
  }

  // the cycles of 2..k arcs over the successor domains, each from its least vertex; false when
  // there are more than MAX_CYCLES
  private static boolean cycles(IntVar[] x, int offset, int k, List<int[]> out) {
    int n = x.length;
    int[] path = new int[k];
    for (int s = 0; s < n; s++) {
      path[0] = s;
      if (!extend(x, offset, k, path, 1, out)) {
        return false;
      }
    }
    return true;
  }

  private static boolean extend(
      IntVar[] x, int offset, int k, int[] path, int length, List<int[]> out) {
    int s = path[0];
    int last = path[length - 1];
    IntVar v = x[last];
    for (int j = s; j < x.length; j++) {
      if (j == last || !v.domain.contains(offset + j)) {
        continue;
      }
      if (j == s) {
        if (length >= 2) {
          out.add(Arrays.copyOf(path, length));
          if (out.size() > MAX_CYCLES) {
            return false;
          }
        }
        continue;
      }
      if (length == k || onPath(path, length, j)) {
        continue;
      }
      path[length] = j;
      if (!extend(x, offset, k, path, length + 1, out)) {
        return false;
      }
    }
    return true;
  }

  private static boolean onPath(int[] path, int length, int j) {
    for (int p = 0; p < length; p++) {
      if (path[p] == j) {
        return true;
      }
    }
    return false;
  }
}
