/*
 * CountStepCostBound.java
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
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * A lower bound on an objective that sums step costs of counts of values in one array.
 *
 * <p>The 2019 MiniZinc Challenge model ptv assigns every passenger a service, counts the passengers
 * of each service at each station ({@code count(p_st, s, pax[s, st])} over the passengers on the
 * train at station st) and pays a step cost per count, {@code if pax < 265 then 0 elseif pax < 529
 * then 10 ...}, flattened as {@code jacop_if_then_else_int} over {@code int_le_reif(pax, k)}. Each
 * count alone may stay below the first step, so the bounds of the cost terms add up to 0; but the
 * passengers on the train at a station must go somewhere, and on pax_period_20_5a five stations
 * cannot keep all their counts below 265. Neither the propagators nor the learnt clauses see that
 * (the optimum 50 is found within two minutes and not proved in 1200 s, while CP-SAT proves it in 2
 * s).
 *
 * <p>For every array whose counted values have such step costs in the objective, the least cost of
 * the counts over the assignments of the array's variables is found by a branch and bound over the
 * step of each count, with a transportation (maximum flow) check that the variables, grouped by
 * their domains, fit under the chosen count limits. The sum of the arrays' least costs bounds the
 * objective: it is posted as {@code objective = sum(s_a) + rest} with {@code s_a} the cost of array
 * a, at least its least cost. Different arrays have different count variables, so their costs add
 * up. This is the bound of a separable concave cost over a transportation polytope of the counts
 * (G. M. Guisewite and P. M. Pardalos, Minimum concave-cost network flow problems: applications,
 * complexity, and algorithms, Annals of Operations Research 25, 1990), computed exactly on the
 * small step functions met in practice.
 *
 * <p>The system property {@code org.jacop.fz.countStepCost=false} turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class CountStepCostBound {

  /** At most this many maximum flow checks over the whole model. */
  static final int MAX_CHECKS = 50_000;

  /** The constraints that state a step cost. */
  private static final Set<String> STEP_KINDS = Set.of("jacop_if_then_else_int");

  /** At most this many counted values with a cost in one array. */
  static final int MAX_COUNTS = 16;

  /** At most this many kinds of variables (by the counted values they can take) in one array. */
  static final int MAX_CLASSES = 200;

  private final Support support;

  private int checks;

  /**
   * A step cost: cost[i] while the count is above limit[i - 1] and at most limit[i]; the last limit
   * is unbounded. The search relaxes the step to a count of at most limit[i] at cost[i]: the steps
   * of an optimal assignment are among the choices, so the least choice is at most the optimum (and
   * equal to it when the costs grow with the count).
   */
  private static final class Step {
    private final IntVar count;
    private final long[] limit;
    private final long[] cost;

    Step(IntVar count, long[] limit, long[] cost) {
      this.count = count;
      this.limit = limit;
      this.cost = cost;
    }
  }

  /** A counted value of an array with the weighted step cost of its count. */
  private static final class Counted {
    private final int value;
    private final Step step;
    private final long weight;
    private final IntVar term;

    Counted(int value, Step step, long weight, IntVar term) {
      this.value = value;
      this.step = step;
      this.weight = weight;
      this.term = term;
    }
  }

  /**
   * It creates the bound reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public CountStepCostBound(Support support) {
    this.support = support;
  }

  /**
   * It tells if the bound is on.
   *
   * @return false if the system property org.jacop.fz.countStepCost is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.countStepCost"));
  }

  /**
   * It finds the step costs of counts in the objective and posts their bound.
   *
   * @param astTree the root of the parsed model.
   * @param skipped constraint nodes that are not posted.
   * @param objective the objective variable, or null.
   * @return the bound posted on the counted terms, 0 if none.
   */
  public long detect(SimpleNode astTree, Set<SimpleNode> skipped, IntVar objective) {
    // a step cost is read from an if-then-else: without one the pass finds nothing
    if (objective == null || !support.hasConstraint(astTree, STEP_KINDS)) {
      return 0;
    }
    List<ASTConstElem> all = FzItems.constraints(astTree, skipped);
    Map<IntVar, long[]> reified = new IdentityHashMap<>();
    Map<IntVar, IntVar> reifiedVar = new IdentityHashMap<>();
    for (ASTConstElem c : all) {
      if (c.getName().equals("int_le_reif")
          && ((ASTScalarFlatExpr) c.jjtGetChild(1)).getType() == 0) {
        IntVar b = support.getVariable((ASTScalarFlatExpr) c.jjtGetChild(2));
        reified.put(b, new long[] {support.getInt((ASTScalarFlatExpr) c.jjtGetChild(1))});
        reifiedVar.put(b, support.getVariable((ASTScalarFlatExpr) c.jjtGetChild(0)));
      }
    }
    Map<IntVar, Step> steps = new IdentityHashMap<>();
    for (ASTConstElem c : all) {
      if (c.getName().equals("jacop_if_then_else_int")) {
        IntVar y = support.getVariable((ASTScalarFlatExpr) c.jjtGetChild(2));
        Step s =
            step(
                support.getVarArray((SimpleNode) c.jjtGetChild(0)),
                support.getIntArray((SimpleNode) c.jjtGetChild(1)),
                reified,
                reifiedVar);
        if (s != null) {
          steps.put(y, s);
        }
      }
    }
    if (steps.isEmpty()) {
      return 0;
    }
    Map<IntVar, Long> weights = new IdentityHashMap<>();
    ASTConstElem row = objectiveRow(all, objective, weights);
    if (row == null) {
      return 0;
    }
    // the counts of each array, by the array's variables
    Map<List<IntVar>, List<Counted>> arrays = new LinkedHashMap<>();
    Map<IntVar, Step> byCount = new IdentityHashMap<>();
    Map<IntVar, IntVar> termOf = new IdentityHashMap<>();
    // a count with two step costs (fixed counts and costs may be one shared variable) is left out
    Map<IntVar, Boolean> ambiguous = new IdentityHashMap<>();
    for (Map.Entry<IntVar, Step> e : steps.entrySet()) {
      Long w = weights.get(e.getKey());
      IntVar count = e.getValue().count;
      if (w == null || w <= 0 || e.getKey().singleton()) {
        continue;
      }
      if (byCount.put(count, e.getValue()) != null) {
        ambiguous.put(count, true);
      }
      termOf.put(count, e.getKey());
    }
    for (IntVar count : ambiguous.keySet()) {
      byCount.remove(count);
    }
    for (ASTConstElem c : all) {
      if (c.getName().equals("jacop_count")
          && ((ASTScalarFlatExpr) c.jjtGetChild(1)).getType() == 0) {
        IntVar count = support.getVariable((ASTScalarFlatExpr) c.jjtGetChild(2));
        Step s = count.singleton() ? null : byCount.remove(count);
        if (s != null) {
          IntVar term = termOf.get(count);
          List<IntVar> xs = List.of(support.getVarArray((SimpleNode) c.jjtGetChild(0)));
          arrays
              .computeIfAbsent(xs, k -> new ArrayList<>())
              .add(
                  new Counted(
                      support.getInt((ASTScalarFlatExpr) c.jjtGetChild(1)),
                      s,
                      weights.get(term),
                      term));
        }
      }
    }
    long total = 0;
    long individual = 0;
    List<IntVar> sums = new ArrayList<>();
    Map<IntVar, Boolean> covered = new IdentityHashMap<>();
    for (Map.Entry<List<IntVar>, List<Counted>> e : arrays.entrySet()) {
      List<Counted> counted = e.getValue();
      if (counted.size() > MAX_COUNTS || !distinctValues(counted)) {
        continue;
      }
      long least = least(e.getKey(), counted);
      long alone = 0;
      for (Counted k : counted) {
        alone += k.weight * k.term.min();
      }
      if (least <= alone) {
        continue;
      }
      IntVar[] vars = new IntVar[counted.size() + 1];
      int[] as = new int[vars.length];
      long max = 0;
      for (int i = 0; i < counted.size(); i++) {
        vars[i] = counted.get(i).term;
        as[i] = (int) counted.get(i).weight;
        max += counted.get(i).weight * counted.get(i).term.max();
        covered.put(vars[i], true);
      }
      if (max > IntDomain.MAX_INT) {
        continue;
      }
      IntVar sum = new IntVar(support.store, (int) least, (int) max);
      vars[counted.size()] = sum;
      as[counted.size()] = -1;
      post(new LinearInt(vars, as, "==", 0));
      sums.add(sum);
      total += least;
      individual += alone;
    }
    if (sums.isEmpty()) {
      return 0;
    }
    postObjectiveRow(row, objective, weights, covered, sums);
    if (support.options.debug()) {
      FzConsole.println(
          "% count step cost bound: "
              + sums.size()
              + " arrays, bound "
              + total
              + " on terms bounded by "
              + individual);
    }
    return total;
  }

  // the step function of if c[0] then x[0] elseif ... else x[n-1] with c[i] = (v <= k[i])
  private static Step step(
      IntVar[] conditions, int[] values, Map<IntVar, long[]> reified, Map<IntVar, IntVar> on) {
    int n = conditions.length;
    if (values == null || n < 2 || values.length != n || !conditions[n - 1].singleton()) {
      return null;
    }
    if (conditions[n - 1].value() != 1) {
      return null;
    }
    IntVar v = null;
    long[] limit = new long[n];
    long[] cost = new long[n];
    for (int i = 0; i < n; i++) {
      cost[i] = values[i];
      if (i == n - 1) {
        limit[i] = Long.MAX_VALUE;
        break;
      }
      long[] k = reified.get(conditions[i]);
      if (k == null || v != null && on.get(conditions[i]) != v || i > 0 && k[0] <= limit[i - 1]) {
        return null;
      }
      v = on.get(conditions[i]);
      limit[i] = k[0];
    }
    return new Step(v, limit, cost);
  }

  // the int_lin_eq that defines the objective with coefficient +-1, and the objective's weight of
  // each other variable in it
  private ASTConstElem objectiveRow(
      List<ASTConstElem> all, IntVar objective, Map<IntVar, Long> weights) {
    for (ASTConstElem c : all) {
      if (!c.getName().equals("int_lin_eq")) {
        continue;
      }
      int[] a = support.getIntArray((SimpleNode) c.jjtGetChild(0));
      IntVar[] x = support.getVarArray((SimpleNode) c.jjtGetChild(1));
      int at = -1;
      for (int i = 0; i < x.length; i++) {
        if (x[i] == objective) {
          at = at < 0 && Math.abs(a[i]) == 1 ? i : -2;
        }
      }
      if (at < 0) {
        continue;
      }
      for (int i = 0; i < x.length; i++) {
        if (i != at) {
          // objective = (r - sum a_t t) / a_o
          weights.merge(x[i], (long) -a[i] * a[at], Long::sum);
        }
      }
      return c;
    }
    return null;
  }

  // objective = r * a_o + sum over the other terms, with the counted terms replaced by the sums
  private void postObjectiveRow(
      ASTConstElem row,
      IntVar objective,
      Map<IntVar, Long> weights,
      Map<IntVar, Boolean> covered,
      List<IntVar> sums) {
    int[] a = support.getIntArray((SimpleNode) row.jjtGetChild(0));
    IntVar[] x = support.getVarArray((SimpleNode) row.jjtGetChild(1));
    long r = support.getInt((ASTScalarFlatExpr) row.jjtGetChild(2));
    long ao = 0;
    for (int i = 0; i < x.length; i++) {
      if (x[i] == objective) {
        ao = a[i];
      }
    }
    List<IntVar> vars = new ArrayList<>();
    List<Long> as = new ArrayList<>();
    vars.add(objective);
    as.add(1L);
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    for (IntVar t : x) {
      if (t != objective && !covered.containsKey(t) && seen.put(t, true) == null) {
        vars.add(t);
        as.add(-weights.get(t));
      }
    }
    for (IntVar s : sums) {
      vars.add(s);
      as.add(-1L);
    }
    int[] coefficients = new int[as.size()];
    for (int i = 0; i < coefficients.length; i++) {
      coefficients[i] = Math.toIntExact(as.get(i));
    }
    post(new LinearInt(vars.toArray(new IntVar[0]), coefficients, "==", Math.toIntExact(r * ao)));
  }

  private void post(LinearInt c) {
    c.setDegreeWeight(0);
    support.delayedConstraints.add(c);
  }

  private static boolean distinctValues(List<Counted> counted) {
    long[] values = counted.stream().mapToLong(k -> k.value).sorted().toArray();
    for (int i = 1; i < values.length; i++) {
      if (values[i] == values[i - 1]) {
        return false;
      }
    }
    return true;
  }

  // the least weighted cost of the counts over the assignments of xs, or Long.MIN_VALUE when the
  // budget of checks runs out
  private long least(List<IntVar> xs, List<Counted> counted) {
    int m = counted.size();
    Map<Integer, Integer> column = new HashMap<>();
    for (int j = 0; j < m; j++) {
      column.put(counted.get(j).value, j);
    }
    // the variables by the counted values they can take and whether they can take another one
    Map<String, int[]> classes = new LinkedHashMap<>();
    Map<String, Integer> sizes = new HashMap<>();
    for (IntVar x : xs) {
      boolean[] in = new boolean[m + 1];
      for (ValueEnumeration en = x.dom().valueEnumeration(); en.hasMoreElements(); ) {
        Integer j = column.get(en.nextElement());
        in[j == null ? m : j] = true;
      }
      String key = Arrays.toString(in);
      classes.computeIfAbsent(key, k -> columns(in));
      sizes.merge(key, 1, Integer::sum);
    }
    if (classes.size() > MAX_CLASSES) {
      return Long.MIN_VALUE;
    }
    int[][] adjacency = classes.values().toArray(new int[0][]);
    int[] count = new int[adjacency.length];
    int c = 0;
    for (String key : classes.keySet()) {
      count[c++] = sizes.get(key);
    }
    long[] caps = new long[m];
    for (int j = 0; j < m; j++) {
      caps[j] = counted.get(j).step.count.max();
    }
    long[] best = {Long.MAX_VALUE};
    search(0, 0, caps, counted, adjacency, count, best);
    return best[0] == Long.MAX_VALUE ? Long.MIN_VALUE : best[0];
  }

  private static int[] columns(boolean[] in) {
    int n = 0;
    for (boolean b : in) {
      n += b ? 1 : 0;
    }
    int[] out = new int[n];
    n = 0;
    for (int j = 0; j < in.length; j++) {
      if (in[j]) {
        out[n++] = j;
      }
    }
    return out;
  }

  // branch and bound over the step of each count, from the cheapest
  private void search(
      int j,
      long cost,
      long[] caps,
      List<Counted> counted,
      int[][] adjacency,
      int[] count,
      long[] best) {
    if (cost >= best[0] || checks >= MAX_CHECKS) {
      return;
    }
    checks++;
    if (!fits(caps, adjacency, count)) {
      return;
    }
    if (j == counted.size()) {
      best[0] = cost;
      return;
    }
    Counted k = counted.get(j);
    Step s = k.step;
    long max = caps[j];
    for (int i = 0; i < s.limit.length; i++) {
      long below = i == 0 ? Long.MIN_VALUE : s.limit[i - 1];
      if (below >= s.count.max() || s.limit[i] < s.count.min()) {
        continue;
      }
      caps[j] = Math.min(max, s.limit[i]);
      search(j + 1, cost + k.weight * s.cost[i], caps, counted, adjacency, count, best);
    }
    caps[j] = max;
    if (checks >= MAX_CHECKS) {
      best[0] = Long.MAX_VALUE;
    }
  }

  // every variable gets a value: a flow of all of them through the counts under their caps (the
  // last column, the values without a cost, takes any number)
  private static boolean fits(long[] caps, int[][] adjacency, int[] count) {
    int m = caps.length;
    int n = adjacency.length;
    // nodes: 0 source, 1..n classes, n+1..n+m+1 columns, n+m+2 sink
    int nodes = n + m + 3;
    long[][] residual = new long[nodes][nodes];
    int sink = nodes - 1;
    long need = 0;
    for (int i = 0; i < n; i++) {
      residual[0][1 + i] = count[i];
      need += count[i];
      for (int j : adjacency[i]) {
        residual[1 + i][1 + n + j] = count[i];
      }
    }
    for (int j = 0; j < m; j++) {
      residual[1 + n + j][sink] = Math.max(0, caps[j]);
    }
    residual[1 + n + m][sink] = need;
    long flow = 0;
    int[] parent = new int[nodes];
    int[] queue = new int[nodes];
    while (flow < need) {
      Arrays.fill(parent, -1);
      parent[0] = 0;
      int head = 0;
      int tail = 0;
      queue[tail++] = 0;
      while (head < tail && parent[sink] < 0) {
        int u = queue[head++];
        for (int w = 0; w < nodes; w++) {
          if (parent[w] < 0 && residual[u][w] > 0) {
            parent[w] = u;
            queue[tail++] = w;
          }
        }
      }
      if (parent[sink] < 0) {
        return false;
      }
      long b = Long.MAX_VALUE;
      for (int w = sink; w != 0; w = parent[w]) {
        b = Math.min(b, residual[parent[w]][w]);
      }
      for (int w = sink; w != 0; w = parent[w]) {
        residual[parent[w]][w] -= b;
        residual[w][parent[w]] += b;
      }
      flow += b;
    }
    return true;
  }
}
