/*
 * CircuitCostDetector.java
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
import org.jacop.constraints.CircuitCost;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.CostAlldifferent;
import org.jacop.constraints.CostGCC;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.SubcircuitCost;
import org.jacop.constraints.SubcircuitCostPair;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds circuits and subcircuits whose cost is a sum of arc costs and posts {@link CircuitCost}
 * or {@link SubcircuitCost} on them as a redundant constraint. MiniZinc models write such a cost as
 * {@code circuit(x) /\ cost = sum(i)(d[i, x[i]])}, which is flattened into a circuit on x, one
 * element constraint with a constant row of d for each x[i], and a linear constraint summing the
 * element values. All these constraints are still posted as usual, so the new constraint only adds
 * pruning.
 *
 * <p>The linear constraint has one element value for each x[i], with any coefficient, and may also
 * have reified tests {@code x[i] = v} or {@code x[i] != v} (the penalty of a node left out of a
 * subcircuit, {@code penalty[i] * (x[i] = i)}), which are folded into the arc costs. It is either
 * an equation with one more variable, which is then the cost, or an inequality {@code sum <= c},
 * whose sum gets a new cost variable with that upper bound (a length budget).
 *
 * <p>On a subcircuit, a sum with an element value for each x[i] is also weighed against each other
 * sum, which may consist of tests only (a prize {@code sum(i)(gold[i] * (x[i] != i))} collected
 * within a length budget), by a {@link SubcircuitCostPair}. The pairs are off under lazy clause
 * generation; the system property {@code org.jacop.fz.circuitCostPair} set to true or false
 * overrides that.
 *
 * <p>The same sums over the variables of an all-different, an inverse or a global cardinality
 * constraint, {@code alldifferent(x) /\ cost = sum(i)(c[i, x[i]])}, get a {@link CostAlldifferent}
 * (the assignment problem) or a {@link CostGCC} (a minimum cost flow), unless the variables are
 * already those of a circuit.
 *
 * <p>Setting the system property {@code org.jacop.fz.circuitCost} to false turns the detection off,
 * and {@code org.jacop.fz.costAlldifferent} set to false turns off only the all-different and
 * global cardinality part.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CircuitCostDetector implements ParserTreeConstants {

  // the most pairs of sums weighed against each other on one subcircuit
  private static final int MAX_PAIRS = 2;

  // the largest cost matrix (variables times values) of an all-different or a GCC
  private static final int MAX_MATRIX = 250_000;

  private final Support support;

  // the element value variable of each index variable with a constant array
  private final Map<IntVar, Element> elements = new IdentityHashMap<>();

  // the test x = v or x != v that each reified 0/1 variable stands for
  private final Map<IntVar, Test> tests = new IdentityHashMap<>();

  private final List<Target> targets = new ArrayList<>();

  private final List<SimpleNode> linears = new ArrayList<>();

  // an element constraint value = array[index - firstIndex] with a constant array
  // (classes rather than records with array components, which would compare the arrays by identity)
  private static final class Element {
    final IntVar value;
    final int[] array;
    final int firstIndex;

    Element(IntVar value, int[] array, int firstIndex) {
      this.value = value;
      this.array = array;
      this.firstIndex = firstIndex;
    }
  }

  // b = (x = value), or b = (x != value) when equal is false
  private record Test(IntVar x, int value, boolean equal) {}

  private enum Kind {
    CIRCUIT,
    SUBCIRCUIT,
    ALLDIFFERENT,
    GCC
  }

  // the variables of a circuit, a subcircuit, an all-different or a GCC, whose m values are
  // offset..offset + m - 1; a GCC has the counters of its values, or null for a value that is not
  // counted
  private static final class Target {
    final IntVar[] x;
    final Kind kind;
    int offset;
    int m;
    int[] values;
    IntVar[] counters;

    Target(IntVar[] x, Kind kind, int offset) {
      this.x = x;
      this.kind = kind;
      this.offset = offset;
      this.m = x.length;
    }

    boolean sub() {
      return kind == Kind.SUBCIRCUIT;
    }

    boolean circuit() {
      return kind == Kind.CIRCUIT || kind == Kind.SUBCIRCUIT;
    }
  }

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public CircuitCostDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.circuitCost is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.circuitCost"));
  }

  private static boolean alldifferentEnabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.costAlldifferent"));
  }

  // the pairs are on by default except under lazy clause generation, where their generic
  // explanations cost more than they prune; org.jacop.fz.circuitCostPair=true or false decides
  private boolean pairsEnabled() {
    String property = System.getProperty("org.jacop.fz.circuitCostPair");
    if (property == null) {
      return !support.options.lcg();
    }
    return "true".equalsIgnoreCase(property);
  }

  /**
   * It scans the constraint items of the model and posts a CircuitCost or a SubcircuitCost for each
   * circuit or subcircuit whose successors have arc costs summed in a linear constraint, and a
   * CostAlldifferent or a CostGCC for each all-different or GCC whose variables do.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    Support.forEachConstraint(astTree, this::collect);
    if (targets.isEmpty() || elements.isEmpty() || linears.isEmpty()) {
      return;
    }
    List<Target> circuits = new ArrayList<>();
    for (Target t : targets) {
      if (t.circuit()) {
        circuits.add(t);
      }
    }
    for (Target t : targets) {
      if (t.circuit() || alldifferentEnabled() && values(t, circuits)) {
        post(t);
      }
    }
  }

  // the values of an all-different or a GCC that is not on the variables of a circuit
  private boolean values(Target t, List<Target> circuits) {
    for (Target c : circuits) {
      if (Arrays.equals(c.x, t.x)) {
        return false;
      }
    }
    int n = t.x.length;
    if (n < 2) {
      return false;
    }
    long lo = Long.MAX_VALUE;
    long hi = Long.MIN_VALUE;
    for (IntVar v : t.x) {
      lo = Math.min(lo, v.min());
      hi = Math.max(hi, v.max());
    }
    long m = hi - lo + 1;
    if (t.kind == Kind.ALLDIFFERENT && m < n || m * n > MAX_MATRIX) {
      return false;
    }
    t.offset = (int) lo;
    t.m = (int) m;
    if (t.kind == Kind.GCC) {
      IntVar[] counters = new IntVar[t.m];
      for (int k = 0; k < t.values.length; k++) {
        long j = (long) t.values[k] - lo;
        if (j >= 0 && j < m) {
          if (counters[(int) j] != null) {
            // a value counted twice
            return false;
          }
          counters[(int) j] = t.counters[k];
        }
      }
      t.counters = counters;
    }
    return true;
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_circuit" ->
          targets.add(new Target(support.getVarArray(child(node, 0)), Kind.CIRCUIT, 1));
      case "jacop_circuit_offset" ->
          targets.add(
              new Target(
                  support.getVarArray(child(node, 0)),
                  Kind.CIRCUIT,
                  support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1))));
      case "jacop_subcircuit" ->
          targets.add(new Target(support.getVarArray(child(node, 0)), Kind.SUBCIRCUIT, 1));
      case "jacop_alldiff" -> alldifferent(support.getVarArray(child(node, 0)));
      case "jacop_assignment" -> {
        alldifferent(support.getVarArray(child(node, 0)));
        alldifferent(support.getVarArray(child(node, 1)));
      }
      case "jacop_count_values" ->
          gcc(
              support.getVarArray(child(node, 0)),
              support.getIntArray(child(node, 1)),
              support.getVarArray(child(node, 2)));
      case "jacop_count_values_bounds" -> {
        int[] low = support.getIntArray(child(node, 2));
        int[] up = support.getIntArray(child(node, 3));
        IntVar[] counters = new IntVar[low.length];
        for (int k = 0; k < low.length && low[k] <= up[k]; k++) {
          counters[k] = new IntVar(support.store, low[k], up[k]);
        }
        gcc(support.getVarArray(child(node, 0)), support.getIntArray(child(node, 1)), counters);
      }
      case "jacop_gcc" -> {
        IntVar[] counters = support.getVarArray(child(node, 1));
        int first = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        int[] values = new int[counters.length];
        for (int k = 0; k < values.length; k++) {
          values[k] = first + k;
        }
        gcc(support.getVarArray(child(node, 0)), values, counters);
      }
      case "array_int_element" -> element(node, support.getIntArray(child(node, 1)), 1);
      case "array_var_int_element" -> element(node, constants(child(node, 1)), 1);
      case "jacop_array_var_int_element_nonshifted" ->
          element(
              node,
              constants(child(node, 1)),
              support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
      case "int_eq_reif" -> test(node, true);
      case "int_ne_reif" -> test(node, false);
      case "int_lin_eq", "int_lin_le" -> linears.add(node);
      default -> {
        // not part of a circuit cost
      }
    }
  }

  private void alldifferent(IntVar[] x) {
    if (!hasDuplicates(x)) {
      targets.add(new Target(x, Kind.ALLDIFFERENT, 0));
    }
  }

  private void gcc(IntVar[] x, int[] values, IntVar[] counters) {
    if (values == null || values.length != counters.length || hasDuplicates(x)) {
      return;
    }
    for (IntVar c : counters) {
      if (c == null) {
        return;
      }
    }
    Target t = new Target(x, Kind.GCC, 0);
    t.values = values;
    t.counters = counters;
    targets.add(t);
  }

  private static boolean hasDuplicates(IntVar[] x) {
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    for (IntVar v : x) {
      if (seen.put(v, Boolean.TRUE) != null) {
        return true;
      }
    }
    return false;
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  // the values of an array of constants, or an empty array if one of them is a variable
  private int[] constants(SimpleNode node) {
    IntVar[] vars = support.getVarArray(node);
    int[] values = new int[vars.length];
    for (int i = 0; i < vars.length; i++) {
      if (!vars[i].singleton()) {
        return new int[0];
      }
      values[i] = vars[i].value();
    }
    return values;
  }

  private void element(ASTConstElem node, int[] array, int firstIndex) {
    if (array == null || array.length == 0) {
      return;
    }
    IntVar index = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar value = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (!index.singleton()) {
      elements.putIfAbsent(index, new Element(value, array, firstIndex));
    }
  }

  private void test(ASTConstElem node, boolean equal) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    Test t = null;
    if (p2.getType() == 0 && p1.getType() != 0) {
      t = new Test(support.getVariable(p1), support.getInt(p2), equal);
    } else if (p1.getType() == 0 && p2.getType() != 0) {
      t = new Test(support.getVariable(p2), support.getInt(p1), equal);
    }
    if (t != null && !b.singleton() && !t.x.singleton()) {
      tests.putIfAbsent(b, t);
    }
  }

  private void post(Target c) {
    int n = c.x.length;
    int m = c.m;
    Map<IntVar, Integer> rowOfValue = new IdentityHashMap<>();
    Map<IntVar, Integer> rowOfSuccessor = new IdentityHashMap<>();
    int[][] arcCosts = new int[n][m];
    int fixed = 0;
    for (int i = 0; i < n; i++) {
      Element e = elements.get(c.x[i]);
      if (e == null && c.x[i].singleton()) {
        // a fixed successor has a constant arc cost, which the linear constraint has as a constant,
        // so its row stays zero
        fixed++;
        continue;
      }
      if (e == null
          || rowOfValue.put(e.value, i) != null
          || rowOfSuccessor.put(c.x[i], i) != null) {
        return;
      }
      for (int j = 0; j < m; j++) {
        // a value without a cost is out of the element's index range, so the element removes it
        int k = c.offset + j - e.firstIndex;
        arcCosts[i][j] = k >= 0 && k < e.array.length ? e.array[k] : 0;
      }
    }
    List<Sum> sums = new ArrayList<>();
    boolean anyEquation = false;
    for (SimpleNode node : linears) {
      Sum sum = sumOf(node, c, arcCosts, fixed, rowOfValue, rowOfSuccessor);
      if (sum != null) {
        sums.add(sum);
        anyEquation |= sum.full && sum.equation;
      }
    }
    for (Sum sum : sums) {
      // an all-different or a GCC with a cost equation leaves out the bounds on the same sum, such
      // as a redundant lower bound in the model, since each one is a whole network flow
      if (!sum.full || !c.circuit() && anyEquation && !sum.equation) {
        continue;
      }
      List<Constraint> posted = new ArrayList<>();
      if (sum.link != null) {
        posted.add(sum.link);
      }
      switch (c.kind) {
        case SUBCIRCUIT -> posted.add(new SubcircuitCost(c.x, sum.costs, sum.cost, c.offset));
        case CIRCUIT -> posted.add(new CircuitCost(c.x, sum.costs, sum.cost, c.offset));
        case ALLDIFFERENT -> posted.add(new CostAlldifferent(c.x, sum.costs, sum.cost, c.offset));
        case GCC -> {
          CostGCC gcc = new CostGCC(c.x, sum.costs, counters(c), sum.cost, c.offset);
          if (support.options.debug()) {
            FzConsole.println("% redundant " + gcc);
          }
          posted.addAll(gcc.decompose(support.store));
        }
      }
      for (Constraint cc : posted) {
        // redundant, so degree-based variable selections see the degrees of the model
        cc.setDegreeWeight(0);
        if (support.options.debug() && (c.kind != Kind.GCC || cc == sum.link)) {
          FzConsole.println("% redundant " + cc);
        }
        support.delayedConstraints.add(cc);
      }
    }
    if (c.sub() && pairsEnabled()) {
      postPairs(c, sums);
    }
  }

  // the counters of a GCC, with a new counter for each value that is not counted
  private IntVar[] counters(Target c) {
    IntVar[] counters = c.counters.clone();
    for (int j = 0; j < counters.length; j++) {
      if (counters[j] == null) {
        counters[j] = new IntVar(support.store, 0, c.x.length);
      }
    }
    return counters;
  }

  // a sum of arc costs, such as a length, weighed against each other sum, such as a prize
  private void postPairs(Target c, List<Sum> sums) {
    Sum first = null;
    for (Sum s : sums) {
      if (s.full) {
        first = s;
        break;
      }
    }
    if (first == null || c.x.length > SubcircuitCostPair.NODE_LIMIT) {
      return;
    }
    int pairs = 0;
    for (Sum s : sums) {
      if (s == first || s.cost == first.cost || pairs == MAX_PAIRS) {
        continue;
      }
      SubcircuitCostPair cc =
          new SubcircuitCostPair(c.x, first.costs, first.cost, s.costs, s.cost, c.offset);
      cc.setDegreeWeight(0);
      if (support.options.debug()) {
        FzConsole.println("% redundant " + cc);
      }
      support.delayedConstraints.add(cc);
      pairs++;
    }
  }

  // sum(a[k] * others[k]) + s = rhs, or <= rhs, with s the sum of the costs
  private Sum partialSum(
      long[][] costs, List<IntVar> others, List<Integer> coefficients, boolean equation, long rhs) {
    if (rhs < IntDomain.MIN_INT || rhs > IntDomain.MAX_INT) {
      return null;
    }
    int[][] result = toInt(costs);
    if (result == null) {
      return null;
    }
    long lo = 0;
    long hi = 0;
    for (int[] row : result) {
      int min = Integer.MAX_VALUE;
      int max = Integer.MIN_VALUE;
      for (int w : row) {
        min = Math.min(min, w);
        max = Math.max(max, w);
      }
      lo += min;
      hi += max;
    }
    if (lo < IntDomain.MIN_INT || hi > IntDomain.MAX_INT) {
      return null;
    }
    IntVar s = new IntVar(support.store, (int) lo, (int) hi);
    IntVar[] list = new IntVar[others.size() + 1];
    int[] weights = new int[list.length];
    for (int k = 0; k < others.size(); k++) {
      list[k] = others.get(k);
      weights[k] = coefficients.get(k);
    }
    list[others.size()] = s;
    weights[others.size()] = 1;
    Sum sum = new Sum(result, s, true);
    sum.equation = equation;
    sum.link = new LinearInt(list, weights, equation ? "==" : "<=", (int) rhs);
    return sum;
  }

  // the costs as ints, or null if one is too large
  private static int[][] toInt(long[][] costs) {
    int[][] result = new int[costs.length][];
    for (int i = 0; i < costs.length; i++) {
      result[i] = new int[costs[i].length];
      for (int j = 0; j < costs[i].length; j++) {
        long w = costs[i][j];
        if (w < Integer.MIN_VALUE / 4 || w > Integer.MAX_VALUE / 4) {
          return null;
        }
        result[i][j] = (int) w;
      }
    }
    return result;
  }

  // the arc costs of a linear constraint and the variable equal to their sum
  private static final class Sum {
    final int[][] costs;
    final IntVar cost;
    // every successor has its arc cost in the sum, not only tests
    final boolean full;
    // the linear constraint of the other terms and the cost, when the sum has other terms
    Constraint link;
    // the sum is equal to the cost, not at most it
    boolean equation;

    Sum(int[][] costs, IntVar cost, boolean full) {
      this.costs = costs;
      this.cost = cost;
      this.full = full;
    }
  }

  /*
   * The linear constraint sum(a[k] * vars[k]) = rhs or <= rhs as costs[i][x[i]] summed over i: one
   * element value of every x[i], tests of the x[i] and constants, plus for an equation one more
   * variable with coefficient 1 or -1, which is the cost.
   */
  private Sum sumOf(
      SimpleNode node,
      Target c,
      int[][] arcCosts,
      int fixed,
      Map<IntVar, Integer> rowOfValue,
      Map<IntVar, Integer> rowOfSuccessor) {
    boolean equation = "int_lin_eq".equals(((ASTConstElem) node).getName());
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] vars = support.getVarArray(child(node, 1));
    if (a == null || a.length != vars.length) {
      return null;
    }
    int n = c.x.length;
    int m = c.m;
    long rhs = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    long[][] costs = new long[n][m];
    boolean[] seen = new boolean[n];
    int found = 0;
    int tested = 0;
    IntVar rest = null;
    int restCoefficient = 0;
    // the terms that are not costs, tests or constants
    List<IntVar> others = new ArrayList<>();
    List<Integer> otherCoefficients = new ArrayList<>();
    for (int k = 0; k < vars.length; k++) {
      IntVar v = vars[k];
      Integer row = rowOfValue.get(v);
      Test t = tests.get(v);
      Integer testRow = t == null ? null : rowOfSuccessor.get(t.x);
      if (row != null && !seen[row]) {
        seen[row] = true;
        found++;
        for (int j = 0; j < m; j++) {
          costs[row][j] += (long) a[k] * arcCosts[row][j];
        }
      } else if (testRow != null) {
        tested++;
        for (int j = 0; j < m; j++) {
          if ((c.offset + j == t.value) == t.equal) {
            costs[testRow][j] += a[k];
          }
        }
      } else if (v.singleton()) {
        rhs -= (long) a[k] * v.value();
      } else {
        if (rest == null && !rowOfSuccessor.containsKey(v)) {
          rest = v;
          restCoefficient = a[k];
        }
        others.add(v);
        otherCoefficients.add(a[k]);
      }
    }
    boolean full = found + fixed == n;
    if (!full && found + tested == 0) {
      return null;
    }
    if (others.size() > 1
        || !others.isEmpty() && (rest == null || !equation || Math.abs(restCoefficient) != 1)) {
      // other terms, such as fixed costs: an all-different or a GCC gets a new variable for its
      // part of the sum and a linear constraint of that variable and the other terms
      return c.circuit() || !full
          ? null
          : partialSum(costs, others, otherCoefficients, equation, rhs);
    }

    IntVar cost;
    if (!equation) {
      if (rest != null) {
        return null;
      }
      // sum <= rhs: a new variable for the sum, at most rhs
      long lo = 0;
      for (long[] row : costs) {
        long min = Long.MAX_VALUE;
        for (long w : row) {
          min = Math.min(min, w);
        }
        lo += min;
      }
      long hi = Math.min(rhs, IntDomain.MAX_INT);
      lo = Math.max(Math.min(lo, hi), IntDomain.MIN_INT);
      if (hi < IntDomain.MIN_INT) {
        return null;
      }
      cost = new IntVar(support.store, (int) lo, (int) hi);
    } else if (rest == null) {
      if (rhs < IntDomain.MIN_INT || rhs > IntDomain.MAX_INT) {
        return null;
      }
      cost = new IntVar(support.store, (int) rhs, (int) rhs);
      rhs = 0;
    } else if (restCoefficient == -1) {
      // sum - cost = rhs, so cost = sum - rhs
      cost = rest;
      rhs = -rhs;
    } else if (restCoefficient == 1) {
      // sum + cost = rhs, so cost = rhs - sum
      cost = rest;
      for (long[] row : costs) {
        for (int j = 0; j < m; j++) {
          row[j] = -row[j];
        }
      }
    } else {
      return null;
    }
    // the constant goes to the first row, which every circuit and subcircuit pays exactly once
    if (rest != null) {
      for (int j = 0; j < m; j++) {
        costs[0][j] += rhs;
      }
    }
    int[][] result = toInt(costs);
    if (result == null) {
      return null;
    }
    Sum sum = new Sum(result, cost, full);
    sum.equation = equation;
    return sum;
  }
}
