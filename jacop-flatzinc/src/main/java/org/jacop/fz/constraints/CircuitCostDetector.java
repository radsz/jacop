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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.CircuitCost;
import org.jacop.constraints.Constraint;
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
 * <p>Setting the system property {@code org.jacop.fz.circuitCost} to false turns the detection off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CircuitCostDetector implements ParserTreeConstants {

  // the most pairs of sums weighed against each other on one subcircuit
  private static final int MAX_PAIRS = 2;

  private final Support support;

  // the element value variable of each index variable with a constant array
  private final Map<IntVar, Element> elements = new IdentityHashMap<>();

  // the test x = v or x != v that each reified 0/1 variable stands for
  private final Map<IntVar, Test> tests = new IdentityHashMap<>();

  private final List<Circuit> circuits = new ArrayList<>();

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

  // a circuit, or a subcircuit, on x whose values are numbered from offset
  private static final class Circuit {
    final IntVar[] x;
    final int offset;
    final boolean sub;

    Circuit(IntVar[] x, int offset, boolean sub) {
      this.x = x;
      this.offset = offset;
      this.sub = sub;
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
   * circuit or subcircuit whose successors have arc costs summed in a linear constraint.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    Support.forEachConstraint(astTree, this::collect);
    if (circuits.isEmpty() || elements.isEmpty() || linears.isEmpty()) {
      return;
    }
    for (Circuit c : circuits) {
      post(c);
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_circuit" ->
          circuits.add(new Circuit(support.getVarArray(child(node, 0)), 1, false));
      case "jacop_circuit_offset" ->
          circuits.add(
              new Circuit(
                  support.getVarArray(child(node, 0)),
                  support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1)),
                  false));
      case "jacop_subcircuit" ->
          circuits.add(new Circuit(support.getVarArray(child(node, 0)), 1, true));
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

  private void post(Circuit c) {
    int n = c.x.length;
    Map<IntVar, Integer> rowOfValue = new IdentityHashMap<>();
    Map<IntVar, Integer> rowOfSuccessor = new IdentityHashMap<>();
    int[][] arcCosts = new int[n][n];
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
      for (int j = 0; j < n; j++) {
        // a value without a cost is out of the element's index range, so the element removes it
        int k = c.offset + j - e.firstIndex;
        arcCosts[i][j] = k >= 0 && k < e.array.length ? e.array[k] : 0;
      }
    }
    List<Sum> sums = new ArrayList<>();
    for (SimpleNode node : linears) {
      Sum sum = sumOf(node, c, arcCosts, fixed, rowOfValue, rowOfSuccessor);
      if (sum == null) {
        continue;
      }
      sums.add(sum);
      if (!sum.full) {
        continue;
      }
      Constraint cc;
      if (c.sub) {
        cc = new SubcircuitCost(c.x, sum.costs, sum.cost, c.offset);
      } else {
        cc = new CircuitCost(c.x, sum.costs, sum.cost, c.offset);
      }
      // redundant, so degree-based variable selections see the degrees of the model
      cc.setDegreeWeight(0);
      if (support.options.debug()) {
        FzConsole.println("% redundant " + cc);
      }
      support.delayedConstraints.add(cc);
    }
    if (c.sub && pairsEnabled()) {
      postPairs(c, sums);
    }
  }

  // a sum of arc costs, such as a length, weighed against each other sum, such as a prize
  private void postPairs(Circuit c, List<Sum> sums) {
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

  // the arc costs of a linear constraint and the variable equal to their sum
  private static final class Sum {
    final int[][] costs;
    final IntVar cost;
    // every successor has its arc cost in the sum, not only tests
    final boolean full;

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
      Circuit c,
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
    long rhs = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    long[][] costs = new long[n][n];
    boolean[] seen = new boolean[n];
    int found = 0;
    int tested = 0;
    IntVar rest = null;
    int restCoefficient = 0;
    for (int k = 0; k < vars.length; k++) {
      IntVar v = vars[k];
      Integer row = rowOfValue.get(v);
      Test t = tests.get(v);
      Integer testRow = t == null ? null : rowOfSuccessor.get(t.x);
      if (row != null && !seen[row]) {
        seen[row] = true;
        found++;
        for (int j = 0; j < n; j++) {
          costs[row][j] += (long) a[k] * arcCosts[row][j];
        }
      } else if (testRow != null) {
        tested++;
        for (int j = 0; j < n; j++) {
          if ((c.offset + j == t.value) == t.equal) {
            costs[testRow][j] += a[k];
          }
        }
      } else if (v.singleton()) {
        rhs -= (long) a[k] * v.value();
      } else if (rest == null && !rowOfSuccessor.containsKey(v)) {
        rest = v;
        restCoefficient = a[k];
      } else {
        return null;
      }
    }
    boolean full = found + fixed == n;
    if (!full && found + tested == 0) {
      return null;
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
        for (int j = 0; j < n; j++) {
          row[j] = -row[j];
        }
      }
    } else {
      return null;
    }
    // the constant goes to the first row, which every circuit and subcircuit pays exactly once
    if (rest != null) {
      for (int j = 0; j < n; j++) {
        costs[0][j] += rhs;
      }
    }
    int[][] result = new int[n][n];
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        long w = costs[i][j];
        if (w < Integer.MIN_VALUE / 4 || w > Integer.MAX_VALUE / 4) {
          return null;
        }
        result[i][j] = (int) w;
      }
    }
    return new Sum(result, cost, full);
  }
}
