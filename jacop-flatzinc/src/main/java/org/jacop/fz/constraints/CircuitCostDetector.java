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
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.CircuitCost;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds circuits whose cost is a sum of arc costs and posts {@link CircuitCost} on them as a
 * redundant constraint. MiniZinc models write such a cost as {@code circuit(x) /\ cost =
 * sum(i)(d[i, x[i]])}, which is flattened into a circuit on x, one element constraint with a
 * constant row of d for each x[i], and a linear equation summing the element values into the cost.
 * All these constraints are still posted as usual, so the CircuitCost only adds pruning.
 *
 * <p>Setting the system property {@code org.jacop.fz.circuitCost} to false turns the detection off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class CircuitCostDetector implements ParserTreeConstants {

  private final Support support;

  // the element value variable of each index variable with a constant array
  private final Map<IntVar, Element> elements = new IdentityHashMap<>();

  private final List<Circuit> circuits = new ArrayList<>();

  private final List<SimpleNode> linears = new ArrayList<>();

  // an element constraint value = array[index - firstIndex] with a constant array
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

  // a circuit on x whose values are numbered from offset
  private static final class Circuit {
    final IntVar[] x;
    final int offset;

    Circuit(IntVar[] x, int offset) {
      this.x = x;
      this.offset = offset;
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

  /**
   * It scans the constraint items of the model and posts a CircuitCost for each circuit whose
   * successors have arc costs summed into one variable.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            collect((ASTConstElem) item);
          }
        }
      }
    }
    if (circuits.isEmpty() || elements.isEmpty() || linears.isEmpty()) {
      return;
    }
    for (Circuit c : circuits) {
      post(c);
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_circuit" -> circuits.add(new Circuit(support.getVarArray(child(node, 0)), 1));
      case "jacop_circuit_offset" ->
          circuits.add(
              new Circuit(
                  support.getVarArray(child(node, 0)),
                  support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1))));
      case "array_int_element" -> element(node, support.getIntArray(child(node, 1)), 1);
      case "array_var_int_element" -> element(node, constants(child(node, 1)), 1);
      case "jacop_array_var_int_element_nonshifted" ->
          element(
              node,
              constants(child(node, 1)),
              support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
      case "int_lin_eq" -> linears.add(node);
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

  private void post(Circuit c) {
    int n = c.x.length;
    Map<IntVar, Integer> rowOfValue = new HashMap<>();
    int[][] costs = new int[n][n];
    for (int i = 0; i < n; i++) {
      Element e = elements.get(c.x[i]);
      if (e == null || rowOfValue.put(e.value, i) != null) {
        return;
      }
      for (int j = 0; j < n; j++) {
        // a value without a cost is out of the element's index range, so the element removes it
        int k = c.offset + j - e.firstIndex;
        costs[i][j] = k >= 0 && k < e.array.length ? e.array[k] : 0;
      }
    }
    IntVar cost = sumOf(rowOfValue, n);
    if (cost == null) {
      return;
    }
    CircuitCost cc = new CircuitCost(c.x, costs, cost, c.offset);
    // redundant, so degree-based variable selections see the degrees of the model
    cc.setDegreeWeight(0);
    if (support.options.debug()) {
      FzConsole.println("% redundant " + cc);
    }
    support.delayedConstraints.add(cc);
  }

  // the variable equal to the sum of the arc costs: int_lin_eq([a, ..., a, -a], [c..., cost], 0)
  private IntVar sumOf(Map<IntVar, Integer> rowOfValue, int n) {
    for (SimpleNode node : linears) {
      int[] a = support.getIntArray(child(node, 0));
      IntVar[] vars = support.getVarArray(child(node, 1));
      int rhs = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
      if (a == null || a.length != n + 1 || rhs != 0) {
        continue;
      }
      int unit = 0;
      IntVar cost = null;
      boolean[] seen = new boolean[n];
      int found = 0;
      for (int k = 0; k <= n; k++) {
        Integer row = rowOfValue.get(vars[k]);
        if (row != null && !seen[row] && (a[k] == 1 || a[k] == -1) && (unit == 0 || a[k] == unit)) {
          unit = a[k];
          seen[row] = true;
          found++;
        } else if (cost == null && row == null) {
          cost = vars[k];
        } else {
          cost = null;
          break;
        }
      }
      if (found == n && cost != null && a[indexOf(vars, cost)] == -unit) {
        return cost;
      }
    }
    return null;
  }

  private static int indexOf(IntVar[] vars, IntVar v) {
    for (int k = 0; k < vars.length; k++) {
      if (vars[k] == v) {
        return k;
      }
    }
    return -1;
  }
}
