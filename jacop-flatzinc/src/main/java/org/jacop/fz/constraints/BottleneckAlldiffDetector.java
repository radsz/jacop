/*
 * BottleneckAlldiffDetector.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.BottleneckAlldiff;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds bottleneck assignments and posts {@link BottleneckAlldiff} on them as a redundant
 * constraint: a variable z that is the maximum (jacop_maximum, array_int_maximum) or an upper bound
 * (int_le(c, z), int_lin_le([1, -1], [c, z], 0)) of at least two costs c[i] = a_i[x[i]] given by
 * element constraints over constant arrays, whose indexes x[i] are different variables of one
 * alldifferent (jacop_alldiff, jacop_alldistinct or a list of jacop_assignment). The model's
 * constraints are all posted as usual, so the new constraint only adds pruning: the lower bound of
 * z from a matching of the cheap values (the costs of different variables cannot all be cheap when
 * they compete for the same cheap values), and the values that no matching under max(z) uses.
 *
 * <p>Setting the system property {@code org.jacop.fz.bottleneckAlldiff} to false turns the
 * detection off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class BottleneckAlldiffDetector implements ParserTreeConstants {

  /** A cost a[x - first] of variable x. */
  private record Cost(IntVar x, int[] array, int first) {}

  private final Support support;

  // the alldifferent group of each variable, the first group it is found in
  private final Map<IntVar, Integer> group = new IdentityHashMap<>();
  private int groups;

  private final Map<IntVar, Cost> costs = new IdentityHashMap<>();

  // the terms each bound variable bounds from above, in model order
  private final Map<IntVar, List<IntVar>> bounded = new LinkedHashMap<>();

  /** The number of BottleneckAlldiff constraints posted. */
  public int posted;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public BottleneckAlldiffDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.bottleneckAlldiff is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.bottleneckAlldiff"));
  }

  /**
   * It scans the constraint items of the model and posts a BottleneckAlldiff for each maximum of
   * element costs of alldifferent variables.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    List<ASTConstElem> items = new ArrayList<>();
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            items.add((ASTConstElem) item);
          }
        }
      }
    }
    for (ASTConstElem node : items) {
      alldifferent(node);
    }
    if (group.isEmpty()) {
      return;
    }
    for (ASTConstElem node : items) {
      collect(node);
    }
    for (Map.Entry<IntVar, List<IntVar>> e : bounded.entrySet()) {
      post(e.getKey(), e.getValue());
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private void alldifferent(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_alldiff", "jacop_alldistinct" -> addGroup(support.getVarArray(child(node, 0)));
      case "jacop_assignment" -> {
        addGroup(support.getVarArray(child(node, 0)));
        addGroup(support.getVarArray(child(node, 1)));
      }
      default -> {
        // not an alldifferent
      }
    }
  }

  private void addGroup(IntVar[] x) {
    int g = groups++;
    for (IntVar v : x) {
      if (!v.singleton()) {
        group.putIfAbsent(v, g);
      }
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "array_int_element" -> element(node, support.getIntArray(child(node, 1)), 1);
      case "array_var_int_element" -> element(node, constants(child(node, 1)), 1);
      case "jacop_array_var_int_element_nonshifted" ->
          element(
              node,
              constants(child(node, 1)),
              support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
      case "jacop_maximum", "array_int_maximum" -> {
        IntVar z = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
        for (IntVar c : support.getVarArray(child(node, 1))) {
          bound(z, c);
        }
      }
      case "int_le" ->
          bound(
              support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1)),
              support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0)));
      case "int_lin_le" -> linear(node);
      default -> {
        // not part of a bottleneck assignment
      }
    }
  }

  private int[] constants(SimpleNode array) {
    IntVar[] vars = support.getVarArray(array);
    int[] a = new int[vars.length];
    for (int k = 0; k < vars.length; k++) {
      if (!vars[k].singleton()) {
        return null;
      }
      a[k] = vars[k].value();
    }
    return a;
  }

  private void element(ASTConstElem node, int[] array, int first) {
    if (array == null || array.length == 0) {
      return;
    }
    IntVar x = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (group.containsKey(x) && !c.singleton()) {
      costs.putIfAbsent(c, new Cost(x, array, first));
    }
  }

  // c - z <= 0
  private void linear(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] vars = support.getVarArray(child(node, 1));
    if (a == null || a.length != 2 || vars.length != 2) {
      return;
    }
    if (support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)) != 0) {
      return;
    }
    if (a[0] == 1 && a[1] == -1) {
      bound(vars[1], vars[0]);
    } else if (a[0] == -1 && a[1] == 1) {
      bound(vars[0], vars[1]);
    }
  }

  private void bound(IntVar z, IntVar c) {
    if (z != null && c != null && !z.singleton()) {
      bounded.computeIfAbsent(z, k -> new ArrayList<>()).add(c);
    }
  }

  // the costs among the terms whose variables are in the largest group
  private void post(IntVar z, List<IntVar> terms) {
    Map<Integer, List<Cost>> byGroup = new LinkedHashMap<>();
    for (IntVar c : terms) {
      Cost cost = costs.get(c);
      if (cost != null && cost.x != z) {
        List<Cost> list = byGroup.computeIfAbsent(group.get(cost.x), k -> new ArrayList<>());
        if (list.stream().noneMatch(o -> o.x == cost.x)) {
          list.add(cost);
        }
      }
    }
    List<Cost> best = null;
    for (List<Cost> list : byGroup.values()) {
      if (best == null || list.size() > best.size()) {
        best = list;
      }
    }
    if (best == null || best.size() < 2) {
      return;
    }
    int offset = Integer.MAX_VALUE;
    long last = Long.MIN_VALUE;
    for (Cost c : best) {
      offset = Math.min(offset, c.first);
      last = Math.max(last, (long) c.first + c.array.length - 1);
    }
    if (last - offset + 1 > 1_000_000L) {
      return;
    }
    int n = best.size();
    IntVar[] x = new IntVar[n];
    int[][] rows = new int[n][];
    for (int i = 0; i < n; i++) {
      Cost c = best.get(i);
      x[i] = c.x;
      int shift = c.first - offset;
      rows[i] = new int[shift + c.array.length];
      // the element forbids the values below its first index
      Arrays.fill(rows[i], 0, shift, IntDomain.MAX_INT);
      System.arraycopy(c.array, 0, rows[i], shift, c.array.length);
    }
    BottleneckAlldiff b = new BottleneckAlldiff(x, rows, offset, z);
    // redundant, so degree-based variable selections see the degrees of the model
    b.setDegreeWeight(0);
    if (support.options.debug()) {
      FzConsole.println("% redundant " + b);
    }
    support.delayedConstraints.add(b);
    posted++;
  }
}
