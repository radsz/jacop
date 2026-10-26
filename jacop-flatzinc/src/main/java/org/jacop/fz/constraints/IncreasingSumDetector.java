/*
 * IncreasingSumDetector.java
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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.IncreasingSum;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds sums over variables that are ordered and posts {@link IncreasingSum} on them as a
 * redundant constraint. The order comes from increasing and decreasing constraints or from chains
 * of x[i] &le; x[i+1], as symmetry breaking writes them; the sum is an int_lin_eq or int_lin_le
 * with unit coefficients over exactly the ordered variables, optionally with one more variable of
 * the opposite sign as the sum. All constraints are still posted as usual, so the IncreasingSum
 * only adds pruning.
 *
 * <p>Setting the system property {@code org.jacop.fz.increasingSum} to false turns the detection
 * off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class IncreasingSumDetector implements ParserTreeConstants {

  private final Support support;

  // for each variable the variables that are at least as large; true when strictly larger
  private final Map<IntVar, Map<IntVar, Boolean>> above = new IdentityHashMap<>();

  private final List<ASTConstElem> linears = new ArrayList<>();

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public IncreasingSumDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.increasingSum is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.increasingSum"));
  }

  /**
   * It scans the constraint items of the model and posts an IncreasingSum for each sum over ordered
   * variables.
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
    if (above.isEmpty()) {
      return;
    }
    for (ASTConstElem node : linears) {
      sum(node);
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_increasing" -> chain(support.getVarArray(child(node, 0)), false, false);
      case "jacop_strictly_increasing" -> chain(support.getVarArray(child(node, 0)), true, false);
      case "jacop_decreasing" -> chain(support.getVarArray(child(node, 0)), false, true);
      case "jacop_strictly_decreasing" -> chain(support.getVarArray(child(node, 0)), true, true);
      case "int_le" -> order(var(node, 0), var(node, 1), false);
      case "int_lt" -> order(var(node, 0), var(node, 1), true);
      case "int_lin_le" -> {
        difference(node);
        linears.add(node);
      }
      case "int_lin_eq" -> linears.add(node);
      default -> {
        // not part of an increasing sum
      }
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private IntVar var(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private void chain(IntVar[] x, boolean strict, boolean reversed) {
    for (int i = 0; i + 1 < x.length; i++) {
      if (reversed) {
        order(x[i + 1], x[i], strict);
      } else {
        order(x[i], x[i + 1], strict);
      }
    }
  }

  // k * (x0 - x1) <= c with k != 0: x0 <= x1 when floor(c / |k|) is 0, x0 < x1 when it is below
  private void difference(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    if (a == null || a.length != 2 || a[0] != -a[1] || a[0] == 0) {
      return;
    }
    IntVar[] x = support.getVarArray(child(node, 1));
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int gap = Math.floorDiv(c, Math.abs(a[0]));
    if (gap <= 0) {
      if (a[0] > 0) {
        order(x[0], x[1], gap < 0);
      } else {
        order(x[1], x[0], gap < 0);
      }
    }
  }

  // smaller <= larger, or smaller < larger when strict
  private void order(IntVar smaller, IntVar larger, boolean strict) {
    if (smaller == larger) {
      return;
    }
    above
        .computeIfAbsent(smaller, k -> new IdentityHashMap<>())
        .merge(larger, strict, Boolean::logicalOr);
  }

  // sign * (sum of x) - sign * s <= or = c, or sign * (sum of x) <= or = c without s
  private void sum(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] vars = support.getVarArray(child(node, 1));
    if (a == null || a.length < 3 || a.length != vars.length) {
      return;
    }
    int plus = 0;
    for (int k : a) {
      if (k == 1) {
        plus++;
      } else if (k != -1) {
        return;
      }
    }
    int minus = a.length - plus;
    int sign;
    if (minus == 0 || plus == 0) {
      sign = plus > 0 ? 1 : -1;
    } else if (minus == 1) {
      sign = 1;
    } else if (plus == 1) {
      sign = -1;
    } else {
      return;
    }
    IntVar s = null;
    List<IntVar> chain = new ArrayList<>();
    for (int k = 0; k < a.length; k++) {
      if (a[k] == sign) {
        chain.add(vars[k]);
      } else {
        s = vars[k];
      }
    }
    IntVar[] x = ordered(chain);
    if (x == null) {
      return;
    }
    boolean strict = true;
    for (int i = 0; i + 1 < x.length; i++) {
      strict &= above.get(x[i]).get(x[i + 1]);
    }
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    boolean equation = node.getName().equals("int_lin_eq");
    IntVar total = total(x, s, sign, c, equation);
    if (total == null) {
      return;
    }
    IncreasingSum is = new IncreasingSum(x, total, strict);
    // redundant, so degree-based variable selections see the degrees of the model
    is.setDegreeWeight(0);
    if (support.options.debug()) {
      FzConsole.println("% redundant " + is);
    }
    support.delayedConstraints.add(is);
  }

  /**
   * The variable equal to the sum of x: s itself, s shifted by a constant, or a new variable that
   * the bound of a sum without s restricts; null when the linear constraint has no such variable.
   */
  private IntVar total(IntVar[] x, IntVar s, int sign, int c, boolean equation) {
    long low = 0;
    long high = 0;
    for (IntVar v : x) {
      low += v.min();
      high += v.max();
    }
    long shift = (long) sign * c;
    if (s != null) {
      // sum of x = s + sign * c
      if (!equation) {
        return null;
      }
      if (shift == 0) {
        return s;
      }
      long min = s.min() + shift;
      long max = s.max() + shift;
      if (min < IntDomain.MIN_INT || max > IntDomain.MAX_INT) {
        return null;
      }
      IntVar t = new IntVar(support.store, (int) min, (int) max);
      support.delayedConstraints.add(new XplusCeqZ(s, (int) shift, t).setDegreeWeight(0));
      return t;
    }
    // sum of x = sign * c, sum of x <= c for sign 1, or sum of x >= -c for sign -1
    long min = equation || sign < 0 ? shift : low;
    long max = equation || sign > 0 ? shift : high;
    min = Math.max(min, IntDomain.MIN_INT);
    max = Math.min(max, IntDomain.MAX_INT);
    if (min > max) {
      return null;
    }
    return new IntVar(support.store, (int) min, (int) max);
  }

  /**
   * The variables in the order of the chain, which must be the only topological order of the order
   * relation among them; null if there is none or more than one.
   */
  private IntVar[] ordered(List<IntVar> vars) {
    Map<IntVar, Integer> indegree = new IdentityHashMap<>();
    int tops = 0;
    for (IntVar v : vars) {
      if (indegree.put(v, 0) != null) {
        return null;
      }
      if (!above.containsKey(v)) {
        tops++;
      }
    }
    // only the last variable of a chain may have nothing above it
    if (tops > 1) {
      return null;
    }
    for (IntVar v : vars) {
      Map<IntVar, Boolean> up = above.get(v);
      if (up != null) {
        for (IntVar w : up.keySet()) {
          indegree.computeIfPresent(w, (k, d) -> d + 1);
        }
      }
    }
    ArrayDeque<IntVar> ready = new ArrayDeque<>();
    for (IntVar v : vars) {
      if (indegree.get(v) == 0) {
        ready.add(v);
      }
    }
    IntVar[] order = new IntVar[vars.size()];
    int n = 0;
    while (ready.size() == 1) {
      IntVar v = ready.poll();
      order[n++] = v;
      Map<IntVar, Boolean> up = above.get(v);
      if (up != null) {
        for (IntVar w : up.keySet()) {
          Integer d = indegree.computeIfPresent(w, (k, old) -> old - 1);
          if (d != null && d == 0) {
            ready.add(w);
          }
        }
      }
    }
    // a unique topological order has an arc between every two consecutive variables
    return n == order.length ? order : null;
  }
}
