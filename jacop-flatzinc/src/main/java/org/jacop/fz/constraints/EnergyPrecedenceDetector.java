/*
 * EnergyPrecedenceDetector.java
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
import java.util.List;
import org.jacop.constraints.cumulative.EnergyPrecedence;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It posts {@link EnergyPrecedence} on each {@code jacop_cumulative} of a model whose tasks are
 * ordered by precedences, as in project scheduling models. The precedences are the difference
 * constraints {@code x + c <= y} of the model ({@code int_lin_le}, {@code int_lin_eq}, {@code
 * int_le}, {@code int_lt}) over any variables, so a chain through tasks of other resources and a
 * makespan that follows the last tasks count too.
 *
 * <p>The cumulative and the precedences are still posted as usual, so the constraint only adds
 * pruning; it has degree weight 0, so it does not change the static degrees that variable
 * selections such as most_constrained read.
 *
 * <p>Setting the system property {@code org.jacop.fz.energyPrecedence} to false turns the detection
 * off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class EnergyPrecedenceDetector implements ParserTreeConstants {

  private final Support support;

  private final List<IntVar> from = new ArrayList<>();
  private final List<IntVar> to = new ArrayList<>();
  private final List<Integer> lag = new ArrayList<>();

  private final List<IntVar[][]> cumulatives = new ArrayList<>();

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public EnergyPrecedenceDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.energyPrecedence is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.energyPrecedence"));
  }

  /**
   * It scans the constraint items of the model and posts energy precedence reasoning on each
   * cumulative resource whose tasks have precedences.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    long start = System.nanoTime();
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
    if (from.isEmpty() || cumulatives.isEmpty()) {
      return;
    }
    IntVar[] f = from.toArray(new IntVar[0]);
    IntVar[] t = to.toArray(new IntVar[0]);
    int[] l = lag.stream().mapToInt(Integer::intValue).toArray();
    int posted = 0;
    for (IntVar[][] c : cumulatives) {
      EnergyPrecedence ep = new EnergyPrecedence(c[0], c[1], c[2], c[3][0], f, t, l);
      if (ep.propagates()) {
        // redundant, so degree-based variable selections see the degrees of the model
        ep.setDegreeWeight(0);
        support.delayedConstraints.add(ep);
        posted++;
      }
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% energy precedence on "
              + posted
              + " of "
              + cumulatives.size()
              + " cumulatives, "
              + f.length
              + " precedences, "
              + (System.nanoTime() - start) / 1_000_000
              + " ms");
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_cumulative" -> cumulative(node);
      case "int_lin_le" -> linear(node, false);
      case "int_lin_eq" -> linear(node, true);
      case "int_le" -> difference(var(node, 0), var(node, 1), 0);
      case "int_lt" -> difference(var(node, 0), var(node, 1), 1);
      default -> {
        // not a precedence
      }
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private IntVar var(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private void cumulative(ASTConstElem node) {
    IntVar[] s = support.getVarArray(child(node, 0));
    IntVar[] d = support.getVarArray(child(node, 1));
    IntVar[] r = support.getVarArray(child(node, 2));
    IntVar b = var(node, 3);
    if (s.length >= 2) {
      cumulatives.add(new IntVar[][] {s, d, r, {b}});
    }
  }

  // a*x + b*y <= c (or = c) with b = -a: a difference constraint between x and y
  private void linear(ASTConstElem node, boolean equation) {
    int[] a = support.getIntArray(child(node, 0));
    if (a == null || a.length != 2 || a[0] != -a[1] || a[0] == 0) {
      return;
    }
    IntVar[] x = support.getVarArray(child(node, 1));
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int k = Math.abs(a[0]);
    // k * (x0 - x1) <= c, so x1 >= x0 - floor(c / k); with a negative a[0] the roles swap
    IntVar first = a[0] > 0 ? x[0] : x[1];
    IntVar second = a[0] > 0 ? x[1] : x[0];
    difference(first, second, -Math.floorDiv(c, k));
    if (equation && c % k == 0) {
      difference(second, first, c / k);
    }
  }

  // second >= first + distance
  private void difference(IntVar first, IntVar second, int distance) {
    if (first != second) {
      from.add(first);
      to.add(second);
      lag.add(distance);
    }
  }
}
