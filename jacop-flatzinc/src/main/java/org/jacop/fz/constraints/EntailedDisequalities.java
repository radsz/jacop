/*
 * EntailedDisequalities.java
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.Node;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Removes the disequalities {@code int_ne} and {@code int_lin_ne} that the declared domains already
 * satisfy, before the detectors read the model. MiniZinc flattens implications such as {@code
 * kind[i] != kind[j] -> g[i] != g[j]} of gfd-schedule (MiniZinc Challenge 2015-2022) into one
 * disequality per pair, and the ranges it gives the variables make 15,040 of the 15,041 of
 * n180f7d50m30k18 true: the all-different, symmetry, XOR and LP detectors each scanned them, which
 * took most of the 4.8 s of its set-up. Off with {@code
 * -Dorg.jacop.fz.entailedDisequalities=false}.
 */
public final class EntailedDisequalities implements ParserTreeConstants {

  private final Support support;

  private int removed;

  /**
   * Creates the pass.
   *
   * @param support the support of the model's constraints
   */
  public EntailedDisequalities(Support support) {
    this.support = support;
  }

  /**
   * Whether the pass runs.
   *
   * @return false when {@code org.jacop.fz.entailedDisequalities} is false
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.entailedDisequalities"));
  }

  /**
   * Removes the disequalities that the domains of their variables satisfy from the constraint items
   * of the model.
   *
   * @param astTree the root of the parsed model
   * @return the number of constraints removed
   */
  public int remove(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode items = (SimpleNode) astTree.jjtGetChild(i);
      if (items.getId() == JJTCONSTRAINTITEMS) {
        items.retainChildren(this::kept);
      }
    }
    return removed;
  }

  private boolean kept(Node constraint) {
    if (constraint.jjtGetNumChildren() == 0
        || !(constraint.jjtGetChild(0) instanceof ASTConstElem element)) {
      return true;
    }
    boolean entailed =
        switch (element.getName()) {
          case "int_ne" -> entailedNe(element);
          case "int_lin_ne" -> entailedLinear(element);
          default -> false;
        };
    if (entailed) {
      removed++;
    }
    return !entailed;
  }

  private boolean entailedNe(ASTConstElem element) {
    IntDomain x = support.getVariable((ASTScalarFlatExpr) element.jjtGetChild(0)).dom();
    IntDomain y = support.getVariable((ASTScalarFlatExpr) element.jjtGetChild(1)).dom();
    if (x.singleton()) {
      return !y.contains(x.value());
    }
    if (y.singleton()) {
      return !x.contains(y.value());
    }
    return x.max() < y.min() || y.max() < x.min();
  }

  private boolean entailedLinear(ASTConstElem element) {
    int[] a = support.getIntArray((SimpleNode) element.jjtGetChild(0));
    IntVar[] x = support.getVarArray((SimpleNode) element.jjtGetChild(1));
    if (a == null || x == null || a.length != x.length) {
      return false;
    }
    long c = support.getInt((ASTScalarFlatExpr) element.jjtGetChild(2));
    if (a.length == 1) {
      // a * x != c holds when c is no multiple of a or c / a is not in the domain of x
      return a[0] != 0 && (c % a[0] != 0 || !x[0].dom().contains((int) (c / a[0])));
    }
    long min = 0;
    long max = 0;
    for (int i = 0; i < a.length; i++) {
      long lo = (long) a[i] * x[i].min();
      long hi = (long) a[i] * x[i].max();
      min += Math.min(lo, hi);
      max += Math.max(lo, hi);
    }
    return c < min || c > max;
  }
}
