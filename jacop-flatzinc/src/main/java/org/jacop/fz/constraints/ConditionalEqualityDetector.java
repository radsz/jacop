/*
 * ConditionalEqualityDetector.java
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

import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.ConditionalSelect;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.SimpleNode;

/**
 * Posts, redundantly, the value selected by an if-then-else over reified equalities of one
 * variable.
 *
 * <p>MiniZinc flattens a constraint {@code if c then x = a else x = b endif} as {@code
 * jacop_if_then_else_bool([c, true], [p, q], true)} with {@code int_eq_reif(x, a, p)} and {@code
 * int_eq_reif(x, b, q)}. The reified equalities only fix p or q once x is known or excluded from a
 * value, so x keeps every value of its declared domain (all integers when it is declared {@code var
 * int}) although it is a or b. In work-task-variation (MiniZinc Challenge 2025) the objective sums
 * 480 such variables: their domains never shrink, the linear relaxation bounds the objective only
 * by the integer range, and each lazy clause generation reason of the sum cites about 260 bounds.
 * The pass posts {@code ConditionalSelect([c, true], [a, b], x)}, which keeps x within the branches
 * still possible (the constraint the front end posts for {@code jacop_if_then_else_int}); most x
 * are then fixed at the root, the reasons of the sum shrink to about 17 atoms and the linear
 * relaxation bounds the objective by 0.
 */
public final class ConditionalEqualityDetector {

  private static final Set<String> KINDS = Set.of("jacop_if_then_else_bool");

  private final Support support;

  private int posted;

  /**
   * It creates the pass reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public ConditionalEqualityDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the pass is on.
   *
   * @return false if the system property org.jacop.fz.conditionalEquality is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.conditionalEquality"));
  }

  /**
   * Finds the if-then-else constraints over reified equalities of one variable and posts their
   * selections.
   *
   * @param astTree the root of the parsed model.
   * @return the number of selections posted.
   */
  public int detect(SimpleNode astTree) {
    if (!support.hasConstraint(astTree, KINDS)) {
      return 0;
    }
    List<ASTConstElem> all = FzItems.constraints(astTree, Set.of());
    // each reified equality by its 0/1 variable: the two sides
    Map<IntVar, IntVar[]> equalities = new IdentityHashMap<>();
    for (ASTConstElem c : all) {
      if (c.getName().equals("int_eq_reif")) {
        IntVar p = support.getVariable((ASTScalarFlatExpr) c.jjtGetChild(2));
        IntVar[] sides = {
          support.getVariable((ASTScalarFlatExpr) c.jjtGetChild(0)),
          support.getVariable((ASTScalarFlatExpr) c.jjtGetChild(1))
        };
        if (!p.singleton()) {
          // two equalities reified by one variable: neither is read
          equalities.put(p, equalities.containsKey(p) ? null : sides);
        }
      }
    }
    for (ASTConstElem c : all) {
      if (c.getName().equals("jacop_if_then_else_bool")) {
        IntVar y = support.getVariable((ASTScalarFlatExpr) c.jjtGetChild(2));
        if (y.singleton(1)) {
          select(
              support.getVarArray((SimpleNode) c.jjtGetChild(0)),
              support.getVarArray((SimpleNode) c.jjtGetChild(1)),
              equalities);
        }
      }
    }
    return posted;
  }

  // b: the conditions, p: the branches (each true iff x equals its value)
  private void select(IntVar[] b, IntVar[] p, Map<IntVar, IntVar[]> equalities) {
    if (b.length != p.length || b.length < 2 || !b[b.length - 1].singleton(1)) {
      return;
    }
    IntVar[] first = equalities.get(p[0]);
    if (first == null) {
      return;
    }
    // the variable that every branch equates to a value: one of the sides of the first equality
    for (int side = 0; side < 2; side++) {
      IntVar x = first[side];
      if (x.singleton()) {
        continue;
      }
      IntVar[] values = new IntVar[p.length];
      boolean all = true;
      for (int i = 0; i < p.length && all; i++) {
        IntVar[] e = equalities.get(p[i]);
        if (e == null) {
          all = false;
        } else if (e[0] == x) {
          values[i] = e[1];
        } else if (e[1] == x) {
          values[i] = e[0];
        } else {
          all = false;
        }
      }
      if (all) {
        support.pose(new ConditionalSelect(b, values, x));
        posted++;
        return;
      }
    }
  }
}
