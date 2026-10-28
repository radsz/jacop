/*
 * LinearForms.java
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

package org.jacop.constraints;

import java.util.Arrays;
import org.jacop.core.IntVar;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;

/**
 * Reads constraints as linear relations, for presolve rules that reason on linear constraints and
 * clauses alike. Boolean constraints whose result is fixed are read as the linear relations they
 * stand for: a clause is {@code sum x - sum y >= 1 - |y|}, {@code a /\ b = false} is {@code a + b
 * <= 1}.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class LinearForms {

  private LinearForms() {}

  /**
   * Returns the constraint as a linear relation.
   *
   * @param c the constraint.
   * @return the linear form, or null if the constraint is not a linear relation that this method
   *     reads (a reified Boolean constraint whose result is not fixed, a subclass, a nonlinear
   *     constraint).
   */
  public static LinearForm of(Constraint c) {
    Class<?> k = c.getClass();
    if (c instanceof LinearExplainable l) {
      return l.linearForm();
    }
    if (k == LinearInt.class || k == LinearIntDom.class) {
      return ((LinearInt) c).lcgForm();
    }
    if (k == LinearBool.class) {
      return linearBool((LinearBool) c);
    }
    if (k == SumWeight.class) {
      SumWeight s = (SumWeight) c;
      return new LinearForm(s.list, s.weights, s.equalTo, LinearForm.EQ);
    }
    if (k == BoolClause.class) {
      return ((BoolClause) c).clauseForm();
    }
    if (k == AndBoolSimple.class || k == OrBoolSimple.class) {
      AbstractBoolSimple s = (AbstractBoolSimple) c;
      return bool(new IntVar[] {s.a, s.b}, s.result, k == AndBoolSimple.class);
    }
    if (k == AndBoolVector.class || k == OrBoolVector.class) {
      AbstractBoolVector v = (AbstractBoolVector) c;
      return bool(v.list, v.result, k == AndBoolVector.class);
    }
    return null;
  }

  private static LinearForm linearBool(LinearBool l) {
    IntVar[] vars = l.x;
    long[] weights = l.w;
    long rhs = l.c;
    if (l.z != null) {
      int n = vars.length;
      vars = Arrays.copyOf(vars, n + 1);
      weights = Arrays.copyOf(weights, n + 1);
      vars[n] = l.z;
      weights[n] = -1;
      rhs = 0;
    }
    int relation =
        switch (l.relationType) {
          case LinearBool.EQ -> LinearForm.EQ;
          case LinearBool.LE -> LinearForm.LE;
          default -> LinearForm.GE;
        };
    return new LinearForm(vars, weights, rhs, relation);
  }

  // a conjunction or disjunction with a fixed result
  private static LinearForm bool(IntVar[] list, IntVar result, boolean and) {
    if (!result.singleton()) {
      return null;
    }
    long[] ones = new long[list.length];
    Arrays.fill(ones, 1);
    boolean holds = result.value() == 1;
    if (and) {
      return holds
          ? new LinearForm(list, ones, list.length, LinearForm.GE)
          : new LinearForm(list, ones, list.length - 1L, LinearForm.LE);
    }
    return holds
        ? new LinearForm(list, ones, 1, LinearForm.GE)
        : new LinearForm(list, ones, 0, LinearForm.LE);
  }
}
