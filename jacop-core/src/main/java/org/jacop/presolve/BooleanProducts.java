/*
 * BooleanProducts.java
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

package org.jacop.presolve;

import java.util.HashMap;
import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;

/**
 * Products with a 0/1 factor (CP-SAT's {@code int_prod: boolean affine term}). A product {@code z =
 * x * b} with {@code b} in 0..1 is replaced by
 *
 * <pre>
 *   b -&gt; z = x,   z &lt;= max(x) * b,   z &gt;= min(x) * b
 * </pre>
 *
 * <p>For {@code b = 0} the two inequalities fix {@code z} to 0, and for {@code b = 1} the
 * implication makes {@code z} equal to {@code x}, so the three constraints have the solutions of
 * the product over the domains of the moment. They are linear or a half-reified equality, which
 * propagate both ways at once ({@code z != 0} sets {@code b}, a {@code z} outside the domain of
 * {@code x} clears it) and have short explanations under lazy clause generation, where {@code
 * XmulYeqZ} often falls back to a generic one. It keeps every solution. The system property {@code
 * jacop.presolve.booleanProducts=false} switches it off.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class BooleanProducts implements Rule {

  private final boolean enabled;
  private int replaced;

  /** It creates the rule, on unless the system property jacop.presolve.booleanProducts is false. */
  public BooleanProducts() {
    this(Boolean.parseBoolean(System.getProperty("jacop.presolve.booleanProducts", "true")));
  }

  /**
   * It creates the rule.
   *
   * @param enabled false for a rule that does nothing.
   */
  public BooleanProducts(boolean enabled) {
    this.enabled = enabled;
  }

  @Override
  public void apply(Context context) {
    if (!enabled) {
      return;
    }
    Map<IntVar, Offset> offsets = null;
    for (Constraint c : context.constraints()) {
      if (c instanceof XmulYeqZ m && !context.removed(c)) {
        if (offsets == null) {
          offsets = offsets(context);
        }
        if (isBoolean(m.y()) && rewrite(context, offsets, m, m.x(), m.y())) {
          replaced++;
        } else if (isBoolean(m.x()) && rewrite(context, offsets, m, m.y(), m.x())) {
          replaced++;
        }
      }
    }
  }

  /** A variable defined as {@code u + c}. */
  private record Offset(IntVar u, int c) {}

  // the variables x that an equality x = u + c defines, with the first such equality
  private static Map<IntVar, Offset> offsets(Context context) {
    Map<IntVar, Offset> offsets = new HashMap<>();
    for (Constraint c : context.constraints()) {
      if (c instanceof LinearExplainable e && !context.removed(c)) {
        LinearForm f = e.linearForm();
        // a constraint may have no linear form for its current arguments
        if (f != null
            && f.relation() == LinearForm.EQ
            && f.vars().length == 2
            && f.vars()[0] != f.vars()[1]
            && Math.abs(f.weights()[0]) == 1
            && f.weights()[0] == -f.weights()[1]
            && Math.abs(f.c()) <= IntDomain.MAX_INT) {
          // w * (x - u) = c, so x = u + w * c and u = x - w * c
          int shift = (int) (f.weights()[0] * f.c());
          offsets.putIfAbsent(f.vars()[0], new Offset(f.vars()[1], shift));
          offsets.putIfAbsent(f.vars()[1], new Offset(f.vars()[0], -shift));
        }
      }
    }
    return offsets;
  }

  // rewrites z = x * b; false if the product is left as it is
  private static boolean rewrite(
      Context context, Map<IntVar, Offset> offsets, XmulYeqZ m, IntVar x, IntVar b) {
    IntVar z = m.z();
    if (x == b || z == b || x == z || isBoolean(x) || b.singleton()) {
      // x * x, b * x = b and z = z * b are not products of independent factors, a product of two
      // 0/1 variables is a conjunction, and a fixed factor is for the constraint's own simplify()
      return false;
    }
    Offset o = offsets.get(x);
    if (o != null && o.u() != b && o.u() != z) {
      context.impose(new Implies(b, new XplusCeqZ(o.u(), o.c(), z)));
    } else {
      context.impose(new Implies(b, new XeqY(x, z)));
    }
    context.impose(new LinearInt(new IntVar[] {z, b}, new int[] {1, -x.max()}, "<=", 0));
    context.impose(new LinearInt(new IntVar[] {z, b}, new int[] {1, -x.min()}, ">=", 0));
    context.remove(m);
    return true;
  }

  private static boolean isBoolean(IntVar v) {
    return v.min() >= 0 && v.max() <= 1;
  }

  /**
   * Returns how many products the rule replaced over all its rounds.
   *
   * @return the number of products replaced.
   */
  public int replaced() {
    return replaced;
  }
}
