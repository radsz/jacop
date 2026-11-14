/*
 * Lex.java
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

package org.jacop.set.constraints;

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.set.core.SetVar;

/**
 * It creates a {@literal <=} b constraint on two set variables. The set variables are constrained
 * to be lexicographically ordered.
 *
 * <p>For example, {}{@literal <=}lex {} {}{@literal <=}lex {1} {1, 2}{@literal <=}lex {1, 2} {1,
 * 3}{@literal <=}lex {2} {1}{@literal <=} {2}
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class AleB extends AbstractAleqB implements Copyable<AleB> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs an Lexical ordering constraint to restrict the domain of the variables a and b.
   *
   * @param a variable that is restricted to be less than b with lexical order.
   * @param b variable that is restricted to be greater than a with lexical order.
   */
  public AleB(SetVar a, SetVar b) {

    super(idNumber, a, b);
    negatedConstraint = new AltB(b, a, true);
  }

  /**
   * It constructs an Lexical ordering to be used in negated constrained. Not to be used for
   * imposing constraints.
   *
   * @param a variable that is restricted to be less than b with lexical order.
   * @param b variable that is restricted to be greater than a with lexical order.
   * @param negated used to distinguish constructors only.
   */
  AleB(SetVar a, SetVar b, boolean negated) {
    super(a, b);
  }

  @Override
  public void consistency(Store store) {
    // every set is at most itself; the propagation treats a and b as independent
    if (a == b) {
      return;
    }
    propagateOrder(store, false);
  }

  @Override
  boolean setLexCompare(IntDomain x, IntDomain y) {

    if (x.getSize() == 0 && y.getSize() >= 0) {
      return true;
    }

    ValueEnumeration xe = x.valueEnumeration();
    ValueEnumeration ye = y.valueEnumeration();

    boolean le = false;

    while (xe.hasMoreElements() && ye.hasMoreElements()) {
      int xv = xe.nextElement();
      int yv = ye.nextElement();

      if (xv < yv) {
        return true;
      } else if (xv > yv) {
        return false;
      }
    }
    if (!xe.hasMoreElements()) {
      return true;
    }

    return le;
  }

  @Override
  public boolean satisfied() {
    return a == b || super.satisfied();
  }

  @Override
  Boolean explainedOrder() {
    return getClass() == AleB.class ? Boolean.FALSE : null;
  }

  @Override
  public String toString() {

    return id() + " : AleB(" + a + ", " + b + ")";
  }

  @Override
  public AleB copy(VarMap map) {
    return new AleB(map.get(a), map.get(b));
  }
}
