/*
 * XplusClteqZImplied.java
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

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Constraint b =&gt; X + C{@literal <=} Z, where b is a 0/1 variable (half reification).
 *
 * <p>It is equivalent to {@code new Implies(b, new XplusClteqZ(x, c, z))} and prunes the same,
 * without the overhead of a wrapper around a nested constraint. Boundary consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class XplusClteqZImplied extends PrimitiveConstraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies variable x. */
  public final IntVar x;

  /** It specifies constant c. */
  public final int c;

  /** It specifies variable z. */
  public final IntVar z;

  /** It specifies the 0/1 variable that implies x + c &lt;= z. */
  public final IntVar b;

  /**
   * It constructs constraint b =&gt; X + C{@literal <=} Z.
   *
   * @param b the 0/1 variable that implies the inequality.
   * @param x variable x.
   * @param c constant c.
   * @param z variable z.
   */
  public XplusClteqZImplied(IntVar b, IntVar x, int c, IntVar z) {

    checkInputForNullness(new String[] {"b", "x", "z"}, new Object[] {b, x, z});
    if (b.min() < 0 || b.max() > 1) {
      throw new IllegalArgumentException(
          "Variable b in XplusClteqZImplied must be 0/1 but is " + b);
    }

    numberId = idNumber.incrementAndGet();

    this.b = b;
    this.x = x;
    this.c = c;
    this.z = z;

    checkSumOverflow(x.min(), x.max(), c, c, z.min(), z.max());
    setScope(b, x, z);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public int getBoundPruningEvent(Var v) {
    // consistency() reads both bounds of b, but only the minimum of x and the maximum of z
    if (v == b || x == z) {
      return IntDomain.BOUND;
    }
    return v == x ? IntDomain.MIN : IntDomain.MAX;
  }

  @Override
  public void consistency(final Store store) {

    if (b.max() == 0) {
      removeConstraint();
    } else if (b.min() == 1) {
      x.domain.inMax(store.level, x, z.max() - c);
      z.domain.inMin(store.level, z, x.min() + c);
      if (x.max() + c <= z.min()) {
        removeConstraint();
      }
    } else if (x.min() + c > z.max()) {
      b.domain.inValue(store.level, b, 0);
      removeConstraint();
    } else if (x.max() + c <= z.min()) {
      removeConstraint();
    }
  }

  @Override
  public void notConsistency(final Store store) {

    // not (b => x + c <= z) is b and x + c > z.
    b.domain.inValue(store.level, b, 1);
    x.domain.inMin(store.level, x, z.min() - c + 1);
    z.domain.inMax(store.level, z, x.max() + c - 1);
  }

  @Override
  public boolean satisfied() {
    return b.max() == 0 || x.max() + c <= z.min();
  }

  @Override
  public boolean notSatisfied() {
    return b.min() == 1 && x.min() + c > z.max();
  }

  @Override
  public String toString() {

    return id() + " : XplusClteqZImplied(" + b + ", " + x + ", " + c + ", " + z + " )";
  }
}
