/*
 * AintersectBeqC.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It creates a constraint that makes sure that A intersected with B is equal to C. A /\ B = C.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.10
 */
public class AintersectBeqC extends Constraint implements UsesQueueVariable, SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies set variable a. */
  public final SetVar a;

  /** It specifies set variable b. */
  public final SetVar b;

  /** It specifies set variable c. */
  public final SetVar c;

  /**
   * It specifies if the constrain attempts to perform expensive and yet unlikely propagation due to
   * cardinality information.
   */
  public final boolean performCardinalityReasoning = false;

  private boolean aHasChanged = true;

  private boolean bHasChanged = true;

  private boolean cHasChanged = true;

  /**
   * It constructs an AintersectBeqC constraint.
   *
   * @param a set variable a, which is being intersected with set variable b.
   * @param b set variable b, which is being intersected with set variable a.
   * @param c variable that is restricted to be the intersection of a and b.
   */
  public AintersectBeqC(SetVar a, SetVar b, SetVar c) {

    checkInputForNullness(new String[] {"a", "b", "c"}, new Object[] {a, b, c});

    numberId = idNumber.incrementAndGet();

    this.a = a;
    this.b = b;
    this.c = c;

    setScope(a, b, c);
  }

  @Override
  public void consistency(Store store) {

    // FIXME, TODO, implement cardinality reasoning as specified in the comments.

    do {

      store.propagationHasOccurred = false;

      boolean aHasChanged = this.aHasChanged;
      boolean bHasChanged = this.bHasChanged;
      boolean cHasChanged = this.cHasChanged;

      this.aHasChanged = false;
      this.bHasChanged = false;
      this.cHasChanged = false;

      if (cHasChanged) a.domain.inGLB(store.level, a, c.domain.glb());

      if (bHasChanged || cHasChanged) {
        IntDomain temp = b.domain.glb().subtract(c.domain.lub());
        if (!temp.isEmpty()) a.domain.inLUB(store.level, a, a.domain.lub().subtract(temp));
      }

      if (cHasChanged) b.domain.inGLB(store.level, b, c.domain.glb());

      if (cHasChanged || aHasChanged) {
        IntDomain temp = a.domain.glb().subtract(c.domain.lub());
        if (!temp.isEmpty()) b.domain.inLUB(store.level, b, b.domain.lub().subtract(temp));
      }

      if (bHasChanged || aHasChanged)
        c.domain.inGLB(store.level, c, a.domain.glb().intersect(b.domain.glb()));

      if (bHasChanged || aHasChanged)
        c.domain.inLUB(store.level, c, a.domain.lub().intersect(b.domain.lub()));

      if (performCardinalityReasoning) {

        int sizeOf4 = a.domain.glb().subtract(b.domain.lub()).getSize();
        a.domain.inCardinality(store.level, a, sizeOf4 + c.domain.card().min(), Integer.MAX_VALUE);

        int sizeOf_6_7 = a.domain.lub().intersect(b.domain.glb()).getSize();
        if (sizeOf_6_7 > c.domain.card().max()) {
          int reserved = sizeOf_6_7 - c.domain.card().max();
          a.domain.inCardinality(
              store.level, a, Integer.MIN_VALUE, a.domain.lub().getSize() - reserved);
        }

        int sizeOf8 = b.domain.glb().subtract(a.domain.lub()).getSize();
        b.domain.inCardinality(store.level, b, sizeOf8 + c.domain.card().min(), Integer.MAX_VALUE);

        int sizeOf_5_6 = b.domain.lub().intersect(a.domain.glb()).getSize();
        if (sizeOf_5_6 > c.domain.card().max()) {
          int reserved = sizeOf_5_6 - c.domain.card().max();
          b.domain.inCardinality(
              store.level, b, Integer.MIN_VALUE, b.domain.lub().getSize() - reserved);
        }

        int sizeOf1_4 = a.domain.lub().subtract(b.domain.lub()).getSize();
        int sizeOf3_8 = b.domain.lub().subtract(a.domain.lub()).getSize();
        int sizeOf6 = a.domain.glb().intersect(b.domain.glb()).getSize();
        int sizeOf2_5_6_7 = a.domain.lub().intersect(b.domain.lub()).getSize();

        int max =
            Math.max(a.domain.card().min() - sizeOf1_4, 0)
                + Math.max(b.domain.card().min() - sizeOf3_8, 0);

        max -= sizeOf6 + sizeOf2_5_6_7;
        if (max > 0) c.domain.inCardinality(store.level, c, sizeOf6 + max, Integer.MAX_VALUE);

        c.domain.inCardinality(store.level, c, Integer.MIN_VALUE, a.domain.card().max() - sizeOf4);
        c.domain.inCardinality(store.level, c, Integer.MIN_VALUE, b.domain.card().max() - sizeOf8);
      }

    } while (store.propagationHasOccurred);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return SetDomain.ANY;
  }

  @Override
  public boolean satisfied() {
    return grounded() && a.domain.intersect(b.domain).eq(c.domain);
  }

  @Override
  public String toString() {
    return id() + " : AintersectBeqC(" + a + ", " + b + ", " + c + " )";
  }

  @Override
  public void queueVariable(int level, Var variable) {

    if (variable == a) {
      aHasChanged = true;
      return;
    }

    if (variable == b) {
      bHasChanged = true;
      return;
    }

    if (variable == c) {
      cHasChanged = true;
      return;
    }
  }
}
