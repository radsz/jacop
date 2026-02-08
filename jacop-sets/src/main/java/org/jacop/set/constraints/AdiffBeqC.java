/*
 * AdiffBeqC.java
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
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It creates a constraints that subtracts from set variable A the elements from of the set variable
 * B and assigns the result to set variable C.
 *
 * <p>A \ B = C.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class AdiffBeqC extends Constraint implements UsesQueueVariable, SatisfiedPresent {

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
   * It constructs an AdiffBeqC constraint to restrict the domain of the variables A, B and C.
   *
   * @param a set variable a
   * @param b set variable b
   * @param c set variable that is restricted to be the set difference of a and b.
   */
  public AdiffBeqC(SetVar a, SetVar b, SetVar c) {

    checkInputForNullness(new String[] {"a", "b", "c"}, new Object[] {a, b, c});

    this.numberId = idNumber.incrementAndGet();

    this.a = a;
    this.b = b;
    this.c = c;

    setScope(a, b, c);
  }

  @Override
  public void consistency(Store store) {

    do {

      store.propagationHasOccurred = false;

      boolean aHasChanged = this.aHasChanged;
      boolean bHasChanged = this.bHasChanged;
      boolean cHasChanged = this.cHasChanged;

      this.aHasChanged = false;
      this.bHasChanged = false;
      this.cHasChanged = false;

      if (cHasChanged) {
        a.domain.inGlb(store.level, a, c.domain.glb());
      }

      if (bHasChanged || cHasChanged) {
        a.domain.inLub(store.level, a, b.domain.lub().union(c.domain.lub()));
      }

      if (cHasChanged) {
        b.domain.inLub(store.level, b, b.domain.lub().subtract(c.domain.glb()));
      }

      if (aHasChanged || bHasChanged) {
        c.domain.inGlb(store.level, c, a.domain.glb().subtract(b.domain.lub()));
        c.domain.inLub(store.level, c, a.domain.lub().subtract(b.domain.glb()));
      }

      // FIXME, TODO, implement cardinality based reasoning.
      if (performCardinalityReasoning) {

        // TODO: check the code below, so that is can fire and propagate properly.

        int aMinCard = a.domain.card().min();
        if (aMinCard > 0) {
          int sizeOf4 = a.domain.glb().subtract(b.domain.lub()).getSize();

          if (aMinCard - sizeOf4 > 0) {
            int sizeOf8 = b.domain.glb().getSize();
            if (sizeOf8 > 0) {
              sizeOf8 = b.domain.glb().subtract(a.domain.lub()).getSize();
            }
            int sizeOf2_7 =
                a.domain.lub().intersect(b.domain.lub()).subtract(a.domain.glb()).getSize();
            int min = b.domain.card().max() - sizeOf8;
            if (min > sizeOf2_7) {
              min = sizeOf2_7;
            }
            int max = aMinCard - sizeOf4 - min;
            if (max > 0) {
              c.domain.inCardinality(store.level, c, sizeOf4 + max, Integer.MAX_VALUE);
            }
          }
        }

        int sizeOf6 = a.domain.glb().intersect(b.domain.glb()).getSize();
        int minLeft = a.domain.card().max() - sizeOf6;
        int minRight = a.domain.lub().subtract(b.domain.glb()).getSize();
        int max = b.domain.card().min();
        if (max > 0) {
          int sizeOf6_7_8 = b.domain.glb().getSize();
          max -= sizeOf6_7_8;
          if (max > 0) {
            int sizeOf3 =
                b.domain.lub().subtract(a.domain.lub()).subtract(b.domain.glb()).getSize();
            max -= sizeOf3;
            if (max > 0) {
              minRight -= max;
            }
          }
        }
        c.domain.inCardinality(store.level, c, Integer.MIN_VALUE, Math.min(minLeft, minRight));

        int sizeOf_4_5 = a.domain.glb().subtract(b.domain.glb()).getSize();
        minLeft = b.domain.glb().getSize() + Math.max(0, sizeOf_4_5 - c.domain.card().max());
        minRight = a.domain.card().max() - c.domain.card().max();
        if (minLeft < minRight) {
          minLeft = minRight;
        }

        b.domain.inCardinality(
            store.level, c, b.domain.glb().getSize() + minLeft, Integer.MAX_VALUE);

        int sizeOf1_4 = a.domain.lub().subtract(b.domain.lub()).getSize();
        int min = c.domain.card().min() - sizeOf1_4;

        if (min > 0) {
          b.domain.inCardinality(store.level, b, Integer.MIN_VALUE, b.domain.lub().getSize() - min);
        }

        min = c.domain.card().min() + b.domain.glb().intersect(a.domain.glb()).getSize();
        if (b.domain.lub().getSize() - a.domain.lub().getSize() < b.domain.card().min()) {
          min =
              min
                  + Math.max(
                      0, b.domain.card().min() - b.domain.lub().subtract(a.domain.glb()).getSize());
        }

        a.domain.inCardinality(store.level, a, min, Integer.MAX_VALUE);
      }

    } while (store.propagationHasOccurred);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return SetDomain.ANY;
  }

  @Override
  public boolean satisfied() {
    return grounded() && a.domain.subtract(b.domain).eq(c.domain);
  }

  @Override
  public String toString() {
    return id() + " : AdiffBeqC(" + a + ", " + b + ", " + c + " )";
  }

  @Override
  public void queueVariable(int level, Var variable) {

    if (variable == a) {
      aHasChanged = true;
    } else if (variable == b) {
      bHasChanged = true;
    } else if (variable == c) {
      cHasChanged = true;
    }
  }
}
