/*
 * AbstractAleqB.java
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
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * Abstract base class for set lexicographic ordering constraints (AleB and AltB). Provides shared
 * fields, pruning event defaults, and negation delegation.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractAleqB extends PrimitiveConstraint {

  /** It specifies the first variable of the constraint. */
  protected final SetVar a;

  /** It specifies the second variable of the constraint. */
  protected final SetVar b;

  /** Negated constraint used for notConsistency and notSatisfied delegation. */
  PrimitiveConstraint negatedConstraint;

  /**
   * Constructs a lex ordering constraint with full initialization.
   *
   * @param idNum the atomic id counter for the constraint type
   * @param a the left-hand set variable
   * @param b the right-hand set variable
   */
  protected AbstractAleqB(AtomicInteger idNum, SetVar a, SetVar b) {
    checkInputForNullness(new String[] {"a", "b"}, new Object[] {a, b});
    numberId = idNum.incrementAndGet();
    this.a = a;
    this.b = b;
    setScope(a, b);
  }

  /**
   * Constructs a lex ordering constraint for use as a negated helper only. Does not set scope or
   * numberId.
   *
   * @param a the left-hand set variable
   * @param b the right-hand set variable
   */
  protected AbstractAleqB(SetVar a, SetVar b) {
    this.a = a;
    this.b = b;
  }

  /**
   * Performs the lexicographic comparison on two ground set domains.
   *
   * @param x the first domain
   * @param y the second domain
   * @return true if x is lexicographically ordered with respect to y
   */
  abstract boolean setLexCompare(IntDomain x, IntDomain y);

  @Override
  public void notConsistency(Store store) {
    negatedConstraint.consistency(store);
  }

  @Override
  public boolean satisfied() {
    if (a.domain.singleton() && b.domain.singleton()) {
      return setLexCompare(a.domain.glb(), b.domain.glb());
    }
    return false;
  }

  @Override
  public boolean notSatisfied() {
    return ((AbstractAleqB) negatedConstraint).satisfied();
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return SetDomain.ANY;
  }

  /**
   * Shared consistency logic for the common prefix comparison between a's lub and b's glb.
   *
   * @param store the constraint store
   */
  protected void consistencyCommonPrefix(Store store) {
    if (b.domain.glb().getSize() <= 0) {
      return;
    }
    ValueEnumeration aLubEnum = a.domain.lub().valueEnumeration();
    ValueEnumeration bGlbEnum = b.domain.glb().valueEnumeration();
    int be = bGlbEnum.nextElement();
    compareCommonPrefixLoop(store, aLubEnum, bGlbEnum, be);
  }

  /**
   * Compares elements in the common prefix of a's lub and b's glb. Returns when comparison
   * determines ordering; throws Store.failException if incompatible.
   */
  private void compareCommonPrefixLoop(
      Store store, ValueEnumeration aLubEnum, ValueEnumeration bGlbEnum, int be) {
    int ae;
    do {
      if (!aLubEnum.hasMoreElements()) {
        return; // b has more elements and up to now all equal
      }
      ae = aLubEnum.nextElement();

      if (ae == be) {
        if (bGlbEnum.hasMoreElements()) {
          be = bGlbEnum.nextElement();
          if (!aLubEnum.hasMoreElements()) {
            return; // b has more elements than a
          }
        } else {
          afterCommonPrefix(store, a, b, aLubEnum, ae);
          return;
        }
      } else if (ae < be) {
        return; // b already greater
      } else {
        throw Store.failException;
      }
    } while (true);
  }

  /**
   * Hook called after the common prefix loop when bGlbEnum is exhausted. Subclasses may override to
   * add strict-less-than checks.
   *
   * @param store the constraint store
   * @param a the first set variable
   * @param b the second set variable
   * @param aLubEnum the enumeration of a's lub values (positioned after the common prefix)
   * @param lastAe the last element value read from aLubEnum
   */
  protected void afterCommonPrefix(
      Store store, SetVar a, SetVar b, ValueEnumeration aLubEnum, int lastAe) {
    // Default: no additional check (used by AleB)
  }
}
