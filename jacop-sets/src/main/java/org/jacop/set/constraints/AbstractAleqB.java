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
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
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
  /**
   * The common propagation of a {@literal <=} b and a {@literal <} b: a non-empty a makes b
   * non-empty with no element below the smallest element a may have, and the constraint fails when
   * even the lexicographically smallest value of a is not before the largest value of b.
   *
   * @param store the constraint store
   */
  protected void consistencyLexBounds(Store store) {

    if (!a.domain.lub().isEmpty() && (a.domain.card().min() > 0 || !a.domain.glb().isEmpty())) {
      // b = {} is before any non-empty a, and an element of b below min(a) puts b before a
      b.domain.inCardinality(store.level, b, 1, IntDomain.MAX_INT);
      b.domain.inLub(store.level, b, new IntervalDomain(a.domain.lub().min(), IntDomain.MAX_INT));
    }

    if (!setLexCompare(lexMin(a), lexMax(b))) {
      throw Store.failException;
    }
  }

  /**
   * The lexicographically smallest value of a set variable, ignoring its cardinality: the elements
   * of the lub up to the largest element of the glb (a proper prefix is smaller and an element
   * between two glb elements makes the sequence smaller).
   */
  static IntDomain lexMin(SetVar v) {
    IntDomain glb = v.domain.glb();
    if (glb.isEmpty()) {
      return glb;
    }
    return v.domain.lub().intersect(IntDomain.MIN_INT, glb.max());
  }

  /**
   * The lexicographically largest value of a set variable, ignoring its cardinality: the glb
   * followed by the largest element of the lub (an element between glb elements would make the
   * sequence smaller, and one more element at the end makes it larger).
   */
  static IntDomain lexMax(SetVar v) {
    IntDomain lub = v.domain.lub();
    if (lub.isEmpty()) {
      return lub;
    }
    return v.domain.glb().union(lub.max());
  }
}
