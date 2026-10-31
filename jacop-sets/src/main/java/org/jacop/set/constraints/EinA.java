/*
 * EinA.java
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
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It constructs a constraint which makes sure that a given element is in the domain of the set
 * variable.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class EinA extends PrimitiveConstraint implements Copyable<EinA>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies the element which must be present in the set variable. */
  private final int element;

  /** It specifies the set variable which must contain a specified element. */
  private final SetVar a;

  /** It specifies if the inclusion relation is strict. */
  private boolean strict;

  /**
   * It constructs an eInA constraint to restrict the domain of the variable.
   *
   * @param a variable a for which the restriction is applied.
   * @param element the element that has to be a part of the variable domain.
   * @param strict it specifies if the inclusion relation is strict.
   */
  public EinA(int element, SetVar a, boolean strict) {
    this(element, a);
    this.strict = strict;
  }

  /**
   * It constructs an eInA constraint to restrict the domain of the variable.
   *
   * @param a variable a for which the restriction is applied.
   * @param element the element that has to be a part of the variable domain.
   */
  public EinA(int element, SetVar a) {

    checkInputForNullness("a", new Object[] {a});

    numberId = idNumber.incrementAndGet();

    this.a = a;
    this.element = element;

    setScope(a);
  }

  @Override
  public void consistency(Store store) {

    a.domain.inGlb(store.level, a, element);

    if (strict) {
      a.domain.inCardinality(store.level, a, 2, Integer.MAX_VALUE);
    }
  }

  @Override
  public void notConsistency(Store store) {

    if (!strict) {
      a.domain.inLubComplement(store.level, a, element);
    } else if (a.domain.glb().contains(element)) {
      // the strict inclusion is violated only by a = {element}
      a.domain.inLub(store.level, a, new IntervalDomain(element, element));
    } else if (!a.domain.glb().isEmpty() || a.domain.card().min() > 1) {
      // a cannot be {element}
      a.domain.inLubComplement(store.level, a, element);
    }
  }

  @Override
  public boolean notSatisfied() {
    return !a.domain.lub().contains(element)
        || strict && (a.domain.card().max() <= 1 || a.domain.lub().getSize() <= 1);
  }

  // e in a, on the membership of each element, or null when the explanations are generic
  private SetExplanation.Relation relation(boolean in) {
    return getClass() == EinA.class && !strict ? (e, m) -> e != element || m[0] == in : null;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    SetExplanation.Relation r = relation(true);
    return r != null && SetExplanation.explain(trail, entry, new SetVar[] {a}, r, out);
  }

  @Override
  public boolean explainNegated(AtomicTrail trail, int entry, EntryList out) {
    SetExplanation.Relation r = relation(false);
    return r != null && SetExplanation.explain(trail, entry, new SetVar[] {a}, r, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    SetExplanation.Relation r = relation(true);
    return r != null && SetExplanation.explainFailure(trail, new SetVar[] {a}, r, out);
  }

  @Override
  public boolean explainNegatedFailure(AtomicTrail trail, EntryList out) {
    SetExplanation.Relation r = relation(false);
    return r != null && SetExplanation.explainFailure(trail, new SetVar[] {a}, r, out);
  }

  @Override
  public boolean explainEntailment(
      AtomicTrail trail, int position, boolean entailed, EntryList out) {
    return getClass() == EinA.class
        && !strict
        && SetExplanation.membership(trail, a, element, position, entailed, out);
  }

  @Override
  public boolean satisfied() {
    return a.domain.glb().contains(element)
        && (!strict || a.domain.glb().getSize() > 1 || a.domain.card().min() > 1);
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return SetDomain.ANY;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return SetDomain.ANY;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return SetDomain.GLB_EVENT;
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return SetDomain.ANY;
  }

  @Override
  public String toString() {
    return id() + " : EinA(" + element + ", " + a + " )";
  }

  @Override
  public EinA copy(VarMap map) {
    return new EinA(element, map.get(a), strict);
  }
}
