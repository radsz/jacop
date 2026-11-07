/*
 * In.java
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
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.DomainCover;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;

/**
 * Constraints X to belong to a specified domain.
 *
 * <p>Domain consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class In extends PrimitiveConstraint implements Copyable<In>, Explainable, PbEncodable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies variable x whose domain must lie within a specified domain. */
  final IntVar x;

  /** It specifies domain d which restricts the possible value of the specified variable. */
  final IntDomain dom;

  /** It specifies all the values which can not be taken by a variable. */
  private final IntDomain domComplement;

  /**
   * It constructs an In constraint to restrict the domain of the variable.
   *
   * @param x variable x for which the restriction is applied.
   * @param dom the domain to which the variables domain is restricted.
   */
  public In(IntVar x, IntDomain dom) {

    checkInputForNullness(new String[] {"x", "dom"}, new Object[] {x, dom});

    numberId = idNumber.incrementAndGet();

    this.x = x;
    this.dom = dom;
    this.domComplement = dom.complement();

    setScope(x);
  }

  @Override
  public void consistency(Store store) {
    x.domain.in(store.level, x, dom);

    removeConstraint();
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return Domain.NONE;
  }

  @Override
  public void notConsistency(Store store) {
    x.domain.in(store.level, x, domComplement);
  }

  @Override
  public boolean notSatisfied() {
    return !x.domain.isIntersecting(dom);
    // !dom.contains(x.domain);
  }

  @Override
  public boolean satisfied() {
    return // x.singleton() &&
    dom.contains(x.domain);
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
    return Domain.NONE;
  }

  // the values the constraint (or its negation) rules out need no reason
  private DomainCover.ValueReason outside(boolean in) {
    return (v, out) -> dom.contains(v) != in;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return getClass() == In.class && DomainCover.entry(trail, entry, outside(true), out);
  }

  @Override
  public boolean explainNegated(AtomicTrail trail, int entry, EntryList out) {
    return getClass() == In.class && DomainCover.entry(trail, entry, outside(false), out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == In.class && DomainCover.domain(trail, x, trail.size(), outside(true), out);
  }

  @Override
  public boolean explainNegatedFailure(AtomicTrail trail, EntryList out) {
    return getClass() == In.class
        && DomainCover.domain(trail, x, trail.size(), outside(false), out);
  }

  @Override
  public boolean explainEntailment(
      AtomicTrail trail, int position, boolean entailed, EntryList out) {
    // entailed: each value between the bounds of x is in dom or out of the domain of x
    return getClass() == In.class
        && DomainCover.domain(trail, x, position, outside(!entailed), out);
  }

  @Override
  public String toString() {
    return id() + " : In(" + x + ", " + dom + " )";
  }

  @Override
  public Constraint getGuideConstraint() {
    return new XeqC(x, x.min());
  }

  @Override
  public int getGuideValue() {
    return x.min();
  }

  @Override
  public Var getGuideVariable() {
    return x;
  }

  @Override
  public In copy(VarMap map) {
    return new In(map.get(x), dom);
  }

  @Override
  public boolean encode(PbModel model) {
    return encodeImplied(model, "1", false);
  }

  /**
   * States the domain, or its negation, by a clause per interval of values x cannot take: the
   * intervals outside the domain, or those of the domain when negated.
   */
  @Override
  public boolean encodeImplied(PbModel model, String literal, boolean negated) {
    if (getClass() != In.class) {
      return false;
    }
    if ("0".equals(literal)) {
      return true;
    }
    IntDomain root = model.domain(x);
    IntDomain excluded = negated ? dom : domComplement;
    for (IntervalEnumeration e = excluded.intervalEnumeration(); e.hasMoreElements(); ) {
      Interval i = e.nextElement();
      if (i.max() < root.min() || i.min() > root.max()) {
        continue;
      }
      // not (l <= x <= u)
      String above = i.max() >= root.max() ? "0" : model.atLeast(x, i.max() + 1);
      model.clause(PbModel.not(literal), PbModel.not(model.atLeast(x, i.min())), above);
    }
    return true;
  }
}
