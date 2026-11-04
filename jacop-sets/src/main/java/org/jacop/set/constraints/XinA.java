/*
 * XinA.java
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
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.DomainCover;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It creates a constraint that makes sure that the value assigned to integer variable x is included
 * in the set assigned to the set variable a.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski.
 * @version 5.0
 */
public class XinA extends PrimitiveConstraint implements Copyable<XinA>, Explainable, PbEncodable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies variable a. */
  private final IntVar x;

  /** It specifies variable b. */
  private final SetVar a;

  /** It specifies if the inclusion relation is strict. */
  private boolean strict;

  /**
   * It constructs an XinY constraint to restrict the domain of the variables X and Y.
   *
   * @param x variable x that is restriction to be a subset of y.
   * @param a variable that is restricted to contain x.
   * @param strict it specifies if the inclusion relation is strict.
   */
  public XinA(IntVar x, SetVar a, boolean strict) {

    this(x, a);
    this.strict = strict;
  }

  /**
   * It constructs an XinA constraint to restrict the domain of the variables X and A.
   *
   * @param x variable x that is restriction to be a subset of A.
   * @param a variable that is restricted to contain x.
   */
  public XinA(IntVar x, SetVar a) {

    checkInputForNullness(new String[] {"x", "a"}, new Object[] {x, a});

    this.numberId = idNumber.incrementAndGet();

    this.x = x;
    this.a = a;

    setScope(x, a);
  }

  @Override
  public void consistency(Store store) {

    x.domain.in(store.level, x, a.domain.lub());

    if (strict) {
      a.domain.inCardinality(store.level, a, 2, Integer.MAX_VALUE);
    } else {
      a.domain.inCardinality(store.level, a, 1, Integer.MAX_VALUE);
    }

    if (x.singleton()) {
      a.domain.inGlb(store.level, a, x.value());
    }

    if (!x.domain.isIntersecting(a.domain.lub())) {
      throw Store.failException;
    }
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {

    // If consistency function mode
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }

    if (v == x) {
      return IntDomain.ANY;
    } else {
      return SetDomain.ANY;
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    throw new IllegalStateException("Not implemented as more precise variant exists.");
  }

  @Override
  public int getNotConsistencyPruningEvent(Var v) {
    Integer possibleEvent = getNotConsistencyPruningEventFromMap(v);
    if (possibleEvent != null) {
      return possibleEvent;
    }

    if (v == x) {
      return IntDomain.ANY;
    } else {
      return SetDomain.GLB_EVENT;
    }
  }

  @Override
  public void notConsistency(Store store) {

    if (strict && a.domain.glb().getSize() <= 1 && a.domain.card().min() <= 1) {
      // a may still be {x}, which violates the strict inclusion
      notConsistencyStrict(store);
      return;
    }

    if (x.singleton()) {
      a.domain.inLubComplement(store.level, a, x.value());
    }

    IntDomain xDom = x.domain.subtract(a.domain.glb());

    if (xDom.getSize() == 0) {
      throw Store.failException;
    }

    x.domain.in(store.level, x, xDom);
  }

  /**
   * The negation of the strict inclusion, x not in a or a = {x}, while a has at most one element in
   * its glb and may have one element.
   */
  private void notConsistencyStrict(Store store) {

    if (a.domain.glb().isEmpty()) {
      return;
    }
    int g = a.domain.glb().min();
    if (!x.singleton()) {
      return;
    }
    if (x.value() == g) {
      // x is in a, so a must be {x}
      a.domain.inLub(store.level, a, a.domain.glb());
    } else {
      // a contains g, so it is not {x}
      a.domain.inLubComplement(store.level, a, x.value());
    }
  }

  @Override
  public boolean notSatisfied() {

    return !a.domain.lub().isIntersecting(x.domain)
        || strict && (a.domain.card().max() <= 1 || a.domain.lub().getSize() <= 1);
  }

  @Override
  public boolean satisfied() {
    return a.domain.glb().contains(x.domain) && (!strict || a.domain.glb().getSize() > 1);
  }

  @Override
  public int getNestedPruningEvent(Var v, boolean mode) {
    if (mode) {
      Integer possibleEvent = getConsistencyPruningEventFromMap(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    } else {
      Integer possibleEvent = getNotConsistencyPruningEventFromMap(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }
    if (v == x) {
      return IntDomain.ANY;
    } else {
      return SetDomain.GLB_EVENT;
    }
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    throw new IllegalStateException("Not implemented as more precise variant exists.");
  }

  // the explanations cover x in a (or x not in a) only, with a mirrored
  private SetMirror mirror() {
    return getClass() == XinA.class && !strict ? a.lcgMirror() : null;
  }

  // a value of x is ruled out by its element being out of a (in a for the negation)
  private DomainCover.ValueReason elementOut(AtomicTrail trail, int position, boolean in) {
    return (v, out) -> SetExplanation.membership(trail, a, v, position, !in, out);
  }

  // the element whose membership variable is y, or null
  private static Integer elementOf(SetMirror m, IntVar y) {
    for (int e : m.elements()) {
      if (m.member(e) == y) {
        return e;
      }
    }
    return null;
  }

  // an atom of x (values ruled out by the set), of a membership (x fixed to the element) or of the
  // cardinality (at least one element, from the constraint alone)
  private boolean explainEntry(AtomicTrail trail, int entry, boolean in, EntryList out) {
    SetMirror m = mirror();
    if (m == null) {
      return false;
    }
    IntVar y = trail.variable(entry);
    if (y == x) {
      return DomainCover.entry(trail, entry, elementOut(trail, entry, in), out);
    }
    int kind = trail.kind(entry);
    if (y == m.cardinality()) {
      return in && kind == AtomicTrail.GE && trail.value(entry) <= 1;
    }
    Integer e = elementOf(m, y);
    boolean member = kind == AtomicTrail.GE || kind == AtomicTrail.NE && trail.value(entry) == 0;
    if (e == null
        || member != in
        || trail.minBefore(x, entry) != e
        || trail.maxBefore(x, entry) != e) {
      return false;
    }
    trail.addLowerBound(x, entry, out);
    trail.addUpperBound(x, entry, out);
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return explainEntry(trail, entry, true, out);
  }

  @Override
  public boolean explainNegated(AtomicTrail trail, int entry, EntryList out) {
    return explainEntry(trail, entry, false, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int now = trail.size();
    return mirror() != null && DomainCover.domain(trail, x, now, elementOut(trail, now, true), out);
  }

  @Override
  public boolean explainNegatedFailure(AtomicTrail trail, EntryList out) {
    int now = trail.size();
    return mirror() != null
        && DomainCover.domain(trail, x, now, elementOut(trail, now, false), out);
  }

  @Override
  public boolean explainEntailment(
      AtomicTrail trail, int position, boolean entailed, EntryList out) {
    // entailed: each value between the bounds of x is in a or out of the domain of x
    return mirror() != null
        && DomainCover.domain(trail, x, position, elementOut(trail, position, !entailed), out);
  }

  @Override
  public String toString() {
    return id() + " : XinA(" + x + ", " + a + " )";
  }

  @Override
  public XinA copy(VarMap map) {
    return new XinA(map.get(x), map.get(a), strict);
  }

  @Override
  public boolean encode(PbModel model) {
    return encodeImplied(model, "1", false);
  }

  /** Writes that the value of x is in a (or not in a), and that a is not empty. */
  @Override
  public boolean encodeImplied(PbModel model, String literal, boolean negated) {
    if (getClass() != XinA.class || strict || !SetPb.stated(a)) {
      return false;
    }
    return model.implied(
        literal,
        () -> {
          for (ValueEnumeration e = model.domain(x).valueEnumeration(); e.hasMoreElements(); ) {
            int v = e.nextElement();
            String in = SetPb.in(model, a, v);
            model.clause(PbModel.not(model.equalTo(x, v)), negated ? PbModel.not(in) : in);
          }
          if (!negated) {
            SetPb.cardinalities(
                model,
                new SetVar[] {a},
                new long[] {1},
                new IntVar[0],
                new long[0],
                LinearForm.GE,
                1);
          }
          return true;
        });
  }
}
