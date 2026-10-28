/*
 * SetMirror.java
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

package org.jacop.set.constraints;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * Mirrors a set variable by integer variables for lazy clause generation: a 0/1 variable for the
 * membership of each element of its least upper bound that is not in its greatest lower bound, and
 * a variable for its cardinality. The two are kept equal both ways: this constraint passes the
 * mirror's values to the set, and every change of the set's domain is passed to the mirror at once,
 * inside the constraint that made it ({@link SetVar#domainHasChanged}), so the mirror's atoms get
 * that constraint as reason. The atoms of the mirror then describe the set's domain and stand for
 * it in the generic reasons of the set constraints.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class SetMirror extends Constraint implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private final SetVar set;

  private final int[] elements;

  private final IntVar[] members;

  private final IntVar cardinality;

  private final IntVar[] mirror;

  private final Store store;

  // the set's domain when the mirror was made
  private final IntDomain glb;

  private final IntDomain lub;

  /**
   * Creates the mirror of a set variable, with its variables in the set's store, and attaches it to
   * the set. It still has to be imposed.
   *
   * @param set the set variable
   */
  public SetMirror(SetVar set) {
    this(set, openElements(set), null);
  }

  private SetMirror(SetVar set, int[] elements, IntVar[] mirror) {
    checkInputForNullness("set", new Object[] {set});
    this.numberId = idNumber.incrementAndGet();
    this.set = set;
    this.store = set.getStore();
    this.elements = elements;
    SetDomain d = set.domain;
    glb = d.glb().cloneLight();
    lub = d.lub().cloneLight();
    if (mirror == null) {
      mirror = new IntVar[elements.length + 1];
      for (int k = 0; k < elements.length; k++) {
        mirror[k] = new IntVar(store, set.id() + "_has_" + elements[k], 0, 1);
      }
      IntDomain card = d.card();
      mirror[elements.length] = new IntVar(store, set.id() + "_card", card.min(), card.max());
    }
    this.mirror = mirror;
    members = Arrays.copyOf(mirror, elements.length);
    cardinality = mirror[elements.length];
    Var[] scope = Arrays.copyOf(mirror, mirror.length + 1, Var[].class);
    scope[mirror.length] = set;
    setScope(scope);
    set.setMirror(this);
  }

  // the elements of the least upper bound that are not in the greatest lower bound
  private static int[] openElements(SetVar set) {
    IntDomain open = set.domain.lub().subtract(set.domain.glb());
    int[] elements = new int[open.getSize()];
    int k = 0;
    for (var e = open.valueEnumeration(); e.hasMoreElements(); ) {
      elements[k++] = e.nextElement();
    }
    return elements;
  }

  /**
   * Copies the set variable into another store, with its domain when this mirror was made, and
   * imposes there its mirror by the given variables.
   *
   * @param target the store of the copy
   * @param mirror the mirror's variables in that store, in the order of {@link #mirrorVariables()}
   * @return the copy of the set variable
   */
  public SetVar copyTo(Store target, IntVar[] mirror) {
    SetVar copy = new SetVar(target, set.id(), new BoundSetDomain(glb, lub));
    target.impose(new SetMirror(copy, elements, mirror));
    return copy;
  }

  /**
   * Returns the integer variables of the mirror: the memberships, then the cardinality.
   *
   * @return the variables
   */
  public IntVar[] mirrorVariables() {
    return mirror;
  }

  /** Passes the set's current domain to the mirror. */
  public void follow() {
    int level = store.level;
    SetDomain d = set.domain;
    IntDomain glb = d.glb();
    IntDomain lub = d.lub();
    for (int i = 0; i < elements.length; i++) {
      // a membership fixed the other way fails, as it may not have reached the set yet
      IntVar b = members[i];
      if (glb.contains(elements[i])) {
        if (b.min() == 0) {
          b.domain.in(level, b, 1, 1);
        }
      } else if (!lub.contains(elements[i]) && b.max() == 1) {
        b.domain.in(level, b, 0, 0);
      }
    }
    IntDomain card = d.card();
    if (cardinality.min() < card.min() || cardinality.max() > card.max()) {
      cardinality.domain.in(level, cardinality, card.min(), card.max());
    }
  }

  @Override
  public void consistency(Store store) {
    int level = store.level;
    for (int i = 0; i < elements.length; i++) {
      IntVar b = members[i];
      if (b.singleton()) {
        SetDomain d = set.domain;
        if (b.value() == 1) {
          if (!d.glb().contains(elements[i])) {
            d.inGlb(level, set, elements[i]);
          }
        } else if (d.lub().contains(elements[i])) {
          d.inLubComplement(level, set, elements[i]);
        }
      }
    }
    IntDomain card = set.domain.card();
    if (cardinality.min() > card.min() || cardinality.max() < card.max()) {
      set.domain.inCardinality(level, set, cardinality.min(), cardinality.max());
    }
    follow();
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    throw new IllegalStateException("Not implemented as more precise variant exists.");
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }
    if (v == set) {
      return SetDomain.ANY;
    }
    return v == cardinality ? IntDomain.BOUND : IntDomain.GROUND;
  }

  @Override
  public boolean satisfied() {
    return grounded();
  }

  @Override
  public String toString() {
    return id() + " : setMirror(" + set + ", " + Arrays.toString(mirror) + ")";
  }
}
