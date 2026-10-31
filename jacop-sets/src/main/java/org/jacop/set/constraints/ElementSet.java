/*
 * ElementSet.java
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

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It is an element constraint that make sure that set variable value has a domain equal to the
 * index-th element of the supplied list of sets.
 *
 * <p>By default, indexing starts from 1, if it is required to be different for example starting
 * from 0, then indexOffset must be specified to be equal to -1.
 *
 * @author Radoslaw Szymanek, Krzysztof Kuchcinski and Robert Åkemalm
 * @version 5.0
 */
public class ElementSet extends Constraint
    implements SatisfiedPresent, Copyable<ElementSet>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies what element from the list of sets is equal to set variable value. */
  private final IntVar index;

  /**
   * It specifies a list of sets from which one element will be made equal to set variable value.
   */
  private final IntDomain[] list;

  /**
   * It specifies the set variable which is equal to one of the sets from the list as indicated by
   * int variable index.
   */
  private final SetVar value;

  /**
   * It allows to offset the indexing. By default the indexing starts from 1, if index variable
   * starts from 0, and 0 denotes the first element then indexOffset should be set to -1.
   */
  private final int indexOffset;

  /**
   * It constructs a constraint to restrict the domains of the variables index and value.
   *
   * @param value variable that is restricted to have the same elements as list[index].
   * @param list array of sets that contains possible values for variable value.
   * @param index variable that is restricted to be the index of sets for which list[index] ==
   *     value.
   * @param indexOffset the shift applied to the index variable.
   */
  public ElementSet(IntVar index, IntDomain[] list, SetVar value, int indexOffset) {

    checkInputForNullness(
        new String[] {"index", "list", "value"}, new Object[][] {{index}, list, {value}});

    numberId = idNumber.incrementAndGet();

    this.index = index;
    this.value = value;
    this.indexOffset = indexOffset;
    this.list = Arrays.copyOf(list, list.length);

    setScope(index, value);
  }

  /**
   * It constructs an elementSet constraint to restrict the domains of the variables index and
   * value.
   *
   * @param value variable that is restricted to have the same elements as list[index].
   * @param list array of sets that contains possible values for variable value.
   * @param index variable that is restricted to be the index of sets for which list[index] ==
   *     value.
   */
  public ElementSet(IntVar index, IntDomain[] list, SetVar value) {
    this(index, list, value, 0);
  }

  @Override
  public void consistency(Store store) {

    SetDomain valueDom = value.domain;
    IntDomain indexDom = index.domain;
    IntDomain newIndex = new IntervalDomain();

    IntDomain newValueGlb = valueDom.lub().cloneLight();
    IntDomain newValueLub = new IntervalDomain();

    ValueEnumeration enumer = indexDom.valueEnumeration();
    int el;

    // Only the indexes whose set is compatible with the current domain of value (bounds and
    // cardinality) remain, and only those support the new bounds of value; otherwise pruning
    // index would require another run.
    while (enumer.hasMoreElements()) {
      el = enumer.nextElement() - 1 - indexOffset;
      if (el >= 0) {
        if (el >= list.length) {
          break;
        }
        if (valueDom.lub().contains(list[el])
            && list[el].contains(valueDom.glb())
            && valueDom.card().contains(list[el].getSize())) {
          newIndex.unionAdapt(el + 1 + indexOffset, el + 1 + indexOffset);
          newValueGlb = newValueGlb.intersect(list[el]);
          newValueLub.addDom(list[el]);
        }
      }
    }

    index.domain.in(store.level, index, newIndex);
    value.domain.in(store.level, value, newValueGlb, newValueLub);
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
    if (v == value) {
      return SetDomain.ANY;
    } else {
      return IntDomain.ANY;
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    throw new IllegalStateException("Not implemented as more precise variants exist.");
  }

  /*
   * LCG explanations: an index is excluded when its set has an element out of value, misses an
   * element in value, or has a size outside value's cardinality; a membership or a cardinality bound
   * of value holds for every set of an index left; the failure is that no index is left.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    SetMirror m = value.lcgMirror();
    if (getClass() != ElementSet.class || m == null) {
      return false;
    }
    IntVar y = trail.variable(entry);
    int kind = trail.kind(entry);
    int v = trail.value(entry);
    int mark = out.size();
    boolean done;
    if (y == index) {
      done =
          switch (kind) {
            case AtomicTrail.NE -> incompatible(trail, m, v, entry, out);
            case AtomicTrail.GE ->
                indexesImpossible(trail, m, Integer.MIN_VALUE, v - 1, entry, out);
            default -> indexesImpossible(trail, m, v + 1, Integer.MAX_VALUE, entry, out);
          };
    } else {
      done = m.explain(trail, entry, out);
      if (!done) {
        out.truncate(mark);
        done = everyIndex(trail, m, entry, out);
      }
    }
    if (!done) {
      out.truncate(mark);
    }
    return done;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    SetMirror m = value.lcgMirror();
    if (getClass() != ElementSet.class || m == null) {
      return false;
    }
    int mark = out.size();
    if (indexesImpossible(trail, m, Integer.MIN_VALUE, Integer.MAX_VALUE, trail.size(), out)) {
      return true;
    }
    out.truncate(mark);
    return false;
  }

  // whether every index value in [lo, hi] was removed before the position or names an incompatible
  // set; the bounds of the index cited narrow the range
  private boolean indexesImpossible(
      AtomicTrail trail, SetMirror m, int lo, int hi, int position, EntryList out) {
    int from = Math.max(lo, 1 + indexOffset);
    int to = Math.min(hi, list.length + indexOffset);
    if (from < trail.minBefore(index, position)) {
      trail.addLowerBound(index, position, out);
      from = trail.minBefore(index, position);
    }
    if (to > trail.maxBefore(index, position)) {
      trail.addUpperBound(index, position, out);
      to = trail.maxBefore(index, position);
    }
    for (int v = from; v <= to; v++) {
      if (!trail.excludedBefore(index, v, position, out)
          && !incompatible(trail, m, v, position, out)) {
        return false;
      }
    }
    return true;
  }

  // whether the set of index value v cannot be value just before the position
  private boolean incompatible(AtomicTrail trail, SetMirror m, int v, int position, EntryList out) {
    int i = v - 1 - indexOffset;
    if (i < 0 || i >= list.length) {
      return true;
    }
    IntDomain set = list[i];
    for (ValueEnumeration e = set.valueEnumeration(); e.hasMoreElements(); ) {
      if (SetExplanation.membership(trail, value, e.nextElement(), position, false, out)) {
        return true;
      }
    }
    for (ValueEnumeration e = m.rootGlb().valueEnumeration(); e.hasMoreElements(); ) {
      if (!set.contains(e.nextElement())) {
        return true;
      }
    }
    for (int e : m.elements()) {
      if (!set.contains(e) && SetExplanation.membership(trail, value, e, position, true, out)) {
        return true;
      }
    }
    IntVar[] vars = m.mirrorVariables();
    IntVar card = vars[vars.length - 1];
    int size = set.getSize();
    if (size < trail.minBefore(card, position)) {
      trail.addBoundReaching(card, position, true, size + 1L, out);
      return true;
    }
    if (size > trail.maxBefore(card, position)) {
      trail.addBoundReaching(card, position, false, size - 1L, out);
      return true;
    }
    return false;
  }

  // whether an atom of value holds for the set of every index left: the indexes whose set breaks it
  // are cited as excluded
  private boolean everyIndex(AtomicTrail trail, SetMirror m, int entry, EntryList out) {
    IntVar y = trail.variable(entry);
    int kind = trail.kind(entry);
    int v = trail.value(entry);
    IntVar[] vars = m.mirrorVariables();
    boolean isCard = y == vars[vars.length - 1];
    int element = 0;
    if (!isCard) {
      boolean found = false;
      for (int e : m.elements()) {
        if (m.member(e) == y) {
          element = e;
          found = true;
          break;
        }
      }
      if (!found) {
        return false;
      }
    }
    boolean in = kind == AtomicTrail.GE || (kind == AtomicTrail.NE && v == 0);
    int from = Math.max(1 + indexOffset, trail.minBefore(index, entry));
    int to = Math.min(list.length + indexOffset, trail.maxBefore(index, entry));
    trail.addLowerBound(index, entry, out);
    trail.addUpperBound(index, entry, out);
    for (int w = from; w <= to; w++) {
      IntDomain set = list[w - 1 - indexOffset];
      boolean holds;
      if (isCard) {
        holds =
            switch (kind) {
              case AtomicTrail.GE -> set.getSize() >= v;
              case AtomicTrail.LE -> set.getSize() <= v;
              default -> set.getSize() != v;
            };
      } else {
        holds = set.contains(element) == in;
      }
      if (!holds && !trail.excludedBefore(index, w, entry, out)) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean satisfied() {
    if (!grounded()) {
      return false;
    }
    int position = index.value() - 1 - indexOffset;
    return position >= 0 && position < list.length && list[position].eq(value.domain.glb());
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder();

    result.append(id()).append(" : ElementSet( ").append(index).append(", [ ");

    for (IntDomain s : list) {
      result.append(s).append(" ");
    }

    result.append(" ], ").append(value).append(" )");

    return result.toString();
  }

  @Override
  public ElementSet copy(VarMap map) {
    return new ElementSet(map.get(index), list, map.get(value), indexOffset);
  }
}
