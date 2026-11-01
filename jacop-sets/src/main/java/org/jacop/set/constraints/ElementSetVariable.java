/*
 * ElementSetVariable.java
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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.constraints.AbstractElement;
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
 * ElementSetVariable constraint defines a relation list[index - indexOffset] = value. This version
 * uses bounds consistency.
 *
 * <p>The first element of the list corresponds to index - indexOffset = 1. By default indexOffset
 * is equal 0 so first value within a list corresponds to index equal 1.
 *
 * <p>If index has a domain from 0 to list.length-1 then indexOffset has to be equal -1 to make
 * addressing of list array starting from 1.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ElementSetVariable extends AbstractElement
    implements Copyable<ElementSetVariable>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies variable value within an element constraint list[index - indexOffset] = value. */
  private final SetVar value;

  /**
   * It specifies list of variables within an element constraint list[index - indexOffset] = value.
   * The list is addressed by positive integers ({@code >=1}) if indexOffset is equal to 0.
   */
  private final SetVar[] list;

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of variables from which an index-th element is taken
   * @param value a value of the index-th element from list
   * @param indexOffset shift applied to index variable.
   */
  public ElementSetVariable(IntVar index, SetVar[] list, SetVar value, int indexOffset) {

    super(index, indexOffset);
    checkInputForNullness(new String[] {"index", "value"}, new Object[] {index, value});
    checkInputForNullness("list", list);

    queueIndex = 2;

    this.numberId = idNumber.incrementAndGet();
    this.value = value;
    this.list = Arrays.copyOf(list, list.length);

    setScope(Stream.concat(Stream.concat(Stream.of(index), Arrays.stream(list)), Stream.of(value)));
  }

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of variables from which an index-th element is taken
   * @param value a value of the index-th element from list
   */
  public ElementSetVariable(IntVar index, List<? extends SetVar> list, SetVar value) {

    this(index, list.toArray(new SetVar[0]), value, 0);
  }

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of variables from which an index-th element is taken
   * @param value a value of the index-th element from list
   * @param indexOffset shift applied to index variable.
   */
  public ElementSetVariable(
      IntVar index, List<? extends SetVar> list, SetVar value, int indexOffset) {

    this(index, list.toArray(new SetVar[0]), value, indexOffset);
  }

  /**
   * It constructs an element constraint.
   *
   * @param index variable index
   * @param list list of variables from which an index-th element is taken
   * @param value a value of the index-th element from list
   */
  public ElementSetVariable(IntVar index, SetVar[] list, SetVar value) {

    this(index, list, value, 0);
  }

  @Override
  protected int listLength() {
    return list.length;
  }

  @Override
  public void impose(Store store) {
    imposeInit(store);
  }

  @Override
  public void consistency(Store store) {

    if (init.begin(store)) {
      initFirstConsistencyCheck(store);
    }

    if (value.singleton() && index.singleton()) {
      SetVar v = list[index.value() - 1 - indexOffset];
      v.domain.in(store.level, v, value.dom());
      v.domain.inCardinality(store.level, v, value.domain.card().min(), value.domain.card().max());
      removeConstraint();
      return;
    }

    if (index.singleton()) {
      SetVar v = list[index.value() - 1 - indexOffset];
      v.domain.in(store.level, v, value.dom());
      value.domain.in(store.level, value, v.dom());
      v.domain.inCardinality(store.level, v, value.domain.card().min(), value.domain.card().max());
      value.domain.inCardinality(store.level, value, v.domain.card().min(), v.domain.card().max());
      return;
    }

    IntDomain glb = new IntervalDomain(IntDomain.MIN_INT, IntDomain.MAX_INT);
    IntDomain lub = new IntervalDomain();
    IntervalDomain indexDom = new IntervalDomain(5); // create with size 5 ;)
    for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
      int position = e.nextElement() - 1 - indexOffset;

      if (!list[position].domain.glb().subtract(value.domain.lub()).isEmpty()
          || !value.domain.glb().subtract(list[position].domain.lub()).isEmpty()) {
        if (indexDom.size == 0) {
          indexDom.unionAdapt(position + 1 + indexOffset);
        } else {
          indexDom.addLastElement(position + 1 + indexOffset);
        }
      } else {
        glb = glb.intersect(list[position].domain.glb());
        lub.unionAdapt(list[position].domain.lub());
      }
    }
    index.domain.in(store.level, index, indexDom.complement());
    value.domain.in(store.level, value, glb, lub);

    if (index.singleton()) {
      // index is singleton; value == list[index - 1 - offset]
      SetVar lp = list[index.value() - 1 - indexOffset];
      lp.domain.in(store.level, lp, value.dom());
      value.domain.in(store.level, value, lp.dom());
      lp.domain.inCardinality(
          store.level, lp, value.domain.card().min(), value.domain.card().max());
      value.domain.inCardinality(
          store.level, value, lp.domain.card().min(), lp.domain.card().max());
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
    // the set variables need the set ANY event; IntDomain.ANY is the set LUB event
    return v == index ? IntDomain.ANY : SetDomain.ANY;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    throw new IllegalStateException("Not implemented as more precise variants exist.");
  }

  /*
   * LCG explanations: an index is excluded when its set and value disagree on an element (in one,
   * out of the other); an element is in (out of) value when it is in (out of) the set of every index
   * left; with the index fixed, the set it names and value pass memberships and cardinality bounds
   * to each other. The failure is that no index is left.
   */

  // the mirrored set and element of each membership variable (element MIN_VALUE: the cardinality);
  // set -1 is value
  private IdentityHashMap<IntVar, int[]> owners;

  private SetVar set(int k) {
    return k < 0 ? value : list[k];
  }

  private int[] owner(IntVar y) {
    if (owners == null) {
      IdentityHashMap<IntVar, int[]> map = new IdentityHashMap<>();
      for (int k = -1; k < list.length; k++) {
        SetMirror m = set(k).lcgMirror();
        if (m == null) {
          continue;
        }
        for (int e : m.elements()) {
          map.putIfAbsent(m.member(e), new int[] {k, e});
        }
        map.putIfAbsent(m.cardinality(), new int[] {k, Integer.MIN_VALUE});
      }
      owners = map;
    }
    return owners.get(y);
  }

  private boolean mirrored() {
    if (getClass() != ElementSetVariable.class || value.lcgMirror() == null) {
      return false;
    }
    // a set fixed when the mirrors were made has none and does not change
    for (SetVar s : list) {
      if (s.lcgMirror() == null && !s.singleton()) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (!mirrored()) {
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
            case AtomicTrail.NE -> incompatible(trail, v, entry, out);
            case AtomicTrail.GE -> indexesImpossible(trail, Integer.MIN_VALUE, v - 1, entry, out);
            default -> indexesImpossible(trail, v + 1, Integer.MAX_VALUE, entry, out);
          };
    } else {
      int[] o = owner(y);
      if (o == null) {
        return false;
      }
      done = set(o[0]).lcgMirror().explain(trail, entry, out);
      if (!done) {
        out.truncate(mark);
        done = o[0] < 0 && everyIndex(trail, o[1], entry, out);
        if (!done) {
          out.truncate(mark);
          done = fromOther(trail, o, entry, out);
        }
      }
    }
    if (!done) {
      out.truncate(mark);
    }
    return done;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (!mirrored()) {
      return false;
    }
    int mark = out.size();
    if (indexesImpossible(trail, Integer.MIN_VALUE, Integer.MAX_VALUE, trail.size(), out)) {
      return true;
    }
    out.truncate(mark);
    return false;
  }

  // whether every index value in [lo, hi] was removed before the position or names a set that
  // disagrees with value; the bounds of the index cited narrow the range
  private boolean indexesImpossible(
      AtomicTrail trail, int lo, int hi, int position, EntryList out) {
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
          && !incompatible(trail, v, position, out)) {
        return false;
      }
    }
    return true;
  }

  // whether the set of index value v and value disagree on an element just before the position
  private boolean incompatible(AtomicTrail trail, int v, int position, EntryList out) {
    int i = v - 1 - indexOffset;
    if (i < 0 || i >= list.length) {
      return true;
    }
    return disagree(trail, list[i], value, position, out)
        || disagree(trail, value, list[i], position, out);
  }

  // whether an element is in a and out of b just before the position
  private static boolean disagree(
      AtomicTrail trail, SetVar a, SetVar b, int position, EntryList out) {
    SetMirror m = a.lcgMirror();
    IntDomain lub = m == null ? a.domain.lub() : m.rootLub();
    for (ValueEnumeration en = lub.valueEnumeration(); en.hasMoreElements(); ) {
      int e = en.nextElement();
      int mark = out.size();
      if (SetExplanation.membership(trail, a, e, position, true, out)) {
        if (SetExplanation.membership(trail, b, e, position, false, out)) {
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  // whether an element's membership in value holds for the set of every index left; the indexes
  // whose set does not have it are cited as excluded
  private boolean everyIndex(AtomicTrail trail, int element, int entry, EntryList out) {
    if (element == Integer.MIN_VALUE) {
      return false;
    }
    int kind = trail.kind(entry);
    boolean in = kind == AtomicTrail.GE || (kind == AtomicTrail.NE && trail.value(entry) == 0);
    int from = Math.max(1 + indexOffset, trail.minBefore(index, entry));
    int to = Math.min(list.length + indexOffset, trail.maxBefore(index, entry));
    trail.addLowerBound(index, entry, out);
    trail.addUpperBound(index, entry, out);
    for (int w = from; w <= to; w++) {
      if (!trail.excludedBefore(index, w, entry, out)
          && !SetExplanation.membership(
              trail, list[w - 1 - indexOffset], element, entry, in, out)) {
        return false;
      }
    }
    return true;
  }

  // with the index fixed, an atom of the set it names from the same membership or cardinality of
  // value, or an atom of value from that set
  private boolean fromOther(AtomicTrail trail, int[] o, int entry, EntryList out) {
    int w = trail.minBefore(index, entry);
    if (trail.maxBefore(index, entry) != w
        || o[0] >= 0 && w != o[0] + 1 + indexOffset
        || w - 1 - indexOffset < 0
        || w - 1 - indexOffset >= list.length) {
      return false;
    }
    SetVar other = o[0] < 0 ? list[w - 1 - indexOffset] : value;
    trail.addLowerBound(index, entry, out);
    trail.addUpperBound(index, entry, out);
    int kind = trail.kind(entry);
    int v = trail.value(entry);
    if (o[1] != Integer.MIN_VALUE) {
      boolean in = kind == AtomicTrail.GE || (kind == AtomicTrail.NE && v == 0);
      return SetExplanation.membership(trail, other, o[1], entry, in, out);
    }
    if (other.lcgMirror() == null) {
      int size = other.domain.glb().getSize();
      return kind == AtomicTrail.GE ? size >= v : kind == AtomicTrail.LE && size <= v;
    }
    IntVar card = other.lcgMirror().cardinality();
    if (kind == AtomicTrail.GE && trail.minBefore(card, entry) >= v) {
      trail.addBoundReaching(card, entry, true, v, out);
      return true;
    }
    if (kind == AtomicTrail.LE && trail.maxBefore(card, entry) <= v) {
      trail.addBoundReaching(card, entry, false, v, out);
      return true;
    }
    return false;
  }

  @Override
  public String toString() {
    return buildToString("elementSetVariable", list, value, true);
  }

  @Override
  public ElementSetVariable copy(VarMap map) {
    return new ElementSetVariable(map.get(index), map.get(list), map.get(value), indexOffset);
  }
}
