/*
 * AbstractChannel.java
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

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.function.ToIntFunction;
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.api.Violation;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;

abstract class AbstractChannel extends Constraint
    implements Violation, SatisfiedPresent, Explainable, PbEncodable {

  final IntVar x;
  final int n;
  final Item[] item;
  final Map<Integer, IntVar> valueMap = new HashMap<>();
  TimeStamp<Integer> position;

  AbstractChannel(int numberId, IntVar x, IntVar[] bs, int[] value, String constraintName) {
    checkInputForNullness(new String[] {"x", "bs"}, new Object[] {x}, bs);
    checkInputForNullness("value", value);
    if (value.length != bs.length) {
      throw new IllegalArgumentException(
          constraintName
              + ": Status array size ("
              + bs.length
              + "), has not equal size as number of values "
              + value.length);
    }

    checkBooleans(bs, constraintName);
    if (Arrays.stream(value).distinct().count() != value.length) {
      throw new IllegalArgumentException(
          constraintName + ": values " + Arrays.toString(value) + " contain repeated values");
    }

    this.numberId = numberId;
    this.x = x;
    this.n = bs.length;

    item = new Item[n];
    for (int i = 0; i < n; i++) {
      item[i] = new Item(bs[i], value[i]);
    }

    for (int i = 0; i < value.length; i++) {
      valueMap.put(value[i], bs[i]);
    }

    setScope(Stream.concat(Stream.of(x), Arrays.stream(bs)));
    this.queueIndex = 0;
  }

  AbstractChannel(int numberId, IntVar x, Map<Integer, ? extends IntVar> bs) {
    checkInputForNullness(new String[] {"x", "bs"}, new Object[] {x, bs});
    checkInputForNullness("bs", bs.values().toArray());
    checkBooleans(bs.values().toArray(IntVar[]::new), getClass().getSimpleName());
    this.numberId = numberId;
    this.x = x;
    this.n = bs.size();

    item = new Item[n];
    IntVar[] bbs = new IntVar[n];
    int i = 0;
    for (Map.Entry<Integer, ? extends IntVar> e : bs.entrySet()) {
      int val = e.getKey();
      IntVar b = e.getValue();
      item[i] = new Item(b, val);

      valueMap.put(val, b);
      bbs[i] = b;
      i++;
    }

    setScope(Stream.concat(Stream.of(x), Arrays.stream(bbs)));
    this.queueIndex = 0;
  }

  private static void checkBooleans(IntVar[] bs, String constraintName) {
    for (IntVar b : bs) {
      if (b.min() < 0 || b.max() > 1) {
        throw new IllegalArgumentException(
            constraintName + ": variable " + b + " must have a domain within 0..1");
      }
    }
  }

  // each item's b is [x = value] (ChannelReif) or implies it (ChannelImply)
  @Override
  public boolean encode(PbModel model) {
    boolean equivalence = getClass() == ChannelReif.class;
    if (!equivalence && getClass() != ChannelImply.class) {
      return false;
    }
    for (int i = 0; i < n; i++) {
      if (item[i].b() == x) {
        return false;
      }
    }
    for (int i = 0; i < n; i++) {
      model.reified(
          item[i].b(),
          new LinearForm(new IntVar[] {x}, new long[] {1}, item[i].value(), LinearForm.EQ),
          equivalence);
    }
    return true;
  }

  /** The counterparts of the 0/1 variables, in the order of {@link #itemValues()}. */
  IntVar[] itemVariables(VarMap map) {
    IntVar[] bs = new IntVar[n];
    for (int i = 0; i < n; i++) {
      bs[i] = map.get(item[i].b());
    }
    return bs;
  }

  /** The values of the items, in their current order. */
  int[] itemValues() {
    int[] values = new int[n];
    for (int i = 0; i < n; i++) {
      values[i] = item[i].value();
    }
    return values;
  }

  static int[] toArray(IntDomain d) {
    int[] vs = new int[d.getSize()];
    int i = 0;
    for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
      int v = e.nextElement();
      vs[i++] = v;
    }
    return vs;
  }

  void swap(int i, int j) {
    if (i != j) {
      Item tmp = item[i];
      item[i] = item[j];
      item[j] = tmp;
    }
  }

  public boolean satisfied() {
    if (!x.singleton()) {
      return false;
    }
    int value = x.value();
    for (Item i : item) {
      if (!i.b.singleton() || !itemSatisfied(i.b.value() == 1, value == i.value)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Tells whether one item holds once x and its variable b are fixed.
   *
   * @param on whether b is 1
   * @param equal whether x is equal to the value of the item
   * @return true if the item holds
   */
  protected abstract boolean itemSatisfied(boolean on, boolean equal);

  @Override
  public void impose(Store store) {
    super.impose(store);
    position = new TimeStamp<>(store, 0);
  }

  /**
   * Handles the case when b.max() == 0 for a given item index.
   *
   * @param store the constraint store
   * @param i the index of the item
   */
  protected abstract void handleBmaxZero(Store store, int i);

  /**
   * Handles the case when b.min() == 1 for a given item index.
   *
   * @param store the constraint store
   * @param i the index of the item
   */
  protected abstract void handleBminOne(Store store, int i);

  /**
   * Propagates constraints when x becomes a singleton.
   *
   * @param store the constraint store
   * @param start the starting index for propagation
   */
  protected abstract void propagateWhenXisSingleton(Store store, int start);

  @Override
  public void consistency(final Store store) {

    // The same b variable may be used for several values, so fixing b for one value can affect an
    // item that was already visited; repeat the pass until it does not change any domain.
    do {
      store.propagationHasOccurred = false;
      if (!singlePass(store)) {
        return;
      }
    } while (store.propagationHasOccurred);
  }

  /**
   * It executes one pass of the channeling propagation.
   *
   * @param store the constraint store.
   * @return false if the constraint does not need any further propagation, true otherwise.
   */
  private boolean singlePass(final Store store) {

    int start = position.value();
    boolean startChanged = false;

    for (int i = start; i < n; i++) {

      if (item[i].b().max() == 0) {
        handleBmaxZero(store, i);
        swap(start, i);
        start++;
        startChanged = true;
        continue;
      } else if (item[i].b().min() == 1) {
        handleBminOne(store, i);
      }

      if (!x.domain.contains(item[i].value())) {
        item[i].b().domain.inValue(store.level, item[i].b(), 0);
        swap(start, i);
        start++;
        startChanged = true;
      }
    }

    if (startChanged) {
      position.update(start);
    }

    if (start == n) {
      if (!x.singleton()) {
        removeConstraint();
      }
      return false;
    }

    if (x.singleton()) {
      if (!valueMap.containsKey(x.value())) {
        // x is also one of the b variables and was fixed during this pass to a value without an
        // item; the next pass sets the remaining b to 0
        return true;
      }
      propagateWhenXisSingleton(store, start);
    }
    return true;
  }

  // values walked for one reason before giving up on it
  private static final int LCG_MAX_VALUES = 4096;

  // whether b = 0 also forces x != value (ChannelReif), not only b = 1 forcing x = value
  private boolean lcgReified() {
    return getClass() == ChannelReif.class;
  }

  private boolean lcgExplained() {
    if (getClass() != ChannelReif.class && getClass() != ChannelImply.class) {
      return false;
    }
    for (Item it : item) {
      if (it.b() == x) {
        return false;
      }
    }
    return true;
  }

  /**
   * Explains an atom of x by the 0/1 variables fixed before it, and a 0/1 variable by the domain of
   * x.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (!lcgExplained()) {
      return false;
    }
    IntVar y = trail.variable(entry);
    int kind = trail.kind(entry);
    int a = trail.value(entry);
    if (y == x) {
      // x = v for an item whose b was 1
      for (Item it : item) {
        int v = it.value();
        boolean implied =
            kind == AtomicTrail.GE ? v >= a : kind == AtomicTrail.LE ? v <= a : v != a;
        if (implied && trail.minBefore(it.b(), entry) >= 1) {
          trail.addLowerBound(it.b(), entry, out);
          return true;
        }
      }
      // every removed value is out of x already or has its b at 0
      switch (kind) {
        case AtomicTrail.NE -> {
          return offByB(trail, entry, a, out);
        }
        case AtomicTrail.GE -> {
          trail.addLowerBound(x, entry, out);
          return valuesOff(trail, entry, trail.minBefore(x, entry), a - 1L, out);
        }
        default -> {
          trail.addUpperBound(x, entry, out);
          return valuesOff(trail, entry, a + 1L, trail.maxBefore(x, entry), out);
        }
      }
    }
    boolean one = kind == AtomicTrail.GE || kind == AtomicTrail.NE && a == 0;
    int lo = trail.minBefore(x, entry);
    boolean fixed = lo == trail.maxBefore(x, entry);
    for (Item it : item) {
      if (it.b() != y) {
        continue;
      }
      if (one) {
        if (fixed && lo == it.value()) {
          trail.addLowerBound(x, entry, out);
          trail.addUpperBound(x, entry, out);
          return true;
        }
      } else if (trail.excludedBefore(x, it.value(), entry, out)) {
        return true;
      }
    }
    if (!one && fixed) {
      // x is fixed to a value whose own b is another variable
      trail.addLowerBound(x, entry, out);
      trail.addUpperBound(x, entry, out);
      return valueMap.get(lo) != y;
    }
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (!lcgExplained()) {
      return false;
    }
    int now = trail.size();
    int mark = out.size();
    for (Item it : item) {
      if (trail.minBefore(it.b(), now) >= 1) {
        if (trail.excludedBefore(x, it.value(), now, out)) {
          trail.addLowerBound(it.b(), now, out);
          return true;
        }
        for (Item other : item) {
          if (other.b() != it.b()
              && other.value() != it.value()
              && trail.minBefore(other.b(), now) >= 1) {
            trail.addLowerBound(it.b(), now, out);
            trail.addLowerBound(other.b(), now, out);
            return true;
          }
        }
      }
    }
    out.truncate(mark);
    int lo = trail.minBefore(x, now);
    if (valuesOff(trail, now, lo, trail.maxBefore(x, now), out)) {
      trail.addLowerBound(x, now, out);
      trail.addUpperBound(x, now, out);
      return true;
    }
    out.truncate(mark);
    return false;
  }

  // the values from..to of x are out of x before the position, or have their b at 0
  private boolean valuesOff(AtomicTrail trail, int position, long from, long to, EntryList out) {
    if (to - from >= LCG_MAX_VALUES) {
      return false;
    }
    for (long u = from; u <= to; u++) {
      if (!trail.excludedBefore(x, (int) u, position, out)
          && !offByB(trail, position, (int) u, out)) {
        return false;
      }
    }
    return true;
  }

  // ChannelReif: value v's b was 0 before the position
  private boolean offByB(AtomicTrail trail, int position, int v, EntryList out) {
    IntVar b = valueMap.get(v);
    if (!lcgReified() || b == null || trail.maxBefore(b, position) > 0) {
      return false;
    }
    trail.addUpperBound(b, position, out);
    return true;
  }

  record Item(IntVar b, int value) {
    @Override
    public String toString() {
      return "[" + b + ", " + value + "]";
    }
  }

  @Override
  public long violation(ToIntFunction<IntVar> value) {
    int xv = value.applyAsInt(x);
    long violated = 0;
    for (Item i : item) {
      if (!itemSatisfied(value.applyAsInt(i.b()) == 1, xv == i.value())) {
        violated++;
      }
    }
    return violated;
  }
}
