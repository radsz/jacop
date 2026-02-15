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
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;

abstract class AbstractChannel extends Constraint implements SatisfiedPresent {

  final IntVar x;
  final int n;
  final Item[] item;
  final Map<Integer, IntVar> valueMap = new HashMap<>();
  TimeStamp<Integer> position;

  AbstractChannel(int numberId, IntVar x, IntVar[] bs, int[] value, String constraintName) {
    if (value.length != bs.length) {
      throw new IllegalArgumentException(
          constraintName
              + ": Status array size ("
              + bs.length
              + "), has not equal size as number of values "
              + value.length);
    }

    checkInputForNullness(new String[] {"x", "bs"}, new Object[] {x}, bs);
    for (IntVar b : bs) {
      if (b.min() > 1 || b.max() < 0) {
        throw new IllegalArgumentException(
            constraintName + ": Variable b in reified constraint must have domain at most 0..1");
      }
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
    int one = findSingleActiveIndexOrMinValue();
    return one != Integer.MIN_VALUE && x.value() == item[one].value;
  }

  /**
   * If all items are singleton and exactly one has value 1, returns that index; otherwise
   * Integer.MIN_VALUE.
   */
  private int findSingleActiveIndexOrMinValue() {
    int one = Integer.MIN_VALUE;
    for (int i = 0; i < n; i++) {
      if (!item[i].b.singleton()) {
        return Integer.MIN_VALUE;
      }
      if (item[i].b.value() == 1) {
        if (one == -1) {
          one = i;
        } else {
          return Integer.MIN_VALUE;
        }
      } else {
        return Integer.MIN_VALUE;
      }
    }
    return one;
  }

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
  protected abstract void handleBMaxZero(Store store, int i);

  /**
   * Handles the case when b.min() == 1 for a given item index.
   *
   * @param store the constraint store
   * @param i the index of the item
   */
  protected abstract void handleBMinOne(Store store, int i);

  /**
   * Propagates constraints when x becomes a singleton.
   *
   * @param store the constraint store
   * @param start the starting index for propagation
   */
  protected abstract void propagateWhenXIsSingleton(Store store, int start);

  @Override
  public void consistency(final Store store) {

    int start = position.value();
    boolean startChanged = false;

    for (int i = start; i < n; i++) {

      if (item[i].b().max() == 0) {
        handleBMaxZero(store, i);
        swap(start, i);
        start++;
        startChanged = true;
        continue;
      } else if (item[i].b().min() == 1) {
        handleBMinOne(store, i);
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
      return;
    }

    if (x.singleton()) {
      propagateWhenXIsSingleton(store, start);
    }
  }

  record Item(IntVar b, int value) {
    public String toString() {
      return "[" + b + ", " + value + "]";
    }
  }
}
