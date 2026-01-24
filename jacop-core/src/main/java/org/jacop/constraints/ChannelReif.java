/*
 * ChannelReif.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.constraints;

import java.util.Arrays;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * ChannelReif constraints "constraint" {@literal <=>} B.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */
public class ChannelReif extends AbstractChannel {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  public ChannelReif(IntVar x, IntVar[] bs, int[] value) {
    super(idNumber.incrementAndGet(), x, bs, value, "ChannelReif");
  }

  public ChannelReif(IntVar x, IntVar[] bs, IntDomain value) {
    this(x, bs, toArray(value));
  }

  public ChannelReif(IntVar x, IntVar[] bs) {
    this(x, bs, toArray(x.domain));
  }

  public ChannelReif(IntVar x, Map<Integer, ? extends IntVar> bs) {
    super(idNumber.incrementAndGet(), x, bs);
  }

  @Override
  public void consistency(final Store store) {

    int start = position.value();
    boolean startChanged = false;

    for (int i = start; i < n; i++) {

      if (item[i].b().max() == 0) {
        x.domain.inComplement(store.level, x, item[i].value());
        swap(start, i);
        start++;
        startChanged = true;
        continue;
      } else if (item[i].b().min() == 1) {
        x.domain.in(store.level, x, item[i].value(), item[i].value());
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
      IntVar b = valueMap.get(x.value());
      b.domain.inValue(store.level, b, 1);

      for (int i = start; i < n; i++) {
        if (item[i].b() != b) {
          item[i].b().domain.inValue(store.level, item[i].b(), 0);
        }
      }
    }
  }

  @Override
  public String toString() {
    return id() + " : ChannelReif(" + x + ", " + Arrays.asList(item) + " )";
  }
}
