/*
 * ChannelReif.java
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
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * ChannelReif constraints "constraint" {@literal <=>} B.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ChannelReif extends AbstractChannel {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * Constructs a ChannelReif constraint with explicit value mapping.
   *
   * @param x the integer variable being channelled.
   * @param bs the array of boolean variables representing reification status.
   * @param value the array of values corresponding to each boolean variable.
   */
  public ChannelReif(IntVar x, IntVar[] bs, int[] value) {
    super(idNumber.incrementAndGet(), x, bs, value, "ChannelReif");
  }

  /**
   * Constructs a ChannelReif constraint with values taken from the given domain.
   *
   * @param x the integer variable being channelled.
   * @param bs the array of boolean variables representing reification status.
   * @param value the domain whose values correspond to each boolean variable.
   */
  public ChannelReif(IntVar x, IntVar[] bs, IntDomain value) {
    this(x, bs, toArray(value));
  }

  /**
   * Constructs a ChannelReif constraint using values from the domain of x.
   *
   * @param x the integer variable being channelled.
   * @param bs the array of boolean variables representing reification status.
   */
  public ChannelReif(IntVar x, IntVar[] bs) {
    this(x, bs, toArray(x.domain));
  }

  /**
   * Constructs a ChannelReif constraint using a map from values to boolean variables.
   *
   * @param x the integer variable being channelled.
   * @param bs the map from integer values to their corresponding boolean variables.
   */
  public ChannelReif(IntVar x, Map<Integer, ? extends IntVar> bs) {
    super(idNumber.incrementAndGet(), x, bs);
  }

  @Override
  protected void handleBMaxZero(Store store, int i) {
    x.domain.inComplement(store.level, x, item[i].value());
  }

  @Override
  protected void handleBMinOne(Store store, int i) {
    x.domain.in(store.level, x, item[i].value(), item[i].value());
  }

  @Override
  protected void propagateWhenXIsSingleton(Store store, int start) {
    IntVar b = valueMap.get(x.value());
    b.domain.inValue(store.level, b, 1);

    for (int i = start; i < n; i++) {
      if (item[i].b() != b) {
        item[i].b().domain.inValue(store.level, item[i].b(), 0);
      }
    }
  }

  @Override
  public String toString() {
    return id() + " : ChannelReif(" + x + ", " + Arrays.asList(item) + " )";
  }
}
