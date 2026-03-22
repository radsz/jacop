/*
 * ChannelImply.java
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
 * ChannelImply constraints "B {@literal =>} constraint".
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ChannelImply extends AbstractChannel {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * Constructs a ChannelImply constraint with explicit value mapping.
   *
   * @param x the integer variable being channelled.
   * @param bs the array of boolean variables representing implication status.
   * @param value the array of values corresponding to each boolean variable.
   */
  public ChannelImply(IntVar x, IntVar[] bs, int[] value) {
    super(idNumber.incrementAndGet(), x, bs, value, "ChannelImply");
  }

  /**
   * Constructs a ChannelImply constraint with values taken from the given domain.
   *
   * @param x the integer variable being channelled.
   * @param bs the array of boolean variables representing implication status.
   * @param value the domain whose values correspond to each boolean variable.
   */
  public ChannelImply(IntVar x, IntVar[] bs, IntDomain value) {
    this(x, bs, toArray(value));
  }

  /**
   * Constructs a ChannelImply constraint using values from the domain of x.
   *
   * @param x the integer variable being channelled.
   * @param bs the array of boolean variables representing implication status.
   */
  public ChannelImply(IntVar x, IntVar[] bs) {
    this(x, bs, toArray(x.domain));
  }

  /**
   * Constructs a ChannelImply constraint using a map from values to boolean variables.
   *
   * @param x the integer variable being channelled.
   * @param bs the map from integer values to their corresponding boolean variables.
   */
  public ChannelImply(IntVar x, Map<Integer, ? extends IntVar> bs) {
    super(idNumber.incrementAndGet(), x, bs);
  }

  @Override
  protected void handleBmaxZero(Store store, int i) {
    // No action needed for ChannelImply when b.max() == 0
  }

  @Override
  protected void handleBminOne(Store store, int i) {
    x.domain.inValue(store.level, x, item[i].value());
  }

  @Override
  protected void propagateWhenXisSingleton(Store store, int start) {
    IntVar b = valueMap.get(x.value());

    for (int i = start; i < n; i++) {
      if (item[i].b() != b) {
        item[i].b().domain.inValue(store.level, item[i].b(), 0);
      }
    }
  }

  @Override
  public String toString() {
    return id() + " : ChannelImply(" + x + ", " + Arrays.asList(item) + " )";
  }
}
