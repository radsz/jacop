/*
 * TimeStampInt.java
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

package org.jacop.core;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.Arrays;
import org.jacop.api.Stateful;

/**
 * A {@link TimeStamp} specialised for int values. It keeps the values in an int array, so reading
 * the value does not unbox an {@code Integer} (one dependent load less) and an update to a value
 * outside the {@code Integer} cache does not allocate. It behaves exactly like a {@code
 * TimeStamp<Integer>}: a value updated at a level is removed when the level is removed.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class TimeStampInt implements Stateful {

  private final int index;

  private final Store store;

  /** The position of the most recent value; -1 once the level of creation was removed. */
  public int pointer4Last = -1;

  private int[] stamps = new int[10];

  private int[] values = new int[10];

  /**
   * The constructor.
   *
   * @param store the store where the timestamp is registered.
   * @param input the value of the stamp to be stored.
   */
  public TimeStampInt(Store store, int input) {
    this.store = store;
    index = store.registerTimeStamp();
    addLast(input, store.level);
  }

  private void addLast(int input, int level) {
    int p = ++pointer4Last;
    if (p >= stamps.length) {
      int newCapacity = stamps.length * 3 / 2 + 1;
      values = Arrays.copyOf(values, newCapacity);
      stamps = Arrays.copyOf(stamps, newCapacity);
    }
    values[p] = input;
    stamps[p] = level;
    store.recordTimeStampLevel(this, level);
  }

  /**
   * It removes all the values from the most recent until the level (inclusive) specified by the
   * parameter.
   *
   * @param level the number of the level.
   */
  @Override
  public void removeLevel(int level) {
    int p = pointer4Last;
    while (p >= 0 && stamps[p] >= level) {
      p--;
    }
    pointer4Last = p;
  }

  /**
   * It returns the level of the most recent value within that timestamp.
   *
   * @return the stamp value.
   */
  public int stamp() {
    return stamps[pointer4Last];
  }

  /**
   * It updates the value of the timestamp with the provided value.
   *
   * @param val value to which the timestamp needs to be updated.
   */
  public void update(int val) {
    int p = pointer4Last;
    int level = store.level;
    int stamp = stamps[p];
    if (ASSERTS_ENABLED && stamp > level) {
      throw new IllegalStateException(
          "Error - Timestamp" + this + "has greater level than store - missing remove");
    }
    if (stamp == level) {
      values[p] = val;
    } else if (stamp < level) {
      addLast(val, level);
    }
  }

  /**
   * It returns the most recent value of the timestamp.
   *
   * @return the most recent value of the timestamp.
   */
  public int value() {
    return values[pointer4Last];
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("TimeStampInt<").append(index).append("> = ");
    for (int i = pointer4Last; i >= 0; i--) {
      s.append('v').append(values[i]).append('s').append(stamps[i]);
    }
    return s.toString();
  }
}
