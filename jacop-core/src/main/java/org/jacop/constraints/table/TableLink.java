/*
 * TableLink.java
 * <p>
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

package org.jacop.constraints.table;

import java.util.ArrayList;
import java.util.List;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/**
 * The sub-tuples on a set of variables shared by several {@link HybridTable} constraints, for
 * pairwise consistency between them as in eSTR (C. Lecoutre, A. Paparrizou, K. Stergiou, "Extending
 * STR to a Higher-Order Consistency", AAAI 2013). Each table numbers its rows by their sub-tuple on
 * the shared variables (a key). A key stays alive while every table of the link has a valid row
 * with it; when one table loses its last row with a key, the key dies and the other tables remove
 * their rows with it. Pairwise consistency on the shared set is then the arc consistency of a
 * hidden variable over the keys, as with the factor variables of C. Likitvivatanavong, W. Xia, R.
 * H. C. Yap, "Higher-Order Consistencies through GAC on Factor Variables", CP 2014, but without the
 * variable and its column.
 *
 * <p>The live keys are a sparse set whose size is trailed, so the keys that died since a table last
 * looked are the ones between the current size and the size the table recorded.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class TableLink {

  /** The number of keys. */
  final int keys;

  private final int[] dense;
  private final int[] position;
  private TimeStamp<Integer> size;
  private Store store;

  /** The tables of the link. */
  final List<HybridTable> tables = new ArrayList<>();

  /**
   * It creates a link over the given number of keys, all alive.
   *
   * @param keys the number of sub-tuples, numbered from 0.
   */
  public TableLink(int keys) {
    if (keys <= 0) {
      throw new IllegalArgumentException("TableLink: at least one key is needed");
    }
    this.keys = keys;
    dense = new int[keys];
    position = new int[keys];
    for (int k = 0; k < keys; k++) {
      dense[k] = k;
      position[k] = k;
    }
  }

  void attach(Store store) {
    if (this.store == null) {
      this.store = store;
      size = new TimeStamp<>(store, keys);
    }
  }

  /**
   * It gives the number of live keys.
   *
   * @return the live keys, which are the keys at positions 0 .. size() - 1.
   */
  int size() {
    return size.value();
  }

  /** The key at a position of the sparse set. */
  int key(int p) {
    return dense[p];
  }

  boolean alive(int k) {
    return position[k] < size.value();
  }

  /**
   * It kills a key that a table has no valid row for any more, and wakes the other tables.
   *
   * @param k the key.
   * @param by the table that lost its last row with the key.
   */
  void kill(int k, HybridTable by) {
    int s = size.value();
    int p = position[k];
    if (p >= s) {
      return;
    }
    int last = s - 1;
    int other = dense[last];
    dense[last] = k;
    position[k] = last;
    dense[p] = other;
    position[other] = p;
    size.update(last);
    if (last == 0) {
      throw Store.failException;
    }
    for (HybridTable t : tables) {
      if (t != by) {
        store.addChanged(t);
      }
    }
  }
}
