/*
 * DiffnKHandleProbing.java
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

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.List;
import org.jacop.constraints.diffn.DiffnK;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Finds presence handles for non-strict {@link DiffnK} constraints by probing at the root.
 *
 * <p>A box whose lengths can be 0 in several dimensions can be made absent by the constraint only
 * through a presence handle: a length that is 0 whenever any length of the box is 0. For each such
 * box every length that can be 0 is set to 0 in turn and the store propagated; a length that
 * becomes 0 in every probe is the handle. A probe that fails proves the length positive, which is
 * kept at the root.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class DiffnKHandleProbing {

  /** At most this many probes over all constraints, so that probing stays cheap. */
  static final int MAX_PROBES = 20_000;

  private final Store store;
  private int probes;

  DiffnKHandleProbing(Store store) {
    this.store = store;
  }

  /**
   * Probes the boxes of the constraints and sets the handles it finds. The store must be at a
   * fixpoint.
   *
   * @return false if the store failed after the lengths proved positive were pruned.
   */
  boolean probe(List<DiffnK> constraints) {
    for (DiffnK c : constraints) {
      IntVar[] handle = new IntVar[c.boxes()];
      boolean found = false;
      List<IntVar> positive = new ArrayList<>();
      for (int i = 0; i < handle.length && probes < MAX_PROBES; i++) {
        handle[i] = handleOf(c.lengths(i), positive);
        found |= handle[i] != null;
      }
      if (found) {
        c.setPresenceHandles(handle);
      }
      if (!positive.isEmpty()) {
        try {
          for (IntVar l : positive) {
            l.domain.inMin(store.level, l, 1);
          }
        } catch (FailException _) {
          return false;
        }
        if (!store.consistency()) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * The handle of a box with the given lengths, or null; lengths proved positive go to positive.
   */
  private IntVar handleOf(IntVar[] length, List<IntVar> positive) {
    int k = length.length;
    boolean[] candidate = new boolean[k];
    int zeroCapable = 0;
    for (int d = 0; d < k; d++) {
      if (length[d].max() <= 0) {
        return null; // already absent
      }
      candidate[d] = length[d].min() == 0;
      if (candidate[d]) {
        zeroCapable++;
      }
    }
    if (zeroCapable < 2) {
      return null; // the constraint sets the only length that can be 0 itself
    }

    boolean[] canBeZero = candidate.clone();
    int level = store.level;
    for (int e = 0; e < k; e++) {
      if (!canBeZero[e]) {
        continue;
      }
      probes++;
      store.setLevel(level + 1);
      length[e].domain.in(store.level, length[e], 0, 0);
      if (store.consistency()) {
        for (int d = 0; d < k; d++) {
          candidate[d] &= length[d].max() == 0;
        }
      } else {
        positive.add(length[e]);
      }
      store.removeLevel(level + 1);
      store.setLevel(level);
    }
    for (int d = 0; d < k; d++) {
      // a length proved positive cannot be the handle; a box that cannot be absent needs none
      if (candidate[d] && !positive.contains(length[d])) {
        return length[d];
      }
    }
    return null;
  }
}
