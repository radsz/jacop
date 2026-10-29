/*
 * LevelSlots.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2026 Radoslaw Szymanek
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

package org.jacop.constraints.regular;

import java.util.Arrays;
import java.util.Map;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * The values labelling the edges of each level of a layered graph (its slots), with the queue of
 * the levels whose variables changed, the stamps of removed and supported slots and the pruning of
 * the values that lost their support. It is shared by CostRegular and MultiCostRegular.
 */
final class LevelSlots {

  private final IntVar[] list;

  private final Map<IntVar, Integer> mapping;

  // the values labelling edges of level l are value[levelStart[l]..levelStart[l+1]-1]
  private final int[] levelStart;
  private final int[] value;

  /** Stamp of the consistency call in which a slot lost its value. */
  final int[] removed;

  /** Stamp of the pass in which a slot was supported by an edge. */
  final int[] supported;

  /** The number of supported slots per level in the last pass. */
  final int[] levelSupported;

  private final int[] queue;
  private final boolean[] queued;
  private int queueSize;

  private int stamp;

  /**
   * Returns the value of a slot.
   *
   * @param slot the slot
   * @return the value labelling its edges
   */
  int value(int slot) {
    return value[slot];
  }

  LevelSlots(IntVar[] list, int[] levelStart, int[] value, Class<?> owner) {
    this.list = list;
    this.levelStart = levelStart;
    this.value = value;
    this.mapping = Var.positionMapping(list, true, owner);
    this.removed = new int[value.length];
    this.supported = new int[value.length];
    this.levelSupported = new int[list.length];
    this.queue = new int[list.length];
    this.queued = new boolean[list.length];
  }

  /** It queues the level of variable v, if v is a variable of the word. */
  void queue(Var v) {
    Integer p = mapping.get(v);
    if (p != null) {
      queueLevel(p);
    }
  }

  private void queueLevel(int level) {
    if (!queued[level]) {
      queued[level] = true;
      queue[queueSize++] = level;
    }
  }

  boolean queueEmpty() {
    return queueSize == 0;
  }

  /** It empties the queue, whose changes are undone by backtracking. */
  void clearQueue() {
    for (int i = 0; i < queueSize; i++) {
      queued[queue[i]] = false;
    }
    queueSize = 0;
  }

  /** It returns the stamp of the last pass. */
  int stamp() {
    return stamp;
  }

  /** It returns a new stamp. */
  int nextStamp() {
    if (++stamp == Integer.MAX_VALUE) {
      Arrays.fill(removed, 0);
      Arrays.fill(supported, 0);
      stamp = 1;
    }
    return stamp;
  }

  /**
   * It restricts every variable to the values of its slots and queues every level, since the graph
   * was built at impose and values removed since then must be checked on every level.
   */
  void restrictToSlots(Store store) {
    for (int level = 0; level < list.length; level++) {
      IntervalDomain labels = new IntervalDomain();
      for (int s = levelStart[level]; s < levelStart[level + 1]; s++) {
        labels.unionAdapt(value[s], value[s]);
      }
      list[level].domain.in(store.level, list[level], labels);
    }
    for (int level = 0; level < list.length; level++) {
      queueLevel(level);
    }
  }

  /**
   * It stamps the slots of the queued levels whose values were removed and empties the queue.
   *
   * @return the first level with a removed value, or the number of levels when there is none.
   */
  int markRemoved(int removedStamp) {
    int from = list.length;
    for (int i = 0; i < queueSize; i++) {
      int level = queue[i];
      queued[level] = false;
      IntDomain dom = list[level].domain;
      for (int s = levelStart[level]; s < levelStart[level + 1]; s++) {
        if (!dom.contains(value[s])) {
          removed[s] = removedStamp;
          from = Math.min(from, level);
        }
      }
    }
    queueSize = 0;
    return from;
  }

  /** It removes the values whose slots were not supported in the last pass. */
  void pruneUnsupported(Store store) {
    int support = stamp;
    for (int level = 0; level < list.length; level++) {
      IntVar x = list[level];
      if (levelSupported[level] == x.getSize()) {
        continue;
      }
      for (int s = levelStart[level]; s < levelStart[level + 1]; s++) {
        if (supported[s] != support && x.domain.contains(value[s])) {
          x.domain.inComplement(store.level, x, value[s]);
        }
      }
    }
  }
}
