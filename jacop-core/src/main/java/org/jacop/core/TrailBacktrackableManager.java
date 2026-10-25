/*
 * TrailBacktrackableManager.java
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

import java.util.Arrays;

/**
 * It records the objects (variables) changed at each level on a stack, so removing a level visits
 * only the objects changed at that level.
 *
 * <p>An object is pushed once per level, at its first change at that level. Each entry keeps the
 * level of the object's previous entry, so after the entry is popped a new change at the same level
 * is pushed again. Setting a level does no work, and memory grows with the number of changes on the
 * current search path.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class TrailBacktrackableManager implements BacktrackableManager {

  private static final int NOT_RECORDED = -1;

  private Backtrackable[] objects;

  private int noOfObjects;

  private int currentLevel;

  /** For each object, the level of its most recent entry on the trail, or NOT_RECORDED. */
  private int[] recordedAt;

  /** The index of the object of each entry. */
  private int[] trailIndex = new int[64];

  /** The level of each entry. */
  private int[] trailLevel = new int[64];

  /** The value of recordedAt of the entry's object before the entry was pushed. */
  private int[] trailPrevious = new int[64];

  private int trailSize;

  /**
   * It creates a manager for the given objects.
   *
   * @param objects the objects whose changes are recorded.
   * @param noOfObjects the number of objects in use, at the beginning of the array.
   */
  public TrailBacktrackableManager(Backtrackable[] objects, int noOfObjects) {
    this.objects = objects;
    this.noOfObjects = noOfObjects;
    recordedAt = new int[objects.length];
    Arrays.fill(recordedAt, NOT_RECORDED);
  }

  @Override
  public void addChanged(int index) {
    int previous = recordedAt[index];
    if (previous == currentLevel) {
      return;
    }
    if (trailSize >= trailIndex.length) {
      grow();
    }
    trailIndex[trailSize] = index;
    trailLevel[trailSize] = currentLevel;
    trailPrevious[trailSize] = previous;
    trailSize++;
    recordedAt[index] = currentLevel;
  }

  private void grow() {
    int capacity = Math.max(64, 2 * trailSize + 1);
    trailIndex = Arrays.copyOf(trailIndex, capacity);
    trailLevel = Arrays.copyOf(trailLevel, capacity);
    trailPrevious = Arrays.copyOf(trailPrevious, capacity);
  }

  @Override
  public void removeLevel(int removedLevel) {
    while (trailSize > 0 && trailLevel[trailSize - 1] >= removedLevel) {
      trailSize--;
      int index = trailIndex[trailSize];
      objects[index].remove(trailLevel[trailSize]);
      recordedAt[index] = trailPrevious[trailSize];
    }
  }

  @Override
  public void setSize(int size) {
    if (size > recordedAt.length) {
      int old = recordedAt.length;
      recordedAt = Arrays.copyOf(recordedAt, Math.max(size, old * 2));
      Arrays.fill(recordedAt, old, recordedAt.length, NOT_RECORDED);
    }
    noOfObjects = size;
  }

  @Override
  public boolean isRecognizedAsChanged(int index) {
    return recordedAt[index] == currentLevel;
  }

  @Override
  public int getLevel() {
    return currentLevel;
  }

  @Override
  public void setLevel(int level) {
    currentLevel = level;
  }

  @Override
  public void update(Backtrackable[] objects, int noOfObjects) {
    this.objects = objects;
    setSize(Math.max(noOfObjects, objects.length));
    this.noOfObjects = noOfObjects;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder("Level ").append(currentLevel).append(", trail [");
    for (int i = 0; i < trailSize; i++) {
      if (i > 0) {
        result.append(", ");
      }
      result.append(trailIndex[i]).append('@').append(trailLevel[i]);
    }
    return result.append("], objects ").append(noOfObjects).toString();
  }
}
