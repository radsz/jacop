/*
 * RectanglePlacementSelect.java
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

package org.jacop.search;

import java.util.IdentityHashMap;
import java.util.Map;
import java.util.function.BooleanSupplier;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntVar;

/**
 * Places rectangles one at a time, bottom-left: the rectangle that can start first in the first
 * dimension (ties to the one that can start first in the second) gets its origin in the first
 * dimension, its length in the first dimension, its origin in the second and its length in the
 * second set to their smallest values, before the next rectangle is chosen. A rectangle whose
 * placement has begun is completed first. This is the bottom-left rule of Baker, Coffman and Rivest
 * (Orthogonal packings in two dimensions, SIAM Journal on Computing 9(4), 1980) and the
 * one-rectangle-at-a-time branching of Simonis and O'Sullivan (Search strategies for rectangle
 * packing, CP 2008), with variable lengths fixed with the rectangle.
 *
 * <p>The selection keeps no state between calls: it scans the rectangles at every decision. While a
 * given condition does not hold it chooses nothing, so that a {@link SequenceSelect} passes on to
 * the next selection.
 */
public class RectanglePlacementSelect implements SelectChoicePoint<IntVar> {

  // per rectangle: origin and length in the first dimension, origin and length in the second
  private final IntVar[][] rectangles;

  private final Map<IntVar, Integer> position = new IdentityHashMap<>();

  private final BooleanSupplier active;

  private IntVar chosen;

  /**
   * Creates the selection.
   *
   * @param rectangles per rectangle its origin in the first dimension, its origin in the second
   *     dimension, its length in the first dimension and its length in the second, the order of
   *     {@link org.jacop.constraints.diffn.Nooverlap#rectangles()}.
   */
  public RectanglePlacementSelect(IntVar[][] rectangles) {
    this(rectangles, () -> true);
  }

  /**
   * Creates the selection that places rectangles only while a condition holds.
   *
   * @param rectangles the rectangles, as for {@link #RectanglePlacementSelect(IntVar[][])}.
   * @param active the condition; while it does not hold the selection chooses nothing.
   */
  public RectanglePlacementSelect(IntVar[][] rectangles, BooleanSupplier active) {
    this.active = active;
    this.rectangles = new IntVar[rectangles.length][];
    for (int i = 0; i < rectangles.length; i++) {
      IntVar[] r = rectangles[i];
      if (r.length != 4) {
        throw new IllegalArgumentException("A rectangle needs two origins and two lengths");
      }
      // the branching order: origin and length of the first dimension, then of the second
      this.rectangles[i] = new IntVar[] {r[0], r[2], r[1], r[3]};
      for (IntVar x : this.rectangles[i]) {
        position.putIfAbsent(x, position.size());
      }
    }
  }

  @Override
  public IntVar getChoiceVariable(int index) {
    chosen = null;
    if (!active.getAsBoolean()) {
      return null;
    }
    IntVar[] best = null;
    for (IntVar[] r : rectangles) {
      if (r[0].singleton()) {
        IntVar open = firstOpen(r);
        if (open != null) {
          // a rectangle whose placement has begun
          chosen = open;
          return open;
        }
      } else if (best == null || before(r, best)) {
        best = r;
      }
    }
    if (best != null) {
      chosen = best[0];
    }
    return chosen;
  }

  private static boolean before(IntVar[] r, IntVar[] best) {
    int a = r[0].min();
    int b = best[0].min();
    return a < b || a == b && r[2].min() < best[2].min();
  }

  private static IntVar firstOpen(IntVar[] r) {
    for (int k = 1; k < r.length; k++) {
      if (!r[k].singleton()) {
        return r[k];
      }
    }
    return null;
  }

  @Override
  public int getChoiceValue() {
    return chosen.min();
  }

  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    return null;
  }

  @Override
  public Map<IntVar, Integer> getVariablesMapping() {
    return position;
  }

  @Override
  public int getIndex() {
    return 0;
  }

  @Override
  public String toString() {
    return "RectanglePlacementSelect(" + rectangles.length + " rectangles)";
  }
}
