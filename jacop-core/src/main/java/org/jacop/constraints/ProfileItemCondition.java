/*
 * ProfileItemCondition.java
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

import java.util.Iterator;
import java.util.LinkedList;

/**
 * Defines a basic structure used to update profile DisjointConditional when some rectangles can
 * share the same place.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class ProfileItemCondition extends ProfileItem {

  LinkedList<int[]> rectangles = new LinkedList<>();

  ProfileItemCondition() {}

  ProfileItemCondition(int a, int b, int val, int[] rect) {
    super(a, b, val);
    rectangles.add(rect);
  }

  ProfileItemCondition(int a, int b, int val, LinkedList<int[]> rects) {
    super(a, b, val);
    rectangles.addAll(rects);
  }

  void addRect(int[] r) {
    rectangles.add(r);
  }

  int exclusiveRectsSize(ExclusiveList exList) {
    int rectHight = 0;

    for (ExclusiveItem exI : exList) {
      for (Iterator<int[]> e = rectangles.listIterator(0); e.hasNext(); ) {
        int[] el = e.next();

        if (exI.i2() == el[0] && exI.cond().min() == 0) {
          rectHight += el[1];
        }
      }
    }

    return rectHight;
  }

  /**
   * Computes the adjusted value for the other profile item based on exclusive rectangles.
   *
   * @param aValue the value from the other profile item
   * @param exList the exclusive list for computing rectangle sizes
   * @return the adjusted value
   */
  private int computeConditionValue(int aValue, ExclusiveList exList) {
    int val = exclusiveRectsSize(exList);
    return val == 0 ? aValue : aValue > val ? aValue - val : 0;
  }

  void overlap(
      ProfileItemCondition a,
      ProfileItemCondition left,
      ProfileItemCondition overlap,
      ProfileItemCondition right,
      ExclusiveList exList,
      int[] r) {

    if (a.min == min) {
      // left = null;
      if (a.max < max) {
        if (min != a.max) {
          int v = computeConditionValue(a.value, exList);
          overlap.set(min, a.max, value + v, rectangles);
          int[] rR = {r[0], v};
          overlap.addRect(rR);
        }
        right.set(a.max, max, value, rectangles);
      } else {
        // Max <= a.Max
        int v = computeConditionValue(a.value, exList);
        overlap.set(min, max, value + v, rectangles);
        int[] rR = {r[0], v};
        overlap.addRect(rR);
        if (max != a.max) {
          right.set(max, a.max, a.value, r);
        }
      }
    } else {
      // a.Min != Min
      if (a.min < min) {
        left.set(a.min, min, a.value, r);
        if (a.max == max) {
          int v = computeConditionValue(a.value, exList);
          overlap.set(min, max, value + v, rectangles);
          int[] rR = {r[0], v};
          overlap.addRect(rR);
          // right = null;
        } else {
          if (a.max < max) {
            if (min != a.max) {
              int val = exclusiveRectsSize(exList);
              int v = val == 0 ? a.value : a.value > val ? a.value - val : 0;
              overlap.set(min, a.max, value + v, rectangles);
              int[] rR = {r[0], v};
              overlap.addRect(rR);
            }
            right.set(a.max, max, value, rectangles);
          } else {
            // Max <= a.Max
            int val = exclusiveRectsSize(exList);
            int v = val == 0 ? a.value : a.value > val ? a.value - val : 0;
            overlap.set(min, max, value + v, rectangles);
            int[] rR = {r[0], v};
            overlap.addRect(rR);
            if (max != a.max) {
              right.set(max, a.max, a.value, r);
            }
          }
        }
      } else {
        // Min < a.Min
        left.set(min, a.min, value, rectangles);
        if (a.max == max) {
          int v = computeConditionValue(a.value, exList);
          overlap.set(a.min, a.max, value + v, rectangles);
          int[] rR = {r[0], v};
          overlap.addRect(rR);
          // right = null;
        } else {
          if (a.max < max) {
            int val = exclusiveRectsSize(exList);
            int v = val == 0 ? a.value : a.value > val ? a.value - val : 0;
            overlap.set(a.min, a.max, value + v, rectangles);
            int[] rR = {r[0], v};
            overlap.addRect(rR);
            right.set(a.max, max, value, rectangles);
          } else {
            // Max <= a.Max
            int val = exclusiveRectsSize(exList);
            int v = val == 0 ? a.value : a.value > val ? a.value - val : 0;
            overlap.set(a.min, max, value + v, rectangles);
            int[] rR = {r[0], v};
            overlap.addRect(rR);
            if (max != a.max) {
              right.set(max, a.max, a.value, r);
            }
          }
        }
      }
    }
  }

  void set(int a, int b, int val, int[] r) {
    super.set(a, b, val);
    rectangles.add(r);
  }

  void set(int a, int b, int val, LinkedList<int[]> r) {
    super.set(a, b, val);
    rectangles.addAll(r);
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder("{[");
    result.append(min).append("..").append(max).append(") = ").append(value).append(", [");

    for (Iterator<int[]> e = rectangles.listIterator(0); e.hasNext(); ) {
      int[] el = e.next();
      result.append("[").append(el[0]).append(", ").append(el[1]).append("], ");
    }
    result.append("]");

    return result.toString();
  }
}
