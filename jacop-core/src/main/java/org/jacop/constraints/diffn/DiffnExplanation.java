/*
 * DiffnExplanation.java
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

package org.jacop.constraints.diffn;

import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of non-overlapping rectangles by pairs. Rectangle i placed at origin u in dimension
 * d overlaps rectangle j however both are placed, when i's lengths are at least li, j's at least lj
 * (all positive), and
 *
 * <ul>
 *   <li>in d: {@code u < min(oj) + lj} and {@code u + li > max(oj)};
 *   <li>in the other dimension: {@code max(oi) < min(oj) + lj} and {@code min(oi) + li > max(oj)}.
 * </ul>
 *
 * <p>So the values of i's origin in d that j forbids form an interval, and an atom removing values
 * of an origin holds when those intervals, the bounds and the holes the origin had before cover the
 * removed values. A failure is explained the same way for a rectangle with no value left. Pruning
 * that needs several rectangles at once (the profile and area checks) is not explained, so the
 * generic reason is used for it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class DiffnExplanation {

  /** The most values one by one between the forbidden intervals. */
  private static final int VALUE_LIMIT = 256;

  private final AtomicTrail trail;
  private final Rectangle[] rectangle;
  private final int position;
  private final int[][] originMin;
  private final int[][] originMax;
  private final int[][] lengthMin;

  private DiffnExplanation(AtomicTrail trail, Rectangle[] rectangle, int position) {
    this.trail = trail;
    this.rectangle = rectangle;
    this.position = position;
    int n = rectangle.length;
    originMin = new int[2][n];
    originMax = new int[2][n];
    lengthMin = new int[2][n];
    for (int k = 0; k < n; k++) {
      for (int d = 0; d < 2; d++) {
        originMin[d][k] = trail.minBefore(rectangle[k].origin[d], position);
        originMax[d][k] = trail.maxBefore(rectangle[k].origin[d], position);
        lengthMin[d][k] = trail.minBefore(rectangle[k].length[d], position);
      }
    }
  }

  /**
   * Adds to {@code out} the reason of an entry of one of the rectangles' origins.
   *
   * @param trail the trail
   * @param entry the entry
   * @param rectangle the rectangles
   * @param out where the reason entries are added
   * @return false when no rectangle with that origin has its removed values covered
   */
  static boolean explain(AtomicTrail trail, int entry, Rectangle[] rectangle, EntryList out) {
    IntVar y = trail.variable(entry);
    int lo = trail.removedMin(entry);
    int hi = trail.removedMax(entry);
    DiffnExplanation explanation = null;
    int mark = out.size();
    for (int i = 0; i < rectangle.length; i++) {
      for (int d = 0; d < 2; d++) {
        if (rectangle[i].origin[d] != y) {
          continue;
        }
        if (explanation == null) {
          explanation = new DiffnExplanation(trail, rectangle, entry);
        }
        int from = Math.max(lo, trail.minBefore(y, entry));
        int to = Math.min(hi, trail.maxBefore(y, entry));
        if (from > lo) {
          trail.addLowerBound(y, entry, out);
        }
        if (to < hi) {
          trail.addUpperBound(y, entry, out);
        }
        if (explanation.cover(i, d, from, to, out)) {
          out.sortUnique(mark);
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  /**
   * Adds to {@code out} the reason of a failure: some rectangle has no origin left in a dimension.
   *
   * @param trail the trail
   * @param rectangle the rectangles
   * @param out where the reason entries are added
   * @return false when no rectangle is found so
   */
  static boolean explainFailure(AtomicTrail trail, Rectangle[] rectangle, EntryList out) {
    int now = trail.size();
    DiffnExplanation explanation = new DiffnExplanation(trail, rectangle, now);
    int mark = out.size();
    for (int i = 0; i < rectangle.length; i++) {
      for (int d = 0; d < 2; d++) {
        IntVar y = rectangle[i].origin[d];
        trail.addLowerBound(y, now, out);
        trail.addUpperBound(y, now, out);
        if (explanation.cover(
            i, d, explanation.originMin[d][i], explanation.originMax[d][i], out)) {
          out.sortUnique(mark);
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  /**
   * Whether rectangle i cannot have its origin in dimension d anywhere in [from, to]: each value is
   * forbidden by another rectangle or was out of the origin's domain. If so the reason goes to out.
   */
  private boolean cover(int i, int d, int from, int to, EntryList out) {
    if (from > to) {
      return true;
    }
    int e = 1 - d;
    int li = lengthMin[d][i];
    int liOther = lengthMin[e][i];
    if (li < 1 || liOther < 1) {
      return false;
    }
    int n = rectangle.length;
    int[] start = new int[n];
    int[] end = new int[n];
    int count = 0;
    int[] which = new int[n];
    for (int j = 0; j < n; j++) {
      if (j == i || lengthMin[d][j] < 1 || lengthMin[e][j] < 1) {
        continue;
      }
      // overlapping in the other dimension wherever both are
      if (originMax[e][i] >= originMin[e][j] + lengthMin[e][j]
          || originMin[e][i] + liOther <= originMax[e][j]) {
        continue;
      }
      int s = originMax[d][j] - li + 1;
      int t = originMin[d][j] + lengthMin[d][j] - 1;
      if (s <= t && t >= from && s <= to) {
        start[count] = s;
        end[count] = t;
        which[count++] = j;
      }
    }
    IntVar y = rectangle[i].origin[d];
    boolean[] used = new boolean[n];
    long cur = from;
    while (cur <= to) {
      int best = -1;
      long bestEnd = cur - 1;
      long nextStart = Long.MAX_VALUE;
      for (int k = 0; k < count; k++) {
        if (start[k] <= cur) {
          if (end[k] > bestEnd) {
            bestEnd = end[k];
            best = k;
          }
        } else {
          nextStart = Math.min(nextStart, start[k]);
        }
      }
      if (best >= 0) {
        int j = which[best];
        if (!used[j]) {
          used[j] = true;
          addRectangle(j, out);
        }
        cur = bestEnd + 1;
      } else {
        long gapEnd = Math.min(to, nextStart - 1);
        if (gapEnd - cur >= VALUE_LIMIT) {
          return false;
        }
        for (long v = cur; v <= gapEnd; v++) {
          if (!trail.excludedBefore(y, (int) v, position, out)) {
            return false;
          }
        }
        cur = gapEnd + 1;
      }
    }
    IntVar other = rectangle[i].origin[e];
    trail.addLowerBound(other, position, out);
    trail.addUpperBound(other, position, out);
    trail.addLowerBound(rectangle[i].length[d], position, out);
    trail.addLowerBound(rectangle[i].length[e], position, out);
    return true;
  }

  // the bounds of rectangle j that make it forbid values of another rectangle's origin
  private void addRectangle(int j, EntryList out) {
    Rectangle r = rectangle[j];
    for (int d = 0; d < 2; d++) {
      trail.addLowerBound(r.origin[d], position, out);
      trail.addUpperBound(r.origin[d], position, out);
      trail.addLowerBound(r.length[d], position, out);
    }
  }
}
