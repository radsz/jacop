/*
 * RandomConvexCosts.java
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

package org.jacop;

import java.util.Random;
import java.util.function.LongUnaryOperator;
import org.jacop.constraints.ConvexCost;

/**
 * Random convex costs for the tests of {@link org.jacop.constraints.ConvexAllocation}, each with an
 * evaluation written independently of {@link ConvexCost}, so that a brute force does not trust the
 * code it checks.
 */
final class RandomConvexCosts {

  /** A cost, its own evaluation and a description. */
  record Cost(ConvexCost cost, LongUnaryOperator value, String text) {}

  private RandomConvexCosts() {}

  /**
   * A sum of one or two random convex pieces: weighted absolute values, squares, dead zones,
   * squared dead zones (as in the balanced academic curriculum), affine functions and convex
   * tables.
   *
   * @param r the random source
   * @param lo the least value the cost is evaluated at
   * @param hi the greatest value the cost is evaluated at
   * @return the cost
   */
  static Cost random(Random r, int lo, int hi) {
    Cost c = piece(r, lo, hi);
    if (r.nextInt(3) == 0) {
      Cost d = piece(r, lo, hi);
      LongUnaryOperator a = c.value();
      LongUnaryOperator b = d.value();
      c =
          new Cost(
              c.cost().plus(d.cost()),
              v -> a.applyAsLong(v) + b.applyAsLong(v),
              c.text() + " + " + d.text());
    }
    return c;
  }

  private static Cost piece(Random r, int lo, int hi) {
    long w = 1 + r.nextInt(3);
    long a = 1 + r.nextInt(3);
    long b = -4 + r.nextInt(9);
    switch (r.nextInt(6)) {
      case 0 -> {
        return new Cost(
            ConvexCost.abs(w, a, b), v -> w * Math.abs(a * v + b), w + "|" + a + "v+" + b + "|");
      }
      case 1 -> {
        return new Cost(
            ConvexCost.square(w, a, -b),
            v -> w * (a * v - b) * (a * v - b),
            w + "(" + a + "v-" + b + ")^2");
      }
      case 2 -> {
        // a dead zone: 0 from p to q, slope w outside
        long p = lo + r.nextInt(hi - lo + 1);
        long q = p + r.nextInt(3);
        return new Cost(
            ConvexCost.max(w, new long[] {1, -1, 0}, new long[] {-q, p, 0}),
            v -> w * Math.max(Math.max(v - q, p - v), 0),
            w + "*max(v-" + q + "," + p + "-v,0)");
      }
      case 3 -> {
        // max(v - ceil, floor - v)^2 with floor in {ceil - 1, ceil}, never negative on integers
        long ceil = lo + r.nextInt(hi - lo + 1);
        long floor = ceil - r.nextInt(2);
        return new Cost(
            ConvexCost.squaredMax(w, new long[] {1, -1}, new long[] {-ceil, floor}),
            v -> {
              long m = Math.max(v - ceil, floor - v);
              return w * m * m;
            },
            w + "*max(v-" + ceil + "," + floor + "-v)^2");
      }
      case 4 -> {
        long s = -3 + r.nextInt(7);
        return new Cost(ConvexCost.linear(s, b), v -> s * v + b, s + "v+" + b);
      }
      default -> {
        // a convex table over lo..hi with non-decreasing differences
        int len = hi - lo + 1;
        long[] t = new long[len];
        long d = -4 + r.nextInt(3);
        t[0] = r.nextInt(5);
        for (int k = 1; k < len; k++) {
          t[k] = t[k - 1] + d;
          d += r.nextInt(3);
        }
        long first = lo;
        return new Cost(
            ConvexCost.table(first, t),
            v -> {
              if (len == 1) {
                return t[0];
              }
              if (v < first) {
                return t[0] - (first - v) * (t[1] - t[0]);
              }
              if (v > first + len - 1) {
                return t[len - 1] + (v - first - len + 1) * (t[len - 1] - t[len - 2]);
              }
              return t[(int) (v - first)];
            },
            "table" + java.util.Arrays.toString(t) + "@" + first);
      }
    }
  }
}
