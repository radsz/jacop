/*
 * DivModPowBoundsTest.java
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

package org.jacop.constraints;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Random;
import org.jacop.core.IntDomain;
import org.junit.jupiter.api.Test;

/**
 * Compares the box narrowing of div, mod and pow with the hull of the solutions found by brute
 * force: equal when the divisors are enumerated, and containing it with the interval rules that
 * replace the enumeration for many divisors.
 */
class DivModPowBoundsTest {

  private interface Relation {
    /** The z of x op y, or null when there is none. */
    Long apply(long x, long y);
  }

  private static Long div(long x, long y) {
    return y == 0 ? null : x / y;
  }

  private static Long mod(long x, long y) {
    return y == 0 ? null : x % y;
  }

  private static Long pow(long x, long y) {
    if (y < 0) {
      if (x == 0) {
        return null;
      }
      return x == 1 ? 1L : x == -1 ? ((y & 1) == 0 ? 1L : -1L) : 0L;
    }
    long p = 1;
    for (long i = 0; i < y; i++) {
      p *= x;
      if (p > IntDomain.MAX_INT || p < IntDomain.MIN_INT) {
        return null;
      }
    }
    return p;
  }

  // the hull of the solutions in box b, or null when there are none
  private static long[] hull(long[] b, Relation r) {
    long[] h = {Long.MAX_VALUE, Long.MIN_VALUE, Long.MAX_VALUE, Long.MIN_VALUE, Long.MAX_VALUE, 0};
    h[5] = Long.MIN_VALUE;
    boolean any = false;
    for (long x = b[0]; x <= b[1]; x++) {
      for (long y = b[2]; y <= b[3]; y++) {
        Long z = r.apply(x, y);
        if (z != null && z >= b[4] && z <= b[5]) {
          any = true;
          long[] t = {x, y, z};
          for (int i = 0; i < 3; i++) {
            h[2 * i] = Math.min(h[2 * i], t[i]);
            h[2 * i + 1] = Math.max(h[2 * i + 1], t[i]);
          }
        }
      }
    }
    return any ? h : null;
  }

  private static long[] box(Random rnd, int x, int y, int z) {
    long[] b = new long[6];
    int[] r = {x, y, z};
    for (int i = 0; i < 3; i++) {
      long a = rnd.nextInt(2 * r[i] + 1) - r[i];
      long c = rnd.nextInt(2 * r[i] + 1) - r[i];
      b[2 * i] = Math.min(a, c);
      b[2 * i + 1] = Math.max(a, c);
    }
    return b;
  }

  private static void check(long[] b, Relation r, DivModPowBounds.Narrowing f, boolean exact) {
    long[] expected = hull(b, r);
    long[] narrowed = b.clone();
    boolean any = f.narrow(narrowed);
    if (expected == null) {
      if (exact) {
        assertThat(any).as("no solution in %s", java.util.Arrays.toString(b)).isFalse();
      }
      return;
    }
    assertThat(any).as("solutions in %s", java.util.Arrays.toString(b)).isTrue();
    for (int i = 0; i < 3; i++) {
      String what = "variable " + i + " of " + java.util.Arrays.toString(b);
      if (exact) {
        assertThat(narrowed[2 * i]).as(what).isEqualTo(expected[2 * i]);
        assertThat(narrowed[2 * i + 1]).as(what).isEqualTo(expected[2 * i + 1]);
      } else {
        assertThat(narrowed[2 * i]).as(what).isLessThanOrEqualTo(expected[2 * i]);
        assertThat(narrowed[2 * i + 1]).as(what).isGreaterThanOrEqualTo(expected[2 * i + 1]);
      }
    }
  }

  @Test
  void divIsTheHullOfItsSolutions() {
    Random rnd = new Random(1);
    for (int i = 0; i < 20_000; i++) {
      long[] b = box(rnd, 1 + rnd.nextInt(40), 1 + rnd.nextInt(12), 1 + rnd.nextInt(20));
      check(b, DivModPowBoundsTest::div, DivModPowBounds::div, true);
      int limit = rnd.nextInt(4);
      check(b, DivModPowBoundsTest::div, c -> DivModPowBounds.div(c, limit), false);
    }
  }

  @Test
  void modIsTheHullOfItsSolutions() {
    Random rnd = new Random(2);
    for (int i = 0; i < 20_000; i++) {
      long[] b = box(rnd, 1 + rnd.nextInt(40), 1 + rnd.nextInt(12), 1 + rnd.nextInt(12));
      check(b, DivModPowBoundsTest::mod, DivModPowBounds::mod, true);
      int limit = rnd.nextInt(4);
      check(b, DivModPowBoundsTest::mod, c -> DivModPowBounds.mod(c, limit), false);
    }
  }

  @Test
  void powIsTheHullOfItsSolutions() {
    Random rnd = new Random(3);
    for (int i = 0; i < 20_000; i++) {
      long[] b = box(rnd, 1 + rnd.nextInt(6), 1 + rnd.nextInt(40), 1 + rnd.nextInt(200));
      check(b, DivModPowBoundsTest::pow, DivModPowBounds::pow, true);
    }
  }

  /** Large values: solutions picked at random stay in the narrowed box around them. */
  @Test
  void largeValuesKeepTheirSolutions() {
    Random rnd = new Random(4);
    DivModPowBounds.Narrowing[] narrowing = {
      DivModPowBounds::div, DivModPowBounds::mod, DivModPowBounds::pow
    };
    Relation[] relation = {
      DivModPowBoundsTest::div, DivModPowBoundsTest::mod, DivModPowBoundsTest::pow
    };
    for (int i = 0; i < 30_000; i++) {
      int k = i % 3;
      long x = rnd.nextInt(2 * IntDomain.MAX_INT) + IntDomain.MIN_INT + 1;
      long y = k == 2 ? rnd.nextInt(40) - 5 : rnd.nextInt(2001) - 1000;
      if (k == 2 && rnd.nextBoolean()) {
        x = rnd.nextInt(201) - 100;
      }
      Long z = relation[k].apply(x, y);
      if (z == null) {
        continue;
      }
      long[] t = {x, y, z};
      long[] b = new long[6];
      for (int j = 0; j < 3; j++) {
        long span = rnd.nextBoolean() ? rnd.nextInt(5) : rnd.nextInt(IntDomain.MAX_INT);
        b[2 * j] = Math.max(IntDomain.MIN_INT, t[j] - (rnd.nextBoolean() ? 0 : span));
        b[2 * j + 1] = Math.min(IntDomain.MAX_INT, t[j] + (rnd.nextBoolean() ? 0 : span));
      }
      long[] narrowed = b.clone();
      assertThat(narrowing[k].narrow(narrowed)).as("%d %d %d", x, y, z).isTrue();
      for (int j = 0; j < 3; j++) {
        assertThat(t[j]).as("%d %d %d", x, y, z).isBetween(narrowed[2 * j], narrowed[2 * j + 1]);
      }
    }
  }
}
