/*
 * BinpackingSameWeightTest.java
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

package org.jacop.constraints.binpacking;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/** The closed form of NoSum for items of equal weight agrees with Shaw's NoSum. */
class BinpackingSameWeightTest {

  @Test
  void closedFormAgreesWithShawsNoSumOnEqualWeights() {
    Random random = new Random(7);
    long[] shaw = new long[2];
    long[] closed = new long[2];
    for (int t = 0; t < 20_000; t++) {
      int w = 1 + random.nextInt(5);
      int len = 1 + random.nextInt(12);
      int[] x = new int[len];
      Arrays.fill(x, w);
      long sum = (long) w * len;
      long alpha = random.nextInt((int) sum + 3) - 1;
      long beta = random.nextBoolean() ? alpha : alpha + random.nextInt(2 * w + 1);
      boolean expected = Binpacking.noSum(x, len, sum, alpha, beta, shaw);
      boolean got = Binpacking.sameWeightNoSum(w, len, alpha, beta, closed);
      assertThat(got).as("w=%d len=%d [%d, %d]", w, len, alpha, beta).isEqualTo(expected);
      if (expected) {
        assertThat(closed).as("w=%d len=%d [%d, %d]", w, len, alpha, beta).containsExactly(shaw);
      }
    }
  }

  @Test
  void equalWeightShortcutsPruneAsTheGeneralRules() {
    Random random = new Random(11);
    for (int t = 0; t < 400; t++) {
      long seed = random.nextLong();
      List<String> fast = run(seed, true);
      List<String> general = run(seed, false);
      assertThat(fast).as("seed %d", seed).isEqualTo(general);
    }
  }

  // the domains after each of a few decisions with propagation, or "fail"
  private static List<String> run(long seed, boolean shortcuts) {
    boolean before = Binpacking.sameWeightShortcuts;
    Binpacking.sameWeightShortcuts = shortcuts;
    try {
      Random r = new Random(seed);
      Store store = new Store();
      int bins = 2 + r.nextInt(5);
      int items = 2 + r.nextInt(9);
      int w = 1 + r.nextInt(3);
      IntVar[] bin = new IntVar[items + 2];
      int[] weight = new int[items + 2];
      for (int i = 0; i < items; i++) {
        IntervalDomain d = new IntervalDomain();
        for (int b = 0; b < bins; b++) {
          if (r.nextInt(3) > 0) {
            d.unionAdapt(b, b);
          }
        }
        if (d.isEmpty()) {
          d.unionAdapt(0, 0);
        }
        bin[i] = new IntVar(store, "b" + i, d);
        weight[i] = w;
      }
      // two fixed items of another weight, which are never candidates
      bin[items] = new IntVar(store, "f0", 0, 0);
      weight[items] = w + 2;
      bin[items + 1] = new IntVar(store, "f1", bins - 1, bins - 1);
      weight[items + 1] = 2 * w + 1;
      IntVar[] load = new IntVar[bins];
      for (int b = 0; b < bins; b++) {
        int lo = r.nextInt(w * 3 + 1);
        load[b] = new IntVar(store, "l" + b, lo, lo + r.nextInt(w * 4 + 2));
      }
      store.impose(new Binpacking(bin, load, weight, 0));
      List<String> out = new ArrayList<>();
      for (int step = 0; step < 4; step++) {
        try {
          if (!store.consistency()) {
            out.add("fail");
            return out;
          }
        } catch (FailException e) {
          out.add("fail");
          return out;
        }
        out.add(Arrays.toString(bin) + Arrays.toString(load));
        IntVar x = bin[r.nextInt(items)];
        if (!x.singleton()) {
          store.setLevel(store.level + 1);
          int v = r.nextBoolean() ? x.min() : x.max();
          x.domain.in(store.level, x, v, v);
        }
      }
      return out;
    } finally {
      Binpacking.sameWeightShortcuts = before;
    }
  }
}
