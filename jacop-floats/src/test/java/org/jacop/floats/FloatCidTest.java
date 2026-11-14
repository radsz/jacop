/*
 * FloatCidTest.java
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

package org.jacop.floats;

import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.core.Store;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.constraints.PowPeqR;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.FloatCid;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

/**
 * Checks that the 3BCID contractor ({@link FloatCid}) and skipping small narrowings ({@link
 * FloatDomain#setMinReduction}) never remove a solution: random quadratic systems are built around
 * a random point, and random dives towards the point run the contractor at every node.
 *
 * <p>Systems are {@code floats.cid.trials} (default 300) for each ratio of {@code
 * floats.cid.ratios} (default 0.01,0.1).
 */
class FloatCidTest {

  private static final int TRIALS = Integer.getInteger("floats.cid.trials", 300);

  @AfterEach
  void restore() {
    FloatDomain.setMinReduction(0);
  }

  @Test
  void contractorKeepsTheSolution() {
    // without a minimal reduction (ratio 0) propagation of these systems can crawl by ulps for
    // minutes, the slow convergence the ratio is for
    for (String r : System.getProperty("floats.cid.ratios", "0.01,0.1").split(",")) {
      double ratio = Double.parseDouble(r);
      FloatDomain.setMinReduction(ratio);
      Random random = new Random(20261114L);
      assertTimeoutPreemptively(
          Duration.ofMinutes(5),
          () -> {
            for (int t = 0; t < TRIALS; t++) {
              long start = System.nanoTime();
              trial(random, ratio, t);
              long ms = (System.nanoTime() - start) / 1_000_000;
              if (ms > 1000) {
                System.err.println("slow trial " + t + " ratio " + ratio + ": " + ms + " ms");
              }
            }
          });
    }
  }

  private static void trial(Random random, double ratio, int t) {
    Store store = new Store();
    int n = 2 + random.nextInt(3);
    FloatVar[] x = new FloatVar[n];
    double[] point = new double[n];
    for (int i = 0; i < n; i++) {
      x[i] = new FloatVar(store, "x" + i, -3, 3);
      point[i] = -3 + 6 * random.nextDouble();
    }
    int equations = 1 + random.nextInt(n);
    for (int e = 0; e < equations; e++) {
      List<FloatVar> terms = new ArrayList<>();
      List<Double> weights = new ArrayList<>();
      double value = 0;
      for (int k = 0; k < 3; k++) {
        int i = random.nextInt(n);
        int j = random.nextInt(n);
        double w = random.nextInt(7) - 3;
        if (w == 0) {
          continue;
        }
        FloatVar term = new FloatVar(store, -100, 100);
        double v;
        switch (random.nextInt(3)) {
          case 0 -> {
            store.impose(new PmulQeqR(x[i], x[j], term));
            v = point[i] * point[j];
          }
          case 1 -> {
            int power = 2 + random.nextInt(2);
            store.impose(new PowPeqR(x[i], power, term));
            v = Math.pow(point[i], power);
          }
          default -> {
            term = x[i];
            v = point[i];
          }
        }
        terms.add(term);
        weights.add(w);
        value += w * v;
      }
      if (terms.isEmpty()) {
        continue;
      }
      FloatVar[] list = terms.toArray(new FloatVar[0]);
      double[] ws = weights.stream().mapToDouble(Double::doubleValue).toArray();
      store.impose(new LinearFloat(list, ws, "<=", value + 1e-9));
      store.impose(new LinearFloat(list, ws, ">=", value - 1e-9));
    }
    FloatCid cid = new FloatCid(store, x, random.nextBoolean() ? 10 : 0, n);
    String context =
        "trial " + t + " ratio " + ratio + " point " + java.util.Arrays.toString(point);
    if (!store.consistency() || !cid.executeAfterConsistency(true)) {
      fail("root failed, " + context);
    }
    check(x, point, context);
    for (int depth = 0; depth < 40; depth++) {
      store.setLevel(store.level + 1);
      int i = random.nextInt(n);
      double cut = x[i].min() + (x[i].max() - x[i].min()) * random.nextDouble();
      if (point[i] <= cut) {
        x[i].domain.in(store.level, x[i], x[i].min(), Math.max(cut, point[i]));
      } else {
        x[i].domain.in(store.level, x[i], Math.min(cut, point[i]), x[i].max());
      }
      boolean ok = store.consistency() && cid.executeAfterConsistency(true);
      if (!ok) {
        fail("failed at depth " + depth + ", " + context);
      }
      check(x, point, context + " depth " + depth);
    }
    assertTrue(cid.probes >= 0);
  }

  private static void check(FloatVar[] x, double[] point, String context) {
    for (int i = 0; i < x.length; i++) {
      if (!x[i].domain.contains(point[i])) {
        fail(x[i] + " lost " + point[i] + ", " + context);
      }
    }
  }
}
