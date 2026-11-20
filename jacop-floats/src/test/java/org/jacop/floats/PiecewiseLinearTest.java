/*
 * PiecewiseLinearTest.java
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

package org.jacop.floats;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Random;
import org.jacop.core.Store;
import org.jacop.floats.constraints.PiecewiseLinear;
import org.jacop.floats.core.FloatVar;
import org.junit.jupiter.api.Test;

/** Tests of {@link PiecewiseLinear}. */
class PiecewiseLinearTest {

  private static final double[] XS = {0, 2, 2, 5};
  private static final double[] YS = {1, 5, 0, 3};

  @Test
  void narrowsYFromXAndXFromY() {
    Store store = new Store();
    FloatVar x = new FloatVar(store, "x", 0.5, 1.0);
    FloatVar y = new FloatVar(store, "y", -100, 100);
    store.impose(new PiecewiseLinear(x, y, XS, YS));
    assertTrue(store.consistency());
    assertEquals(2.0, y.min(), 1e-9);
    assertEquals(3.0, y.max(), 1e-9);

    store = new Store();
    x = new FloatVar(store, "x", -100, 100);
    y = new FloatVar(store, "y", 4.0, 4.0);
    store.impose(new PiecewiseLinear(x, y, XS, YS));
    assertTrue(store.consistency());
    // y = 4 at x = 1.5 on the first segment, nowhere on the jump at x = 2 (0..5 includes 4)
    assertEquals(1.5, x.min(), 1e-9);
    assertEquals(2.0, x.max(), 1e-9);
  }

  @Test
  void failsOffTheLine() {
    Store store = new Store();
    FloatVar x = new FloatVar(store, "x", 3.0, 3.0);
    FloatVar y = new FloatVar(store, "y", 2.0, 2.0);
    store.impose(new PiecewiseLinear(x, y, XS, YS));
    assertFalse(store.consistency());

    store = new Store();
    x = new FloatVar(store, "x", 6.0, 9.0);
    y = new FloatVar(store, "y", -100, 100);
    store.impose(new PiecewiseLinear(x, y, XS, YS));
    assertFalse(store.consistency());
  }

  @Test
  void randomBoxesKeepEveryPointOfTheLine() {
    Random random = new Random(11);
    for (int trial = 0; trial < 2000; trial++) {
      int k = 1 + random.nextInt(5);
      double[] xs = new double[k];
      double[] ys = new double[k];
      double at = random.nextInt(5) - 2;
      for (int i = 0; i < k; i++) {
        at += random.nextInt(3) * 0.75;
        xs[i] = at;
        ys[i] = random.nextInt(9) - 4 + random.nextDouble();
      }
      double xLo = random.nextInt(12) * 0.5 - 3;
      double xHi = xLo + random.nextInt(8) * 0.5;
      double yLo = random.nextInt(12) * 0.5 - 4;
      double yHi = yLo + random.nextInt(8) * 0.5;
      Store store = new Store();
      FloatVar x = new FloatVar(store, "x", xLo, xHi);
      FloatVar y = new FloatVar(store, "y", yLo, yHi);
      PiecewiseLinear c = new PiecewiseLinear(x, y, xs, ys);
      store.impose(c);
      boolean ok = store.consistency();
      // every point of the line inside the box stays
      for (int i = 0; i < Math.max(1, k - 1); i++) {
        int j = Math.min(i + 1, k - 1);
        for (int step = 0; step <= 64; step++) {
          double s = step / 64.0;
          double px = xs[i] + s * (xs[j] - xs[i]);
          double py = ys[i] + s * (ys[j] - ys[i]);
          if (px >= xLo && px <= xHi && py >= yLo && py <= yHi) {
            String at2 = "trial " + trial + " point (" + px + ", " + py + ") " + c;
            assertTrue(ok, at2);
            assertTrue(
                x.min() <= px + 1e-9
                    && px - 1e-9 <= x.max()
                    && y.min() <= py + 1e-9
                    && py - 1e-9 <= y.max(),
                at2);
            Store point = new Store();
            FloatVar fx = new FloatVar(point, "x", px, px);
            FloatVar fy = new FloatVar(point, "y", py, py);
            PiecewiseLinear pc = new PiecewiseLinear(fx, fy, xs, ys);
            point.impose(pc);
            assertTrue(point.consistency(), at2);
            assertTrue(pc.satisfied(), at2);
          }
        }
      }
    }
  }
}
