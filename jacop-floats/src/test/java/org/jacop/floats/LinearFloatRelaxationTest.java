/*
 * LinearFloatRelaxationTest.java
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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.core.Store;
import org.jacop.floats.constraints.LinearFloatRelaxation;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.junit.jupiter.api.Test;

/**
 * Tests of {@link LinearFloatRelaxation}: the bound it proves, the boxes it fails, and that it
 * never removes a real point that satisfies its rows and products (random models built around a
 * point).
 */
class LinearFloatRelaxationTest {

  private static final int TRIALS = Integer.getInteger("float.relaxation.trials", 2000);

  private static final double INF = Double.POSITIVE_INFINITY;

  /** Minimise 2x + 3y with x + y >= 4: the bound is 8, which interval propagation does not see. */
  @Test
  void boundsTheCostByTheLinearProgram() {
    Store store = new Store();
    FloatVar x = new FloatVar(store, "x", 0, 10);
    FloatVar y = new FloatVar(store, "y", 0, 10);
    FloatVar cost = new FloatVar(store, "cost", -100, 100);
    store.impose(
        new LinearFloatRelaxation(
            new FloatVar[][] {{cost, x, y}, {x, y}},
            new double[][] {{1, -2, -3}, {1, 1}},
            new double[] {0, 4},
            new double[] {0, INF},
            cost));
    assertTrue(store.consistency());
    assertTrue(cost.min() > 8 - 1e-6 && cost.min() <= 8, "bound " + cost.min());
  }

  /** x + y, y + z and x + z at least 2 force x + y + z >= 3: a sum at most 2.9 fails. */
  @Test
  void failsAnInfeasibleBoxByItsFarkasRay() {
    Store store = new Store();
    FloatVar x = new FloatVar(store, "x", 0, 2);
    FloatVar y = new FloatVar(store, "y", 0, 2);
    FloatVar z = new FloatVar(store, "z", 0, 2);
    FloatVar cost = new FloatVar(store, "cost", -10, 10);
    store.impose(
        new LinearFloatRelaxation(
            new FloatVar[][] {{x, y}, {y, z}, {x, z}, {x, y, z}, {cost, x}},
            new double[][] {{1, 1}, {1, 1}, {1, 1}, {1, 1, 1}, {1, -1}},
            new double[] {2, 2, 2, -INF, 0},
            new double[] {INF, INF, INF, 2.9, 0},
            cost));
    assertFalse(store.consistency());
  }

  /**
   * Random rows and products around a random point, over a random box that holds the point: the
   * relaxation must keep the box and bound the cost by at most its value at the point.
   */
  @Test
  void neverCutsOffARealPoint() {
    neverCutsOffARealPoint(new Random(20261114), new double[] {1});
  }

  /**
   * The same over variables of very different magnitudes, as in Ibex's ex6_1_3 (1e-7 to 1e8): the
   * rounding errors of the rows of the products must stay inside the safe bound.
   */
  @Test
  void neverCutsOffARealPointOverWideRanges() {
    neverCutsOffARealPoint(new Random(20261115), new double[] {1e-7, 1e-3, 1, 1e3, 1e8});
  }

  private static void neverCutsOffARealPoint(Random random, double[] scales) {
    for (int trial = 0; trial < TRIALS; trial++) {
      Store store = new Store();
      int n = 2 + random.nextInt(4);
      double[] point = new double[n];
      FloatVar[] vars = new FloatVar[n];
      for (int i = 0; i < n; i++) {
        double scale = scales[random.nextInt(scales.length)];
        point[i] =
            scale * (random.nextInt(3) == 0 ? random.nextInt(5) - 2 : 10 * random.nextDouble() - 5);
        double lo = point[i] - (random.nextBoolean() ? 0 : 5 * scale * random.nextDouble());
        double hi = point[i] + (random.nextBoolean() ? 0 : 5 * scale * random.nextDouble());
        vars[i] = new FloatVar(store, "x" + i, lo, hi);
      }
      List<FloatVar[]> products = new ArrayList<>();
      List<Double> productValues = new ArrayList<>();
      int p = random.nextInt(4);
      for (int k = 0; k < p; k++) {
        int a = random.nextInt(n);
        int b = random.nextBoolean() ? a : random.nextInt(n);
        double v = point[a] * point[b];
        FloatVar z =
            new FloatVar(
                store,
                "z" + k,
                v - Math.max(1, Math.abs(v)) * (3 * random.nextDouble() + 1e-9),
                v + Math.max(1, Math.abs(v)) * (3 * random.nextDouble() + 1e-9));
        products.add(new FloatVar[] {vars[a], vars[b], z});
        productValues.add(v);
      }
      // the columns: the variables, then the products
      int columns = n + p;
      FloatVar[] all = new FloatVar[columns];
      double[] value = new double[columns];
      for (int i = 0; i < n; i++) {
        all[i] = vars[i];
        value[i] = point[i];
      }
      for (int k = 0; k < p; k++) {
        all[n + k] = products.get(k)[2];
        value[n + k] = productValues.get(k);
      }
      int m = 1 + random.nextInt(4);
      FloatVar cost = new FloatVar(store, "cost", -1e150, 1e150);
      FloatVar[][] rowVars = new FloatVar[m + 1][];
      double[][] rowWeights = new double[m + 1][];
      double[] rowLo = new double[m + 1];
      double[] rowHi = new double[m + 1];
      double costValue = 0;
      double costMagnitude = 0;
      for (int r = 0; r <= m; r++) {
        int size = 1 + random.nextInt(columns);
        FloatVar[] rv = new FloatVar[size + (r == 0 ? 1 : 0)];
        double[] rw = new double[rv.length];
        double activity = 0;
        // the size of the terms, for the rounding error of the activity
        double magnitude = 0;
        for (int k = 0; k < size; k++) {
          int j = random.nextInt(columns);
          rv[k] = all[j];
          rw[k] = random.nextInt(7) - 3 + (random.nextBoolean() ? 0 : random.nextDouble());
          activity += rw[k] * value[j];
          magnitude += Math.abs(rw[k] * value[j]);
        }
        if (r == 0) {
          // cost = the terms of the row
          rv[size] = cost;
          rw[size] = -1;
          costValue = activity;
          costMagnitude = magnitude;
          rowLo[r] = 0;
          rowHi[r] = 0;
        } else {
          double slack = 1e-9 * (1 + magnitude);
          switch (random.nextInt(3)) {
            case 0 -> {
              rowLo[r] = activity - slack;
              rowHi[r] = activity + slack;
            }
            case 1 -> {
              rowLo[r] = -INF;
              rowHi[r] = activity + slack + (random.nextBoolean() ? 0 : random.nextDouble());
            }
            default -> {
              rowLo[r] = activity - slack - (random.nextBoolean() ? 0 : random.nextDouble());
              rowHi[r] = INF;
            }
          }
        }
        rowVars[r] = rv;
        rowWeights[r] = rw;
      }
      String model = "trial " + trial + " point " + Arrays.toString(value);
      store.impose(
          new LinearFloatRelaxation(
              rowVars, rowWeights, rowLo, rowHi, products.toArray(new FloatVar[0][]), cost));
      for (FloatVar[] t : products) {
        store.impose(new PmulQeqR(t[0], t[1], t[2]));
      }
      assertTrue(store.consistency(), "failed with a real point: " + model);
      double eps = FloatDomain.epsilon(costValue) + 1e-9 * (1 + costMagnitude);
      assertTrue(
          cost.min() <= costValue + eps,
          "bound " + cost.min() + " above the cost " + costValue + " of " + model);
    }
  }
}
