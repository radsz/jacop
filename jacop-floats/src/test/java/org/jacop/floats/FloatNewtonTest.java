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

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.core.Store;
import org.jacop.floats.constraints.CosPeqR;
import org.jacop.floats.constraints.ExpPeqR;
import org.jacop.floats.constraints.FloatNewton;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.constraints.PowPeqR;
import org.jacop.floats.constraints.SinPeqR;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * Checks that the interval Newton contractor ({@link FloatNewton}) never removes a solution. Random
 * square systems are built around a random point, and random dives that keep the point run the
 * contractor at every node.
 *
 * <p>Polynomial systems use points on a grid of quarters, where every product, power and sum is
 * exact in double, so the point is an exact solution and must stay in the domains. Systems with
 * exp, sin and cos have a solution within rounding of the point; dives keep a margin around it and
 * the domains must stay within 1e-6 of it. {@code floats.newton.trials} (default 2000) systems of
 * each kind.
 */
class FloatNewtonTest {

  private static final int TRIALS = Integer.getInteger("floats.newton.trials", 2000);

  private static final double MARGIN = 1e-6;

  @BeforeEach
  void weakFixpoint() {
    FloatDomain.setMinReduction(0.01);
  }

  @AfterEach
  void restore() {
    FloatDomain.setMinReduction(0);
  }

  @Test
  void polynomialSystemsKeepTheExactSolution() {
    Random random = new Random(20261115L);
    long narrowings = 0;
    for (int t = 0; t < TRIALS; t++) {
      narrowings += trial(random, t, false);
    }
    assertTrue(narrowings > 0, "the contractor never narrowed a domain");
  }

  @Test
  void transcendentalSystemsKeepTheSolution() {
    Random random = new Random(20261116L);
    long narrowings = 0;
    for (int t = 0; t < TRIALS; t++) {
      narrowings += trial(random, t, true);
    }
    assertTrue(narrowings > 0, "the contractor never narrowed a domain");
  }

  private static long trial(Random random, int t, boolean transcendental) {
    Store store = new Store();
    int n = 1 + random.nextInt(4);
    FloatVar[] x = new FloatVar[n];
    double[] point = new double[n];
    for (int i = 0; i < n; i++) {
      x[i] = new FloatVar(store, "x" + i, -4, 4);
      point[i] = (random.nextInt(25) - 12) / 4.0;
    }
    List<FloatVar> all = new ArrayList<>(Arrays.asList(x));
    List<Double> values = new ArrayList<>();
    for (double p : point) {
      values.add(p);
    }
    for (int e = 0; e < n; e++) {
      List<FloatVar> terms = new ArrayList<>();
      List<Double> weights = new ArrayList<>();
      double value = 0;
      // a linear term in x[e] keeps most systems regular
      terms.add(x[e]);
      weights.add((double) (1 + random.nextInt(3)));
      value += weights.get(0) * point[e];
      for (int k = 0; k < 2; k++) {
        int i = random.nextInt(n);
        int j = random.nextInt(n);
        double w = random.nextInt(5) - 2;
        if (w == 0) {
          continue;
        }
        FloatVar term = new FloatVar(store, -1e4, 1e4);
        double v;
        int kind = random.nextInt(transcendental ? 5 : 2);
        switch (kind) {
          case 0 -> {
            store.impose(new PmulQeqR(x[i], x[j], term));
            v = point[i] * point[j];
          }
          case 1 -> {
            int power = 2 + random.nextInt(2);
            store.impose(new PowPeqR(x[i], power, term));
            v = Math.pow(point[i], power);
          }
          case 2 -> {
            store.impose(new ExpPeqR(x[i], term));
            v = Math.exp(point[i]);
          }
          case 3 -> {
            store.impose(new SinPeqR(x[i], term));
            v = Math.sin(point[i]);
          }
          default -> {
            store.impose(new CosPeqR(x[i], term));
            v = Math.cos(point[i]);
          }
        }
        all.add(term);
        values.add(v);
        terms.add(term);
        weights.add(w);
        value += w * v;
      }
      FloatVar[] list = terms.toArray(new FloatVar[0]);
      double[] ws = weights.stream().mapToDouble(Double::doubleValue).toArray();
      store.impose(new LinearFloat(list, ws, "==", value));
    }
    FloatNewton newton = new FloatNewton(store, x);
    assertTrue(newton.isSquare(), "trial " + t + " is not square");
    double margin = transcendental ? MARGIN : 0;
    String context = "trial " + t + " point " + Arrays.toString(point);
    if (!store.consistency() || !newton.executeAfterConsistency(true)) {
      fail("root failed, " + context);
    }
    check(all, values, margin, context);
    for (int depth = 0; depth < 30; depth++) {
      store.setLevel(store.level + 1);
      int i = random.nextInt(n);
      double cut = x[i].min() + (x[i].max() - x[i].min()) * random.nextDouble();
      if (point[i] <= cut) {
        x[i].domain.in(store.level, x[i], x[i].min(), Math.max(cut, point[i] + margin));
      } else {
        x[i].domain.in(store.level, x[i], Math.min(cut, point[i] - margin), x[i].max());
      }
      if (!store.consistency() || !newton.executeAfterConsistency(true)) {
        fail("failed at depth " + depth + ", " + context);
      }
      check(all, values, margin, context + " depth " + depth);
    }
    return newton.narrowings;
  }

  private static void check(
      List<FloatVar> vars, List<Double> values, double margin, String context) {
    for (int i = 0; i < vars.size(); i++) {
      FloatVar v = vars.get(i);
      double p = values.get(i);
      double tolerance = margin * Math.max(1, Math.abs(p));
      if (v.min() > p + tolerance || v.max() < p - tolerance) {
        fail(v + " lost " + p + ", " + context);
      }
    }
  }
}
