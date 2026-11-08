/*
 * CapacityCutsTest.java
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

package org.jacop.constraints.lp;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import org.jacop.constraints.Linearizations.Implication;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.LinearForm;
import org.junit.jupiter.api.Test;

/**
 * Checks the perspective cuts of {@link PerspectiveCuts} on small random half-reified linear
 * relations: no cut may cut off an integer solution, found by enumeration, whatever the LP values
 * the cut was separated from; and a point that some subset inequality of the hull cuts off by a
 * clear margin, found by trying every subset, gets a cut.
 */
class PerspectiveCutsTest {

  private static final int INSTANCES = Integer.getInteger("perspective.instances", 2000);

  @Test
  void cutsKeepEverySolutionAndSeparateTheHull() {
    Random rnd = new Random(5);
    int cuts = 0;
    for (int run = 0; run < INSTANCES; run++) {
      Store store = new Store();
      int n = 2 + rnd.nextInt(3);
      IntVar[] x = new IntVar[n];
      long[] a = new long[n];
      long least = 0;
      long most = 0;
      for (int i = 0; i < n; i++) {
        int lo = rnd.nextInt(7) - 3;
        x[i] = new IntVar(store, "x" + i, lo, lo + rnd.nextInt(5));
        a[i] = (rnd.nextInt(4) + 1) * (rnd.nextBoolean() ? 1 : -1);
        least += a[i] * (a[i] > 0 ? x[i].min() : x[i].max());
        most += a[i] * (a[i] > 0 ? x[i].max() : x[i].min());
      }
      long c = least + rnd.nextInt((int) (most - least + 1));
      IntVar b = new IntVar(store, "b", 0, 1);
      boolean when = rnd.nextBoolean();
      Implication imp = new Implication(x, a, c, b, when);
      Map<IntVar, Integer> columnOf = new IdentityHashMap<>();
      for (int i = 0; i < n; i++) {
        columnOf.put(x[i], i);
      }
      columnOf.put(b, n);
      List<long[]> solutions = solutions(x, a, c, when);
      PerspectiveCuts p = new PerspectiveCuts(List.of(imp));
      for (int point = 0; point < 10; point++) {
        double[] value = new double[n + 1];
        for (int i = 0; i < n; i++) {
          value[i] = x[i].min() + rnd.nextDouble() * (x[i].max() - x[i].min());
        }
        value[n] = rnd.nextDouble();
        List<MirCut> found = p.separate(columnOf, value, 10);
        for (MirCut cut : found) {
          cuts++;
          for (long[] s : solutions) {
            long activity = 0;
            for (int k = 0; k < cut.columns.length; k++) {
              activity += cut.weights[k] * s[cut.columns[k]];
            }
            assertThat(activity)
                .as("run %d cut %s at %s", run, cut, s)
                .isLessThanOrEqualTo(cut.rhs);
          }
        }
        if (mostViolated(x, a, c, when, value) > 0.01) {
          assertThat(found).as("run %d %s", run, imp).isNotEmpty();
        }
      }
    }
    assertThat(cuts).isGreaterThan(INSTANCES);
  }

  @Test
  void cutsOffTheFractionalPointOfBigM() {
    // b -> x + y <= 3 with x, y in [0, 10]: the big-M row x + y + 17 b <= 20 admits b = 1/2,
    // x = 10, y = 3/2; the cut x + 7 b <= 10 (b -> x <= 3) cuts it off
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 10);
    IntVar y = new IntVar(store, "y", 0, 10);
    IntVar b = new IntVar(store, "b", 0, 1);
    Map<IntVar, Integer> columnOf = new IdentityHashMap<>(Map.of(x, 0, y, 1, b, 2));
    PerspectiveCuts p =
        new PerspectiveCuts(
            List.of(new Implication(new IntVar[] {x, y}, new long[] {1, 1}, 3, b, true)));
    List<MirCut> cuts = p.separate(columnOf, new double[] {10, 1.5, 0.5}, 10);
    assertThat(cuts).hasSize(1);
    assertThat(cuts.get(0).columns).containsExactly(0, 2);
    assertThat(cuts.get(0).weights).containsExactly(1, 7);
    assertThat(cuts.get(0).rhs).isEqualTo(10);
    // at b = 0 the box is the hull
    assertThat(p.separate(columnOf, new double[] {10, 10, 0}, 10)).isEmpty();
  }

  @Test
  void pairRowsKeepEverySolution() {
    Random rnd = new Random(9);
    int rows = 0;
    for (int run = 0; run < INSTANCES; run++) {
      Store store = new Store();
      int n = 2 + rnd.nextInt(3);
      IntVar[] x = new IntVar[n];
      long[] a = new long[n];
      long least = 0;
      long most = 0;
      for (int i = 0; i < n; i++) {
        x[i] =
            rnd.nextInt(3) == 0
                ? new IntVar(store, "x" + i, -2, 3)
                : new IntVar(store, "x" + i, 0, 1);
        a[i] = (rnd.nextInt(4) + 1) * (rnd.nextBoolean() ? 1 : -1);
        least += a[i] * (a[i] > 0 ? x[i].min() : x[i].max());
        most += a[i] * (a[i] > 0 ? x[i].max() : x[i].min());
      }
      long c = least + rnd.nextInt((int) (most - least + 1));
      IntVar b = new IntVar(store, "b", 0, 1);
      boolean when = rnd.nextBoolean();
      List<LinearForm> made = PerspectiveCuts.pairRows(List.of(new Implication(x, a, c, b, when)));
      rows += made.size();
      for (long[] s : solutions(x, a, c, when)) {
        for (LinearForm f : made) {
          long activity = 0;
          for (int k = 0; k < f.vars().length; k++) {
            activity +=
                f.weights()[k]
                    * (f.vars()[k] == b ? s[n] : s[Arrays.asList(x).indexOf(f.vars()[k])]);
          }
          assertThat(f.relation() == LinearForm.LE ? activity <= f.c() : activity >= f.c())
              .as("run %d %s at %s", run, f, Arrays.toString(s))
              .isTrue();
        }
      }
    }
    assertThat(rows).isGreaterThan(INSTANCES / 4);
  }

  @Test
  void hintsMakeCliquesButNoRowsOfTheirOwn() {
    // the model states x + y <= 1; the hints b -> x = 0 and b -> y = 0 close the clique {x, y, b},
    // and the hint !c -> x = 0 is alone
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 1);
    IntVar y = new IntVar(store, "y", 0, 1);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar c = new IntVar(store, "c", 0, 1);
    LinearForm model = new LinearForm(new IntVar[] {x, y}, new long[] {1, 1}, 1, LinearForm.LE);
    List<LinearForm> hints =
        List.of(
            new LinearForm(new IntVar[] {x, b}, new long[] {1, 1}, 1, LinearForm.LE),
            new LinearForm(new IntVar[] {y, b}, new long[] {1, 1}, 1, LinearForm.LE),
            new LinearForm(new IntVar[] {x, c}, new long[] {1, -1}, 0, LinearForm.LE));
    PairCliques merged = PairCliques.merge(List.of(model), List.of(), hints);
    assertThat(merged.cliques).isEqualTo(1);
    assertThat(merged.rows).hasSize(1);
    assertThat(merged.rows.get(0).vars()).containsExactlyInAnyOrder(x, y, b);
    assertThat(merged.further).isEmpty();
    // hints alone: the clique is a further row
    PairCliques alone =
        PairCliques.merge(
            List.of(),
            List.of(),
            List.of(
                hints.get(0),
                hints.get(1),
                new LinearForm(new IntVar[] {x, y}, new long[] {1, 1}, 1, LinearForm.LE)));
    assertThat(alone.rows).isEmpty();
    assertThat(alone.further).hasSize(1);
  }

  // the integer points (x, b) of [b = when] -> sum a x <= c in the box
  private static List<long[]> solutions(IntVar[] x, long[] a, long c, boolean when) {
    int n = x.length;
    List<long[]> out = new ArrayList<>();
    long[] v = new long[n + 1];
    for (int i = 0; i < n; i++) {
      v[i] = x[i].min();
    }
    while (true) {
      long sum = 0;
      for (int i = 0; i < n; i++) {
        sum += a[i] * v[i];
      }
      for (int b = 0; b <= 1; b++) {
        if ((b == 1) != when || sum <= c) {
          long[] s = v.clone();
          s[n] = b;
          out.add(s);
        }
      }
      int i = 0;
      while (i < n && v[i] == x[i].max()) {
        v[i] = x[i].min();
        i++;
      }
      if (i == n) {
        return out;
      }
      v[i]++;
    }
  }

  // the largest violation over the norm of the subset inequalities of the hull, unrounded, over
  // every subset
  private static double mostViolated(IntVar[] x, long[] a, long c, boolean when, double[] value) {
    int n = x.length;
    double beta = when ? value[n] : 1 - value[n];
    double best = Double.NEGATIVE_INFINITY;
    for (int mask = 1; mask < 1 << n; mask++) {
      double lhs = 0;
      double inS = 0;
      double norm = 0;
      double k = -c;
      for (int i = 0; i < n; i++) {
        double lo = a[i] * (a[i] > 0 ? x[i].min() : x[i].max());
        double hi = a[i] * (a[i] > 0 ? x[i].max() : x[i].min());
        if ((mask >> i & 1) == 1) {
          lhs += a[i] * value[i];
          norm += (double) a[i] * a[i];
          inS += hi;
          k += hi;
        } else {
          k += lo;
        }
      }
      best = Math.max(best, (lhs + beta * k - inS) / Math.sqrt(norm + k * k));
    }
    return best;
  }
}
