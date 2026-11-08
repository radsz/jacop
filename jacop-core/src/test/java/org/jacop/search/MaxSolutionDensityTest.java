/*
 * MaxSolutionDensityTest.java
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

package org.jacop.search;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.SolutionDensities;
import org.jacop.constraints.regular.Regular;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;
import org.junit.jupiter.api.Test;

/**
 * Solution densities against brute force, and the maxSD search against plain search.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class MaxSolutionDensityTest {

  private static final int TRIALS = Integer.getInteger("density.trials", 150);

  private interface Check {
    boolean holds(int[] t);
  }

  /** The exact densities, by enumerating the tuples of the current domains. */
  private static Map<IntVar, Map<Integer, Double>> bruteForce(IntVar[] x, Check check) {
    int[] t = new int[x.length];
    Map<IntVar, Map<Integer, Double>> counts = new IdentityHashMap<>();
    double[] total = {0};
    enumerate(x, 0, t, check, counts, total);
    for (Map<Integer, Double> m : counts.values()) {
      double s = m.values().stream().mapToDouble(Double::doubleValue).sum();
      m.replaceAll((v, c) -> c / s);
    }
    return counts;
  }

  private static void enumerate(
      IntVar[] x,
      int i,
      int[] t,
      Check check,
      Map<IntVar, Map<Integer, Double>> counts,
      double[] total) {
    if (i == x.length) {
      if (check.holds(t)) {
        total[0]++;
        for (int k = 0; k < x.length; k++) {
          counts.computeIfAbsent(x[k], z -> new HashMap<>()).merge(t[k], 1.0d, Double::sum);
        }
      }
      return;
    }
    for (ValueEnumeration e = x[i].dom().valueEnumeration(); e.hasMoreElements(); ) {
      t[i] = e.nextElement();
      enumerate(x, i + 1, t, check, counts, total);
    }
  }

  private static Map<IntVar, Map<Integer, Double>> reported(Constraint c) {
    Map<IntVar, Map<Integer, Double>> got = new IdentityHashMap<>();
    boolean ok =
        new SolutionDensities()
            .densities(c, (x, v, d) -> got.computeIfAbsent(x, z -> new HashMap<>()).put(v, d));
    return ok ? got : null;
  }

  private static void assertSame(
      IntVar[] x, Map<IntVar, Map<Integer, Double>> exact, Map<IntVar, Map<Integer, Double>> got) {
    assertNotNull(got);
    for (IntVar y : x) {
      if (y.singleton()) {
        continue;
      }
      Map<Integer, Double> e = exact.get(y);
      Map<Integer, Double> g = got.get(y);
      assertNotNull(g, y.id());
      for (ValueEnumeration en = y.dom().valueEnumeration(); en.hasMoreElements(); ) {
        int v = en.nextElement();
        double expected = e == null ? 0.0d : e.getOrDefault(v, 0.0d);
        assertEquals(expected, g.getOrDefault(v, -1.0d), 1e-9, y.id() + "=" + v);
      }
    }
  }

  // a few random decisions, each undone if it fails
  private static void narrow(Store store, IntVar[] x, Random random) {
    for (int k = random.nextInt(3); k > 0; k--) {
      IntVar y = x[random.nextInt(x.length)];
      if (y.singleton()) {
        continue;
      }
      store.setLevel(store.level + 1);
      int v = y.min() + random.nextInt(y.max() - y.min() + 1);
      try {
        y.domain.inComplement(store.level, y, v);
        if (!store.consistency()) {
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
        }
      } catch (org.jacop.core.FailException f) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }
    }
  }

  @Test
  void linearDensitiesAreExact() {
    Random random = new Random(7);
    int checked = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      Store store = new Store();
      int n = 2 + random.nextInt(4);
      IntVar[] x = new IntVar[n];
      int[] a = new int[n];
      for (int i = 0; i < n; i++) {
        int lo = random.nextInt(5) - 2;
        x[i] = new IntVar(store, "x" + i, lo, lo + 1 + random.nextInt(4));
        if (random.nextInt(4) == 0) {
          x[i].domain.inComplement(0, x[i], lo + 1);
        }
        a[i] = random.nextInt(7) - 3;
        if (a[i] == 0) {
          a[i] = 2;
        }
      }
      String[] rels = {"==", "<=", ">=", "<", ">"};
      String rel = rels[random.nextInt(rels.length)];
      int b = random.nextInt(9) - 4;
      LinearInt c = new LinearInt(x, a, rel, b);
      store.impose(c);
      if (!store.consistency()) {
        continue;
      }
      narrow(store, x, random);
      Check check =
          t -> {
            long s = 0;
            for (int i = 0; i < n; i++) {
              s += (long) a[i] * t[i];
            }
            return switch (rel) {
              case "==" -> s == b;
              case "<=" -> s <= b;
              case ">=" -> s >= b;
              case "<" -> s < b;
              default -> s > b;
            };
          };
      assertTrue(SolutionDensities.supports(c));
      Map<IntVar, Map<Integer, Double>> got = reported(c);
      if (got == null) {
        continue;
      }
      assertSame(x, bruteForce(x, check), got);
      checked++;
    }
    assertTrue(checked > TRIALS / 3, "checked " + checked);
  }

  @Test
  void regularDensitiesAreExact() {
    Random random = new Random(11);
    int checked = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      Store store = new Store();
      int n = 2 + random.nextInt(4);
      int values = 2 + random.nextInt(3);
      int states = 2 + random.nextInt(4);
      int[][] next = new int[states][values];
      boolean[] accepting = new boolean[states];
      Fsm fsm = new Fsm();
      FsmState[] state = new FsmState[states];
      for (int q = 0; q < states; q++) {
        state[q] = new FsmState();
        fsm.allStates.add(state[q]);
      }
      fsm.initState = state[0];
      for (int q = 0; q < states; q++) {
        accepting[q] = random.nextInt(3) > 0;
        if (accepting[q]) {
          fsm.finalStates.add(state[q]);
        }
        for (int v = 0; v < values; v++) {
          next[q][v] = random.nextInt(10) < 8 ? random.nextInt(states) : -1;
          if (next[q][v] >= 0) {
            state[q].addTransition(new FsmTransition(new IntervalDomain(v, v), state[next[q][v]]));
          }
        }
      }
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, values - 1);
      }
      Regular regular = new Regular(fsm, x);
      store.impose(regular);
      if (!store.consistency()) {
        continue;
      }
      narrow(store, x, random);
      Check check =
          t -> {
            int q = 0;
            for (int v : t) {
              q = next[q][v];
              if (q < 0) {
                return false;
              }
            }
            return accepting[q];
          };
      Map<IntVar, Map<Integer, Double>> got = reported(regular);
      if (got == null) {
        continue;
      }
      assertSame(x, bruteForce(x, check), got);
      checked++;
    }
    assertTrue(checked > TRIALS / 3, "checked " + checked);
  }

  /** The Brégman–Minc bound of the value matrix with x = v, computed for each pair. */
  private static double bound(IntVar[] x, IntVar fixed, int value) {
    double log = 0;
    for (IntVar y : x) {
      if (y == fixed || y.singleton()) {
        continue;
      }
      int d = y.getSize() - (y.domain.contains(value) ? 1 : 0);
      for (IntVar z : x) {
        if (z.singleton() && z != fixed && y.domain.contains(z.value())) {
          return 0;
        }
      }
      if (d == 0) {
        return 0;
      }
      double logFact = 0;
      for (int k = 2; k <= d; k++) {
        logFact += Math.log(k);
      }
      log += logFact / d;
    }
    return Math.exp(log);
  }

  @Test
  void alldifferentDensitiesFollowTheBound() {
    Random random = new Random(3);
    int checked = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      Store store = new Store();
      int n = 2 + random.nextInt(5);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        IntDomain d = new IntervalDomain();
        for (int v = 0; v < n + 2; v++) {
          if (random.nextInt(3) > 0) {
            d.unionAdapt(v, v);
          }
        }
        if (d.isEmpty()) {
          d.unionAdapt(0, 0);
        }
        x[i] = new IntVar(store, "x" + i, d);
      }
      Alldistinct alldistinct = new Alldistinct(x);
      store.impose(alldistinct);
      if (!store.consistency()) {
        continue;
      }
      narrow(store, x, random);
      Map<IntVar, Map<Integer, Double>> got = reported(alldistinct);
      boolean anyFree = false;
      for (IntVar y : x) {
        anyFree |= !y.singleton();
      }
      if (!anyFree) {
        continue;
      }
      assertNotNull(got);
      for (IntVar y : x) {
        if (y.singleton()) {
          continue;
        }
        double sum = 0;
        for (ValueEnumeration e = y.dom().valueEnumeration(); e.hasMoreElements(); ) {
          sum += bound(x, y, e.nextElement());
        }
        for (ValueEnumeration e = y.dom().valueEnumeration(); e.hasMoreElements(); ) {
          int v = e.nextElement();
          assertEquals(bound(x, y, v) / sum, got.get(y).get(v), 1e-9, y.id() + "=" + v);
        }
      }
      checked++;
    }
    assertTrue(checked > TRIALS / 3, "checked " + checked);
  }

  @Test
  void maxSdFindsAllSolutions() {
    Random random = new Random(5);
    for (int trial = 0; trial < TRIALS / 3; trial++) {
      long seed = random.nextLong();
      int plain = countSolutions(seed, false);
      int counting = countSolutions(seed, true);
      assertEquals(plain, counting, "seed " + seed);
    }
  }

  private static int countSolutions(long seed, boolean maxSd) {
    Random random = new Random(seed);
    Store store = new Store();
    int n = 4 + random.nextInt(2);
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, n);
    }
    store.impose(new Alldistinct(x));
    int[] a = new int[n];
    for (int i = 0; i < n; i++) {
      a[i] = 1 + random.nextInt(3);
    }
    store.impose(new LinearInt(x, a, "<=", 2 * n + random.nextInt(3 * n)));
    IntVar extra = new IntVar(store, "y", 0, 3);
    store.impose(new LinearInt(new IntVar[] {x[0], extra}, new int[] {1, -1}, "==", 0));
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    IntVar[] all = new IntVar[n + 1];
    System.arraycopy(x, 0, all, 0, n);
    all[n] = extra;
    SelectChoicePoint<IntVar> plain = new SimpleSelect<>(all, null, new IndomainMin<>());
    @SuppressWarnings({"unchecked", "rawtypes"})
    SelectChoicePoint<IntVar> select =
        maxSd
            ? (SelectChoicePoint) new SequenceSelect(List.of(new MaxSolutionDensity(all), plain))
            : plain;
    search.labeling(store, select);
    return search.getSolutionListener().solutionsNo();
  }

  @Test
  void maxSdPicksTheDensestPair() {
    Store store = new Store();
    // x0 in {0, 1}, x1 in {0, 1, 2}: x0 = 0 and x0 = 1 leave x1 two values each, bound f(2) =
    // sqrt(2) for both, density 1/2; x1 = 2 leaves x0 both values, sqrt(2), and x1 = 0 and x1 = 1
    // one, so x1 = 2 has density sqrt(2) / (2 + sqrt(2)) = 0.41 (exactly 1/2), below x0's
    IntVar x0 = new IntVar(store, "x0", 0, 1);
    IntVar x1 = new IntVar(store, "x1", 0, 2);
    store.impose(new Alldistinct(new IntVar[] {x0, x1}));
    assertTrue(store.consistency());
    MaxSolutionDensity select = new MaxSolutionDensity(new IntVar[] {x0, x1});
    IntVar chosen = select.getChoiceVariable(0);
    assertNotNull(chosen);
    assertEquals(x0, chosen);
    assertEquals(0, select.getChoiceValue());
    assertFalse(select.countingConstraints().isEmpty());
  }
}
