/*
 * FunctionalTabuSearchTest.java
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

package org.jacop.search.ls;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.core.IntDomain;
import org.jacop.core.IntervalDomain;
import org.junit.jupiter.api.Test;

/**
 * Checks the tabu search over functional models: after every move the values it keeps equal the
 * values of the definitions (partial sums put into their readers included), its best cost equals
 * the cost of its best assignment and is never below the optimum of an enumeration, and it reaches
 * that optimum on small models, low autocorrelation binary sequences and random ones with
 * restrictive domains.
 */
class FunctionalTabuSearchTest {

  // a model under construction: one entry per variable
  private static final class Model {
    final List<Integer> kind = new ArrayList<>();
    final List<int[]> inputs = new ArrayList<>();
    final List<long[]> coefficients = new ArrayList<>();
    final List<Long> constant = new ArrayList<>();
    final List<FunctionalTabuSearch.Definition> functions = new ArrayList<>();
    final List<IntDomain> domains = new ArrayList<>();

    int add(int k, int[] in, long[] cs, long c, IntDomain d) {
      kind.add(k);
      inputs.add(in);
      coefficients.add(cs);
      constant.add(c);
      functions.add(null);
      domains.add(d);
      return kind.size() - 1;
    }

    int decision(IntDomain d) {
      return add(FunctionalTabuSearch.DECISION, new int[0], new long[0], 0, d);
    }

    int linear(int[] in, long[] cs, long c, IntDomain d) {
      return add(FunctionalTabuSearch.LINEAR, in, cs, c, d);
    }

    int product(int x, int y, IntDomain d) {
      return add(FunctionalTabuSearch.PRODUCT, new int[] {x, y}, new long[0], 0, d);
    }

    int max(int[] in, IntDomain d) {
      int v = add(FunctionalTabuSearch.FUNCTION, in, new long[0], 0, d);
      functions.set(
          v,
          value -> {
            long m = Long.MIN_VALUE;
            for (int u : in) {
              m = Math.max(m, value.applyAsInt(u));
            }
            return m;
          });
      return v;
    }

    FunctionalTabuSearch search(int cost, long seed) {
      int n = kind.size();
      FunctionalTabuSearch ts =
          new FunctionalTabuSearch(
              kind.stream().mapToInt(Integer::intValue).toArray(),
              inputs.toArray(new int[0][]),
              coefficients.toArray(new long[0][]),
              constant.stream().mapToLong(Long::longValue).toArray(),
              functions.toArray(new FunctionalTabuSearch.Definition[n]),
              domains.toArray(new IntDomain[0]),
              cost,
              seed);
      ts.setVerify(true);
      return ts;
    }
  }

  private static IntDomain interval(int min, int max) {
    return new IntervalDomain(min, max);
  }

  private static IntDomain plusMinusOne() {
    IntervalDomain d = new IntervalDomain(-1, -1);
    d.unionAdapt(1, 1);
    return d;
  }

  // low autocorrelation binary sequences of length n, the sums split in partial sums of 3 terms
  private static int labs(Model m, int n, int[] xs) {
    for (int i = 0; i < n; i++) {
      xs[i] = m.decision(plusMinusOne());
    }
    List<Integer> squares = new ArrayList<>();
    for (int k = 1; k < n; k++) {
      List<Integer> ys = new ArrayList<>();
      for (int i = 0; i + k < n; i++) {
        ys.add(m.product(xs[i], xs[i + k], plusMinusOne()));
      }
      int c = partialSums(m, ys);
      squares.add(m.product(c, c, interval(0, n * n)));
    }
    return partialSums(m, squares);
  }

  private static int partialSums(Model m, List<Integer> terms) {
    List<Integer> parts = new ArrayList<>();
    for (int k = 0; k < terms.size(); k += 3) {
      List<Integer> part = terms.subList(k, Math.min(terms.size(), k + 3));
      parts.add(sum(m, part));
    }
    return parts.size() == 1 ? parts.get(0) : sum(m, parts);
  }

  private static int sum(Model m, List<Integer> terms) {
    int[] in = terms.stream().mapToInt(Integer::intValue).toArray();
    long[] cs = new long[in.length];
    java.util.Arrays.fill(cs, 1);
    return m.linear(in, cs, 0, interval(-1_000_000, 1_000_000));
  }

  private static long energy(int[] s) {
    long e = 0;
    for (int k = 1; k < s.length; k++) {
      long c = 0;
      for (int i = 0; i + k < s.length; i++) {
        c += s[i] * s[i + k];
      }
      e += c * c;
    }
    return e;
  }

  private static long labsOptimum(int n) {
    long best = Long.MAX_VALUE;
    int[] s = new int[n];
    for (int a = 0; a < (1 << n); a++) {
      for (int i = 0; i < n; i++) {
        s[i] = ((a >> i) & 1) == 1 ? 1 : -1;
      }
      best = Math.min(best, energy(s));
    }
    return best;
  }

  @Test
  void reachesTheOptimumOfShortSequences() {
    for (int n = 3; n <= 14; n++) {
      Model m = new Model();
      int[] xs = new int[n];
      int cost = labs(m, n, xs);
      FunctionalTabuSearch ts = m.search(cost, n);
      assertTrue(ts.start(null));
      long optimum = labsOptimum(n);
      for (int round = 0; round < 200 && ts.best() > optimum; round++) {
        ts.run(1000, () -> false);
      }
      assertEquals(optimum, ts.best(), "n=" + n);
      int[] values = ts.bestValues();
      int[] s = new int[n];
      for (int i = 0; i < n; i++) {
        s[i] = values[xs[i]];
      }
      assertEquals(optimum, energy(s), "n=" + n);
      assertEquals(optimum, values[cost], "n=" + n);
    }
  }

  @Test
  void improvesFromAGivenStart() {
    int n = 20;
    Model m = new Model();
    int[] xs = new int[n];
    int cost = labs(m, n, xs);
    FunctionalTabuSearch ts = m.search(cost, 7);
    int[] start = new int[m.kind.size()];
    for (int i = 0; i < n; i++) {
      start[xs[i]] = 1;
    }
    assertTrue(ts.start(start));
    long from = ts.cost();
    ts.forgetBest();
    ts.improve(2000, () -> false);
    assertTrue(ts.best() < from);
    // the optimum of n = 20 is 26
    assertTrue(ts.best() >= 26);
  }

  @Test
  void rejectsCyclicDefinitions() {
    Model m = new Model();
    int x = m.decision(interval(0, 3));
    int a = m.kind.size();
    m.linear(new int[] {a + 1, x}, new long[] {1, 1}, 0, interval(-100, 100));
    m.linear(new int[] {a}, new long[] {1}, 0, interval(-100, 100));
    assertThrows(IllegalArgumentException.class, () -> m.search(a, 1));
  }

  // random models: a few decisions with holes, products, linear rows with tight domains, maxima
  @Test
  void randomModelsReachTheOptimumOfAnEnumeration() {
    Random random = new Random(42);
    int checked = 0;
    for (int trial = 0; trial < 300; trial++) {
      Model m = new Model();
      int nd = 2 + random.nextInt(4);
      int[] ds = new int[nd];
      int[][] values = new int[nd][];
      for (int d = 0; d < nd; d++) {
        int lo = -2 + random.nextInt(3);
        IntervalDomain dom = new IntervalDomain(lo, lo + 1 + random.nextInt(3));
        if (random.nextBoolean() && dom.getSize() > 2) {
          dom.subtractAdapt(lo + 1);
        }
        ds[d] = m.decision(dom);
        values[d] = new int[dom.getSize()];
        int k = 0;
        for (var e = dom.valueEnumeration(); e.hasMoreElements(); ) {
          values[d][k++] = e.nextElement();
        }
      }
      List<Integer> pool = new ArrayList<>();
      for (int d : ds) {
        pool.add(d);
      }
      int defined = 2 + random.nextInt(6);
      for (int k = 0; k < defined; k++) {
        int a = pool.get(random.nextInt(pool.size()));
        int b = pool.get(random.nextInt(pool.size()));
        int v =
            switch (random.nextInt(3)) {
              case 0 -> m.product(a, b, interval(-20 + random.nextInt(15), 30));
              case 1 ->
                  m.linear(
                      new int[] {a, b},
                      new long[] {1 + random.nextInt(3), -2 + random.nextInt(5)},
                      random.nextInt(3),
                      interval(-15 + random.nextInt(10), 5 + random.nextInt(20)));
              default -> m.max(new int[] {a, b}, interval(-10, 10));
            };
        pool.add(v);
      }
      int last = pool.size() - 1;
      int[] terms = new int[3];
      long[] cs = new long[3];
      for (int k = 0; k < 3; k++) {
        terms[k] = pool.get(nd + random.nextInt(last - nd + 1));
        cs[k] = random.nextBoolean() ? 1 : -1;
      }
      int cost = m.linear(terms, cs, 0, interval(-1000, 1000));
      long optimum = enumerate(m, ds, values, cost);
      if (optimum == Long.MAX_VALUE) {
        continue;
      }
      FunctionalTabuSearch ts = m.search(cost, trial);
      boolean started = false;
      for (int k = 0; k < 1000 && !started; k++) {
        started = ts.start(null);
      }
      if (!started) {
        continue;
      }
      ts.run(3000, () -> false);
      assertTrue(ts.best() >= optimum, "trial " + trial);
      assertEquals(ts.best(), ts.bestValues()[cost], "trial " + trial);
      checked++;
    }
    assertTrue(checked > 100, "checked " + checked);
  }

  // the least cost over every assignment of the decisions whose defined values lie in the domains
  private static long enumerate(Model m, int[] ds, int[][] values, int cost) {
    int n = m.kind.size();
    long best = Long.MAX_VALUE;
    int[] at = new int[ds.length];
    while (true) {
      long[] vs = new long[n];
      for (int d = 0; d < ds.length; d++) {
        vs[ds[d]] = values[d][at[d]];
      }
      boolean ok = true;
      for (int v = 0; v < n && ok; v++) {
        int[] in = m.inputs.get(v);
        switch (m.kind.get(v)) {
          case FunctionalTabuSearch.LINEAR -> {
            long s = m.constant.get(v);
            for (int k = 0; k < in.length; k++) {
              s += m.coefficients.get(v)[k] * vs[in[k]];
            }
            vs[v] = s;
          }
          case FunctionalTabuSearch.PRODUCT -> vs[v] = vs[in[0]] * vs[in[1]];
          case FunctionalTabuSearch.FUNCTION -> vs[v] = Math.max(vs[in[0]], vs[in[1]]);
          default -> {}
        }
        ok = m.domains.get(v).contains((int) vs[v]);
      }
      if (ok) {
        best = Math.min(best, vs[cost]);
      }
      int k = 0;
      while (k < at.length && ++at[k] == values[k].length) {
        at[k] = 0;
        k++;
      }
      if (k == at.length) {
        return best;
      }
    }
  }
}
