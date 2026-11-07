/*
 * AlldifferentRowsTest.java
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
import java.util.List;
import java.util.Random;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Linearizations;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.lcg.LinearForm;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.junit.jupiter.api.Test;

/**
 * Checks the LP rows of all-different constraints on random instances, against every solution found
 * by enumeration: the sorting-network formulation of the permutahedron ({@link
 * Linearizations#alldifferentNetwork}) is satisfied by every permutation and its LP optimum is the
 * best permutation, the Hall cuts of {@link AlldifferentCuts} never cut off a solution whatever LP
 * values they are separated from, and a relaxation with both keeps the optimum of random models.
 */
class AlldifferentRowsTest {

  private static final int INSTANCES = Integer.getInteger("alldiff.instances", 200);

  /** By the 0-1 principle, the comparators sort every input when they sort every 0-1 input. */
  @Test
  void comparatorsSortEveryZeroOneInput() {
    for (int n = 2; n <= 16; n++) {
      List<int[]> network = Linearizations.comparators(n);
      for (int bits = 0; bits < 1 << n; bits++) {
        int[] w = new int[n];
        for (int i = 0; i < n; i++) {
          w[i] = bits >> i & 1;
        }
        for (int[] c : network) {
          if (w[c[0]] > w[c[1]]) {
            int t = w[c[0]];
            w[c[0]] = w[c[1]];
            w[c[1]] = t;
          }
        }
        for (int i = 1; i < n; i++) {
          assertThat(w[i - 1])
              .as("n %d input %s", n, Integer.toBinaryString(bits))
              .isLessThanOrEqualTo(w[i]);
        }
      }
    }
  }

  /**
   * Every permutation of the values satisfies the network rows (the LP with the variables fixed to
   * it is feasible), and the LP minimum of a random cost over the rows is the best permutation
   * (Goemans: the projection is the permutahedron).
   */
  @Test
  void networkRowsAreThePermutahedron() {
    Random rnd = new Random(7);
    for (int run = 0; run < INSTANCES; run++) {
      int n = 3 + rnd.nextInt(4);
      int[] values = values(rnd, n);
      Store store = new Store();
      IntVar[] x = new IntVar[n];
      // the first variable takes every value, so the union of the domains is all of them
      IntDomain all = new IntervalDomain();
      for (int v : values) {
        all.unionAdapt(v, v);
      }
      x[0] = new IntVar(store, "x0", all);
      for (int i = 1; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, domain(rnd, values, values[rnd.nextInt(n)], true));
      }
      List<LinearForm> rows = Linearizations.alldifferentNetwork(x);
      assertThat(rows).as("run %d", run).isNotEmpty();
      Lp lp = new Lp(rows, x);
      long[] cost = new long[n];
      for (int i = 0; i < n; i++) {
        cost[i] = rnd.nextInt(21) - 10;
      }
      long best = Long.MAX_VALUE;
      for (int[] p : permutations(values)) {
        boolean inDomains = true;
        for (int i = 0; i < n; i++) {
          inDomains &= x[i].domain.contains(p[i]);
        }
        if (inDomains) {
          assertThat(lp.feasible(p)).as("run %d permutation %s", run, Arrays.toString(p)).isTrue();
        }
        long c = 0;
        for (int i = 0; i < n; i++) {
          c += cost[i] * p[i];
        }
        best = Math.min(best, c);
      }
      assertThat(lp.minimum(cost, values[0], values[n - 1]))
          .as("run %d", run)
          .isCloseTo((double) best, org.assertj.core.data.Offset.offset(1e-6));
    }
  }

  /** A list that is not a permutation of its values gets no network rows. */
  @Test
  void noNetworkWithoutAPermutation() {
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "a", 1, 4), new IntVar(store, "b", 1, 3), new IntVar(store, "c", 1, 3)
    };
    assertThat(Linearizations.alldifferentNetwork(x)).isEmpty();
  }

  /**
   * No Hall cut cuts off an all-different solution, for random domains with holes and random LP
   * values, and a point inside the hull of the solutions violates none; a point that breaks a pair
   * bound gets a cut.
   */
  @Test
  void hallCutsKeepEverySolution() {
    Random rnd = new Random(11);
    int found = 0;
    for (int run = 0; run < INSTANCES; run++) {
      int n = 3 + rnd.nextInt(4);
      Store store = new Store();
      IntVar[] x = new IntVar[n];
      int[] pool = values(rnd, n + rnd.nextInt(3));
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, domain(rnd, pool, pool[rnd.nextInt(pool.length)], false));
      }
      List<int[]> solutions = solutions(x);
      AlldifferentCuts cuts = new AlldifferentCuts(x);
      for (int t = 0; t < 20; t++) {
        double[] value = new double[n];
        for (int i = 0; i < n; i++) {
          value[i] = x[i].min() + rnd.nextDouble() * (x[i].max() - x[i].min());
        }
        for (AlldifferentCuts.Cut cut : cuts.separate(value, 100)) {
          found++;
          assertThat(activity(cut, value) < cut.bound() == cut.lower()).as("violated").isTrue();
          for (int[] s : solutions) {
            assertThat(holds(cut, s))
                .as("run %d cut %s solution %s", run, cut, Arrays.toString(s))
                .isTrue();
          }
        }
        if (!solutions.isEmpty()) {
          // a convex combination of solutions is in the hull
          double[] mix = new double[n];
          double total = 0;
          for (int[] s : solutions) {
            double w = rnd.nextDouble();
            total += w;
            for (int i = 0; i < n; i++) {
              mix[i] += w * s[i];
            }
          }
          for (int i = 0; i < n; i++) {
            mix[i] /= total;
          }
          assertThat(cuts.separate(mix, 100)).as("run %d", run).isEmpty();
        }
      }
    }
    assertThat(found).isPositive();
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < 3; i++) {
      x[i] = new IntVar(store, "y" + i, 1, 3);
    }
    List<AlldifferentCuts.Cut> cut =
        new AlldifferentCuts(x).separate(new double[] {1.2, 1.2, 3.6}, 10);
    assertThat(cut).isNotEmpty();
    assertThat(cut.get(0).lower()).isTrue();
    assertThat(cut.get(0).bound()).isEqualTo(3);
    assertThat(cut.get(0).vars()).containsExactly(0, 1);
  }

  /** The sums of the smallest and largest values of a domain with holes. */
  @Test
  void extremeSums() {
    IntDomain d = new IntervalDomain(1, 3);
    d.unionAdapt(10, 11);
    assertThat(AlldifferentCuts.extremeSum(d, 4, true)).isEqualTo(1 + 2 + 3 + 10);
    assertThat(AlldifferentCuts.extremeSum(d, 3, false)).isEqualTo(11 + 10 + 3);
    assertThat(AlldifferentCuts.extremeSum(d, 5, true)).isEqualTo(27);
  }

  /**
   * Random models with an all-different and a linear objective keep their optimum with the
   * relaxation, its network rows and its Hall cuts, under depth-first search; the root bound is not
   * above the optimum.
   */
  @Test
  void relaxationKeepsTheOptimum() {
    int moved = 0;
    for (int run = 0; run < INSTANCES / 4; run++) {
      boolean permutation = run % 2 == 0;
      long expected = new Model(run, permutation).optimum();
      Model m = new Model(run, permutation);
      LinearRelaxation r =
          LinearRelaxation.of(
              m.store,
              m.cost,
              false,
              List.of(),
              permutation ? Linearizations.alldifferentNetwork(m.x) : List.of(),
              java.util.Set.of(),
              LinearRelaxation.Simplex.DENSE);
      assertThat(r).as("run %d", run).isNotNull();
      m.store.impose(r);
      long got = m.optimum();
      assertThat(got).as("run %d", run).isEqualTo(expected);
      assertThat(r.rootBound).as("run %d", run).isLessThanOrEqualTo(expected + 1e-6);
      if (!Double.isNaN(r.alldiffBound)) {
        assertThat(r.alldiffBound).as("run %d", run).isLessThanOrEqualTo(expected + 1e-6);
      }
      moved += r.alldiffCuts > 0 || r.simplexFreeColumns() > 0 ? 1 : 0;
    }
    assertThat(moved).isPositive();
  }

  /**
   * A random model: an all-different over n variables (a permutation of n spread values, or domains
   * from a larger pool), with a linear cost {@code cost = sum c_i x_i} and, to tie the cost to the
   * constraint only through it, nothing else.
   */
  private static final class Model {
    final Store store = new Store();
    final IntVar[] x;
    final IntVar cost;

    Model(int seed, boolean permutation) {
      Random rnd = new Random(seed * 7919L + 5);
      int n = 4 + rnd.nextInt(4);
      int[] values = values(rnd, permutation ? n : n + 2);
      x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        IntDomain d = new IntervalDomain();
        for (int v : values) {
          if (permutation || rnd.nextInt(4) > 0) {
            d.unionAdapt(v, v);
          }
        }
        if (d.isEmpty()) {
          d.unionAdapt(values[0], values[0]);
        }
        x[i] = new IntVar(store, "x" + i, d);
      }
      long[] w = new long[n + 1];
      IntVar[] vars = Arrays.copyOf(x, n + 1);
      long range = 0;
      for (int i = 0; i < n; i++) {
        w[i] = rnd.nextInt(19) - 9;
        range +=
            Math.abs(w[i]) * Math.max(Math.abs(values[0]), Math.abs(values[values.length - 1]));
      }
      cost = new IntVar(store, "cost", (int) -range, (int) range);
      vars[n] = cost;
      w[n] = -1;
      int[] wi = new int[n + 1];
      for (int i = 0; i <= n; i++) {
        wi[i] = (int) w[i];
      }
      store.impose(new LinearInt(vars, wi, "==", 0));
      store.impose(new Alldistinct(x));
    }

    long optimum() {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      boolean found =
          search.labeling(store, new InputOrderSelect<>(store, x, new IndomainMin<>()), cost);
      return found ? search.getCostValue() : Long.MIN_VALUE;
    }
  }

  // the network rows over the variables and the free columns, as a dense LP
  private static final class Lp {
    final List<IntVar> columns = new ArrayList<>();
    final double[][] a;
    final double[] lo;
    final double[] hi;
    final int n;

    Lp(List<LinearForm> rows, IntVar[] x) {
      n = x.length;
      columns.addAll(Arrays.asList(x));
      for (LinearForm f : rows) {
        for (IntVar v : f.vars()) {
          if (!columns.contains(v)) {
            columns.add(v);
          }
        }
      }
      a = new double[rows.size()][columns.size()];
      lo = new double[rows.size()];
      hi = new double[rows.size()];
      for (int i = 0; i < rows.size(); i++) {
        LinearForm f = rows.get(i);
        for (int k = 0; k < f.vars().length; k++) {
          a[i][columns.indexOf(f.vars()[k])] += f.weights()[k];
        }
        lo[i] = f.relation() == LinearForm.LE ? Double.NEGATIVE_INFINITY : f.c();
        hi[i] = f.relation() == LinearForm.GE ? Double.POSITIVE_INFINITY : f.c();
      }
    }

    private DualSimplex simplex(double[] cost) {
      double[][] copy = new double[a.length][];
      for (int i = 0; i < a.length; i++) {
        copy[i] = a[i].clone();
      }
      DualSimplex s = new DualSimplex(copy, lo.clone(), hi.clone(), cost);
      for (int j = n; j < columns.size(); j++) {
        assertThat(columns.get(j)).isInstanceOf(LpColumn.class);
        assertThat(((LpColumn) columns.get(j)).isFree()).isTrue();
        s.setBounds(j, columns.get(j).min(), columns.get(j).max());
      }
      return s;
    }

    boolean feasible(int[] p) {
      DualSimplex s = simplex(new double[columns.size()]);
      for (int j = 0; j < n; j++) {
        s.setBounds(j, p[j], p[j]);
      }
      return s.solve(100_000) == LpSolver.OPTIMAL;
    }

    double minimum(long[] cost, int min, int max) {
      double[] c = new double[columns.size()];
      for (int j = 0; j < n; j++) {
        c[j] = cost[j];
      }
      DualSimplex s = simplex(c);
      for (int j = 0; j < n; j++) {
        s.setBounds(j, min, max);
      }
      assertThat(s.solve(100_000)).isEqualTo(LpSolver.OPTIMAL);
      double v = 0;
      for (int j = 0; j < n; j++) {
        v += cost[j] * s.value(j);
      }
      return v;
    }
  }

  // n distinct increasing values with random gaps, around 0
  private static int[] values(Random rnd, int n) {
    int[] v = new int[n];
    int at = -5 + rnd.nextInt(5);
    for (int i = 0; i < n; i++) {
      at += 1 + (rnd.nextInt(3) == 0 ? rnd.nextInt(4) : 0);
      v[i] = at;
    }
    return v;
  }

  // a random subset of the values that holds the given one
  private static IntDomain domain(Random rnd, int[] values, int holds, boolean dense) {
    IntDomain d = new IntervalDomain();
    for (int v : values) {
      if (v == holds || rnd.nextInt(dense ? 4 : 2) > 0) {
        d.unionAdapt(v, v);
      }
    }
    return d;
  }

  private static List<int[]> permutations(int[] values) {
    List<int[]> out = new ArrayList<>();
    permute(values.clone(), 0, out);
    return out;
  }

  private static void permute(int[] a, int k, List<int[]> out) {
    if (k == a.length) {
      out.add(a.clone());
      return;
    }
    for (int i = k; i < a.length; i++) {
      int t = a[k];
      a[k] = a[i];
      a[i] = t;
      permute(a, k + 1, out);
      a[i] = a[k];
      a[k] = t;
    }
  }

  // every all-different solution of the domains
  private static List<int[]> solutions(IntVar[] x) {
    List<int[]> out = new ArrayList<>();
    extend(x, new int[x.length], 0, out);
    return out;
  }

  private static void extend(IntVar[] x, int[] s, int k, List<int[]> out) {
    if (k == x.length) {
      out.add(s.clone());
      return;
    }
    for (var en = x[k].domain.valueEnumeration(); en.hasMoreElements(); ) {
      int v = en.nextElement();
      boolean used = false;
      for (int i = 0; i < k; i++) {
        used |= s[i] == v;
      }
      if (!used) {
        s[k] = v;
        extend(x, s, k + 1, out);
      }
    }
  }

  private static double activity(AlldifferentCuts.Cut cut, double[] value) {
    double sum = 0;
    for (int i : cut.vars()) {
      sum += value[i];
    }
    return sum;
  }

  private static boolean holds(AlldifferentCuts.Cut cut, int[] s) {
    long sum = 0;
    for (int i : cut.vars()) {
      sum += s[i];
    }
    return cut.lower() ? sum >= cut.bound() : sum <= cut.bound();
  }
}
