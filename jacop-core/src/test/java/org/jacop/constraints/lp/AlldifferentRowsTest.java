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
import org.jacop.constraints.AlldifferentExceptZero;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.GCC;
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
  /**
   * The cuts of a cardinality whose least counts no longer fit in a prefix (two copies of 1 and two
   * of 2 over three variables) skip that prefix instead of unboxing the missing bound: a seed of
   * {@link #variantCutsKeepEverySolution} threw a NullPointerException there.
   */
  @Test
  void cardinalityCutsSkipPrefixesWhereTheLeastCountsDoNotFit() {
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 2);
    }
    for (boolean closed : new boolean[] {true, false}) {
      AlldifferentCuts cuts =
          AlldifferentCuts.cardinality(
              x, new int[] {1, 2}, new int[] {2, 2}, new int[] {2, 2}, closed);
      assertThat(cuts.separate(new double[] {1.5, 1.5, 1.5}, 100)).isNotNull();
    }
  }

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

  /**
   * No Hall cut with value copies cuts off a solution: all-different with exceptions, closed and
   * open cardinality constraints with fixed or variable counts, random domains with holes and
   * random LP values (some variables left out); a convex mix of solutions violates none.
   */
  @Test
  void variantCutsKeepEverySolution() {
    Random rnd = new Random(23);
    int[] found = new int[4];
    for (int run = 0; run < INSTANCES * 2; run++) {
      int kind = run % 4;
      int n = 3 + rnd.nextInt(4);
      Store store = new Store();
      IntVar[] x = new IntVar[n];
      int[] pool = values(rnd, 2 + rnd.nextInt(n));
      for (int i = 0; i < n; i++) {
        IntDomain d = domain(rnd, pool, pool[rnd.nextInt(pool.length)], false);
        if (kind == 0 && rnd.nextBoolean()) {
          d.unionAdapt(0, 0);
        }
        x[i] = new IntVar(store, "x" + i, d);
      }
      int[] counted = kind == 3 ? subset(rnd, pool) : pool;
      int[] least = new int[counted.length];
      int[] most = new int[counted.length];
      IntVar[] counters = new IntVar[counted.length];
      for (int k = 0; k < counted.length; k++) {
        least[k] = rnd.nextInt(3) == 0 ? rnd.nextInt(2) : 0;
        most[k] = least[k] + rnd.nextInt(3);
        counters[k] = new IntVar(store, "c" + k, least[k], most[k]);
      }
      int[] exceptions = rnd.nextBoolean() ? new int[] {0} : new int[] {0, pool[0]};
      AlldifferentCuts cuts =
          switch (kind) {
            case 0 -> AlldifferentCuts.except(x, exceptions);
            case 1 -> AlldifferentCuts.cardinality(x, counted, least, most, true);
            case 2 -> AlldifferentCuts.cardinality(x, counted, counters, true);
            default -> AlldifferentCuts.cardinality(x, counted, least, most, false);
          };
      List<int[]> solutions = new ArrayList<>();
      for (int[] s : tuples(x)) {
        if (kind == 0
            ? exceptDistinct(s, exceptions)
            : counts(s, counted, least, most, kind != 3)) {
          solutions.add(s);
        }
      }
      for (int t = 0; t < 20; t++) {
        double[] value = new double[n];
        for (int i = 0; i < n; i++) {
          value[i] =
              rnd.nextInt(8) == 0
                  ? Double.NaN
                  : x[i].min() + rnd.nextDouble() * (x[i].max() - x[i].min());
        }
        for (AlldifferentCuts.Cut cut : cuts.separate(value, 100)) {
          found[kind]++;
          assertThat(activity(cut, value) < cut.bound() == cut.lower()).as("violated").isTrue();
          for (int i : cut.vars()) {
            assertThat(value[i]).isNotNaN();
          }
          for (int[] s : solutions) {
            assertThat(holds(cut, s))
                .as("run %d kind %d cut %s solution %s", run, kind, cut, Arrays.toString(s))
                .isTrue();
          }
        }
        if (!solutions.isEmpty()) {
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
          assertThat(cuts.separate(mix, 100)).as("run %d kind %d", run, kind).isEmpty();
        }
      }
    }
    assertThat(Arrays.stream(found).min().orElse(0)).as(Arrays.toString(found)).isPositive();
  }

  /** The bounds with value copies on small cases. */
  @Test
  void variantBounds() {
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < 3; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 3);
    }
    // all-different except 0: the three take at most 3 + 2 + 1
    List<AlldifferentCuts.Cut> cut =
        AlldifferentCuts.except(x, new int[] {0}).separate(new double[] {2.9, 2.9, 2.9}, 10);
    assertThat(cut).isNotEmpty();
    assertThat(cut.get(0).lower()).isFalse();
    assertThat(cut.get(0).bound()).isEqualTo(6);
    // but any number of them may be 0
    assertThat(AlldifferentCuts.except(x, new int[] {0}).separate(new double[] {0, 0, 0}, 10))
        .isEmpty();
    // four variables over {1, 2}, each value taken exactly twice: three of them sum to 5 at most
    // and to 4 at least
    IntVar[] y = new IntVar[4];
    for (int i = 0; i < 4; i++) {
      y[i] = new IntVar(store, "y" + i, 1, 2);
    }
    AlldifferentCuts gcc =
        AlldifferentCuts.cardinality(y, new int[] {2, 1}, new int[] {2, 2}, new int[] {2, 2}, true);
    List<AlldifferentCuts.Cut> low = gcc.separate(new double[] {1.2, 1.2, 1.2, 2}, 10);
    assertThat(low).isNotEmpty();
    assertThat(low.get(0).lower()).isTrue();
    assertThat(low.get(0).vars()).containsExactly(0, 1, 2);
    assertThat(low.get(0).bound()).isEqualTo(4);
    List<AlldifferentCuts.Cut> high = gcc.separate(new double[] {1, 1.8, 1.8, 1.8}, 10);
    assertThat(high).isNotEmpty();
    assertThat(high.get(0).lower()).isFalse();
    assertThat(high.get(0).bound()).isEqualTo(5);
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
      if (!Double.isNaN(r.alldiffBound) && expected != Long.MIN_VALUE) {
        // an infeasible model (Long.MIN_VALUE) has no optimum to bound
        assertThat(r.alldiffBound).as("run %d", run).isLessThanOrEqualTo(expected + 1e-6);
      }
      moved += r.alldiffCuts > 0 || r.simplexFreeColumns() > 0 ? 1 : 0;
    }
    assertThat(moved).isPositive();
  }

  /**
   * Random models with an all-different-except-0 or a global cardinality constraint and a linear
   * objective keep their optimum with the relaxation and the Hall cuts with value copies, at the
   * root and in search; the root bound is not above the optimum.
   */
  @Test
  void variantRelaxationKeepsTheOptimum() {
    int used = 0;
    int lists = 0;
    for (int run = 0; run < INSTANCES / 4; run++) {
      long expected = new VariantModel(run).optimum();
      VariantModel m = new VariantModel(run);
      LinearRelaxation r =
          LinearRelaxation.of(
              m.store,
              m.cost,
              false,
              List.of(),
              List.of(),
              java.util.Set.of(),
              LinearRelaxation.Simplex.DENSE);
      assertThat(r).as("run %d", run).isNotNull();
      r.setAlldiffSearch(true);
      m.store.impose(r);
      long got = m.optimum();
      assertThat(got).as("run %d", run).isEqualTo(expected);
      if (!Double.isNaN(r.alldiffBound) && expected != Long.MIN_VALUE) {
        // an infeasible model (Long.MIN_VALUE) has no optimum to bound
        assertThat(r.alldiffBound).as("run %d", run).isLessThanOrEqualTo(expected + 1e-6);
      }
      lists += (int) r.alldiffVariantLists;
      used += r.alldiffCuts + r.alldiffSearchCuts > 0 ? 1 : 0;
    }
    assertThat(lists).isPositive();
    assertThat(used).isPositive();
  }

  /**
   * The Hall cuts in search after the rows of the other constraints are dropped: a variable that is
   * a column only through those rows is no longer one, and the cuts leave it out (it was read past
   * the columns of the simplex).
   */
  @Test
  void searchCutsAfterTheExtraRowsAreDropped() throws ReflectiveOperationException {
    java.lang.reflect.Field before = LinearRelaxation.class.getDeclaredField("beforeExtra");
    before.setAccessible(true);
    java.lang.reflect.Method drop = LinearRelaxation.class.getDeclaredMethod("dropExtraRows");
    drop.setAccessible(true);
    int dropped = 0;
    long cuts = 0;
    for (int run = 0; run < INSTANCES / 4; run++) {
      long expected = new VariantModel(run, true).optimum();
      VariantModel m = new VariantModel(run, true);
      LinearRelaxation r =
          LinearRelaxation.of(
              m.store,
              m.cost,
              false,
              m.extra(),
              java.util.Set.of(),
              LinearRelaxation.Simplex.DENSE);
      assertThat(r).as("run %d", run).isNotNull();
      r.setAlldiffSearch(true);
      m.store.impose(r);
      if (!m.store.consistency()) {
        continue;
      }
      if (before.get(r) != null) {
        drop.invoke(r);
        dropped++;
      }
      long got = m.optimum();
      assertThat(got).as("run %d", run).isEqualTo(expected);
      cuts += r.alldiffSearchCuts;
    }
    assertThat(dropped).isPositive();
    assertThat(cuts).isPositive();
  }

  /**
   * A random model: an all-different-except-0 (even seeds) or a global cardinality constraint with
   * variable counts (odd seeds) over n variables, with a linear cost.
   */
  static final class VariantModel {
    final Store store = new Store();
    final IntVar[] x;
    final IntVar cost;

    VariantModel(int seed) {
      this(seed, false);
    }

    // with split, the last variable is left out of the cost and of the knapsack: it is a column
    // only through the row of extra()
    VariantModel(int seed, boolean split) {
      Random rnd = new Random(seed * 6151L + 3);
      boolean except = seed % 2 == 0;
      int n = 4;
      x = new IntVar[n];
      int first = except ? 0 : 1 + rnd.nextInt(3);
      // more values than the LP encodes value by value (128), so the LP sees only the cuts
      int m = 160;
      for (int i = 0; i < n; i++) {
        IntDomain d = new IntervalDomain();
        for (int v = first; v < first + m; v++) {
          if (rnd.nextInt(8) > 0 || v == 0) {
            d.unionAdapt(v, v);
          }
        }
        if (d.isEmpty()) {
          d.unionAdapt(first, first);
        }
        x[i] = new IntVar(store, "x" + i, d);
      }
      long[] w = new long[n + 1];
      IntVar[] vars = Arrays.copyOf(x, n + 1);
      long range = 0;
      int shared = split ? n - 1 : n;
      for (int i = 0; i < shared; i++) {
        // all-different-except-0: every variable wants a large value
        w[i] = except ? -1 - rnd.nextInt(9) : rnd.nextInt(19) - 9;
        range += Math.abs(w[i]) * (first + m);
      }
      cost = new IntVar(store, "cost", (int) -range, (int) range);
      vars[n] = cost;
      w[n] = -1;
      int[] wi = new int[n + 1];
      for (int i = 0; i <= n; i++) {
        wi[i] = (int) w[i];
      }
      store.impose(new LinearInt(vars, wi, "==", 0));
      // a second row, as the relaxation needs two: a knapsack over the variables
      int[] a = new int[shared];
      long most = 0;
      for (int i = 0; i < shared; i++) {
        a[i] = 1 + rnd.nextInt(3);
        most += (long) a[i] * (first + m - 1);
      }
      store.impose(
          new LinearInt(
              Arrays.copyOf(x, shared), a, "<=", (int) (most * (6 + rnd.nextInt(4)) / 10)));
      if (except) {
        store.impose(new AlldifferentExceptZero(x));
      } else {
        IntVar[] counters = new IntVar[m];
        for (int k = 0; k < m; k++) {
          // mostly at most one copy, some values two or three, a few needed once
          int lo = rnd.nextInt(80) == 0 ? 1 : 0;
          counters[k] = new IntVar(store, "c" + k, lo, lo + 1 + (rnd.nextInt(8) == 0 ? 2 : 0));
        }
        store.impose(new GCC(x, counters, first));
      }
    }

    // a row over the first and the last variable, which holds in their domains
    List<LinearForm> extra() {
      IntVar last = x[x.length - 1];
      return List.of(
          new LinearForm(
              new IntVar[] {x[0], last},
              new long[] {1, 1},
              (long) x[0].max() + last.max(),
              LinearForm.LE));
    }

    long optimum() {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      boolean found =
          search.labeling(store, new InputOrderSelect<>(store, x, new IndomainMin<>()), cost);
      return found ? search.getCostValue() : Long.MIN_VALUE;
    }
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

  // a nonempty random subset of the values
  private static int[] subset(Random rnd, int[] values) {
    List<Integer> out = new ArrayList<>();
    for (int v : values) {
      if (rnd.nextBoolean()) {
        out.add(v);
      }
    }
    if (out.isEmpty()) {
      out.add(values[0]);
    }
    return out.stream().mapToInt(Integer::intValue).toArray();
  }

  // every tuple of the domains
  private static List<int[]> tuples(IntVar[] x) {
    List<int[]> out = new ArrayList<>();
    out.add(new int[0]);
    for (IntVar v : x) {
      List<int[]> next = new ArrayList<>();
      for (int[] s : out) {
        for (var en = v.domain.valueEnumeration(); en.hasMoreElements(); ) {
          int[] t = Arrays.copyOf(s, s.length + 1);
          t[s.length] = en.nextElement();
          next.add(t);
        }
      }
      out = next;
    }
    return out;
  }

  // the values that are not exceptions are pairwise distinct
  private static boolean exceptDistinct(int[] s, int[] exceptions) {
    for (int i = 0; i < s.length; i++) {
      for (int j = i + 1; j < s.length; j++) {
        int v = s[i];
        if (v == s[j] && Arrays.stream(exceptions).noneMatch(e -> e == v)) {
          return false;
        }
      }
    }
    return true;
  }

  // each counted value is taken within its bounds, and only counted values when closed
  private static boolean counts(int[] s, int[] values, int[] least, int[] most, boolean closed) {
    for (int k = 0; k < values.length; k++) {
      int v = values[k];
      long c = Arrays.stream(s).filter(e -> e == v).count();
      if (c < least[k] || c > most[k]) {
        return false;
      }
    }
    return !closed || Arrays.stream(s).allMatch(e -> Arrays.stream(values).anyMatch(v -> v == e));
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
