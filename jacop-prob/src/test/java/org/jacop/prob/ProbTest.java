/*
 * ProbTest.java
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

package org.jacop.prob;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import org.jacop.api.VarMap;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.jasat.lcg.LcgSolver;
import org.jacop.lcg.LinearForm;
import org.jacop.prob.constraints.ExpectedSum;
import org.jacop.prob.constraints.ScenarioChance;
import org.jacop.prob.dist.Dist;
import org.jacop.prob.num.ProbArith;
import org.jacop.prob.scenario.ScenarioSet;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Tests of the probabilistic module: exact arithmetic, distributions, scenario sets, and the chance
 * and expectation constraints against brute force and against their usual expansion, with and
 * without lazy clause generation. {@code prob.trials} sets the number of random instances of each
 * randomised test (300 in the min profile).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class ProbTest {

  private static final int TRIALS = Integer.getInteger("prob.trials", 2000);

  // ---- exact arithmetic

  @Test
  void testNumeratorRoundsOutward() {
    // 0.1 is slightly above 1/10 as a double, so it rounds up past 1 over 10 only when asked
    assertThat(ProbArith.numerator(0.1, 10, false)).isEqualTo(1);
    assertThat(ProbArith.numerator(0.1, 10, true)).isEqualTo(2);
    assertThat(ProbArith.numerator(0.5, 10, false)).isEqualTo(5);
    assertThat(ProbArith.numerator(0.5, 10, true)).isEqualTo(5);
    assertThat(ProbArith.numerator(1.0, 7, true)).isEqualTo(7);
    assertThat(ProbArith.numerator(0.0, 7, true)).isZero();
    assertThatThrownBy(() -> ProbArith.numerator(1.5, 7, true))
        .isInstanceOf(IllegalArgumentException.class);
    Random random = new Random(1);
    for (int t = 0; t < 1000; t++) {
      double p = random.nextDouble();
      long den = 1L + random.nextInt(1_000_000);
      long lo = ProbArith.numerator(p, den, false);
      long hi = ProbArith.numerator(p, den, true);
      assertThat(hi - lo).isBetween(0L, 1L);
      assertThat((double) lo / den).isLessThanOrEqualTo(p);
      assertThat((double) hi / den).isGreaterThanOrEqualTo(p);
    }
  }

  @Test
  void testCompareRescaleMultiply() {
    assertThat(ProbArith.compare(1, 3, 2, 6)).isZero();
    assertThat(ProbArith.compare(1, 3, 333, 1000)).isPositive();
    assertThat(ProbArith.compare(Long.MAX_VALUE - 1, Long.MAX_VALUE, 1, 1)).isNegative();
    assertThat(ProbArith.rescale(1, 3, 10, false)).isEqualTo(3);
    assertThat(ProbArith.rescale(1, 3, 10, true)).isEqualTo(4);
    assertThat(ProbArith.rescale(-1, 3, 10, false)).isEqualTo(-4);
    assertThat(ProbArith.rescale(-1, 3, 10, true)).isEqualTo(-3);
    assertThat(ProbArith.rescale(5, 10, 2, true)).isEqualTo(1);
    // (1/3) * (1/3) = 1/9 = 11.1.../100
    assertThat(ProbArith.multiply(1, 1, 3, false)).isZero();
    assertThat(ProbArith.multiply(1, 1, 3, true)).isEqualTo(1);
    assertThat(ProbArith.multiply(50, 50, 100, true)).isEqualTo(25);
    assertThat(ProbArith.gcd(-12, 18)).isEqualTo(6);
    assertThatThrownBy(() -> ProbArith.sum(Long.MAX_VALUE, 1))
        .isInstanceOf(ArithmeticException.class);
    assertThatThrownBy(() -> ProbArith.checkProbabilities(new long[] {2, 2}, 3, false))
        .isInstanceOf(IllegalArgumentException.class);
    ProbArith.checkProbabilities(new long[] {1, 2}, 3, true);
  }

  @Test
  void testExactValueOfDoubles() {
    assertThat(ProbArith.exactValue(0.1))
        .isEqualByComparingTo("0.1000000000000000055511151231257827021181583404541015625");
    assertThat(ProbArith.exactValue(-3.75)).isEqualByComparingTo("-3.75");
    assertThat(ProbArith.exactValue(0.0)).isEqualByComparingTo("0");
    Random random = new Random(3);
    for (int t = 0; t < 1000; t++) {
      double d = Double.longBitsToDouble(random.nextLong());
      if (Double.isFinite(d)) {
        java.math.BigDecimal v = ProbArith.exactValue(d);
        assertThat(v.doubleValue()).as("" + d).isEqualTo(d);
        assertThat(v.compareTo(ProbArith.exactValue(Math.nextUp(d)))).isLessThanOrEqualTo(0);
        assertThat(v.compareTo(ProbArith.exactValue(Math.nextDown(d)))).isGreaterThanOrEqualTo(0);
      }
    }
    assertThatThrownBy(() -> ProbArith.exactValue(Double.NaN))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testEnclosure() {
    Random random = new Random(2);
    for (int t = 0; t < 1000; t++) {
      long den = 1L + random.nextInt(Integer.MAX_VALUE);
      long num = random.nextLong(den + 1);
      double[] e = ProbArith.enclosure(num, den);
      assertThat(e[0]).isLessThanOrEqualTo(e[1]);
      assertThat(ProbArith.exactValue(e[0]).multiply(java.math.BigDecimal.valueOf(den)))
          .isLessThanOrEqualTo(java.math.BigDecimal.valueOf(num));
      assertThat(ProbArith.exactValue(e[1]).multiply(java.math.BigDecimal.valueOf(den)))
          .isGreaterThanOrEqualTo(java.math.BigDecimal.valueOf(num));
    }
  }

  // ---- distributions and scenarios

  @Test
  void testDist() {
    Dist d = new Dist(new int[] {3, 1, 3, 2}, new long[] {1, 2, 3, 0}, 6);
    assertThat(d.size()).isEqualTo(2);
    assertThat(d.min()).isEqualTo(1);
    assertThat(d.max()).isEqualTo(3);
    assertThat(d.weight(1)).isEqualTo(4);
    assertThat(d.meanNumerator()).isEqualTo(14L);
    assertThat(d.cdfNumerator(2)).isEqualTo(2);
    assertThat(d.cdfNumerator(0)).isZero();
    assertThat(d.withDenominator(12)).isEqualTo(d);
    Dist coin = Dist.bernoulli(1, 2);
    Dist two = coin.plus(coin);
    assertThat(two).isEqualTo(new Dist(new int[] {0, 1, 2}, new long[] {1, 2, 1}, 4));
    assertThat(Dist.uniform(1, 2, 3).meanNumerator()).isEqualTo(6);
    assertThat(Dist.point(5).meanNumerator()).isEqualTo(5);
    assertThatThrownBy(() -> new Dist(new int[] {1}, new long[] {2}, 3))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testScenarioSet() {
    ScenarioSet s = ScenarioSet.independent(Dist.bernoulli(1, 4), Dist.uniform(5, 6));
    assertThat(s.size()).isEqualTo(4);
    assertThat(s.den()).isEqualTo(8);
    assertThat(Arrays.stream(s.weights()).sum()).isEqualTo(8);
    assertThat(s.marginal(0)).isEqualTo(Dist.bernoulli(1, 4));
    assertThat(s.marginal(1)).isEqualTo(Dist.uniform(5, 6));
    ScenarioSet merged =
        new ScenarioSet(new int[][] {{1, 2}, {1, 2}, {3, 4}}, new long[] {1, 1, 2}, 4);
    assertThat(merged.size()).isEqualTo(2);
    assertThat(merged.weight(0)).isEqualTo(2);
  }

  // ---- ScenarioChance

  @Test
  void testScenarioChancePrunes() {
    // two of x0 + x1 <= 4, x0 <= 1, x1 <= 1 must hold
    Store store = new Store();
    IntVar x0 = new IntVar(store, "x0", 0, 5);
    IntVar x1 = new IntVar(store, "x1", 0, 5);
    store.impose(
        new ScenarioChance(
            new IntVar[] {x0, x1},
            new int[][] {{1, 1}, {1, 0}, {0, 1}},
            new int[] {4, 1, 1},
            new long[] {1, 1, 1},
            2));
    assertThat(store.consistency()).isTrue();
    assertThat(x0.max()).isEqualTo(4);
    assertThat(x1.max()).isEqualTo(4);
    store.setLevel(1);
    x0.domain.inMin(1, x0, 3);
    // x0 <= 1 is lost, so x0 + x1 <= 4 and x1 <= 1 must both hold
    assertThat(store.consistency()).isTrue();
    assertThat(x1.max()).isEqualTo(1);
    assertThat(x0.max()).isEqualTo(4);
    store.removeLevel(1);
    store.setLevel(0);
    assertThat(x1.max()).isEqualTo(4);
  }

  @Test
  void testScenarioChanceFailsAndEntails() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    ScenarioChance c =
        new ScenarioChance(
            new IntVar[] {x}, new int[][] {{1}, {-1}}, new int[] {-1, -5}, new long[] {1, 1}, 1);
    store.impose(c);
    assertThat(store.consistency()).isFalse();

    store = new Store();
    x = new IntVar(store, "x", 0, 3);
    c = new ScenarioChance(new IntVar[] {x}, new int[][] {{1}}, new int[] {3}, new long[] {1}, 1);
    store.impose(c);
    assertThat(c.satisfied()).isTrue();
    assertThat(store.consistency()).isTrue();
  }

  @Test
  void testScenarioChanceRejectsBadInput() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar[] xs = {x};
    assertThatThrownBy(
            () -> new ScenarioChance(xs, new int[][] {{1}}, new int[] {3}, new long[] {-1}, 1))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () -> new ScenarioChance(xs, new int[][] {{1, 2}}, new int[] {3}, new long[] {1}, 1))
        .isInstanceOf(IllegalArgumentException.class);
    IntVar big = new IntVar(store, "big", -2_000_000_000, 2_000_000_000);
    assertThatThrownBy(
            () ->
                new ScenarioChance(
                    new IntVar[] {big, big, big},
                    new int[][] {{2_000_000_000, 2_000_000_000, 2_000_000_000}},
                    new int[] {0},
                    new long[] {1},
                    1))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testScenarioSetLinear() {
    // scenarios (a0, a1, b): x0 + x1 <= 2 with 1/2, 2 x0 <= 2 with 1/4, x1 <= 0 with 1/4
    ScenarioSet set =
        new ScenarioSet(new int[][] {{1, 1, 2}, {2, 0, 2}, {0, 1, 0}}, new long[] {2, 1, 1}, 4);
    Store store = new Store();
    IntVar[] x = {new IntVar(store, "x0", 0, 2), new IntVar(store, "x1", 0, 2)};
    int expected = bruteCount(set, x, 3);
    store.impose(ScenarioChance.linear(x, set, 3));
    assertThat(countSolutions(store, x)).isEqualTo(expected).isEqualTo(6);
  }

  // a random instance over small domains with holes, sometimes with a variable twice
  private static final class Instance {
    final int n;
    final int[] lo;
    final int[] hi;
    final int[][] holes;
    final int[] var;
    final int[][] a;
    final int[] b;
    final long[] w;
    final long alpha;
    final int[] objective;

    Instance(long seed) {
      Random r = new Random(seed);
      n = 1 + r.nextInt(4);
      lo = new int[n];
      hi = new int[n];
      holes = new int[n][];
      for (int i = 0; i < n; i++) {
        lo[i] = -3 + r.nextInt(4);
        hi[i] = lo[i] + 1 + r.nextInt(5);
        holes[i] =
            r.nextInt(3) == 0 ? new int[] {lo[i] + 1 + r.nextInt(hi[i] - lo[i])} : new int[0];
      }
      int columns = n + (r.nextInt(4) == 0 ? 1 : 0);
      var = new int[columns];
      for (int k = 0; k < columns; k++) {
        var[k] = k < n ? k : r.nextInt(n);
      }
      int scenarios = 1 + r.nextInt(7);
      a = new int[scenarios][columns];
      b = new int[scenarios];
      w = new long[scenarios];
      long total = 0;
      for (int s = 0; s < scenarios; s++) {
        for (int k = 0; k < columns; k++) {
          a[s][k] = r.nextInt(3) == 0 ? 0 : -3 + r.nextInt(7);
        }
        b[s] = -4 + r.nextInt(11);
        w[s] = r.nextInt(6);
        total += w[s];
      }
      alpha = total == 0 ? r.nextInt(2) : 1 + r.nextLong(total + 1);
      objective = new int[n];
      for (int i = 0; i < n; i++) {
        objective[i] = -3 + r.nextInt(7);
      }
    }

    IntVar[] vars(Store store) {
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, lo[i], hi[i]);
        for (int h : holes[i]) {
          if (x[i].getSize() > 1) {
            x[i].domain.inComplement(0, x[i], h);
          }
        }
      }
      return x;
    }

    IntVar[] columns(IntVar[] x) {
      IntVar[] c = new IntVar[var.length];
      for (int k = 0; k < var.length; k++) {
        c[k] = x[var[k]];
      }
      return c;
    }

    boolean holds(int[] value) {
      long weight = 0;
      for (int s = 0; s < a.length; s++) {
        long act = 0;
        for (int k = 0; k < var.length; k++) {
          act += (long) a[s][k] * value[var[k]];
        }
        if (act <= b[s]) {
          weight += w[s];
        }
      }
      return weight >= alpha;
    }

    // the usual expansion: a Boolean for each scenario and a weighted sum of them
    void expand(Store store, IntVar[] x) {
      IntVar[] c = columns(x);
      BooleanVar[] ok = new BooleanVar[a.length];
      int[] weights = new int[a.length];
      for (int s = 0; s < a.length; s++) {
        ok[s] = new BooleanVar(store, "ok" + s);
        store.impose(new Reified(new LinearInt(c, a[s], "<=", b[s]), ok[s]));
        weights[s] = (int) w[s];
      }
      store.impose(new LinearInt(ok, weights, ">=", (int) alpha));
    }

    // the native constraint, with indicators for half of the trials
    ScenarioChance post(Store store, IntVar[] x, boolean indicators) {
      IntVar[] ok = null;
      if (indicators) {
        ok = new IntVar[a.length];
        for (int s = 0; s < a.length; s++) {
          ok[s] = new BooleanVar(store, "ok" + s);
        }
      }
      ScenarioChance c = new ScenarioChance(columns(x), a, b, w, alpha, ok);
      store.impose(c);
      return c;
    }

    String describe() {
      return "n="
          + n
          + " lo="
          + Arrays.toString(lo)
          + " hi="
          + Arrays.toString(hi)
          + " holes="
          + Arrays.deepToString(holes)
          + " var="
          + Arrays.toString(var)
          + " a="
          + Arrays.deepToString(a)
          + " b="
          + Arrays.toString(b)
          + " w="
          + Arrays.toString(w)
          + " alpha="
          + alpha;
    }
  }

  private static List<int[]> tuples(IntVar[] x) {
    List<int[]> result = new ArrayList<>();
    result.add(new int[0]);
    for (IntVar v : x) {
      List<int[]> next = new ArrayList<>();
      for (int[] t : result) {
        for (int value = v.min(); value <= v.max(); value++) {
          if (v.domain.contains(value)) {
            int[] u = Arrays.copyOf(t, t.length + 1);
            u[t.length] = value;
            next.add(u);
          }
        }
      }
      result = next;
    }
    return result;
  }

  private static int countSolutions(Store store, IntVar[] x) {
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.setPrintInfo(false);
    if (!search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()))) {
      return 0;
    }
    return search.getSolutionListener().solutionsNo();
  }

  private static int bruteCount(ScenarioSet set, IntVar[] x, long alpha) {
    int count = 0;
    for (int[] t : tuples(x)) {
      long weight = 0;
      for (int s = 0; s < set.size(); s++) {
        long act = 0;
        for (int i = 0; i < x.length; i++) {
          act += (long) set.value(s, i) * t[i];
        }
        if (act <= set.value(s, x.length)) {
          weight += set.weight(s);
        }
      }
      if (weight >= alpha) {
        count++;
      }
    }
    return count;
  }

  @Test
  void testScenarioChanceAgainstBruteForce() {
    for (int t = 0; t < TRIALS; t++) {
      Instance in = new Instance(t);
      Store store = new Store();
      IntVar[] x = in.vars(store);
      int expected = 0;
      for (int[] tuple : tuples(x)) {
        if (in.holds(tuple)) {
          expected++;
        }
      }
      boolean indicators = t % 2 == 1;
      ScenarioChance c = in.post(store, x, indicators);
      String where = in.describe() + " indicators=" + indicators;
      assertThat(countSolutions(store, x)).as(where).isEqualTo(expected);

      // the copy prunes the same way
      Store other = new Store();
      IntVar[] y = in.vars(other);
      Map<Var, Var> copies = new IdentityHashMap<>();
      for (int i = 0; i < x.length; i++) {
        copies.put(x[i], y[i]);
      }
      other.impose(
          c.copy(
              new VarMap() {
                @Override
                public Store target() {
                  return other;
                }

                @Override
                @SuppressWarnings("unchecked")
                public <V extends Var> V get(V v) {
                  return (V) copies.computeIfAbsent(v, k -> new BooleanVar(other, k.id()));
                }
              }));
      assertThat(countSolutions(other, y)).as(where).isEqualTo(expected);
    }
  }

  @Test
  void testScenarioChanceIsNotWeakerThanExpansion() {
    // at the root, the native constraint removes at least the bounds the expansion removes
    for (int t = 0; t < TRIALS; t++) {
      Instance in = new Instance(1_000_000L + t);
      Store natural = new Store();
      IntVar[] x = in.vars(natural);
      in.post(natural, x, t % 2 == 1);
      boolean nativeOk = natural.consistency();
      Store expanded = new Store();
      IntVar[] y = in.vars(expanded);
      in.expand(expanded, y);
      boolean expandedOk = expanded.consistency();
      if (!expandedOk) {
        assertThat(nativeOk).as(in.describe()).isFalse();
        continue;
      }
      if (nativeOk) {
        for (int i = 0; i < x.length; i++) {
          assertThat(x[i].min()).as(in.describe()).isGreaterThanOrEqualTo(y[i].min());
          assertThat(x[i].max()).as(in.describe()).isLessThanOrEqualTo(y[i].max());
        }
      }
    }
  }

  @Test
  void testScenarioChanceWithLcg() {
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int t = 0; t < TRIALS; t++) {
      Instance in = new Instance(2_000_000L + t);
      Integer expected = null;
      {
        Store store = new Store();
        IntVar[] x = in.vars(store);
        for (int[] tuple : tuples(x)) {
          if (in.holds(tuple)) {
            int obj = 0;
            for (int i = 0; i < in.n; i++) {
              obj += in.objective[i] * tuple[i];
            }
            expected = expected == null ? obj : Math.min(expected, obj);
          }
        }
      }
      Store store = new Store();
      IntVar[] x = in.vars(store);
      in.post(store, x, t % 2 == 1);
      IntVar objective = new IntVar(store, "obj", -100, 100);
      store.impose(new LinearInt(x, in.objective, "==", objective));
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.minimize(objective);
      assertThat(status).as(in.describe()).isNotEqualTo(CdclSolver.UNKNOWN);
      assertThat(status == CdclSolver.SAT).as(in.describe()).isEqualTo(expected != null);
      if (status == CdclSolver.SAT) {
        int[] values = new int[in.n];
        for (int i = 0; i < in.n; i++) {
          values[i] = solver.value(x[i]);
        }
        assertThat(in.holds(values)).as(in.describe()).isTrue();
        assertThat(solver.value(objective)).as(in.describe()).isEqualTo(expected);
        sat++;
      } else {
        unsat++;
      }
      long[] counts = solver.explanationStatistics().get("ScenarioChance");
      if (counts != null) {
        own += counts[0] - counts[1] + counts[3] - counts[4];
        generic += counts[1] + counts[4];
      }
    }
    assertThat(sat).isPositive();
    assertThat(unsat).isPositive();
    // the constraint explains most of its own pruning
    assertThat(own).isGreaterThan(generic);
  }

  @Test
  void testRelaxationRowsHoldForEverySolution() {
    // every solution, with its indicators, satisfies the big-M rows and the weighted sum
    for (int t = 0; t < TRIALS; t++) {
      Instance in = new Instance(3_000_000L + t);
      Store store = new Store();
      IntVar[] x = in.vars(store);
      ScenarioChance c = in.post(store, x, true);
      List<LinearForm> rows = c.relaxation();
      assertThat(rows).isNotEmpty();
      for (int[] tuple : tuples(x)) {
        if (!in.holds(tuple)) {
          continue;
        }
        Map<Var, Long> value = new IdentityHashMap<>();
        for (int i = 0; i < x.length; i++) {
          value.put(x[i], (long) tuple[i]);
        }
        for (int s = 0; s < in.a.length; s++) {
          long act = 0;
          for (int k = 0; k < in.var.length; k++) {
            act += (long) in.a[s][k] * tuple[in.var[k]];
          }
          value.put(store.findVariable("ok" + s), act <= in.b[s] ? 1L : 0L);
        }
        for (LinearForm f : rows) {
          long lhs = 0;
          for (int k = 0; k < f.vars().length; k++) {
            lhs += f.weights()[k] * value.get(f.vars()[k]);
          }
          boolean holds =
              switch (f.relation()) {
                case LinearForm.LE -> lhs <= f.c();
                case LinearForm.GE -> lhs >= f.c();
                default -> lhs == f.c();
              };
          assertThat(holds).as(in.describe() + " row " + f).isTrue();
        }
      }
    }
  }

  // ---- ExpectedSum

  @Test
  void testExpectedSum() {
    Store store = new Store();
    IntVar[] x = {new IntVar(store, "x0", 0, 3), new IntVar(store, "x1", 0, 3)};
    // W0 uniform on {1, 3} and W1 Bernoulli(1/2), over 2: means 2 and 1/2
    Dist[] weights = {Dist.uniform(1, 3), Dist.bernoulli(1, 2)};
    IntVar z = new IntVar(store, "z", -100, 100);
    ExpectedSum.of(x, weights, z).imposeDecomposition(store);
    assertThat(store.consistency()).isTrue();
    // z = 2 * (2 x0 + x1 / 2) = 4 x0 + x1
    assertThat(z.min()).isZero();
    assertThat(z.max()).isEqualTo(15);
    store.setLevel(1);
    x[0].domain.in(1, x[0], 2, 2);
    x[1].domain.in(1, x[1], 1, 1);
    assertThat(store.consistency()).isTrue();
    assertThat(z.value()).isEqualTo(9);
    assertThatThrownBy(
            () -> ExpectedSum.of(x, new Dist[] {Dist.uniform(1, 3), Dist.uniform(1, 2, 3)}, z))
        .isInstanceOf(IllegalArgumentException.class);
  }
}
