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

import java.math.BigInteger;
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
import org.jacop.prob.constraints.ChanceSum;
import org.jacop.prob.constraints.ChanceTable;
import org.jacop.prob.constraints.ExpectedSum;
import org.jacop.prob.constraints.ProbMdd;
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
    final int[] aVar;
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
      aVar = new int[columns];
      for (int k = 0; k < columns; k++) {
        aVar[k] = k < n ? k : r.nextInt(n);
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
      IntVar[] c = new IntVar[aVar.length];
      for (int k = 0; k < aVar.length; k++) {
        c[k] = x[aVar[k]];
      }
      return c;
    }

    boolean holds(int[] value) {
      long weight = 0;
      for (int s = 0; s < a.length; s++) {
        long act = 0;
        for (int k = 0; k < aVar.length; k++) {
          act += (long) a[s][k] * value[aVar[k]];
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
          + Arrays.toString(aVar)
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
          for (int k = 0; k < in.aVar.length; k++) {
            act += (long) in.a[s][k] * tuple[in.aVar[k]];
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

  // ---- ChanceSum

  /** A random chance-sum instance: small domains with holes, small supports, exact brute force. */
  private static final class SumInstance {
    final int n;
    final int[][] domains;
    final int[] capDomain;
    final Dist[] w;
    final int[] repeat;
    final long alphaNum;
    final long alphaDen;
    final int[] value;
    final long seed;

    SumInstance(long seed) {
      this.seed = seed;
      Random random = new Random(seed);
      n = 1 + random.nextInt(5);
      domains = new int[n][];
      w = new Dist[n];
      repeat = new int[n];
      value = new int[n];
      boolean binary = random.nextBoolean();
      for (int i = 0; i < n; i++) {
        domains[i] = binary ? new int[] {0, 1} : values(random, 0, 3);
        int size = 1 + random.nextInt(3);
        int[] v = new int[size];
        long[] p = new long[size];
        long den = 1L + random.nextInt(12);
        long left = den;
        for (int k = 0; k < size; k++) {
          v[k] = random.nextInt(7);
          p[k] = k == size - 1 ? left : random.nextInt((int) left + 1);
          left -= p[k];
        }
        w[i] = new Dist(v, p, den);
        // a few items share the variable of an earlier one
        repeat[i] = i > 0 && random.nextInt(6) == 0 ? random.nextInt(i) : -1;
        value[i] = 1 + random.nextInt(9);
      }
      capDomain = values(random, random.nextInt(3) == 0 ? -2 : 0, 14);
      alphaDen = 1L + random.nextInt(20);
      alphaNum = random.nextInt((int) alphaDen + 2);
    }

    private static int[] values(Random random, int lo, int hi) {
      List<Integer> v = new ArrayList<>();
      for (int a = lo; a <= hi; a++) {
        if (a == lo || random.nextInt(4) != 0) {
          v.add(a);
        }
      }
      return v.stream().mapToInt(Integer::intValue).toArray();
    }

    IntVar[] vars(Store store) {
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        if (repeat[i] >= 0) {
          x[i] = x[repeat[i]];
          continue;
        }
        x[i] = new IntVar(store, "x" + i);
        for (int a : domains[i]) {
          x[i].addDom(a, a);
        }
      }
      return x;
    }

    IntVar cap(Store store) {
      IntVar c = new IntVar(store, "c");
      for (int a : capDomain) {
        c.addDom(a, a);
      }
      return c;
    }

    ChanceSum constraint(IntVar[] x, IntVar c) {
      return new ChanceSum(x, w, c, alphaNum, alphaDen);
    }

    // exact Pr(sum w[i] * x[i] <= cap) >= alpha by enumerating the joint supports
    boolean holds(int[] xv, int cap) {
      long num = 0;
      long den = 1;
      for (Dist d : w) {
        den *= d.den();
      }
      int[] k = new int[n];
      while (true) {
        long load = 0;
        long p = 1;
        for (int i = 0; i < n; i++) {
          load += (long) w[i].value(k[i]) * xv[i];
          p *= w[i].weight(k[i]);
        }
        if (load <= cap) {
          num += p;
        }
        int i = 0;
        while (i < n && ++k[i] == w[i].size()) {
          k[i++] = 0;
        }
        if (i == n) {
          break;
        }
      }
      // num / den >= alphaNum / alphaDen
      return java.math.BigInteger.valueOf(num)
              .multiply(java.math.BigInteger.valueOf(alphaDen))
              .compareTo(
                  java.math.BigInteger.valueOf(alphaNum)
                      .multiply(java.math.BigInteger.valueOf(den)))
          >= 0;
    }

    // the values of the distinct variables spread over the items
    int[] itemValues(IntVar[] x, int[] distinctValues, IntVar[] distinct) {
      int[] result = new int[n];
      for (int i = 0; i < n; i++) {
        result[i] = distinctValues[Arrays.asList(distinct).indexOf(x[i])];
      }
      return result;
    }

    String describe() {
      return "seed "
          + seed
          + ": w "
          + Arrays.toString(w)
          + " x "
          + Arrays.deepToString(domains)
          + " repeat "
          + Arrays.toString(repeat)
          + " c "
          + Arrays.toString(capDomain)
          + " alpha "
          + alphaNum
          + "/"
          + alphaDen;
    }
  }

  private static IntVar[] distinct(IntVar[] x) {
    return Arrays.stream(x).distinct().toArray(IntVar[]::new);
  }

  @Test
  void testChanceSumAgainstBruteForce() {
    int sat = 0;
    for (int t = 0; t < TRIALS; t++) {
      SumInstance in = new SumInstance(4_000_000L + t);
      Store store = new Store();
      IntVar[] x = in.vars(store);
      IntVar c = in.cap(store);
      IntVar[] all = Arrays.copyOf(distinct(x), distinct(x).length + 1);
      all[all.length - 1] = c;
      int expected = 0;
      for (int[] tuple : tuples(all)) {
        int[] xv = in.itemValues(x, tuple, distinct(x));
        if (in.holds(xv, tuple[tuple.length - 1])) {
          expected++;
        }
      }
      store.impose(in.constraint(x, c));
      int count = store.consistency() ? countSolutions(store, all) : 0;
      assertThat(count).as(in.describe()).isEqualTo(expected);
      sat += expected > 0 ? 1 : 0;

      // the copy into a fresh store gives the same count
      Store fresh = new Store();
      IntVar[] fx = in.vars(fresh);
      IntVar fc = in.cap(fresh);
      Map<Var, Var> freshMap = new IdentityHashMap<>();
      IntVar[] dx = distinct(x);
      IntVar[] dfx = distinct(fx);
      for (int i = 0; i < dx.length; i++) {
        freshMap.put(dx[i], dfx[i]);
      }
      freshMap.put(c, fc);
      ChanceSum copy = in.constraint(x, c).copy(identityMap(freshMap, fresh));
      fresh.impose(copy);
      IntVar[] freshAll = Arrays.copyOf(dfx, dfx.length + 1);
      freshAll[freshAll.length - 1] = fc;
      int copied = fresh.consistency() ? countSolutions(fresh, freshAll) : 0;
      assertThat(copied).as(in.describe()).isEqualTo(expected);
    }
    assertThat(sat).isPositive();
    assertThat(sat).isLessThan(TRIALS);
  }

  private static VarMap identityMap(Map<Var, Var> map, Store target) {
    return new VarMap() {
      @Override
      public Store target() {
        return target;
      }

      @Override
      @SuppressWarnings("unchecked")
      public <V extends Var> V get(V v) {
        Var u = map.get(v);
        if (u == null) {
          throw new IllegalArgumentException("no mapping for " + v);
        }
        return (V) u;
      }
    };
  }

  @Test
  void testChanceSumIsTight() {
    // after propagation every bound it moves has a support: x[j] at its max with the others at
    // their min and c at its max, c at its min with every x at its min
    for (int t = 0; t < TRIALS; t++) {
      SumInstance in = new SumInstance(5_000_000L + t);
      Store store = new Store();
      IntVar[] x = in.vars(store);
      IntVar c = in.cap(store);
      store.impose(in.constraint(x, c));
      if (!store.consistency()) {
        continue;
      }
      IntVar[] dx = distinct(x);
      int[] low = Arrays.stream(dx).mapToInt(IntVar::min).toArray();
      assertThat(in.holds(in.itemValues(x, low, dx), c.min())).as(in.describe()).isTrue();
      for (int j = 0; j < dx.length; j++) {
        int[] v = low.clone();
        v[j] = dx[j].max();
        assertThat(in.holds(in.itemValues(x, v, dx), c.max())).as(in.describe()).isTrue();
        if (x.length == dx.length && dx[j].domain.getSize() == 2 && dx[j].max() == 1) {
          // 0/1 variables: both values have a support (domain consistency)
          v[j] = 0;
          assertThat(in.holds(in.itemValues(x, v, dx), c.max())).as(in.describe()).isTrue();
        }
      }
    }
  }

  @Test
  void testChanceSumRowsHoldForEverySolution() {
    int checked = 0;
    for (int t = 0; t < TRIALS; t++) {
      SumInstance in = new SumInstance(7_000_000L + t);
      Store store = new Store();
      IntVar[] x = in.vars(store);
      IntVar c = in.cap(store);
      ChanceSum constraint = in.constraint(x, c);
      List<LinearForm> rows = constraint.relaxation();
      IntVar[] dx = distinct(x);
      IntVar[] all = Arrays.copyOf(dx, dx.length + 1);
      all[dx.length] = c;
      for (int[] tuple : tuples(all)) {
        if (!in.holds(in.itemValues(x, tuple, dx), tuple[dx.length])) {
          continue;
        }
        Map<Var, Long> value = new IdentityHashMap<>();
        for (int i = 0; i < all.length; i++) {
          value.put(all[i], (long) tuple[i]);
        }
        for (LinearForm f : rows) {
          long lhs = 0;
          for (int k = 0; k < f.vars().length; k++) {
            lhs += f.weights()[k] * value.get(f.vars()[k]);
          }
          assertThat(lhs).as(in.describe() + " row " + f).isLessThanOrEqualTo(f.c());
          checked++;
        }
      }
    }
    assertThat(checked).isPositive();
  }

  @Test
  void testChanceSumExactTies() {
    // Pr(W <= 1) = 1/3 exactly: alpha 1/3 holds, alpha 1/3 + epsilon does not
    Dist third = new Dist(new int[] {1, 2, 3}, new long[] {1, 1, 1}, 3);
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 1);
    IntVar c = new IntVar(store, "c", 1, 1);
    store.impose(new ChanceSum(new IntVar[] {x}, new Dist[] {third}, c, 1, 3));
    assertThat(store.consistency()).isTrue();
    assertThat(x.max()).isEqualTo(1);
    store = new Store();
    x = new IntVar(store, "x", 0, 1);
    c = new IntVar(store, "c", 1, 1);
    store.impose(
        new ChanceSum(
            new IntVar[] {x}, new Dist[] {third}, c, 1_000_000_000_001L, 3_000_000_000_000L));
    assertThat(store.consistency()).isTrue();
    assertThat(x.max()).isZero();

    // 60 independent items of weight 0 or 1 with probability 1/2 each: Pr(load <= 30) is just
    // above 1/2; a threshold equal to it, and one a hair above, go through the exact comparison
    Dist coin = new Dist(new int[] {0, 1}, new long[] {1, 1}, 2);
    int n = 60;
    java.math.BigInteger num = java.math.BigInteger.ZERO;
    java.math.BigInteger binom = java.math.BigInteger.ONE;
    for (int k = 0; k <= 30; k++) {
      num = num.add(binom);
      binom =
          binom
              .multiply(java.math.BigInteger.valueOf((long) n - k))
              .divide(java.math.BigInteger.valueOf(k + 1L));
    }
    // num / 2^60 fits a long
    long den = 1L << 60;
    for (long delta : new long[] {0, 1}) {
      store = new Store();
      IntVar[] xs = new IntVar[n];
      Dist[] ws = new Dist[n];
      for (int i = 0; i < n; i++) {
        xs[i] = new IntVar(store, "x" + i, i == 0 ? 0 : 1, 1);
        ws[i] = coin;
      }
      c = new IntVar(store, "c", 0, 30);
      // with x0 = 0 the load of 59 coins: Pr(<= 30) is larger, so x0 = 1 decides
      store.impose(new ChanceSum(xs, ws, c, num.longValueExact() + delta, den));
      boolean ok = store.consistency();
      assertThat(ok).isTrue();
      assertThat(xs[0].max()).isEqualTo(delta == 0 ? 1 : 0);
      assertThat(c.min()).isEqualTo(30);
    }
  }

  @Test
  void testChanceSumRejectsBadInput() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", -1, 1);
    IntVar y = new IntVar(store, "y", 0, 1);
    IntVar c = new IntVar(store, "c", 0, 5);
    Dist d = Dist.uniform(1, 2);
    assertThatThrownBy(() -> new ChanceSum(new IntVar[] {x}, new Dist[] {d}, c, 1, 2))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () -> new ChanceSum(new IntVar[] {y}, new Dist[] {Dist.uniform(-1, 2)}, c, 1, 2))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new ChanceSum(new IntVar[] {y, c}, new Dist[] {d, d}, c, 1, 2))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new ChanceSum(new IntVar[] {y}, new Dist[] {d}, c, 1, 0))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testChanceSumWithLcg() {
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int t = 0; t < TRIALS; t++) {
      SumInstance in = new SumInstance(6_000_000L + t);
      Integer expected = null;
      {
        Store store = new Store();
        IntVar[] x = in.vars(store);
        IntVar c = in.cap(store);
        IntVar[] dx = distinct(x);
        IntVar[] all = Arrays.copyOf(dx, dx.length + 1);
        all[dx.length] = c;
        for (int[] tuple : tuples(all)) {
          int[] xv = in.itemValues(x, tuple, dx);
          if (in.holds(xv, tuple[dx.length])) {
            int obj = -tuple[dx.length];
            for (int i = 0; i < dx.length; i++) {
              obj -= in.value[i] * tuple[i];
            }
            expected = expected == null ? obj : Math.min(expected, obj);
          }
        }
      }
      Store store = new Store();
      IntVar[] x = in.vars(store);
      IntVar c = in.cap(store);
      store.impose(in.constraint(x, c));
      IntVar[] dx = distinct(x);
      IntVar[] all = Arrays.copyOf(dx, dx.length + 1);
      all[dx.length] = c;
      int[] coef = new int[all.length];
      for (int i = 0; i < dx.length; i++) {
        coef[i] = -in.value[i];
      }
      coef[dx.length] = -1;
      IntVar objective = new IntVar(store, "obj", -1000, 1000);
      store.impose(new LinearInt(all, coef, "==", objective));
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.minimize(objective);
      assertThat(status).as(in.describe()).isNotEqualTo(CdclSolver.UNKNOWN);
      assertThat(status == CdclSolver.SAT).as(in.describe()).isEqualTo(expected != null);
      if (status == CdclSolver.SAT) {
        int[] values = new int[dx.length];
        for (int i = 0; i < dx.length; i++) {
          values[i] = solver.value(dx[i]);
        }
        assertThat(in.holds(in.itemValues(x, values, dx), solver.value(c)))
            .as(in.describe())
            .isTrue();
        assertThat(solver.value(objective)).as(in.describe()).isEqualTo(expected);
        sat++;
      } else {
        unsat++;
      }
      long[] counts = solver.explanationStatistics().get("ChanceSum");
      if (counts != null) {
        own += counts[0] - counts[1] + counts[3] - counts[4];
        generic += counts[1] + counts[4];
      }
    }
    assertThat(sat).isPositive();
    assertThat(unsat).isPositive();
    assertThat(own).isGreaterThan(generic);
  }

  // a random ChanceTable instance: shared tables over a few variables, scenarios of tables
  private static final class TableInstance {
    final int n;
    final int[][] domains;
    final int[] repeat;
    final int[][] scopes;
    final int[][][] tables;
    final int[][] scenarios;
    final long[] weights;
    final int[] pDomain;
    final long seed;

    TableInstance(long seed) {
      this.seed = seed;
      Random random = new Random(seed);
      n = 1 + random.nextInt(4);
      domains = new int[n][];
      repeat = new int[n];
      for (int i = 0; i < n; i++) {
        domains[i] = SumInstance.values(random, random.nextInt(2), 3 + random.nextInt(2));
        repeat[i] = i > 0 && random.nextInt(8) == 0 ? random.nextInt(i) : -1;
      }
      int f = 1 + random.nextInt(5);
      scopes = new int[f][];
      tables = new int[f][][];
      boolean unary = random.nextInt(3) == 0;
      for (int t = 0; t < f; t++) {
        int arity = unary ? 1 : 1 + random.nextInt(Math.min(3, n));
        scopes[t] = new int[arity];
        for (int k = 0; k < arity; k++) {
          scopes[t][k] = random.nextInt(n);
        }
        int rows = random.nextInt(9);
        tables[t] = new int[rows][arity];
        for (int r = 0; r < rows; r++) {
          for (int k = 0; k < arity; k++) {
            tables[t][r][k] = random.nextInt(6);
          }
        }
      }
      int ns = 1 + random.nextInt(6);
      scenarios = new int[ns][];
      weights = new long[ns];
      long total = 0;
      for (int s = 0; s < ns; s++) {
        scenarios[s] = new int[random.nextInt(3)];
        for (int k = 0; k < scenarios[s].length; k++) {
          scenarios[s][k] = random.nextInt(f);
        }
        weights[s] = random.nextInt(6);
        total += weights[s];
      }
      pDomain = SumInstance.values(random, random.nextInt(3) == 0 ? -1 : 0, (int) total + 1);
    }

    IntVar[] vars(Store store) {
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        if (repeat[i] >= 0) {
          x[i] = x[repeat[i]];
          continue;
        }
        x[i] = new IntVar(store, "x" + i);
        for (int a : domains[i]) {
          x[i].addDom(a, a);
        }
      }
      return x;
    }

    IntVar p(Store store) {
      IntVar p = new IntVar(store, "p");
      for (int a : pDomain) {
        p.addDom(a, a);
      }
      return p;
    }

    ChanceTable constraint(IntVar[] x, IntVar p) {
      return new ChanceTable(x, scopes, tables, scenarios, weights, p);
    }

    // the weight of the scenarios that the values of x (one per position of x) satisfy
    long weightOf(int[] xv) {
      long w = 0;
      for (int s = 0; s < scenarios.length; s++) {
        boolean holds = true;
        for (int t : scenarios[s]) {
          boolean found = false;
          for (int[] row : tables[t]) {
            boolean match = true;
            for (int k = 0; k < row.length; k++) {
              match &= xv[scopes[t][k]] == row[k];
            }
            found |= match;
          }
          holds &= found;
        }
        if (holds) {
          w += weights[s];
        }
      }
      return w;
    }

    int[] values(IntVar[] x, int[] tuple, IntVar[] dx) {
      int[] xv = new int[n];
      for (int i = 0; i < n; i++) {
        xv[i] = tuple[Arrays.asList(dx).indexOf(x[i])];
      }
      return xv;
    }

    String describe() {
      return "seed "
          + seed
          + " scopes "
          + Arrays.deepToString(scopes)
          + " tables "
          + Arrays.deepToString(tables)
          + " scenarios "
          + Arrays.deepToString(scenarios)
          + " weights "
          + Arrays.toString(weights)
          + " domains "
          + Arrays.deepToString(domains)
          + " repeat "
          + Arrays.toString(repeat)
          + " p "
          + Arrays.toString(pDomain);
    }
  }

  @Test
  void testChanceTableAgainstBruteForce() {
    int sat = 0;
    for (int t = 0; t < TRIALS; t++) {
      TableInstance in = new TableInstance(7_000_000L + t);
      Store store = new Store();
      IntVar[] x = in.vars(store);
      IntVar p = in.p(store);
      IntVar[] dx = distinct(x);
      IntVar[] all = Arrays.copyOf(dx, dx.length + 1);
      all[dx.length] = p;
      int expected = 0;
      for (int[] tuple : tuples(all)) {
        if (in.weightOf(in.values(x, tuple, dx)) == tuple[dx.length]) {
          expected++;
        }
      }
      store.impose(in.constraint(x, p));
      int count = store.consistency() ? countSolutions(store, all) : 0;
      assertThat(count).as(in.describe()).isEqualTo(expected);
      if (expected > 0) {
        sat++;
      }

      // a copy into a fresh store gives the same solutions
      Store fresh = new Store();
      IntVar[] fx = in.vars(fresh);
      IntVar fp = in.p(fresh);
      Map<Var, Var> freshMap = new IdentityHashMap<>();
      Store plain = new Store();
      IntVar[] px = in.vars(plain);
      IntVar pp = in.p(plain);
      for (int i = 0; i < x.length; i++) {
        freshMap.put(px[i], fx[i]);
      }
      freshMap.put(pp, fp);
      fresh.impose(in.constraint(px, pp).copy(identityMap(freshMap, fresh)));
      IntVar[] fdx = distinct(fx);
      IntVar[] freshAll = Arrays.copyOf(fdx, fdx.length + 1);
      freshAll[fdx.length] = fp;
      int copied = fresh.consistency() ? countSolutions(fresh, freshAll) : 0;
      assertThat(copied).as(in.describe()).isEqualTo(expected);
    }
    assertThat(sat).isPositive();
    assertThat(sat).isLessThan(TRIALS);
  }

  @Test
  void testChanceTablePrunesByWeight() {
    // two scenarios over x in 0..2: x in {0, 1} with weight 3, x in {1} with weight 2
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 2);
    IntVar p = new IntVar(store, "p", 4, 5);
    int[][] scopes = {{0}, {0}};
    int[][][] tables = {{{0}, {1}}, {{1}}};
    store.impose(
        new ChanceTable(
            new IntVar[] {x}, scopes, tables, new int[][] {{0}, {1}}, new long[] {3, 2}, p));
    assertThat(store.consistency()).isTrue();
    assertThat(x.singleton()).isTrue();
    assertThat(x.value()).isEqualTo(1);
    assertThat(p.value()).isEqualTo(5);
  }

  @Test
  void testChanceTableRejectsBadInput() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 2);
    IntVar p = new IntVar(store, "p", 0, 5);
    IntVar[] xs = {x};
    int[][][] one = {{{0}}};
    assertThatThrownBy(
            () -> new ChanceTable(xs, new int[][] {{1}}, one, new int[][] {{0}}, new long[] {1}, p))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new ChanceTable(xs, new int[][] {{0}}, one, new int[][] {{0}}, new long[] {-1}, p))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () -> new ChanceTable(xs, new int[][] {{0}}, one, new int[][] {{1}}, new long[] {1}, p))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new ChanceTable(
                    new IntVar[] {p}, new int[][] {{0}}, one, new int[][] {{0}}, new long[] {1}, p))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new ChanceTable(
                    xs,
                    new int[][] {{0}},
                    new int[][][] {{{0, 1}}},
                    new int[][] {{0}},
                    new long[] {1},
                    p))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testChanceTableWithLcg() {
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int t = 0; t < TRIALS; t++) {
      TableInstance in = new TableInstance(8_000_000L + t);
      Integer expected = null;
      {
        Store store = new Store();
        IntVar[] x = in.vars(store);
        IntVar p = in.p(store);
        IntVar[] dx = distinct(x);
        for (int[] tuple : tuples(dx)) {
          long w = in.weightOf(in.values(x, tuple, dx));
          if (p.domain.contains((int) w)) {
            expected = expected == null ? (int) -w : Math.min(expected, (int) -w);
          }
        }
      }
      Store store = new Store();
      IntVar[] x = in.vars(store);
      IntVar p = in.p(store);
      store.impose(in.constraint(x, p));
      IntVar objective = new IntVar(store, "obj", -1000, 1000);
      store.impose(new LinearInt(new IntVar[] {p, objective}, new int[] {1, 1}, "==", 0));
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status;
      try {
        status = solver.minimize(objective);
      } catch (IllegalStateException e) {
        throw new AssertionError(in.describe(), e);
      }
      assertThat(status).as(in.describe()).isNotEqualTo(CdclSolver.UNKNOWN);
      assertThat(status == CdclSolver.SAT).as(in.describe()).isEqualTo(expected != null);
      if (status == CdclSolver.SAT) {
        IntVar[] dx = distinct(x);
        int[] values = new int[dx.length];
        for (int i = 0; i < dx.length; i++) {
          values[i] = solver.value(dx[i]);
        }
        assertThat(in.weightOf(in.values(x, values, dx)))
            .as(in.describe())
            .isEqualTo(solver.value(p));
        assertThat(solver.value(objective)).as(in.describe()).isEqualTo(expected);
        sat++;
      } else {
        unsat++;
      }
      long[] counts = solver.explanationStatistics().get("ChanceTable");
      if (counts != null) {
        own += counts[0] - counts[1] + counts[3] - counts[4];
        generic += counts[1] + counts[4];
      }
    }
    assertThat(sat).isPositive();
    assertThat(unsat).isPositive();
    assertThat(own).isGreaterThan(generic);
  }

  // a random ProbMdd instance: decision levels in a random order between chance levels
  private static final class MddInstance {
    final int n;
    final int[][] domains;
    final int[] repeat;
    final int[] levelVar;
    final int[] levelDen;
    final int[] levelSize;
    final int[] nodeEdges;
    final int[] edgeLabel;
    final int[] edgeTarget;
    final long scale;
    final int[] pDomain;
    final long seed;

    MddInstance(long seed) {
      this.seed = seed;
      Random random = new Random(seed);
      n = 1 + random.nextInt(4);
      domains = new int[n][];
      repeat = new int[n];
      for (int i = 0; i < n; i++) {
        domains[i] = SumInstance.values(random, random.nextInt(2), 2 + random.nextInt(2));
        repeat[i] = i > 0 && random.nextInt(10) == 0 ? random.nextInt(i) : -1;
      }
      List<Integer> order = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        if (random.nextInt(5) != 0) {
          order.add(i);
        }
      }
      int chance = random.nextInt(4);
      for (int c = 0; c < chance; c++) {
        order.add(random.nextInt(order.size() + 1), -1);
      }
      if (order.isEmpty()) {
        order.add(-1);
      }
      int levels = order.size();
      levelVar = order.stream().mapToInt(Integer::intValue).toArray();
      levelDen = new int[levels];
      levelSize = new int[levels];
      for (int l = 0; l < levels; l++) {
        levelDen[l] = 1 + random.nextInt(6);
        levelSize[l] = l == 0 ? 1 : 1 + random.nextInt(3);
      }
      List<Integer> counts = new ArrayList<>();
      List<Integer> labels = new ArrayList<>();
      List<Integer> targets = new ArrayList<>();
      for (int l = 0; l < levels; l++) {
        int next = l == levels - 1 ? 0 : levelSize[l + 1];
        for (int node = 0; node < levelSize[l]; node++) {
          int count = 0;
          if (levelVar[l] >= 0) {
            for (int v = 0; v <= 4; v++) {
              if (random.nextInt(3) != 0) {
                labels.add(v);
                targets.add(next == 0 ? -1 : random.nextInt(next));
                count++;
              }
            }
          } else {
            int left = levelDen[l] - (random.nextInt(4) == 0 ? 1 : 0);
            int k = 1 + random.nextInt(3);
            for (int j = 0; j < k && left > 0; j++) {
              int w = j == k - 1 ? left : random.nextInt(left + 1);
              left -= w;
              labels.add(w);
              targets.add(next == 0 ? -1 : random.nextInt(next));
              count++;
            }
          }
          counts.add(count);
        }
      }
      nodeEdges = counts.stream().mapToInt(Integer::intValue).toArray();
      edgeLabel = labels.stream().mapToInt(Integer::intValue).toArray();
      edgeTarget = targets.stream().mapToInt(Integer::intValue).toArray();
      long den = 1;
      for (int l = 0; l < levels; l++) {
        if (levelVar[l] < 0) {
          den *= levelDen[l];
        }
      }
      scale = random.nextBoolean() ? den : 1 + random.nextInt(40);
      pDomain = SumInstance.values(random, random.nextInt(4) == 0 ? -1 : 0, (int) scale + 1);
    }

    IntVar[] vars(Store store) {
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        if (repeat[i] >= 0) {
          x[i] = x[repeat[i]];
          continue;
        }
        x[i] = new IntVar(store, "x" + i);
        for (int a : domains[i]) {
          x[i].addDom(a, a);
        }
      }
      return x;
    }

    IntVar p(Store store) {
      IntVar p = new IntVar(store, "p");
      for (int a : pDomain) {
        p.addDom(a, a);
      }
      return p;
    }

    ProbMdd constraint(IntVar[] x, IntVar p) {
      return new ProbMdd(
          x, levelVar, levelDen, levelSize, nodeEdges, edgeLabel, edgeTarget, scale, p);
    }

    // floor(scale * Pr(T)) for the values of x, by a walk over the paths with exact fractions
    long value(int[] xv) {
      BigInteger[] r = walk(0, 0, xv);
      return r[0].multiply(BigInteger.valueOf(scale)).divide(r[1]).longValueExact();
    }

    // {numerator, denominator} of the probability of reaching T from a node of a level
    private BigInteger[] walk(int level, int node, int[] xv) {
      if (level == levelVar.length) {
        return new BigInteger[] {BigInteger.ONE, BigInteger.ONE};
      }
      int first = 0;
      for (int l = 0; l < level; l++) {
        first += levelSize[l];
      }
      int edge = 0;
      for (int k = 0; k < first + node; k++) {
        edge += nodeEdges[k];
      }
      BigInteger num = BigInteger.ZERO;
      BigInteger den = BigInteger.ONE;
      for (int e = edge; e < edge + nodeEdges[first + node]; e++) {
        int t = edgeTarget[e];
        BigInteger[] child = walk(level + 1, Math.max(t, 0), xv);
        if (levelVar[level] >= 0) {
          if (edgeLabel[e] == xv[levelVar[level]]) {
            return child;
          }
        } else {
          // num / den + w * child / (levelDen * child den)
          BigInteger d = BigInteger.valueOf(levelDen[level]).multiply(child[1]);
          num =
              num.multiply(d)
                  .add(BigInteger.valueOf(edgeLabel[e]).multiply(child[0]).multiply(den));
          den = den.multiply(d);
        }
      }
      return new BigInteger[] {num, den};
    }

    int[] values(IntVar[] x, int[] tuple, IntVar[] dx) {
      int[] xv = new int[n];
      for (int i = 0; i < n; i++) {
        xv[i] = tuple[Arrays.asList(dx).indexOf(x[i])];
      }
      return xv;
    }

    String describe() {
      return "seed "
          + seed
          + " levelVar "
          + Arrays.toString(levelVar)
          + " levelDen "
          + Arrays.toString(levelDen)
          + " levelSize "
          + Arrays.toString(levelSize)
          + " nodeEdges "
          + Arrays.toString(nodeEdges)
          + " labels "
          + Arrays.toString(edgeLabel)
          + " targets "
          + Arrays.toString(edgeTarget)
          + " scale "
          + scale
          + " domains "
          + Arrays.deepToString(domains)
          + " repeat "
          + Arrays.toString(repeat)
          + " p "
          + Arrays.toString(pDomain);
    }
  }

  @Test
  void testProbMddAgainstBruteForce() {
    int sat = 0;
    for (int t = 0; t < TRIALS; t++) {
      MddInstance in = new MddInstance(9_000_000L + t);
      Store store = new Store();
      IntVar[] x = in.vars(store);
      IntVar p = in.p(store);
      IntVar[] dx = distinct(x);
      IntVar[] all = Arrays.copyOf(dx, dx.length + 1);
      all[dx.length] = p;
      int expected = 0;
      for (int[] tuple : tuples(all)) {
        if (in.value(in.values(x, tuple, dx)) == tuple[dx.length]) {
          expected++;
        }
      }
      store.impose(in.constraint(x, p));
      int count = store.consistency() ? countSolutions(store, all) : 0;
      assertThat(count).as(in.describe()).isEqualTo(expected);
      if (expected > 0) {
        sat++;
      }

      Store fresh = new Store();
      IntVar[] fx = in.vars(fresh);
      IntVar fp = in.p(fresh);
      Store plain = new Store();
      IntVar[] px = in.vars(plain);
      IntVar pp = in.p(plain);
      Map<Var, Var> freshMap = new IdentityHashMap<>();
      for (int i = 0; i < x.length; i++) {
        freshMap.put(px[i], fx[i]);
      }
      freshMap.put(pp, fp);
      fresh.impose(in.constraint(px, pp).copy(identityMap(freshMap, fresh)));
      IntVar[] fdx = distinct(fx);
      IntVar[] freshAll = Arrays.copyOf(fdx, fdx.length + 1);
      freshAll[fdx.length] = fp;
      int copied = fresh.consistency() ? countSolutions(fresh, freshAll) : 0;
      assertThat(copied).as(in.describe()).isEqualTo(expected);
    }
    assertThat(sat).isPositive();
    assertThat(sat).isLessThan(TRIALS);
  }

  @Test
  void testProbMddPrunesDecisions() {
    // x0 then a coin of 3/4 towards T: x0 = 1 reaches the coin, x0 = 0 the false sink
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 1);
    IntVar p = new IntVar(store, "p", 1, 4);
    store.impose(
        new ProbMdd(
            new IntVar[] {x},
            new int[] {0, -1},
            new int[] {1, 4},
            new int[] {1, 1},
            new int[] {1, 1},
            new int[] {1, 3},
            new int[] {0, -1},
            4,
            p));
    assertThat(store.consistency()).isTrue();
    assertThat(x.value()).isEqualTo(1);
    assertThat(p.value()).isEqualTo(3);
  }

  @Test
  void testProbMddRejectsBadInput() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 1);
    IntVar p = new IntVar(store, "p", 0, 4);
    IntVar[] xs = {x};
    // two roots, a variable on two levels, probabilities above 1, a repeated label, a bad target
    assertThatThrownBy(
            () ->
                new ProbMdd(
                    xs,
                    new int[] {0},
                    new int[] {1},
                    new int[] {2},
                    new int[] {1, 1},
                    new int[] {0, 1},
                    new int[] {-1, -1},
                    4,
                    p))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new ProbMdd(
                    xs,
                    new int[] {0, 0},
                    new int[] {1, 1},
                    new int[] {1, 1},
                    new int[] {1, 1},
                    new int[] {0, 1},
                    new int[] {0, -1},
                    4,
                    p))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new ProbMdd(
                    xs,
                    new int[] {-1},
                    new int[] {4},
                    new int[] {1},
                    new int[] {2},
                    new int[] {3, 2},
                    new int[] {-1, -1},
                    4,
                    p))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new ProbMdd(
                    xs,
                    new int[] {0},
                    new int[] {1},
                    new int[] {1},
                    new int[] {2},
                    new int[] {1, 1},
                    new int[] {-1, -1},
                    4,
                    p))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new ProbMdd(
                    xs,
                    new int[] {0, -1},
                    new int[] {1, 2},
                    new int[] {1, 1},
                    new int[] {1, 1},
                    new int[] {1, 1},
                    new int[] {1, -1},
                    4,
                    p))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testProbMddWithLcg() {
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int t = 0; t < TRIALS; t++) {
      MddInstance in = new MddInstance(10_000_000L + t);
      Integer expected = null;
      {
        Store store = new Store();
        IntVar[] x = in.vars(store);
        IntVar p = in.p(store);
        IntVar[] dx = distinct(x);
        for (int[] tuple : tuples(dx)) {
          long w = in.value(in.values(x, tuple, dx));
          if (p.domain.contains((int) w)) {
            expected = expected == null ? (int) -w : Math.min(expected, (int) -w);
          }
        }
      }
      Store store = new Store();
      IntVar[] x = in.vars(store);
      IntVar p = in.p(store);
      store.impose(in.constraint(x, p));
      IntVar objective = new IntVar(store, "obj", -100_000, 100_000);
      store.impose(new LinearInt(new IntVar[] {p, objective}, new int[] {1, 1}, "==", 0));
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status;
      try {
        status = solver.minimize(objective);
      } catch (IllegalStateException e) {
        throw new AssertionError(in.describe(), e);
      }
      assertThat(status).as(in.describe()).isNotEqualTo(CdclSolver.UNKNOWN);
      assertThat(status == CdclSolver.SAT).as(in.describe()).isEqualTo(expected != null);
      if (status == CdclSolver.SAT) {
        IntVar[] dx = distinct(x);
        int[] values = new int[dx.length];
        for (int i = 0; i < dx.length; i++) {
          values[i] = solver.value(dx[i]);
        }
        assertThat(in.value(in.values(x, values, dx))).as(in.describe()).isEqualTo(solver.value(p));
        assertThat(solver.value(objective)).as(in.describe()).isEqualTo(expected);
        sat++;
      } else {
        unsat++;
      }
      long[] counts = solver.explanationStatistics().get("ProbMdd");
      if (counts != null) {
        own += counts[0] - counts[1] + counts[3] - counts[4];
        generic += counts[1] + counts[4];
      }
    }
    assertThat(sat).isPositive();
    assertThat(unsat).isPositive();
    assertThat(own).isGreaterThan(generic);
  }
}
