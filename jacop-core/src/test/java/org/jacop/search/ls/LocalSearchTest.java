/*
 * LocalSearchTest.java
 * <p>
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
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.time.Duration;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.AmongSeq;
import org.jacop.constraints.Count;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.regular.Regular;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;
import org.junit.jupiter.api.Test;

/** Tests of {@link LocalSearch}. */
class LocalSearchTest {

  private static final Duration LIMIT = Duration.ofSeconds(10);

  /** n queens with all-distinct diagonals, through views made by x + c = z. */
  @Test
  void findsQueens() {
    queens(false, false);
  }

  /** The same with the diagonals defined by the queens: they follow every move of a queen. */
  @Test
  void findsQueensWithDefinedDiagonals() {
    queens(true, false);
  }

  /** The same with feasibility jump moves. */
  @Test
  void findsQueensWithJumps() {
    queens(true, true);
  }

  /**
   * Feasibility jump on linear rows over wide domains: a planted solution of eight variables in
   * 0..1000 and six rows, each to be within 5 of its value at the planted solution.
   */
  @Test
  void jumpsSatisfyLinearRows() {
    Store store = new Store();
    int n = 8;
    int[] planted = {417, 3, 999, 250, 0, 608, 77, 512};
    int[][] a = {
      {3, -2, 1, 0, 5, 0, -1, 2},
      {0, 4, -3, 2, 0, 1, 0, -1},
      {1, 1, 1, 1, 1, 1, 1, 1},
      {-2, 0, 0, 3, -1, 0, 4, 0},
      {0, -1, 2, 0, 0, -3, 1, 1},
      {5, 0, 0, -1, 2, 0, 0, -4}
    };
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1000);
    }
    for (int[] row : a) {
      int sum = 0;
      for (int i = 0; i < n; i++) {
        sum += row[i] * planted[i];
      }
      store.impose(new LinearInt(x, row, "<=", sum + 5));
      store.impose(new LinearInt(x, row, ">=", sum - 5));
    }
    assertTrue(store.consistency());
    LocalSearch ls =
        LocalSearch.builder(store).order(x).jump(true).timeLimit(LIMIT).seed(7).build();
    assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
    int[] v = ls.getSolution(x);
    for (int[] row : a) {
      long sum = 0;
      long target = 0;
      for (int i = 0; i < n; i++) {
        sum += (long) row[i] * v[i];
        target += (long) row[i] * planted[i];
      }
      assertTrue(Math.abs(sum - target) <= 5, sum + " vs " + target);
    }
  }

  private static void queens(boolean defined, boolean jump) {
    int n = 12;
    Store store = new Store();
    IntVar[] q = new IntVar[n];
    IntVar[] up = new IntVar[n];
    IntVar[] down = new IntVar[n];
    for (int i = 0; i < n; i++) {
      q[i] = new IntVar(store, "q" + i, 0, n - 1);
      up[i] = new IntVar(store, "u" + i, 0, 2 * n);
      down[i] = new IntVar(store, "d" + i, -n, n);
      store.impose(new XplusCeqZ(q[i], i, up[i]));
      store.impose(new XplusCeqZ(q[i], -i, down[i]));
    }
    store.impose(new Alldistinct(q));
    store.impose(new Alldistinct(up));
    store.impose(new Alldistinct(down));
    assertTrue(store.consistency());
    int level = store.level;
    List<int[]> found = new ArrayList<>();
    List<IntVar> diagonals = new ArrayList<>(List.of(up));
    diagonals.addAll(List.of(down));
    LocalSearch ls =
        LocalSearch.builder(store)
            .order(q)
            .defined(defined ? diagonals : List.of())
            .jump(jump)
            .timeLimit(LIMIT)
            .seed(3)
            .onSolution(
                s -> {
                  // the handler sees the solution in the store
                  int[] v = new int[n];
                  for (int i = 0; i < n; i++) {
                    assertTrue(q[i].singleton());
                    v[i] = q[i].value();
                  }
                  found.add(v);
                })
            .build();
    assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
    assertEquals(level, store.level);
    assertEquals(1, found.size());
    int[] v = ls.getSolution(q);
    assertNotNull(v);
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        assertTrue(v[i] != v[j] && v[i] + i != v[j] + j && v[i] - i != v[j] - j);
      }
    }
  }

  /**
   * A Costas array of order 11: a permutation whose difference rows are all distinct, with the
   * differences defined by the permutation. The permutation is kept by swaps, one variable has a
   * smaller domain (x0 < x10), and the duplicates of each row are counted incrementally.
   */
  @Test
  void findsCostasArrayBySwaps() {
    costas(false);
    costas(true);
  }

  private static void costas(boolean jump) {
    int n = 11;
    Store store = new Store();
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 1, n);
    }
    store.impose(new Alldistinct(x));
    store.impose(new XltY(x[0], x[n - 1]));
    List<IntVar> diffs = new ArrayList<>();
    for (int d = 1; d < n - 1; d++) {
      IntVar[] row = new IntVar[n - d];
      for (int j = 0; j + d < n; j++) {
        row[j] = new IntVar(store, "d" + d + "_" + j, -n + 1, n - 1);
        // row[j] + x[j] = x[j + d]
        store.impose(new XplusYeqZ(row[j], x[j], x[j + d]));
        diffs.add(row[j]);
      }
      store.impose(new Alldistinct(row));
    }
    assertTrue(store.consistency());
    LocalSearch ls =
        LocalSearch.builder(store)
            .order(x)
            .defined(diffs)
            .jump(jump)
            .timeLimit(LIMIT)
            .seed(11)
            .build();
    assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
    assertTrue(ls.toString().contains("P:Alldistinct=1"), ls.toString());
    int[] v = ls.getSolution(x);
    assertTrue(v[0] < v[n - 1]);
    for (int d = 0; d < n - 1; d++) {
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          if (d == 0) {
            assertTrue(v[i] != v[j]);
          } else if (j + d < n) {
            assertTrue(v[i + d] - v[i] != v[j + d] - v[j], "row " + d);
          }
        }
      }
    }
  }

  /** Without permutation groups the queens are still found, by value moves. */
  @Test
  void findsQueensWithoutPermutations() {
    int n = 10;
    Store store = new Store();
    IntVar[] q = new IntVar[n];
    IntVar[] up = new IntVar[n];
    IntVar[] down = new IntVar[n];
    for (int i = 0; i < n; i++) {
      q[i] = new IntVar(store, "q" + i, 0, n - 1);
      up[i] = new IntVar(store, "u" + i, 0, 2 * n);
      down[i] = new IntVar(store, "d" + i, -n, n);
      store.impose(new XplusCeqZ(q[i], i, up[i]));
      store.impose(new XplusCeqZ(q[i], -i, down[i]));
    }
    store.impose(new Alldistinct(q));
    store.impose(new Alldistinct(up));
    store.impose(new Alldistinct(down));
    assertTrue(store.consistency());
    LocalSearch ls =
        LocalSearch.builder(store).order(q).permutations(false).timeLimit(LIMIT).seed(3).build();
    assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
    assertTrue(!ls.toString().contains("P:"), ls.toString());
  }

  /**
   * Car sequencing (CSPLib prob001, the example of Dincbas et al. 1988): the classes of 10 cars
   * with at most max[o] cars needing option o in each block of size[o]. The options are sequence
   * constraints over the classes, whose window counts local search keeps up to date (M:AmongSeq),
   * and the class counts are kept by swaps.
   */
  @Test
  void sequencesCarsByWindowCounts() {
    int[] max = {1, 2, 1, 2, 1};
    int[] size = {2, 3, 3, 5, 5};
    int[] cars = {1, 1, 2, 2, 2, 2};
    int[][] need = {
      {1, 0, 1, 1, 0},
      {0, 0, 0, 1, 0},
      {0, 1, 0, 0, 1},
      {0, 1, 0, 1, 0},
      {1, 0, 1, 0, 0},
      {1, 1, 0, 0, 0}
    };
    Store store = new Store();
    IntVar[] x = new IntVar[10];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, cars.length);
    }
    for (int c = 0; c < cars.length; c++) {
      store.impose(new Count(x, new IntVar(store, cars[c], cars[c]), c + 1));
    }
    IntervalDomain[] sets = new IntervalDomain[max.length];
    for (int o = 0; o < max.length; o++) {
      sets[o] = new IntervalDomain();
      for (int c = 0; c < cars.length; c++) {
        if (need[c][o] == 1) {
          sets[o].unionAdapt(c + 1, c + 1);
        }
      }
      store.impose(new AmongSeq(x, sets[o], size[o], 0, max[o]));
    }
    assertTrue(store.consistency());
    LocalSearch ls = LocalSearch.builder(store).order(x).timeLimit(LIMIT).seed(5).build();
    assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
    assertTrue(ls.toString().contains("M:AmongSeq=5"), ls.toString());
    int[] v = ls.getSolution(x);
    for (int o = 0; o < max.length; o++) {
      for (int i = 0; i + size[o] <= v.length; i++) {
        int count = 0;
        for (int j = i; j < i + size[o]; j++) {
          count += sets[o].contains(v[j]) ? 1 : 0;
        }
        assertTrue(count <= max[o], "option " + o + " window " + i);
      }
    }
  }

  /**
   * An all different whose small domains lie far apart is not a permutation; looking for one must
   * not build a small dense union wider than 64 values.
   */
  @Test
  void skipsAllDifferentOverDistantSmallDomains() {
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 0, 1),
      new IntVar(store, "x1", 100, 101),
      new IntVar(store, "x2", 0, 101)
    };
    store.impose(new Alldistinct(x));
    assertTrue(store.consistency());
    LocalSearch ls = LocalSearch.builder(store).order(x).timeLimit(LIMIT).seed(1).build();
    assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
    assertTrue(!ls.toString().contains("P:"), ls.toString());
  }

  /**
   * A constraint imposed as implied by the others is not evaluated, but the store still checks
   * every solution against it.
   */
  @Test
  void skipsImpliedConstraints() {
    for (boolean skip : new boolean[] {true, false}) {
      Store store = new Store();
      IntVar[] x = new IntVar[5];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 4);
      }
      store.impose(new Alldistinct(x));
      store.imposingImplied(true);
      store.impose(new LinearInt(x, new int[] {1, 1, 1, 1, 1}, "==", 10));
      store.imposingImplied(false);
      assertTrue(store.consistency());
      LocalSearch ls =
          LocalSearch.builder(store).order(x).skipImplied(skip).timeLimit(LIMIT).seed(1).build();
      assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
      assertEquals(skip, ls.toString().contains("I:LinearInt=1"), ls.toString());
    }
  }

  /**
   * A symmetry breaking constraint given with a canonicalizer is not evaluated: a solution that
   * breaks it is moved to the symmetric one, which the store accepts.
   */
  @Test
  void canonicalizesSymmetricSolutions() {
    long canonicalized = 0;
    for (int seed = 1; seed <= 20; seed++) {
      Store store = new Store();
      IntVar[] x = new IntVar[6];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 5);
      }
      store.impose(new Alldistinct(x));
      // the weights of x4 and x5 are equal, so the two are interchangeable; x4 < x5 breaks that
      store.impose(new LinearInt(x, new int[] {1, 2, 3, 4, 5, 5}, "==", 52));
      XltY lex = new XltY(x[4], x[5]);
      store.impose(lex);
      assertTrue(store.consistency());
      LocalSearch.Canonicalizer swap =
          (vars, values) -> {
            int i = Arrays.asList(vars).indexOf(x[4]);
            int j = Arrays.asList(vars).indexOf(x[5]);
            if (values[i] > values[j]) {
              int v = values[i];
              values[i] = values[j];
              values[j] = v;
            }
            return true;
          };
      LocalSearch ls =
          LocalSearch.builder(store)
              .order(x)
              .symmetry(List.of(lex), swap)
              .timeLimit(LIMIT)
              .seed(seed)
              .build();
      assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
      assertTrue(ls.toString().contains("S:XltY=1"), ls.toString());
      int[] s = ls.getSolution(x);
      assertTrue(s[4] < s[5], Arrays.toString(s));
      canonicalized += ls.getCanonicalized();
    }
    assertTrue(canonicalized > 0);
  }

  /**
   * Minimises the makespan of tasks on a cumulative resource, with a reified linear constraint
   * between two tasks; each solution reported is better than the last.
   */
  @Test
  void improvesTheCost() {
    Store store = new Store();
    int n = 8;
    int[] dur = {3, 2, 4, 1, 2, 3, 2, 1};
    int[] use = {2, 1, 2, 1, 3, 1, 2, 2};
    IntVar[] s = new IntVar[n];
    IntVar[] d = new IntVar[n];
    IntVar[] r = new IntVar[n];
    IntVar makespan = new IntVar(store, "makespan", 0, 60);
    for (int i = 0; i < n; i++) {
      s[i] = new IntVar(store, "s" + i, 0, 40);
      d[i] = new IntVar(store, dur[i], dur[i]);
      r[i] = new IntVar(store, use[i], use[i]);
      store.impose(new LinearInt(new IntVar[] {s[i], makespan}, new int[] {1, -1}, "<=", -dur[i]));
    }
    store.impose(new Cumulative(s, d, r, new IntVar(store, 3, 3)));
    IntVar b = new IntVar(store, "b", 0, 1);
    store.impose(new Reified(new XeqC(s[0], 0), b));
    store.impose(new XeqC(b, 1));
    assertTrue(store.consistency());
    List<Integer> costs = new ArrayList<>();
    LocalSearch ls =
        LocalSearch.builder(store)
            .order(s)
            .minimize(makespan)
            .timeLimit(Duration.ofSeconds(2))
            .seed(5)
            .onSolution(x -> costs.add(makespan.value()))
            .build();
    assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
    assertTrue(costs.size() >= 1);
    for (int k = 1; k < costs.size(); k++) {
      assertTrue(costs.get(k) < costs.get(k - 1), costs.toString());
    }
    assertEquals(costs.get(costs.size() - 1), ls.getCostValue());
    // the energy is 24 on a capacity of 3
    assertTrue(ls.getCostValue() >= 8);
    assertEquals(0, ls.getSolution(new IntVar[] {s[0]})[0]);
  }

  /**
   * The time limit holds when one step evaluates thousands of costly constraints: two Regular
   * constraints on the sum modulo 40 of 150 variables that no assignment satisfies together.
   */
  @Test
  void stopsInTimeOnCostlySteps() {
    Store store = new Store();
    IntVar[] x = new IntVar[150];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 9);
    }
    store.impose(new Regular(sumModulo(40, 0), x));
    store.impose(new Regular(sumModulo(40, 1), x));
    assertTrue(store.consistency());
    LocalSearch ls = LocalSearch.builder(store).order(x).timeLimit(Duration.ofMillis(300)).build();
    long start = System.nanoTime();
    assertEquals(LocalSearch.Status.UNKNOWN, ls.solve());
    long millis = (System.nanoTime() - start) / 1_000_000;
    assertTrue(millis < 3000, "local search ran " + millis + " ms with a limit of 300 ms");
  }

  // words whose sum is r modulo m
  private static Fsm sumModulo(int m, int r) {
    Fsm fsm = new Fsm();
    FsmState[] s = new FsmState[m];
    for (int i = 0; i < m; i++) {
      s[i] = new FsmState();
      fsm.allStates.add(s[i]);
    }
    fsm.initState = s[0];
    fsm.finalStates.add(s[r]);
    for (int i = 0; i < m; i++) {
      for (int v = 0; v <= 9; v++) {
        s[i].addTransition(new FsmTransition(new IntervalDomain(v, v), s[(i + v) % m]));
      }
    }
    return fsm;
  }
}
