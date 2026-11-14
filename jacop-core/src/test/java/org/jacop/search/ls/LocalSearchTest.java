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

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
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
import org.jacop.constraints.CountValuesBounds;
import org.jacop.constraints.ElementVariableFast;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.regular.Regular;
import org.jacop.constraints.table.HybridTable;
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

  /**
   * Social golfers, 9 golfers in 3 groups of 3 for 4 rounds (Kirkman's schoolgirls), modelled as in
   * the MiniZinc benchmark: each pair of a group looks its cell of a pair matrix up by an element
   * constraint, cell = round. The cells only the element constraints read follow them, so a move of
   * a golfer needs no second move of a cell.
   */
  @Test
  void findsGolfersWithFollowers() {
    int groups = 3;
    int size = 3;
    int rounds = 4;
    int golfers = groups * size;
    Store store = new Store();
    IntVar[][] place = new IntVar[rounds][golfers];
    IntVar[] cell = new IntVar[golfers * golfers];
    for (int k = 0; k < cell.length; k++) {
      cell[k] = new IntVar(store, "c" + k, 0, rounds);
    }
    List<IntVar> defined = new ArrayList<>();
    List<IntVar> order = new ArrayList<>();
    for (int r = 0; r < rounds; r++) {
      for (int p = 0; p < golfers; p++) {
        place[r][p] = new IntVar(store, "p" + r + "_" + p, 1, golfers);
        order.add(place[r][p]);
      }
      store.impose(new Alldistinct(place[r]));
      for (int g = 0; g < groups; g++) {
        for (int i = 0; i < size; i++) {
          for (int j = i + 1; j < size; j++) {
            IntVar a = place[r][g * size + i];
            IntVar b = place[r][g * size + j];
            if (j == i + 1) {
              store.impose(new XltY(a, b));
            }
            IntVar at = new IntVar(store, "at" + r + "_" + g + "_" + i + "_" + j, 1, cell.length);
            // at = golfers * (a - 1) + b
            store.impose(
                new LinearInt(new IntVar[] {a, b, at}, new int[] {golfers, 1, -1}, "=", golfers));
            store.impose(new ElementVariableFast(at, cell, new IntVar(store, r + 1, r + 1)));
            defined.add(at);
          }
        }
      }
    }
    assertTrue(store.consistency());
    LocalSearch ls =
        LocalSearch.builder(store)
            .order(order.toArray(new IntVar[0]))
            .defined(defined)
            .timeLimit(LIMIT)
            .seed(5)
            .build();
    assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
    assertTrue(ls.toString().contains("followers="), ls.toString());
    boolean[][] met = new boolean[golfers + 1][golfers + 1];
    for (int r = 0; r < rounds; r++) {
      int[] v = ls.getSolution(place[r]);
      for (int g = 0; g < groups; g++) {
        for (int i = 0; i < size; i++) {
          for (int j = i + 1; j < size; j++) {
            int a = v[g * size + i];
            int b = v[g * size + j];
            assertTrue(a < b);
            assertTrue(!met[a][b], "golfers " + a + " and " + b + " meet twice");
            met[a][b] = true;
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

  // Fisher and Thompson's 6 x 6 job shop (ft06, optimum 55): machine and duration of each task
  private static final int[][] FT06_MACHINE = {
    {2, 0, 1, 3, 5, 4},
    {1, 2, 4, 5, 0, 3},
    {2, 3, 5, 0, 1, 4},
    {1, 0, 2, 3, 4, 5},
    {2, 1, 4, 5, 0, 3},
    {1, 3, 5, 0, 4, 2}
  };
  private static final int[][] FT06_DURATION = {
    {1, 3, 6, 7, 3, 6},
    {8, 5, 10, 10, 10, 4},
    {5, 4, 8, 9, 1, 7},
    {5, 5, 5, 3, 8, 9},
    {9, 3, 5, 4, 3, 1},
    {3, 3, 9, 10, 4, 1}
  };

  /** The starts of ft06, with job precedences and one unit cumulative per machine. */
  private static IntVar[][] jobShop(Store store) {
    int n = FT06_MACHINE.length;
    IntVar[][] s = new IntVar[n][n];
    for (int j = 0; j < n; j++) {
      for (int k = 0; k < n; k++) {
        s[j][k] = new IntVar(store, "s" + j + "_" + k, 0, 300);
        if (k > 0) {
          store.impose(
              new LinearInt(
                  new IntVar[] {s[j][k - 1], s[j][k]},
                  new int[] {1, -1},
                  "<=",
                  -FT06_DURATION[j][k - 1]));
        }
      }
    }
    for (int m = 0; m < n; m++) {
      List<IntVar> starts = new ArrayList<>();
      List<IntVar> durations = new ArrayList<>();
      for (int j = 0; j < n; j++) {
        for (int k = 0; k < n; k++) {
          if (FT06_MACHINE[j][k] == m) {
            starts.add(s[j][k]);
            durations.add(new IntVar(store, FT06_DURATION[j][k], FT06_DURATION[j][k]));
          }
        }
      }
      IntVar[] one = new IntVar[starts.size()];
      java.util.Arrays.fill(one, new IntVar(store, 1, 1));
      store.impose(
          new Cumulative(
              starts.toArray(new IntVar[0]),
              durations.toArray(new IntVar[0]),
              one,
              new IntVar(store, 1, 1)));
    }
    return s;
  }

  // the makespan of starts that keep the job order and use each machine for one task at a time
  private static int checkedMakespan(int[][] start) {
    int n = start.length;
    int end = 0;
    for (int j = 0; j < n; j++) {
      for (int k = 0; k < n; k++) {
        end = Math.max(end, start[j][k] + FT06_DURATION[j][k]);
        if (k > 0) {
          assertTrue(start[j][k - 1] + FT06_DURATION[j][k - 1] <= start[j][k]);
        }
        for (int i = 0; i < n; i++) {
          for (int l = 0; l < n; l++) {
            if ((i != j || l != k) && FT06_MACHINE[i][l] == FT06_MACHINE[j][k]) {
              assertTrue(
                  start[i][l] + FT06_DURATION[i][l] <= start[j][k]
                      || start[j][k] + FT06_DURATION[j][k] <= start[i][l]);
            }
          }
        }
      }
    }
    return end;
  }

  private static int[][] starts(LocalSearch ls, IntVar[][] s) {
    int[][] start = new int[s.length][];
    for (int j = 0; j < s.length; j++) {
      start[j] = ls.getSolution(s[j]);
    }
    return start;
  }

  /** Each neighbourhood of the critical-path tabu search finds the optimum of ft06. */
  @Test
  void schedulesJobShopByCriticalPathMoves() {
    int[] kinds = {
      LocalSearch.SCHEDULE_NS | LocalSearch.SCHEDULE_N4,
      LocalSearch.SCHEDULE_NS,
      LocalSearch.SCHEDULE_N1,
      LocalSearch.SCHEDULE_N4
    };
    for (int kind : kinds) {
      Store store = new Store();
      IntVar[][] s = jobShop(store);
      IntVar makespan = new IntVar(store, "makespan", 0, 300);
      for (int j = 0; j < s.length; j++) {
        store.impose(
            new LinearInt(
                new IntVar[] {s[j][5], makespan}, new int[] {1, -1}, "<=", -FT06_DURATION[j][5]));
      }
      assertTrue(store.consistency());
      LocalSearch ls =
          LocalSearch.builder(store)
              .minimize(makespan)
              .scheduling(kind)
              .timeLimit(Duration.ofSeconds(5))
              .patience(Duration.ofMillis(300))
              .seed(3)
              .build();
      assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
      assertEquals(55, ls.getCostValue(), "neighbourhoods " + kind);
      assertEquals(55, checkedMakespan(starts(ls, s)));
      assertTrue(ls.getSteps() > 0);
    }
  }

  /**
   * When the cost is not the makespan (here the sum of the job ends), the scheduling search gives
   * way to the general one after its first schedule, and the solutions stay correct.
   */
  @Test
  void leavesOtherObjectivesToTheGeneralSearch() {
    Store store = new Store();
    IntVar[][] s = jobShop(store);
    IntVar[] ends = new IntVar[s.length];
    for (int j = 0; j < s.length; j++) {
      ends[j] = new IntVar(store, "e" + j, 0, 400);
      store.impose(new XplusCeqZ(s[j][5], FT06_DURATION[j][5], ends[j]));
    }
    IntVar total = new IntVar(store, "total", 0, 3000);
    int[] ones = new int[s.length];
    java.util.Arrays.fill(ones, 1);
    IntVar[] terms = java.util.Arrays.copyOf(ends, s.length + 1);
    terms[s.length] = total;
    int[] weights = java.util.Arrays.copyOf(ones, s.length + 1);
    weights[s.length] = -1;
    store.impose(new LinearInt(terms, weights, "==", 0));
    assertTrue(store.consistency());
    List<Integer> costs = new ArrayList<>();
    LocalSearch ls =
        LocalSearch.builder(store)
            .minimize(total)
            .timeLimit(Duration.ofSeconds(2))
            .seed(3)
            .onSolution(x -> costs.add(total.value()))
            .build();
    assertEquals(LocalSearch.Status.SATISFIED, ls.solve());
    int[][] start = starts(ls, s);
    checkedMakespan(start);
    int sum = 0;
    for (int j = 0; j < s.length; j++) {
      sum += start[j][5] + FT06_DURATION[j][5];
    }
    assertEquals(sum, ls.getCostValue());
    for (int k = 1; k < costs.size(); k++) {
      assertTrue(costs.get(k) < costs.get(k - 1), costs.toString());
    }
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

  /**
   * A table violation is the Hamming distance to the nearest tuple, and a key column, all of whose
   * values differ, determines the other columns.
   */
  @Test
  void tableDistanceAndKey() {
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 9);
    }
    int[][] tuples = {{1, 5, 5}, {2, 5, 6}, {3, 7, 7}};
    HybridTable t = new HybridTable(x, tuples);
    int[][] cases = {{1, 5, 5}, {1, 5, 6}, {1, 6, 6}, {9, 9, 9}, {3, 5, 7}};
    for (int[] v : cases) {
      long expected = Long.MAX_VALUE;
      for (int[] tuple : tuples) {
        long d = 0;
        for (int i = 0; i < v.length; i++) {
          d += v[i] == tuple[i] ? 0 : 1;
        }
        expected = Math.min(expected, d);
      }
      List<IntVar> vars = Arrays.asList(x);
      assertEquals(expected, t.violation(y -> v[vars.indexOf(y)]), Arrays.toString(v));
    }
    assertEquals(0, t.keyColumn());
    assertEquals(6, t.keyedValue(2, 2, -1));
    assertEquals(-1, t.keyedValue(2, 4, -1));
    // no column of distinct values
    assertEquals(-1, new HybridTable(x, new int[][] {{1, 5, 5}, {1, 6, 6}, {2, 5, 6}}).keyColumn());
  }

  /**
   * The columns of a table with a key follow the key, and the table is not evaluated; local search
   * moves only the keys (a car sequencing model in miniature: the options of a car follow its
   * class).
   */
  @Test
  void tableColumnsFollowTheKey() {
    for (boolean keys : new boolean[] {true, false}) {
      Store store = new Store();
      int[][] options = {{1, 1, 0}, {2, 0, 1}, {3, 1, 1}, {4, 0, 0}};
      IntVar[] cls = new IntVar[8];
      IntVar[] a = new IntVar[cls.length];
      IntVar[] b = new IntVar[cls.length];
      List<IntVar> defined = new ArrayList<>();
      for (int i = 0; i < cls.length; i++) {
        cls[i] = new IntVar(store, "c" + i, 1, 4);
        a[i] = new IntVar(store, "a" + i, 0, 1);
        b[i] = new IntVar(store, "b" + i, 0, 1);
        store.impose(new HybridTable(new IntVar[] {cls[i], a[i], b[i]}, options));
      }
      // two cars of each class
      store.impose(
          new CountValuesBounds(
              cls, new int[] {2, 2, 2, 2}, new int[] {2, 2, 2, 2}, new int[] {1, 2, 3, 4}));
      // at most one car with option a and one with option b in any two consecutive
      for (int i = 0; i + 1 < cls.length; i++) {
        store.impose(new LinearInt(new IntVar[] {a[i], a[i + 1]}, new int[] {1, 1}, "<=", 1));
        store.impose(new LinearInt(new IntVar[] {b[i], b[i + 1]}, new int[] {1, 1}, "<=", 1));
      }
      assertTrue(store.consistency());
      LocalSearch ls =
          LocalSearch.builder(store)
              .order(cls)
              .defined(defined)
              .tableKeys(keys)
              .timeLimit(LIMIT)
              .seed(1)
              .build();
      assertEquals(LocalSearch.Status.SATISFIED, ls.solve(), ls.toString());
      assertEquals(keys, ls.toString().contains("K:HybridTable=8"), ls.toString());
      int[] c = ls.getSolution(cls);
      int[] count = new int[5];
      for (int i = 0; i < c.length; i++) {
        count[c[i]]++;
        if (i > 0) {
          assertTrue(options[c[i] - 1][1] + options[c[i - 1] - 1][1] <= 1, Arrays.toString(c));
          assertTrue(options[c[i] - 1][2] + options[c[i - 1] - 1][2] <= 1, Arrays.toString(c));
        }
      }
      assertArrayEquals(new int[] {0, 2, 2, 2, 2}, count);
    }
  }

  /**
   * The value counter of a global cardinality keeps the sum of the counts out of their bounds, and
   * the change by a move, equal to counting again.
   */
  @Test
  void cardinalityCounter() {
    java.util.Random random = new java.util.Random(7);
    for (int trial = 0; trial < 200; trial++) {
      int n = 1 + random.nextInt(8);
      int[][] bounds = new int[3][];
      for (int k = 0; k < bounds.length; k++) {
        int low = random.nextInt(3);
        bounds[k] = new int[] {k, low, low + random.nextInt(3)};
      }
      LocalSearch.Counter counter = new LocalSearch.Counter(bounds);
      int[] v = new int[n];
      counter.clear();
      for (int i = 0; i < n; i++) {
        v[i] = random.nextInt(5);
        counter.add(v[i]);
      }
      for (int move = 0; move < 20; move++) {
        assertEquals(cardinalityViolation(v, bounds), counter.duplicates);
        int i = random.nextInt(n);
        int w = random.nextInt(5);
        long after = counter.after(v[i], w);
        counter.remove(v[i]);
        counter.add(w);
        v[i] = w;
        assertEquals(cardinalityViolation(v, bounds), after);
      }
    }
  }

  private static long cardinalityViolation(int[] v, int[][] bounds) {
    long violation = 0;
    for (int[] b : bounds) {
      int c = (int) Arrays.stream(v).filter(x -> x == b[0]).count();
      violation += Math.max(0, b[1] - c) + Math.max(0, c - b[2]);
    }
    return violation;
  }
}
