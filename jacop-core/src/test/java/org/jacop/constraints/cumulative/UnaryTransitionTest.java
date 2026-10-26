/*
 * UnaryTransitionTest.java
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

package org.jacop.constraints.cumulative;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/**
 * Checks {@link UnaryTransition} against brute-force enumeration on random small instances with
 * holes in the start domains, variable and zero durations, families and transitions that need not
 * satisfy the triangle inequality, with each rule on its own and all together. It also checks that
 * each rule prunes more than the pairs on some instances, and the bounds tt(k).
 */
class UnaryTransitionTest {

  /** Random instances per rule set; the {@code min} profile lowers it. */
  private static final int TRIALS = Integer.getInteger("unary.transition.trials", 400);

  private static final long MAX_TUPLES = 200_000;

  private static final int ALL =
      UnaryTransition.OVERLOAD
          | UnaryTransition.DETECTABLE
          | UnaryTransition.NOT_LAST
          | UnaryTransition.EDGE_FIND;

  private static final int[] RULE_SETS = {
    0,
    UnaryTransition.OVERLOAD,
    UnaryTransition.DETECTABLE,
    UnaryTransition.NOT_LAST,
    UnaryTransition.EDGE_FIND,
    ALL
  };

  /** One random instance: start domains, duration bounds, families and their transitions. */
  private record Instance(int[][] starts, int[][] durations, int[] family, int[][] tt) {

    int n() {
      return starts.length;
    }

    IntVar[] post(Store store, int rules) {
      int n = n();
      IntVar[] s = new IntVar[n];
      IntVar[] d = new IntVar[n];
      for (int i = 0; i < n; i++) {
        s[i] = new IntVar(store, "s" + i);
        for (int v : starts[i]) {
          s[i].addDom(v, v);
        }
        d[i] = new IntVar(store, "d" + i, durations[i][0], durations[i][1]);
      }
      UnaryTransition c = new UnaryTransition(s, d, family, tt);
      c.rules = rules;
      store.impose(c);
      IntVar[] all = Arrays.copyOf(s, 2 * n);
      System.arraycopy(d, 0, all, n, n);
      return all;
    }

    boolean satisfied(int[] x) {
      int n = n();
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          if (x[i] + x[n + i] + tt[family[i]][family[j]] > x[j]
              && x[j] + x[n + j] + tt[family[j]][family[i]] > x[i]) {
            return false;
          }
        }
      }
      return true;
    }

    long tuples() {
      long t = 1;
      for (int i = 0; i < n(); i++) {
        t *= starts[i].length * (long) (durations[i][1] - durations[i][0] + 1);
      }
      return t;
    }

    @Override
    public String toString() {
      return "starts="
          + Arrays.deepToString(starts)
          + " durations="
          + Arrays.deepToString(durations)
          + " family="
          + Arrays.toString(family)
          + " tt="
          + Arrays.deepToString(tt);
    }
  }

  private static Instance instance(Random random, int maxTasks, int horizon) {
    while (true) {
      int n = 2 + random.nextInt(maxTasks - 1);
      int families = 1 + random.nextInt(Math.min(n, 4));
      int[][] starts = new int[n][];
      int[][] durations = new int[n][];
      int[] family = new int[n];
      for (int i = 0; i < n; i++) {
        int lo = random.nextInt(horizon / 2);
        int hi = lo + random.nextInt(horizon - lo + 1);
        List<Integer> values = new ArrayList<>();
        for (int v = lo; v <= hi; v++) {
          if (v == lo || v == hi || random.nextInt(4) > 0) {
            values.add(v);
          }
        }
        starts[i] = values.stream().mapToInt(Integer::intValue).toArray();
        int dmin = random.nextInt(4) == 0 ? 0 : 1 + random.nextInt(3);
        int dmax = random.nextBoolean() ? dmin : dmin + random.nextInt(3);
        durations[i] = new int[] {dmin, dmax};
        family[i] = random.nextInt(families);
      }
      int[][] tt = new int[families][families];
      int maxT = 1 + random.nextInt(5);
      for (int a = 0; a < families; a++) {
        for (int b = 0; b < families; b++) {
          tt[a][b] = a == b && random.nextInt(3) > 0 ? 0 : random.nextInt(maxT + 1);
        }
      }
      Instance instance = new Instance(starts, durations, family, tt);
      if (instance.tuples() <= MAX_TUPLES) {
        return instance;
      }
    }
  }

  private static void bruteForce(Instance instance, int[] x, int k, Set<List<Integer>> solutions) {
    int n = instance.n();
    if (k == 2 * n) {
      if (instance.satisfied(x)) {
        solutions.add(Arrays.stream(x).boxed().toList());
      }
      return;
    }
    if (k < n) {
      for (int v : instance.starts[k]) {
        x[k] = v;
        bruteForce(instance, x, k + 1, solutions);
      }
    } else {
      for (int v = instance.durations[k - n][0]; v <= instance.durations[k - n][1]; v++) {
        x[k] = v;
        bruteForce(instance, x, k + 1, solutions);
      }
    }
  }

  private static Set<List<Integer>> solveAll(Instance instance, int rules, int seed) {
    Store store = new Store();
    IntVar[] x = instance.post(store, rules);
    Set<List<Integer>> found = new HashSet<>();
    if (!store.consistency()) {
      return found;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            found.add(Arrays.stream(x).map(IntVar::value).toList());
            return result;
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, new SimpleSelect<>(x, null, new IndomainRandom<>(seed)));
    return found;
  }

  @Test
  void solutionsMatchBruteForce() {
    Random random = new Random(20261026);
    for (int trial = 0; trial < TRIALS; trial++) {
      Instance instance = instance(random, 5, 10);
      Set<List<Integer>> expected = new HashSet<>();
      bruteForce(instance, new int[2 * instance.n()], 0, expected);
      for (int rules : RULE_SETS) {
        Set<List<Integer>> found = solveAll(instance, rules, random.nextInt());
        assertThat(found).as("trial %d rules %d %s", trial, rules, instance).isEqualTo(expected);
      }
    }
  }

  /** Each rule keeps a subset of what the pairs keep, and removes more on some instances. */
  @Test
  void rulesPruneMoreThanPairs() {
    Random random = new Random(7);
    int[] stronger = new int[RULE_SETS.length];
    for (int trial = 0; trial < 3000; trial++) {
      Instance instance = instance(random, 8, 14);
      List<Set<Integer>> base = rootDomains(instance, 0);
      for (int k = 1; k < RULE_SETS.length; k++) {
        List<Set<Integer>> with = rootDomains(instance, RULE_SETS[k]);
        if (base == null) {
          assertThat(with).as("rules %d %s", RULE_SETS[k], instance).isNull();
        } else if (!base.equals(with)) {
          if (with != null) {
            for (int v = 0; v < base.size(); v++) {
              assertThat(base.get(v))
                  .as("rules %d %s", RULE_SETS[k], instance)
                  .containsAll(with.get(v));
            }
          }
          stronger[k]++;
        }
      }
    }
    for (int k = 1; k < RULE_SETS.length; k++) {
      assertThat(stronger[k])
          .as("rules %d %s", RULE_SETS[k], Arrays.toString(stronger))
          .isPositive();
    }
  }

  private static List<Set<Integer>> rootDomains(Instance instance, int rules) {
    Store store = new Store();
    IntVar[] x = instance.post(store, rules);
    if (!store.consistency()) {
      return null;
    }
    List<Set<Integer>> result = new ArrayList<>();
    for (IntVar v : x) {
      Set<Integer> values = new HashSet<>();
      for (var e = v.dom().valueEnumeration(); e.hasMoreElements(); ) {
        values.add(e.nextElement());
      }
      result.add(values);
    }
    return result;
  }

  /**
   * Three tasks of length 1 from three families with transitions 5 need 13 time units; each pair
   * fits in [0, 9), so only the overload check sees it.
   */
  @Test
  void overloadCountsTransitions() {
    for (int rules : new int[] {0, UnaryTransition.OVERLOAD}) {
      Store store = new Store();
      IntVar[] s = new IntVar[3];
      IntVar[] d = new IntVar[3];
      for (int i = 0; i < 3; i++) {
        s[i] = new IntVar(store, 0, 8);
        d[i] = new IntVar(store, 1, 1);
      }
      int[][] tt = {{0, 5, 5}, {5, 0, 5}, {5, 5, 0}};
      UnaryTransition c = new UnaryTransition(s, d, new int[] {0, 1, 2}, tt);
      c.rules = rules;
      store.impose(c);
      assertThat(store.consistency()).as("rules %d", rules).isEqualTo(rules == 0);
    }
  }

  /** Tasks with the same transitions and none between them form one family. */
  @Test
  void tasksWithEqualTransitionsShareFamily() {
    int[][] tt = {
      {0, 0, 3, 4},
      {0, 0, 3, 4},
      {2, 2, 0, 1},
      {5, 5, 1, 0}
    };
    assertThat(UnaryTransition.families(tt)).containsExactly(0, 0, 1, 2);
    int[][] other = {
      {0, 1, 3},
      {0, 0, 3},
      {2, 2, 0}
    };
    assertThat(UnaryTransition.families(other)).containsExactly(0, 1, 2);
  }

  /**
   * The exact bounds are the cheapest paths over k distinct families; the forest and walk bounds
   * are below them; all are superadditive, tt(a + b - 1) &gt;= tt(a) + tt(b), and monotone.
   */
  @Test
  void transitionBounds() {
    Random random = new Random(3);
    for (int trial = 0; trial < 500; trial++) {
      int f = 2 + random.nextInt(6);
      int[][] tt = new int[f][f];
      for (int a = 0; a < f; a++) {
        for (int b = 0; b < f; b++) {
          tt[a][b] = a == b ? 0 : random.nextInt(20);
        }
      }
      long[] exact = UnaryTransition.familyBounds(tt);
      long[] reference = cheapestPaths(tt);
      for (int k = 0; k <= f; k++) {
        assertThat(exact[k]).as("k %d %s", k, Arrays.deepToString(tt)).isEqualTo(reference[k]);
      }
      for (long[] bound :
          List.of(exact, UnaryTransition.forestBounds(tt), UnaryTransition.walkBounds(tt))) {
        for (int k = 1; k <= f; k++) {
          assertThat(bound[k]).isLessThanOrEqualTo(reference[k]);
          assertThat(bound[k]).isGreaterThanOrEqualTo(bound[k - 1]);
          for (int a = 1; a <= k; a++) {
            int b = k + 1 - a;
            assertThat(bound[k])
                .as("%s", Arrays.deepToString(tt))
                .isGreaterThanOrEqualTo(bound[a] + bound[b]);
          }
        }
      }
    }
  }

  // tt(k) by enumerating the orders of every set of k families, with shortest paths as distances
  private static long[] cheapestPaths(int[][] tt) {
    int f = tt.length;
    long[][] dist = new long[f][f];
    for (int a = 0; a < f; a++) {
      for (int b = 0; b < f; b++) {
        dist[a][b] = tt[a][b];
      }
    }
    for (int c = 0; c < f; c++) {
      for (int a = 0; a < f; a++) {
        for (int b = 0; b < f; b++) {
          dist[a][b] = Math.min(dist[a][b], dist[a][c] + dist[c][b]);
        }
      }
    }
    long[] best = new long[f + 1];
    Arrays.fill(best, Long.MAX_VALUE);
    best[0] = 0;
    permutations(dist, new int[f], new boolean[f], 0, 0, best);
    return best;
  }

  private static void permutations(
      long[][] dist, int[] order, boolean[] used, int k, long cost, long[] best) {
    if (k > 0) {
      best[k] = Math.min(best[k], cost);
    }
    for (int a = 0; a < dist.length; a++) {
      if (!used[a]) {
        used[a] = true;
        order[k] = a;
        permutations(dist, order, used, k + 1, k == 0 ? 0 : cost + dist[order[k - 1]][a], best);
        used[a] = false;
      }
    }
  }
}
