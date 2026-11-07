/*
 * FlowSumsTest.java
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

package org.jacop.constraints;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Checks {@link FlowSums}: Landau's condition on a small tournament, an elimination that only the
 * flow sees, the bounds of the totals against the integer points of the relaxation enumerated by
 * brute force, and the solutions of random graphs against the decomposition into sums, found by a
 * search in random order.
 *
 * <p>The number of random graphs is set by {@code flowsums.trials} (default 3000).
 */
class FlowSumsTest {

  private static final int TRIALS = Integer.getInteger("flowsums.trials", 3000);

  // three teams, each pair plays once, one point per game: the scores (2, 2, 0) are impossible
  // since the two teams on 2 points play each other (Landau: the two best take at most 3)
  @Test
  void landauConditionFails() {
    Store store = new Store();
    int[][] games = {{0, 1}, {0, 2}, {1, 2}};
    IntVar[] x = new IntVar[6];
    int[] left = new int[6];
    int[] right = new int[6];
    FlowSums.Node[] gameNodes = new FlowSums.Node[3];
    for (int g = 0; g < 3; g++) {
      gameNodes[g] = FlowSums.Node.of(1, 1);
      for (int k = 0; k < 2; k++) {
        x[2 * g + k] = new IntVar(store, "p" + g + "_" + k, 0, 1);
        left[2 * g + k] = g;
        right[2 * g + k] = games[g][k];
      }
    }
    IntVar[] score = new IntVar[3];
    FlowSums.Node[] teams = new FlowSums.Node[3];
    for (int t = 0; t < 3; t++) {
      score[t] = new IntVar(store, "s" + t, 0, 2);
      teams[t] = FlowSums.Node.of(score[t], 0);
    }
    store.impose(new FlowSums(x, left, right, gameNodes, teams));
    assertThat(store.consistency()).isTrue();
    store.setLevel(1);
    score[0].domain.inValue(1, score[0], 2);
    score[1].domain.inValue(1, score[1], 2);
    // the plain sums allow it until the games are decided; the flow does not
    assertThat(store.consistency()).isFalse();
  }

  // four teams with 10, 9, 9 and 6 points, three points a win and one each for a draw; teams 0, 1
  // and 2 play each other once and team 3 once each. With teams 0, 1 and 2 kept at 12 or less they
  // can take 2 + 3 + 3 = 8 more points, but their own three games give out at least 6, so they take
  // at most 2 from the games against team 3, which give out at least 6: team 3 ends on at least 10,
  // where the sum of its own games alone gives 6
  @Test
  void eliminationBoundsTotal() {
    Store store = new Store();
    int[] initial = {10, 9, 9, 6};
    int[][] games = {{0, 1}, {0, 2}, {1, 2}, {3, 0}, {3, 1}, {3, 2}};
    int n = games.length;
    IntVar[] x = new IntVar[2 * n];
    int[] left = new int[2 * n];
    int[] right = new int[2 * n];
    FlowSums.Node[] gameNodes = new FlowSums.Node[n];
    for (int g = 0; g < n; g++) {
      gameNodes[g] = FlowSums.Node.of(2, 3);
      for (int k = 0; k < 2; k++) {
        IntVar p = new IntVar(store, "p" + g + "_" + k, 0, 1);
        p.addDom(3, 3);
        x[2 * g + k] = p;
        left[2 * g + k] = g;
        right[2 * g + k] = games[g][k];
      }
    }
    IntVar[] score = new IntVar[4];
    FlowSums.Node[] teams = new FlowSums.Node[4];
    for (int t = 0; t < 4; t++) {
      score[t] = new IntVar(store, "s" + t, initial[t], initial[t] + 9);
      teams[t] = FlowSums.Node.of(score[t], -initial[t]);
    }
    store.impose(new FlowSums(x, left, right, gameNodes, teams));
    assertThat(store.consistency()).isTrue();
    assertThat(score[3].min()).isEqualTo(6);
    store.setLevel(1);
    for (int t = 0; t < 3; t++) {
      score[t].domain.in(1, score[t], score[t].min(), 12);
    }
    assertThat(store.consistency()).isTrue();
    assertThat(score[3].min()).isEqualTo(10);
    assertThat(score[3].max()).isEqualTo(15);
    store.removeLevel(1);
    store.setLevel(0);
    assertThat(score[3].min()).isEqualTo(6);
    // capped at 10, they can take only 2 more points from games that give out at least 6
    store.setLevel(1);
    for (int t = 0; t < 3; t++) {
      score[t].domain.in(1, score[t], score[t].min(), 10);
    }
    assertThat(store.consistency()).isFalse();
  }

  // ---- random graphs

  private static final class Instance {
    final Store store = new Store();
    final List<IntVar> vars = new ArrayList<>();
    IntVar[] x;
    int[] left;
    int[] right;
    FlowSums.Node[] leftNodes;
    FlowSums.Node[] rightNodes;

    Instance(long seed, boolean holes) {
      Random rnd = new Random(seed);
      int nl = 1 + rnd.nextInt(3);
      int nr = 1 + rnd.nextInt(3);
      List<int[]> edges = new ArrayList<>();
      for (int i = 0; i < nl; i++) {
        for (int j = 0; j < nr; j++) {
          int k = rnd.nextInt(10) < 6 ? 1 : rnd.nextInt(10) < 3 ? 2 : 0;
          for (int c = 0; c < k; c++) {
            edges.add(new int[] {i, j});
          }
        }
      }
      if (rnd.nextInt(4) == 0) {
        edges.add(new int[] {rnd.nextInt(nl), -1});
      }
      if (rnd.nextInt(4) == 0) {
        edges.add(new int[] {-1, rnd.nextInt(nr)});
      }
      // every node has an edge
      for (int i = 0; i < nl; i++) {
        final int node = i;
        if (edges.stream().noneMatch(e -> e[0] == node)) {
          edges.add(new int[] {i, rnd.nextInt(nr)});
        }
      }
      for (int j = 0; j < nr; j++) {
        final int node = j;
        if (edges.stream().noneMatch(e -> e[1] == node)) {
          edges.add(new int[] {rnd.nextInt(nl), j});
        }
      }
      int m = edges.size();
      x = new IntVar[m];
      left = new int[m];
      right = new int[m];
      int[] lmax = new int[nl];
      int[] rmax = new int[nr];
      for (int e = 0; e < m; e++) {
        int lo = rnd.nextInt(4) == 0 ? -1 : 0;
        int hi = lo + 1 + rnd.nextInt(3);
        x[e] = var("x" + e, lo, hi);
        if (holes && hi - lo >= 2 && rnd.nextBoolean()) {
          x[e].domain.subtractAdapt(lo + 1);
          x[e].refreshBounds();
        }
        left[e] = edges.get(e)[0];
        right[e] = edges.get(e)[1];
        if (left[e] >= 0) {
          lmax[left[e]] += hi;
        }
        if (right[e] >= 0) {
          rmax[right[e]] += hi;
        }
      }
      leftNodes = nodes(rnd, "l", lmax);
      rightNodes = nodes(rnd, "r", rmax);
    }

    private FlowSums.Node[] nodes(Random rnd, String name, int[] max) {
      FlowSums.Node[] result = new FlowSums.Node[max.length];
      for (int i = 0; i < max.length; i++) {
        int a = rnd.nextInt(max[i] + 2) - 1;
        int b = a + rnd.nextInt(4);
        switch (rnd.nextInt(3)) {
          case 0 -> result[i] = FlowSums.Node.of(a, b);
          case 1 -> {
            int offset = rnd.nextInt(3) - 1;
            result[i] = FlowSums.Node.of(var(name + i, a - offset, b + 1 - offset), offset);
          }
          default -> {
            int offset = rnd.nextInt(3) - 1;
            result[i] =
                new FlowSums.Node(
                    var(name + i, a - 1 - offset, b + 2 - offset),
                    offset,
                    rnd.nextBoolean() ? a : Integer.MIN_VALUE,
                    b);
          }
        }
      }
      return result;
    }

    private IntVar var(String name, int min, int max) {
      IntVar v = new IntVar(store, name, min, max);
      vars.add(v);
      return v;
    }

    void decomposition() {
      int nl = leftNodes.length;
      List<List<IntVar>> members = new ArrayList<>();
      for (int i = 0; i < nl + rightNodes.length; i++) {
        members.add(new ArrayList<>());
      }
      for (int e = 0; e < x.length; e++) {
        if (left[e] >= 0) {
          members.get(left[e]).add(x[e]);
        }
        if (right[e] >= 0) {
          members.get(nl + right[e]).add(x[e]);
        }
      }
      for (int i = 0; i < members.size(); i++) {
        FlowSums.Node node = i < nl ? leftNodes[i] : rightNodes[i - nl];
        List<IntVar> s = members.get(i);
        IntVar[] terms = s.toArray(IntVar[]::new);
        int[] ones = new int[terms.length];
        java.util.Arrays.fill(ones, 1);
        if (node.min() != Integer.MIN_VALUE) {
          store.impose(new LinearInt(terms, ones, ">=", node.min()));
        }
        if (node.max() != Integer.MAX_VALUE) {
          store.impose(new LinearInt(terms, ones, "<=", node.max()));
        }
        if (node.total() != null) {
          IntVar[] t = java.util.Arrays.copyOf(terms, terms.length + 1);
          t[terms.length] = node.total();
          int[] c = java.util.Arrays.copyOf(ones, ones.length + 1);
          c[ones.length] = -1;
          store.impose(new LinearInt(t, c, "==", node.offset()));
        }
      }
    }

    FlowSums post() {
      FlowSums c = new FlowSums(x, left, right, leftNodes, rightNodes);
      store.impose(c);
      return c;
    }

    IntVar[] all() {
      return vars.toArray(IntVar[]::new);
    }
  }

  private static int count(Instance in, long seed) {
    if (!in.store.consistency()) {
      return 0;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    SimpleSelect<IntVar> select =
        new SimpleSelect<>(in.all(), null, new IndomainRandom<>((int) seed));
    search.labeling(in.store, select);
    return search.getSolutionListener().solutionsNo();
  }

  @Test
  void solutionsMatchDecomposition() {
    int nonEmpty = 0;
    for (int t = 0; t < TRIALS; t++) {
      long seed = 1 + t;
      Instance reference = new Instance(seed, true);
      reference.decomposition();
      int expected = count(reference, seed);
      Instance alone = new Instance(seed, true);
      alone.post();
      // FlowSums alone, without the sums, must accept exactly the same assignments
      assertThat(count(alone, seed + 7)).as("seed %d alone", seed).isEqualTo(expected);
      Instance both = new Instance(seed, true);
      both.decomposition();
      both.post();
      assertThat(count(both, seed + 13)).as("seed %d with sums", seed).isEqualTo(expected);
      if (expected > 0) {
        nonEmpty++;
      }
    }
    assertThat(nonEmpty).isGreaterThan(TRIALS / 10);
  }

  // the root bounds of every variable against the integer points of the relaxation (interval
  // domains): each total gets exactly its least and greatest value, and no edge loses one
  @Test
  void rootBoundsAreExactForTotals() {
    int narrowed = 0;
    for (int t = 0; t < TRIALS; t++) {
      long seed = 100_000 + t;
      Instance in = new Instance(seed, false);
      int[][] range = range(new Instance(seed, false));
      in.post();
      boolean ok = in.store.consistency();
      IntVar[] all = in.all();
      if (range == null) {
        assertThat(ok).as("seed %d: no point, so it fails", seed).isFalse();
        continue;
      }
      assertThat(ok).as("seed %d: a point exists", seed).isTrue();
      for (int k = 0; k < all.length; k++) {
        IntVar v = all[k];
        assertThat(v.min()).as("seed %d %s min", seed, v.id()).isLessThanOrEqualTo(range[k][0]);
        assertThat(v.max()).as("seed %d %s max", seed, v.id()).isGreaterThanOrEqualTo(range[k][1]);
        if (!v.id().startsWith("x")) {
          assertThat(v.min()).as("seed %d %s min exact", seed, v.id()).isEqualTo(range[k][0]);
          assertThat(v.max()).as("seed %d %s max exact", seed, v.id()).isEqualTo(range[k][1]);
        }
      }
      for (int k = 0; k < all.length; k++) {
        if (all[k].min() > new Instance(seed, false).all()[k].min()
            || all[k].max() < new Instance(seed, false).all()[k].max()) {
          narrowed++;
          break;
        }
      }
    }
    assertThat(narrowed).isGreaterThan(TRIALS / 20);
  }

  // the least and greatest value of each variable over the solutions of the sums, by search
  private static int[][] range(Instance in) {
    in.decomposition();
    if (!in.store.consistency()) {
      return null;
    }
    IntVar[] all = in.all();
    int[][] range = new int[all.length][];
    for (int k = 0; k < all.length; k++) {
      range[k] = new int[] {Integer.MAX_VALUE, Integer.MIN_VALUE};
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(true);
    boolean found = search.labeling(in.store, new SimpleSelect<>(all, null, new IndomainMin<>()));
    if (!found) {
      return null;
    }
    for (int s = 1; s <= search.getSolutionListener().solutionsNo(); s++) {
      for (int k = 0; k < all.length; k++) {
        int v = ((org.jacop.core.IntDomain) search.getSolutionListener().getSolution(s)[k]).value();
        range[k][0] = Math.min(range[k][0], v);
        range[k][1] = Math.max(range[k][1], v);
      }
    }
    return range;
  }
}
