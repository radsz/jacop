/*
 * MultiCumulativeTest.java
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
package org.jacop;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.MultiCumulative;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/**
 * Checks {@link MultiCumulative} against one time-table {@link Cumulative} per resource (the same
 * domains after every decision of random dives) and against enumeration (the same solutions, also
 * with the cumulative constraints that keep only their energy rules, as the FlatZinc front end
 * posts them after {@link MultiCumulative#merge}).
 */
class MultiCumulativeTest {

  /** Random instances; the {@code min} profile lowers it. */
  private static final int TRIALS = Integer.getInteger("multicumulative.trials", 300);

  /** Random tasks over several resources; heights[r][i] may be 0. */
  private record Instance(int[][] starts, int[] dur, int[][] heights, int[][] limits) {

    int n() {
      return dur.length;
    }

    boolean satisfied(int[] s, int[] l) {
      for (int r = 0; r < heights.length; r++) {
        for (int t = 0; t < 40; t++) {
          int use = 0;
          for (int i = 0; i < n(); i++) {
            if (s[i] <= t && t < s[i] + dur[i]) {
              use += heights[r][i];
            }
          }
          if (use > l[r]) {
            return false;
          }
        }
      }
      return true;
    }

    @Override
    public String toString() {
      return "starts="
          + Arrays.deepToString(starts)
          + " dur="
          + Arrays.toString(dur)
          + " heights="
          + Arrays.deepToString(heights)
          + " limits="
          + Arrays.deepToString(limits);
    }
  }

  private static Instance random(Random rnd) {
    int n = 2 + rnd.nextInt(4);
    int m = 2 + rnd.nextInt(2);
    int[][] starts = new int[n][];
    int[] dur = new int[n];
    for (int i = 0; i < n; i++) {
      int lo = rnd.nextInt(6);
      int hi = lo + rnd.nextInt(7);
      starts[i] = values(rnd, lo, hi);
      dur[i] = rnd.nextInt(10) == 0 ? 0 : 1 + rnd.nextInt(5);
    }
    int[][] heights = new int[m][n];
    int[][] limits = new int[m][];
    for (int r = 0; r < m; r++) {
      for (int i = 0; i < n; i++) {
        heights[r][i] = rnd.nextInt(3) == 0 ? 0 : 1 + rnd.nextInt(4);
      }
      int lo = 1 + rnd.nextInt(5);
      limits[r] = rnd.nextInt(3) == 0 ? values(rnd, lo, lo + 3) : new int[] {lo};
    }
    return new Instance(starts, dur, heights, limits);
  }

  // the values lo..hi with some holes, never empty
  private static int[] values(Random rnd, int lo, int hi) {
    List<Integer> v = new ArrayList<>();
    for (int x = lo; x <= hi; x++) {
      if (x == lo || rnd.nextInt(4) != 0) {
        v.add(x);
      }
    }
    return v.stream().mapToInt(Integer::intValue).toArray();
  }

  private record Model(Store store, IntVar[] starts, IntVar[] limits, IntVar[] all) {}

  private static IntVar var(Store store, String name, int[] values) {
    IntervalDomain d = new IntervalDomain();
    for (int v : values) {
      d.unionAdapt(v, v);
    }
    return new IntVar(store, name, d);
  }

  /**
   * kind 0: MultiCumulative; 1: one time-table Cumulative per resource; 2: MultiCumulative with the
   * cumulative constraints that keep their other rules.
   */
  private static Model model(Instance in, int kind) {
    Store store = new Store();
    int n = in.n();
    int m = in.heights().length;
    IntVar[] s = new IntVar[n];
    for (int i = 0; i < n; i++) {
      s[i] = var(store, "s" + i, in.starts()[i]);
    }
    IntVar[] l = new IntVar[m];
    for (int r = 0; r < m; r++) {
      l[r] = var(store, "l" + r, in.limits()[r]);
    }
    List<Constraint> cs = new ArrayList<>();
    for (int r = 0; r < m && kind != 0; r++) {
      IntVar[] d = new IntVar[n];
      IntVar[] h = new IntVar[n];
      for (int i = 0; i < n; i++) {
        d[i] = new IntVar(store, in.dur()[i], in.dur()[i]);
        h[i] = new IntVar(store, in.heights()[r][i], in.heights()[r][i]);
      }
      Cumulative c = new Cumulative(s, d, h, l[r]);
      boolean other = kind == 2;
      c.doEdgeFind(other);
      c.doOverload(other);
      c.doTimeTableEdgeFind(other);
      c.doTimeTableDisjunctive(other);
      cs.add(c);
    }
    if (kind == 2) {
      List<Constraint> merged = MultiCumulative.merge(cs);
      assertThat(merged).hasSize(cs.size() + 1);
      assertThat(merged.get(merged.size() - 1)).isInstanceOf(MultiCumulative.class);
      cs = merged;
    } else if (kind == 0) {
      cs.add(new MultiCumulative(s, in.dur(), in.heights(), l));
    }
    for (Constraint c : cs) {
      store.impose(c);
    }
    IntVar[] all = new IntVar[n + m];
    System.arraycopy(s, 0, all, 0, n);
    System.arraycopy(l, 0, all, n, m);
    return new Model(store, s, l, all);
  }

  @Test
  void prunesAsOneTimeTablePerResource() {
    Random rnd = new Random(1);
    for (int trial = 0; trial < TRIALS; trial++) {
      Instance in = random(rnd);
      Model a = model(in, 0);
      Model b = model(in, 1);
      boolean okA = a.store().consistency();
      boolean okB = b.store().consistency();
      assertThat(okA).as("root of %s", in).isEqualTo(okB);
      List<String> path = new ArrayList<>();
      while (okA && !singleton(a.all())) {
        int i = rnd.nextInt(a.all().length);
        IntVar x = a.all()[i];
        if (x.singleton()) {
          continue;
        }
        int v = x.min() + rnd.nextInt(x.max() - x.min() + 1);
        int op = rnd.nextInt(3);
        path.add(x.id() + (op == 0 ? "<=" : op == 1 ? ">=" : "!=") + v);
        a.store().setLevel(a.store().level + 1);
        b.store().setLevel(b.store().level + 1);
        try {
          a.store().impose(decision(x, op, v));
          b.store().impose(decision(b.all()[i], op, v));
        } catch (org.jacop.core.FailException e) {
          break;
        }
        okA = a.store().consistency();
        okB = b.store().consistency();
        assertThat(okA).as("%s after %s", in, path).isEqualTo(okB);
        if (okA) {
          for (int k = 0; k < a.all().length; k++) {
            assertThat(a.all()[k].dom().toString())
                .as("%s of %s after %s", a.all()[k].id(), in, path)
                .isEqualTo(b.all()[k].dom().toString());
          }
        }
      }
    }
  }

  private static Constraint decision(IntVar x, int op, int v) {
    return switch (op) {
      case 0 -> new XlteqC(x, v);
      case 1 -> new XgteqC(x, v);
      default -> new XneqC(x, v);
    };
  }

  private static boolean singleton(IntVar[] xs) {
    return Arrays.stream(xs).allMatch(IntVar::singleton);
  }

  @Test
  void findsTheSolutionsOfTheResources() {
    Random rnd = new Random(2);
    for (int trial = 0; trial < TRIALS; trial++) {
      Instance in = random(rnd);
      Set<List<Integer>> expected = enumerate(in);
      for (int kind : new int[] {0, 2}) {
        assertThat(solveAll(model(in, kind))).as("kind %d on %s", kind, in).isEqualTo(expected);
      }
    }
  }

  @Test
  void mergesOnlyCumulativesThatShareATaskThatIsNotFixed() {
    Store store = new Store();
    IntVar zero = new IntVar(store, 0, 0);
    IntVar a = new IntVar(store, "a", 0, 10);
    IntVar b = new IntVar(store, "b", 0, 10);
    IntVar c = new IntVar(store, "c", 0, 10);
    IntVar one = new IntVar(store, 1, 1);
    IntVar two = new IntVar(store, 2, 2);
    IntVar limit = new IntVar(store, 2, 2);
    // the first two share only the fixed start zero, the last two share b
    Constraint c1 =
        new Cumulative(
            new IntVar[] {zero, a}, new IntVar[] {two, two}, new IntVar[] {one, one}, limit);
    Constraint c2 =
        new Cumulative(
            new IntVar[] {zero, b}, new IntVar[] {two, two}, new IntVar[] {one, one}, limit);
    Constraint c3 =
        new Cumulative(
            new IntVar[] {b, c}, new IntVar[] {two, two}, new IntVar[] {one, two}, limit);
    List<Constraint> merged = MultiCumulative.merge(List.of(c1, c2, c3));
    assertThat(merged).hasSize(4);
    assertThat(merged.get(3)).isInstanceOf(MultiCumulative.class);
    assertThat(merged.get(3).arguments()).contains(b, c).doesNotContain(a);
  }

  private static Set<List<Integer>> enumerate(Instance in) {
    int n = in.n();
    int m = in.heights().length;
    int[][] doms = new int[n + m][];
    System.arraycopy(in.starts(), 0, doms, 0, n);
    System.arraycopy(in.limits(), 0, doms, n, m);
    Set<List<Integer>> result = new HashSet<>();
    int[] idx = new int[n + m];
    while (true) {
      int[] s = new int[n];
      int[] l = new int[m];
      for (int i = 0; i < n; i++) {
        s[i] = doms[i][idx[i]];
      }
      for (int r = 0; r < m; r++) {
        l[r] = doms[n + r][idx[n + r]];
      }
      if (in.satisfied(s, l)) {
        List<Integer> sol = new ArrayList<>();
        Arrays.stream(s).forEach(sol::add);
        Arrays.stream(l).forEach(sol::add);
        result.add(sol);
      }
      int k = 0;
      while (k < idx.length && ++idx[k] == doms[k].length) {
        idx[k++] = 0;
      }
      if (k == idx.length) {
        return result;
      }
    }
  }

  private static Set<List<Integer>> solveAll(Model model) {
    Set<List<Integer>> found = new HashSet<>();
    if (!model.store().consistency()) {
      return found;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            found.add(Arrays.stream(model.all()).map(IntVar::value).toList());
            return result;
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(model.store(), new SimpleSelect<>(model.all(), null, new IndomainMin<>()));
    return found;
  }
}
