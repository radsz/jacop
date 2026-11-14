/*
 * MultiObjectiveTest.java
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
 * preservation of specified reasonable legal notices and author attributions
 * in accordance with Section 7 of the GNU Affero General Public License.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.search;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Random;
import java.util.TreeSet;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Tests of {@link MultiObjective}: the lexicographic optimum and the Pareto front of random small
 * instances against a brute-force enumeration, in both directions of each objective.
 */
class MultiObjectiveTest {

  private static final int N = 5;
  private static final int MAX_VALUE = 3;
  private static final int TRIALS = 200;

  /** Binary constraints between five variables and two or three weighted-sum objectives. */
  private record Instance(int[][] neq, int[][] lt, int[][] weights, boolean[] maximize) {

    @Override
    public String toString() {
      return "neq "
          + Arrays.deepToString(neq)
          + ", lt "
          + Arrays.deepToString(lt)
          + ", weights "
          + Arrays.deepToString(weights)
          + ", maximize "
          + Arrays.toString(maximize);
    }

    @Override
    public boolean equals(Object o) {
      return o instanceof Instance i && toString().equals(i.toString());
    }

    @Override
    public int hashCode() {
      return toString().hashCode();
    }

    static Instance random(Random rnd) {
      List<int[]> neq = new ArrayList<>();
      List<int[]> lt = new ArrayList<>();
      for (int i = 0; i < N; i++) {
        for (int j = i + 1; j < N; j++) {
          int r = rnd.nextInt(10);
          if (r < 4) {
            neq.add(new int[] {i, j});
          } else if (r < 5) {
            lt.add(rnd.nextBoolean() ? new int[] {i, j} : new int[] {j, i});
          }
        }
      }
      int m = 2 + rnd.nextInt(2);
      int[][] weights = new int[m][N];
      boolean[] maximize = new boolean[m];
      for (int o = 0; o < m; o++) {
        for (int i = 0; i < N; i++) {
          weights[o][i] = rnd.nextInt(7) - 3;
        }
        maximize[o] = rnd.nextBoolean();
      }
      return new Instance(neq.toArray(new int[0][]), lt.toArray(new int[0][]), weights, maximize);
    }

    boolean satisfied(int[] x) {
      for (int[] c : neq) {
        if (x[c[0]] == x[c[1]]) {
          return false;
        }
      }
      for (int[] c : lt) {
        if (x[c[0]] >= x[c[1]]) {
          return false;
        }
      }
      return true;
    }

    int[] objectives(int[] x) {
      int[] v = new int[weights.length];
      for (int o = 0; o < v.length; o++) {
        for (int i = 0; i < N; i++) {
          v[o] += weights[o][i] * x[i];
        }
      }
      return v;
    }

    /** The objective vectors of all solutions. */
    List<int[]> enumerate() {
      List<int[]> all = new ArrayList<>();
      int[] x = new int[N];
      int total = (int) Math.pow(MAX_VALUE + 1.0, N);
      for (int c = 0; c < total; c++) {
        int r = c;
        for (int i = 0; i < N; i++) {
          x[i] = r % (MAX_VALUE + 1);
          r /= MAX_VALUE + 1;
        }
        if (satisfied(x)) {
          all.add(objectives(x));
        }
      }
      return all;
    }

    /** Orders objective vectors lexicographically, better first. */
    Comparator<int[]> lex() {
      return (a, b) -> {
        for (int o = 0; o < a.length; o++) {
          if (a[o] != b[o]) {
            return maximize[o] ? Integer.compare(b[o], a[o]) : Integer.compare(a[o], b[o]);
          }
        }
        return 0;
      };
    }

    boolean dominates(int[] a, int[] b) {
      boolean strictly = false;
      for (int o = 0; o < a.length; o++) {
        int d = maximize[o] ? a[o] - b[o] : b[o] - a[o];
        if (d < 0) {
          return false;
        }
        strictly |= d > 0;
      }
      return strictly;
    }

    /** The Pareto front, one vector per point, ordered lexicographically. */
    List<int[]> front(List<int[]> all) {
      TreeSet<int[]> front = new TreeSet<>(lex());
      for (int[] a : all) {
        if (all.stream().noneMatch(b -> dominates(b, a))) {
          front.add(a);
        }
      }
      return new ArrayList<>(front);
    }
  }

  /** A model of an instance in a fresh store. */
  private static final class Model {
    final Store store = new Store();
    final IntVar[] x = new IntVar[N];
    final IntVar[] objectives;

    Model(Instance in) {
      for (int i = 0; i < N; i++) {
        x[i] = new IntVar(store, "x" + i, 0, MAX_VALUE);
      }
      for (int[] c : in.neq) {
        store.impose(new XneqY(x[c[0]], x[c[1]]));
      }
      for (int[] c : in.lt) {
        store.impose(new XltY(x[c[0]], x[c[1]]));
      }
      objectives = new IntVar[in.weights.length];
      for (int o = 0; o < objectives.length; o++) {
        objectives[o] = new IntVar(store, "o" + o, -100, 100);
        store.impose(new LinearInt(x, in.weights[o], "==", objectives[o]));
      }
    }

    MultiObjective<int[]> multiObjective(boolean[] maximize) {
      SelectChoicePoint<IntVar> select = new SimpleSelect<>(x, null, new IndomainMin<>());
      return new MultiObjective<>(
          new MultiObjective.DepthFirst<>(store, select, objectives, x), maximize);
    }
  }

  @Test
  void lexicographicOptimumMatchesEnumeration() {
    Random rnd = new Random(20261030L);
    for (int t = 0; t < TRIALS; t++) {
      Instance in = Instance.random(rnd);
      List<int[]> all = in.enumerate();
      Model m = new Model(in);
      int level = m.store.level;
      MultiObjective<int[]> mo = m.multiObjective(in.maximize);
      List<int[]> reported = new ArrayList<>();
      mo.setSolutionListener((v, s) -> reported.add(v));
      MultiObjective.Status status = mo.lexicographic();
      assertEquals(level, m.store.level, in::toString);
      if (all.isEmpty()) {
        assertEquals(MultiObjective.Status.UNSATISFIABLE, status, in::toString);
        assertNull(mo.best(), in::toString);
        continue;
      }
      assertEquals(MultiObjective.Status.OPTIMAL, status, in::toString);
      int[] optimum = all.stream().min(in.lex()).orElseThrow();
      assertArrayEquals(optimum, mo.best(), in::toString);
      assertArrayEquals(in.objectives(mo.bestSolution()), mo.best(), in::toString);
      assertTrue(in.satisfied(mo.bestSolution()), in::toString);
      for (int i = 1; i < reported.size(); i++) {
        assertTrue(in.lex().compare(reported.get(i), reported.get(i - 1)) < 0, in::toString);
      }
    }
  }

  @Test
  void paretoFrontMatchesEnumeration() {
    Random rnd = new Random(20261031L);
    for (int t = 0; t < TRIALS; t++) {
      Instance in = Instance.random(rnd);
      List<int[]> all = in.enumerate();
      Model m = new Model(in);
      int level = m.store.level;
      MultiObjective<int[]> mo = m.multiObjective(in.maximize);
      List<int[]> reported = new ArrayList<>();
      mo.setSolutionListener((v, s) -> reported.add(v));
      MultiObjective.Status status = mo.pareto();
      assertEquals(level, m.store.level, in::toString);
      List<int[]> expected = in.front(all);
      assertEquals(
          all.isEmpty() ? MultiObjective.Status.UNSATISFIABLE : MultiObjective.Status.OPTIMAL,
          status,
          in::toString);
      List<int[]> front = mo.front();
      assertEquals(expected.size(), front.size(), in::toString);
      for (int i = 0; i < front.size(); i++) {
        assertArrayEquals(front.get(i), reported.get(i), in::toString);
        int[] solution = mo.frontSolutions().get(i);
        assertTrue(in.satisfied(solution), in::toString);
        assertArrayEquals(front.get(i), in.objectives(solution), in::toString);
      }
      front.sort(in.lex());
      for (int i = 0; i < expected.size(); i++) {
        assertArrayEquals(expected.get(i), front.get(i), in::toString);
      }
    }
  }

  @Test
  void stopsAtTimeOutWithBestSolution() {
    // a zero time limit stops before the first subproblem
    Instance in = Instance.random(new Random(7));
    Model m = new Model(in);
    SelectChoicePoint<IntVar> select = new SimpleSelect<>(m.x, null, new IndomainMin<>());
    MultiObjective.DepthFirst<IntVar> search =
        new MultiObjective.DepthFirst<>(m.store, select, m.objectives, m.x);
    search.setTimeOutMilliseconds(0);
    MultiObjective<int[]> mo = new MultiObjective<>(search, in.maximize);
    assertEquals(MultiObjective.Status.UNKNOWN, mo.pareto());
    assertEquals(MultiObjective.Status.UNKNOWN, mo.lexicographic());
  }

  @Test
  void subsolverSeesBoundsAndExclusions() {
    // a subsolver over an explicit list of objective vectors: the driver's own logic alone
    List<int[]> points =
        List.of(new int[] {1, 5}, new int[] {2, 2}, new int[] {3, 1}, new int[] {2, 3});
    List<MultiObjective.Subproblem> seen = new ArrayList<>();
    MultiObjective.Subsolver<int[]> solver =
        (p, found) -> {
          seen.add(p);
          int[] best = null;
          for (int[] q : points) {
            if (p.allows(q) && (best == null || q[p.objective()] < best[p.objective()])) {
              best = q;
            }
          }
          if (best != null) {
            found.accept(best, best);
          }
          return true;
        };
    MultiObjective<int[]> mo = new MultiObjective<>(solver, false, false);
    assertEquals(MultiObjective.Status.OPTIMAL, mo.pareto());
    assertEquals(3, mo.front().size());
    assertArrayEquals(new int[] {1, 5}, mo.front().get(0));
    assertArrayEquals(new int[] {2, 2}, mo.front().get(1));
    assertArrayEquals(new int[] {3, 1}, mo.front().get(2));
    // per point one subproblem for each objective, and a last one that finds nothing
    assertEquals(7, mo.subproblems());
    assertEquals(3, seen.get(seen.size() - 1).excluded().size());
  }
}
