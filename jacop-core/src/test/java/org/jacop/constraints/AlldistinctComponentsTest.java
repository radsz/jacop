/*
 * AlldistinctComponentsTest.java
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
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.MostConstrainedDynamic;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Checks that {@link Alldistinct}, which keeps the components of its value graph between executions
 * and works only on the changed ones, reaches generalized arc consistency after every change and
 * backtrack of a random walk (against enumeration), and that a search finds the same solutions with
 * the same number of nodes and failures as when all variables are processed at each execution. Both
 * the bit set and the adjacency list representations are covered.
 */
class AlldistinctComponentsTest {

  private static final int TRIALS = Integer.getInteger("alldistinct.components.trials", 300);

  // A value is v * scale, so scale 1000 makes the value span too large for the bit sets.
  private static IntVar[] variables(Store store, Random random, int n, int values, int scale) {
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      IntervalDomain d = new IntervalDomain();
      for (int v = 0; v < values; v++) {
        if (random.nextInt(100) < 65) {
          d.unionAdapt(v * scale, v * scale);
        }
      }
      if (d.isEmpty()) {
        int v = random.nextInt(values) * scale;
        d.unionAdapt(v, v);
      }
      x[i] = new IntVar(store, "x" + i, d);
    }
    return x;
  }

  // Variables of another store with the current domains of x.
  private static IntVar[] copies(IntVar[] x) {
    Store store = new Store();
    IntVar[] copy = new IntVar[x.length];
    for (int i = 0; i < x.length; i++) {
      IntervalDomain d = new IntervalDomain();
      for (int v : x[i].dom().toIntArray()) {
        d.unionAdapt(v, v);
      }
      copy[i] = new IntVar(store, "s" + i, d);
    }
    return copy;
  }

  // Whether the variables can take distinct values with x[fixed] == value.
  private static boolean supported(IntVar[] x, int fixed, int value) {
    List<Integer> used = new ArrayList<>();
    used.add(value);
    return extend(x, fixed, 0, used);
  }

  private static boolean extend(IntVar[] x, int fixed, int i, List<Integer> used) {
    if (i == x.length) {
      return true;
    }
    if (i == fixed) {
      return extend(x, fixed, i + 1, used);
    }
    for (int v : x[i].dom().toIntArray()) {
      if (!used.contains(v)) {
        used.add(v);
        boolean ok = extend(x, fixed, i + 1, used);
        used.remove(used.size() - 1);
        if (ok) {
          return true;
        }
      }
    }
    return false;
  }

  // True if every value of every variable has a support, false if some variable has none.
  private static boolean checkGac(IntVar[] x) {
    for (int i = 0; i < x.length; i++) {
      for (int v : x[i].dom().toIntArray()) {
        assertThat(supported(x, i, v)).as("value %d of %s in %s", v, x[i], List.of(x)).isTrue();
      }
    }
    return true;
  }

  private static boolean anySolution(IntVar[] x) {
    for (int v : x[0].dom().toIntArray()) {
      if (supported(x, 0, v)) {
        return true;
      }
    }
    return false;
  }

  @Test
  void randomWalkKeepsDomainConsistency() {
    for (int trial = 0; trial < TRIALS; trial++) {
      Random random = new Random(trial);
      int n = 3 + random.nextInt(6);
      int values = n + random.nextInt(4);
      int scale = trial % 2 == 0 ? 1 : 1000;
      Store store = new Store();
      IntVar[] x = variables(store, random, n, values, scale);
      // copies of the initial domains, to know whether a failure is right
      IntVar[] shadow = copies(x);
      Alldistinct c = new Alldistinct(x);
      c.keepComponents = !Boolean.getBoolean("alldistinct.components.off");
      store.impose(c);
      store.setLevel(1);
      boolean consistent = store.consistency();
      assertThat(consistent).isEqualTo(anySolution(shadow));
      if (!consistent) {
        continue;
      }
      checkGac(x);

      // the first consistency raises the level, see Store.raiseLevelBeforeConsistency
      int base = store.level;
      int level = base;
      for (int step = 0; step < 40; step++) {
        if (level > base && random.nextInt(4) == 0) {
          // backtrack one or more levels
          int target = base + random.nextInt(level - base);
          for (int l = level; l > target; l--) {
            store.removeLevel(l);
          }
          level = target;
          store.setLevel(level);
          checkGac(x);
          continue;
        }
        List<Integer> open = new ArrayList<>();
        for (int i = 0; i < n; i++) {
          if (!x[i].singleton()) {
            open.add(i);
          }
        }
        if (open.isEmpty()) {
          break;
        }
        level++;
        store.setLevel(level);
        IntVar y = x[open.get(random.nextInt(open.size()))];
        int[] dom = y.dom().toIntArray();
        int v = dom[random.nextInt(dom.length)];
        switch (random.nextInt(3)) {
          case 0 -> y.domain.inValue(level, y, v);
          case 1 -> y.domain.inComplement(level, y, v);
          default -> y.domain.in(level, y, v, y.max());
        }
        shadow = copies(x);
        consistent = store.consistency();
        assertThat(consistent).as("trial %d step %d", trial, step).isEqualTo(anySolution(shadow));
        if (consistent) {
          checkGac(x);
        } else {
          store.removeLevel(level);
          level--;
          store.setLevel(level);
          checkGac(x);
        }
      }
    }
  }

  private record Result(int solutions, int nodes, int failures) {}

  // All solutions of an alldistinct with side constraints x[i] != x[j] + 1, which change domains
  // from outside of the alldistinct.
  private static Result solve(long seed, boolean keepComponents, int scale) {
    Random random = new Random(seed);
    int n = 5 + random.nextInt(4);
    int values = n + random.nextInt(3);
    Store store = new Store();
    IntVar[] x = variables(store, random, n, values, scale);
    Alldistinct c = new Alldistinct(x);
    c.keepComponents = keepComponents;
    store.impose(c);
    for (int k = 0; k < n / 2; k++) {
      int i = random.nextInt(n);
      int j = random.nextInt(n);
      if (i != j) {
        store.impose(new Not(new XplusCeqZ(x[j], scale, x[i])));
      }
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    SimpleSelect<IntVar> select =
        new SimpleSelect<>(x, new MostConstrainedDynamic<>(), new IndomainRandom<>((int) seed));
    search.labeling(store, select);
    return new Result(
        search.getSolutionListener().solutionsNo(), search.getNodes(), search.getWrongDecisions());
  }

  @Test
  void searchIsTheSameAsWithoutComponents() {
    for (int trial = 0; trial < TRIALS; trial++) {
      int scale = trial % 2 == 0 ? 1 : 1000;
      Result kept = solve(trial, true, scale);
      Result full = solve(trial, false, scale);
      assertThat(kept).as("trial %d", trial).isEqualTo(full);
    }
  }

  // A permutation that splits into components: the pairs {2k, 2k+1} share two values.
  @Test
  void splitComponentsStayIndependent() {
    for (int scale : new int[] {1, 1000}) {
      Store store = new Store();
      int n = 8;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        IntervalDomain d = new IntervalDomain();
        for (int v = 0; v < n; v++) {
          d.unionAdapt(v * scale, v * scale);
        }
        x[i] = new IntVar(store, "x" + i, d);
      }
      store.impose(new Alldistinct(x));
      store.setLevel(1);
      assertThat(store.consistency()).isTrue();
      // the first consistency raises the level, see Store.raiseLevelBeforeConsistency
      int pairs = store.level + 1;
      store.setLevel(pairs);
      for (int k = 0; k < n / 2; k++) {
        for (int i : new int[] {2 * k, 2 * k + 1}) {
          // the multiples of scale in the interval are 2k and 2k+1
          x[i].domain.in(pairs, x[i], 2 * k * scale, (2 * k + 1) * scale);
        }
      }
      assertThat(store.consistency()).isTrue();
      checkGac(x);
      // fixing one pair leaves the other pairs alone; backtracking restores both values
      int next = pairs + 1;
      store.setLevel(next);
      x[0].domain.inValue(next, x[0], scale);
      assertThat(store.consistency()).isTrue();
      assertThat(x[1].singleton(0)).isTrue();
      assertThat(x[2].getSize()).isEqualTo(2);
      store.removeLevel(next);
      store.setLevel(pairs);
      assertThat(x[0].getSize()).isEqualTo(2);
      assertThat(x[1].getSize()).isEqualTo(2);
      store.setLevel(next);
      x[3].domain.inValue(next, x[3], 2 * scale);
      assertThat(store.consistency()).isTrue();
      assertThat(x[2].singleton(3 * scale)).isTrue();
      assertThat(x[0].getSize()).isEqualTo(2);
      checkGac(x);
      // a value removed from a pair that the last execution did not touch
      store.setLevel(next + 1);
      x[5].domain.inComplement(next + 1, x[5], 4 * scale);
      assertThat(store.consistency()).isTrue();
      assertThat(x[4].singleton(4 * scale)).isTrue();
      checkGac(x);
    }
  }
}
