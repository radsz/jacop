/*
 * NegativeAndReifiedTableTest.java
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

package org.jacop;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Consumer;
import java.util.function.Predicate;
import org.jacop.constraints.table.NegativeTable;
import org.jacop.constraints.table.TableReified;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Tests {@link NegativeTable} and {@link TableReified} against brute-force enumeration: at every
 * node of complete search trees on random tables the domains must be exactly the values with a
 * support (generalized arc consistency), they must be restored after backtracking, and the
 * solutions found must be exactly the allowed assignments.
 */
class NegativeAndReifiedTableTest {

  private static final int TRIALS = 400;

  private interface Poster {
    void post(Store store, IntVar[] x, IntVar b, int[][] tuples);
  }

  private static int[] randomDomain(Random random, int min, int max) {
    TreeSet<Integer> values = new TreeSet<>();
    int size = 1 + random.nextInt(max - min + 1);
    while (values.size() < size) {
      values.add(min + random.nextInt(max - min + 1));
    }
    return values.stream().mapToInt(Integer::intValue).toArray();
  }

  private static int[][] current(IntVar[] v) {
    int[][] result = new int[v.length][];
    for (int i = 0; i < v.length; i++) {
      List<Integer> values = new ArrayList<>();
      for (var e = v[i].dom().valueEnumeration(); e.hasMoreElements(); ) {
        values.add(e.nextElement());
      }
      result[i] = values.stream().mapToInt(Integer::intValue).toArray();
    }
    return result;
  }

  private static void enumerate(int[][] domains, int[] values, int i, Consumer<int[]> action) {
    if (i == domains.length) {
      action.accept(values);
      return;
    }
    for (int v : domains[i]) {
      values[i] = v;
      enumerate(domains, values, i + 1, action);
    }
  }

  private static int[][] supported(int[][] domains, Predicate<int[]> allowed) {
    List<Set<Integer>> sets = new ArrayList<>();
    for (int i = 0; i < domains.length; i++) {
      sets.add(new TreeSet<>());
    }
    boolean[] any = new boolean[1];
    enumerate(
        domains,
        new int[domains.length],
        0,
        values -> {
          if (allowed.test(values)) {
            any[0] = true;
            for (int i = 0; i < values.length; i++) {
              sets.get(i).add(values[i]);
            }
          }
        });
    return any[0]
        ? sets.stream()
            .map(s -> s.stream().mapToInt(Integer::intValue).toArray())
            .toArray(int[][]::new)
        : null;
  }

  private static void explore(
      Store store,
      IntVar[] v,
      Predicate<int[]> allowed,
      Random random,
      Set<List<Integer>> solutions,
      String what) {
    int[][] before = current(v);
    int[][] expected = supported(before, allowed);
    boolean consistent = store.consistency();
    if (expected == null) {
      assertThat(consistent).as("fails %s at %s", what, Arrays.deepToString(before)).isFalse();
      return;
    }
    assertThat(consistent).as("consistent %s at %s", what, Arrays.deepToString(before)).isTrue();
    int[][] after = current(v);
    assertThat(after).as("GAC %s at %s", what, Arrays.deepToString(before)).isDeepEqualTo(expected);
    int pick = -1;
    for (int i = 0; i < v.length; i++) {
      if (!v[i].singleton()) {
        pick = i;
        break;
      }
    }
    if (pick < 0) {
      solutions.add(Arrays.stream(after).map(d -> d[0]).toList());
      return;
    }
    int value = after[pick][random.nextInt(after[pick].length)];
    boolean equalFirst = random.nextBoolean();
    for (int branch = 0; branch < 2; branch++) {
      int level = store.level;
      store.setLevel(level + 1);
      if ((branch == 0) == equalFirst) {
        v[pick].domain.in(store.level, v[pick], value, value);
      } else {
        v[pick].domain.inComplement(store.level, v[pick], value);
      }
      explore(store, v, allowed, random, solutions, what);
      store.removeLevel(level + 1);
      store.setLevel(level);
      assertThat(current(v)).as("restored %s", what).isDeepEqualTo(after);
    }
  }

  /**
   * It runs random instances. The semantics gets the tuple set and an assignment of x followed by b
   * (when there is one).
   */
  private static void check(
      long seed, boolean control, Poster poster, BiPredicateOnTuples semantics) {
    Random random = new Random(seed);
    for (int trial = 0; trial < TRIALS; trial++) {
      int n = 1 + random.nextInt(4);
      int[][] domains = new int[n + (control ? 1 : 0)][];
      for (int i = 0; i < n; i++) {
        domains[i] = randomDomain(random, 0, 3);
      }
      if (control) {
        domains[n] = randomDomain(random, 0, 1);
      }
      // Dense tables make the negative pruning happen; values outside the domains also occur.
      int k = random.nextInt(random.nextBoolean() ? 6 : 70);
      int[][] tuples = new int[k][n];
      for (int[] t : tuples) {
        for (int j = 0; j < n; j++) {
          t[j] = random.nextInt(random.nextInt(10) == 0 ? 5 : 3);
        }
      }
      Set<List<Integer>> tupleSet = new HashSet<>();
      for (int[] t : tuples) {
        tupleSet.add(Arrays.stream(t).boxed().toList());
      }
      Predicate<int[]> allowed =
          values ->
              semantics.test(
                  tupleSet.contains(Arrays.stream(values, 0, n).boxed().toList()), values, n);
      Set<List<Integer>> expected = new HashSet<>();
      enumerate(
          domains,
          new int[domains.length],
          0,
          values -> {
            if (allowed.test(values)) {
              expected.add(Arrays.stream(values).boxed().toList());
            }
          });
      Store store = new Store();
      IntVar[] v = new IntVar[domains.length];
      for (int i = 0; i < domains.length; i++) {
        IntervalDomain d = new IntervalDomain();
        for (int value : domains[i]) {
          d.unionAdapt(value, value);
        }
        v[i] = new IntVar(store, "v" + i, d);
      }
      poser(poster, store, v, n, control, tuples);
      String what =
          "domains=" + Arrays.deepToString(domains) + " tuples=" + Arrays.deepToString(tuples);
      Set<List<Integer>> found = new HashSet<>();
      explore(store, v, allowed, random, found, what);
      assertThat(found).as("solutions %s", what).isEqualTo(expected);
    }
  }

  private static void poser(
      Poster poster, Store store, IntVar[] v, int n, boolean control, int[][] tuples) {
    poster.post(store, Arrays.copyOf(v, n), control ? v[n] : null, tuples);
  }

  private interface BiPredicateOnTuples {
    boolean test(boolean inTable, int[] values, int n);
  }

  @Test
  void negativeTableReachesGacAndFindsAllSolutions() {
    check(1, false, (s, x, b, t) -> s.impose(new NegativeTable(x, t)), (in, values, n) -> !in);
  }

  @Test
  void reifiedTableReachesGacAndFindsAllSolutions() {
    check(
        2,
        true,
        (s, x, b, t) -> s.impose(new TableReified(x, t, b)),
        (in, values, n) -> in == (values[n] == 1));
  }

  @Test
  void halfReifiedTableReachesGacAndFindsAllSolutions() {
    check(
        3,
        true,
        (s, x, b, t) -> s.impose(new TableReified(x, t, b, true)),
        (in, values, n) -> values[n] == 0 || in);
  }
}
