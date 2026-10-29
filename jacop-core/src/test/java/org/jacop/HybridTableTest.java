/*
 * HybridTableTest.java
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
import static org.assertj.core.api.Assertions.assertThatThrownBy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.table.HybridTable;
import org.jacop.constraints.table.Restriction;
import org.jacop.constraints.table.Restriction.Relation;
import org.jacop.constraints.table.Table;
import org.jacop.constraints.table.TableCompressor;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMiddle;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.SmallestDomain;
import org.jacop.search.SplitSelect;
import org.junit.jupiter.api.Test;

/**
 * Tests {@link HybridTable} against brute-force enumeration: on random hybrid tables it must find
 * exactly the allowed tuples, and at every node of a search tree it must remove exactly the values
 * without a support (generalized arc consistency), also after backtracking. On ground and short
 * tables it must prune exactly as {@link Table} on the expanded table does.
 */
class HybridTableTest {

  private static final int TRIALS = 400;

  private static final int MIN = -1;
  private static final int MAX = 6;

  /** A random instance: the domains and the hybrid tuples. */
  private record Instance(int[][] domains, Restriction[][] tuples) {

    @Override
    public String toString() {
      return "domains=" + Arrays.deepToString(domains) + " tuples=" + Arrays.deepToString(tuples);
    }
  }

  private static int[] randomDomain(Random random) {
    TreeSet<Integer> values = new TreeSet<>();
    int size = 1 + random.nextInt(5);
    while (values.size() < size) {
      values.add(MIN + random.nextInt(MAX - MIN + 1));
    }
    return values.stream().mapToInt(Integer::intValue).toArray();
  }

  private static int value(Random random) {
    return MIN + random.nextInt(MAX - MIN + 1);
  }

  private static Restriction randomRestriction(
      Random random, int column, boolean binary, int kinds) {
    int kind = random.nextInt(kinds);
    return switch (kind) {
      case 0, 1, 2 -> Restriction.eq(value(random));
      case 3 -> Restriction.any();
      case 4 -> Restriction.ne(value(random));
      case 5 -> Restriction.compare(Relation.values()[random.nextInt(6)], value(random));
      case 6 -> Restriction.in(value(random), value(random), value(random));
      case 7 -> Restriction.notIn(value(random), value(random), value(random));
      default -> {
        if (binary && column > 0) {
          // Each column refers to at most one earlier column, so the restrictions between columns
          // of a tuple form a forest and the propagation must reach generalized arc consistency.
          yield Restriction.column(
              Relation.values()[random.nextInt(6)], random.nextInt(column), random.nextInt(5) - 2);
        }
        yield Restriction.eq(value(random));
      }
    };
  }

  private static Instance randomInstance(Random random, int kinds, boolean binary) {
    int n = 1 + random.nextInt(5);
    int[][] domains = new int[n][];
    for (int i = 0; i < n; i++) {
      domains[i] = randomDomain(random);
    }
    int k = random.nextInt(140);
    Restriction[][] tuples = new Restriction[k][n];
    for (Restriction[] tuple : tuples) {
      for (int i = 0; i < n; i++) {
        tuple[i] = randomRestriction(random, i, binary, kinds);
      }
    }
    return new Instance(domains, tuples);
  }

  private static IntVar[] variables(Store store, int[][] domains) {
    IntVar[] x = new IntVar[domains.length];
    for (int i = 0; i < domains.length; i++) {
      IntervalDomain d = new IntervalDomain();
      for (int v : domains[i]) {
        d.unionAdapt(v, v);
      }
      x[i] = new IntVar(store, "x" + i, d);
    }
    return x;
  }

  private static int[][] current(IntVar[] x) {
    int[][] result = new int[x.length][];
    for (int i = 0; i < x.length; i++) {
      List<Integer> values = new ArrayList<>();
      for (var e = x[i].dom().valueEnumeration(); e.hasMoreElements(); ) {
        values.add(e.nextElement());
      }
      result[i] = values.stream().mapToInt(Integer::intValue).toArray();
    }
    return result;
  }

  /** The values of each variable that belong to some allowed tuple, or null if there is none. */
  private static int[][] supported(int[][] domains, Restriction[][] tuples) {
    int n = domains.length;
    List<Set<Integer>> sets = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      sets.add(new TreeSet<>());
    }
    boolean[] any = new boolean[1];
    enumerate(
        domains,
        new int[n],
        0,
        values -> {
          for (Restriction[] tuple : tuples) {
            if (HybridTable.accepts(tuple, values)) {
              any[0] = true;
              for (int i = 0; i < n; i++) {
                sets.get(i).add(values[i]);
              }
              return;
            }
          }
        });
    if (!any[0]) {
      return null;
    }
    return sets.stream()
        .map(s -> s.stream().mapToInt(Integer::intValue).toArray())
        .toArray(int[][]::new);
  }

  private static void enumerate(
      int[][] domains, int[] values, int i, java.util.function.Consumer<int[]> action) {
    if (i == domains.length) {
      action.accept(values);
      return;
    }
    for (int v : domains[i]) {
      values[i] = v;
      enumerate(domains, values, i + 1, action);
    }
  }

  /**
   * It explores the whole search tree with the store's own levels, checks GAC at every node against
   * brute force and collects the solutions.
   */
  private static void explore(
      Store store,
      IntVar[] x,
      Restriction[][] tuples,
      Random random,
      Set<List<Integer>> solutions,
      String what) {
    int[][] before = current(x);
    int[][] expected = supported(before, tuples);
    boolean consistent = store.consistency();
    if (expected == null) {
      assertThat(consistent).as("fails %s at %s", what, Arrays.deepToString(before)).isFalse();
      return;
    }
    assertThat(consistent).as("consistent %s at %s", what, Arrays.deepToString(before)).isTrue();
    int[][] after = current(x);
    assertThat(after).as("GAC %s at %s", what, Arrays.deepToString(before)).isDeepEqualTo(expected);

    int pick = -1;
    for (int i = 0; i < x.length; i++) {
      if (!x[i].singleton()) {
        pick = i;
        break;
      }
    }
    if (pick < 0) {
      solutions.add(Arrays.stream(after).map(d -> d[0]).toList());
      return;
    }
    // Binary branching x = v or x != v, in a random order.
    int v = after[pick][random.nextInt(after[pick].length)];
    boolean equalFirst = random.nextBoolean();
    for (int branch = 0; branch < 2; branch++) {
      int level = store.level;
      store.setLevel(level + 1);
      if ((branch == 0) == equalFirst) {
        x[pick].domain.in(store.level, x[pick], v, v);
      } else {
        x[pick].domain.inComplement(store.level, x[pick], v);
      }
      explore(store, x, tuples, random, solutions, what);
      store.removeLevel(level + 1);
      store.setLevel(level);
      assertThat(current(x)).as("restored %s", what).isDeepEqualTo(after);
    }
  }

  private static void check(Instance instance, Random random) {
    check(instance, random, true);
  }

  private static void check(Instance instance, Random random, boolean expand) {
    Set<List<Integer>> expected = new HashSet<>();
    enumerate(
        instance.domains(),
        new int[instance.domains().length],
        0,
        values -> {
          for (Restriction[] tuple : instance.tuples()) {
            if (HybridTable.accepts(tuple, values)) {
              expected.add(Arrays.stream(values).boxed().toList());
              return;
            }
          }
        });
    Store store = new Store();
    IntVar[] x = variables(store, instance.domains());
    store.impose(new HybridTable(x, instance.tuples(), expand));
    Set<List<Integer>> found = new HashSet<>();
    explore(store, x, instance.tuples(), random, found, instance.toString());
    assertThat(found).as("solutions %s", instance).isEqualTo(expected);
  }

  @Test
  void validTuplesComeBackFromTheStoreTrailOnly() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 3);
    IntVar y = new IntVar(store, "y", 1, 3);
    IntVar z = new IntVar(store, "z", 1, 3);
    IntVar w = new IntVar(store, "w", 1, 2);
    HybridTable table =
        new HybridTable(
            new IntVar[] {x, y, z}, new int[][] {{1, 1, 2}, {2, 2, 3}, {3, 1, 1}, {3, 3, 3}});
    store.impose(table);
    assertThat(store.consistency()).isTrue();
    // The table does not listen to the removal of every level.
    assertThat(store.removeLevelListeners).doesNotContain(table);

    for (int round = 0; round < 3; round++) {
      store.setLevel(store.level + 1);
      x.domain.in(store.level, x, 3, 3);
      assertThat(store.consistency()).isTrue();
      assertThat(y.dom().toString()).isEqualTo("{1, 3}");
      store.setLevel(store.level + 1);
      y.domain.in(store.level, y, 1, 1);
      assertThat(store.consistency()).isTrue();
      assertThat(z.dom().toString()).isEqualTo("1");
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);

      // A failure before the table runs leaves z queued; the backtrack does not tell the table.
      store.setLevel(store.level + 1);
      z.domain.in(store.level, z, 2, 2);
      assertThatThrownBy(() -> w.domain.in(store.level, w, 3, 3)).isInstanceOf(FailException.class);
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);

      store.setLevel(store.level + 1);
      y.domain.in(store.level, y, 2, 2);
      assertThat(store.consistency()).isTrue();
      assertThat(x.dom().toString()).isEqualTo("2");
      assertThat(z.dom().toString()).isEqualTo("3");
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
      assertThat(x.dom().toString()).isEqualTo("{1..3}");
    }
  }

  @Test
  void groundTablesReachGacAndFindAllSolutions() {
    Random random = new Random(1);
    for (int trial = 0; trial < TRIALS; trial++) {
      check(randomInstance(random, 3, false), random);
    }
  }

  @Test
  void shortTablesReachGacAndFindAllSolutions() {
    Random random = new Random(2);
    for (int trial = 0; trial < TRIALS; trial++) {
      check(randomInstance(random, 4, false), random);
    }
  }

  @Test
  void unaryRestrictionsReachGacAndFindAllSolutions() {
    Random random = new Random(3);
    for (int trial = 0; trial < TRIALS; trial++) {
      check(randomInstance(random, 8, false), random);
    }
  }

  @Test
  void restrictionsBetweenColumnsReachGacAndFindAllSolutions() {
    Random random = new Random(4);
    for (int trial = 0; trial < TRIALS; trial++) {
      check(randomInstance(random, 10, true), random);
    }
  }

  @Test
  void restrictionsBetweenColumnsWithoutExpansionReachGacAndFindAllSolutions() {
    Random random = new Random(5);
    for (int trial = 0; trial < TRIALS; trial++) {
      check(randomInstance(random, 10, true), random, false);
    }
  }

  @Test
  void compressedTablesAllowExactlyTheSameTuples() {
    Random random = new Random(41);
    for (int trial = 0; trial < 4 * TRIALS; trial++) {
      int n = 1 + random.nextInt(5);
      int[][] domains = new int[n][];
      for (int i = 0; i < n; i++) {
        domains[i] = randomDomain(random);
      }
      // Tuples within the domains: either random, or expanded from random short tuples, which
      // the compression has something to find in.
      Set<List<Integer>> allowed = new HashSet<>();
      int k = random.nextInt(60);
      boolean structured = random.nextBoolean();
      for (int t = 0; t < k; t++) {
        int[][] cells = new int[n][];
        for (int i = 0; i < n; i++) {
          int[] d = domains[i];
          cells[i] =
              structured && random.nextInt(3) == 0 ? d : new int[] {d[random.nextInt(d.length)]};
        }
        enumerate(cells, new int[n], 0, v -> allowed.add(Arrays.stream(v).boxed().toList()));
      }
      int[][] tuples =
          allowed.stream()
              .map(l -> l.stream().mapToInt(Integer::intValue).toArray())
              .toArray(int[][]::new);
      Store store = new Store();
      IntVar[] x = variables(store, domains);
      boolean sets = trial % 2 == 0;
      Restriction[][] result = TableCompressor.compress(x, tuples, sets);
      if (result == null) {
        for (int[] a : tuples) {
          for (int[] b : tuples) {
            int differ = 0;
            for (int i = 0; i < n; i++) {
              differ += a[i] == b[i] ? 0 : 1;
            }
            assertThat(differ).as("no tuples to merge").isNotEqualTo(1);
          }
        }
      }
      Restriction[][] compressed =
          result != null
              ? result
              : Arrays.stream(tuples)
                  .map(t -> Arrays.stream(t).mapToObj(Restriction::eq).toArray(Restriction[]::new))
                  .toArray(Restriction[][]::new);

      String where = Arrays.deepToString(domains) + " " + Arrays.deepToString(tuples);
      assertThat(Arrays.asList(compressed)).as(where).hasSizeLessThanOrEqualTo(tuples.length);
      if (!sets) {
        for (Restriction[] tuple : compressed) {
          for (Restriction r : tuple) {
            assertThat(r.toString()).as(where).matches("\\*|-?[0-9]+");
          }
        }
      }
      Set<List<Integer>> accepted = new HashSet<>();
      enumerate(
          domains,
          new int[n],
          0,
          v -> {
            for (Restriction[] tuple : compressed) {
              if (HybridTable.accepts(tuple, v)) {
                accepted.add(Arrays.stream(v).boxed().toList());
              }
            }
          });
      assertThat(accepted).as(where).isEqualTo(allowed);
      // No two compressed tuples overlap, so their number bounds the work of the propagator.
      long covered = 0;
      for (Restriction[] tuple : compressed) {
        long[] count = new long[1];
        enumerate(domains, new int[n], 0, v -> count[0] += HybridTable.accepts(tuple, v) ? 1 : 0);
        covered += count[0];
      }
      assertThat(covered).as(where).isEqualTo(allowed.size());
    }
  }

  @Test
  void prunesLikeTableOnTheExpandedTable() {
    Random random = new Random(5);
    for (int trial = 0; trial < TRIALS; trial++) {
      Instance instance = randomInstance(random, 8, true);
      List<int[]> expanded = new ArrayList<>();
      int[][] full = new int[instance.domains().length][];
      Arrays.fill(full, java.util.stream.IntStream.rangeClosed(MIN, MAX).toArray());
      enumerate(
          full,
          new int[full.length],
          0,
          values -> {
            for (Restriction[] tuple : instance.tuples()) {
              if (HybridTable.accepts(tuple, values)) {
                expanded.add(values.clone());
                return;
              }
            }
          });
      Store hybridStore = new Store();
      IntVar[] x = variables(hybridStore, instance.domains());
      hybridStore.impose(new HybridTable(x, instance.tuples()));
      Store tableStore = new Store();
      IntVar[] y = variables(tableStore, instance.domains());
      tableStore.impose(new Table(y, expanded.toArray(int[][]::new)));
      boolean a = hybridStore.consistency();
      boolean b = tableStore.consistency();
      assertThat(a).as("%s", instance).isEqualTo(b);
      if (a) {
        assertThat(current(x)).as("%s", instance).isDeepEqualTo(current(y));
      }
    }
  }

  /**
   * The values of each variable that belong to a tuple of a ground table within the domains, or
   * null if there is none.
   */
  private static int[][] supportedByGround(IntVar[] x, int[][] tuples) {
    List<Set<Integer>> sets = new ArrayList<>();
    for (int i = 0; i < x.length; i++) {
      sets.add(new TreeSet<>());
    }
    boolean any = false;
    for (int[] tuple : tuples) {
      boolean allowed = true;
      for (int i = 0; i < x.length && allowed; i++) {
        allowed = x[i].domain.contains(tuple[i]);
      }
      if (allowed) {
        any = true;
        for (int i = 0; i < x.length; i++) {
          sets.get(i).add(tuple[i]);
        }
      }
    }
    return any
        ? sets.stream()
            .map(set -> set.stream().mapToInt(Integer::intValue).toArray())
            .toArray(int[][]::new)
        : null;
  }

  /**
   * Large ground tables with a key column of many values, as MiniZinc writes for lookups: the
   * supports of such a column are kept sparse, the column is filtered from the valid tuples when
   * they are few, and many values go in one domain change. GAC is checked along random dives with
   * backtracking, on interval, bit-set and small dense domains.
   */
  @Test
  void largeTablesWithKeyColumnsReachGac() {
    Random random = new Random(6);
    for (int trial = 0; trial < 30; trial++) {
      int arity = 2 + random.nextInt(3);
      int keys = 70 + random.nextInt(600);
      int[] spans = new int[arity];
      spans[0] = keys;
      for (int i = 1; i < arity; i++) {
        spans[i] = random.nextBoolean() ? 2 + random.nextInt(8) : 70 + random.nextInt(200);
      }
      Set<List<Integer>> rows = new HashSet<>();
      int count = 500 + random.nextInt(2500);
      for (int k = 0; k < count; k++) {
        List<Integer> row = new ArrayList<>();
        for (int i = 0; i < arity; i++) {
          // A few rows per key, as in a lookup table; offsets on the other columns.
          row.add(i == 0 ? random.nextInt(keys) : random.nextInt(spans[i]) - 3);
        }
        rows.add(row);
      }
      int[][] tuples =
          rows.stream()
              .map(r -> r.stream().mapToInt(Integer::intValue).toArray())
              .sorted(Arrays::compare)
              .toArray(int[][]::new);
      Store store = new Store();
      IntVar[] x = new IntVar[arity];
      for (int i = 0; i < arity; i++) {
        int lo = i == 0 ? 0 : -3;
        int hi = lo + spans[i] - 1 + random.nextInt(3);
        x[i] =
            random.nextInt(4) == 0
                ? new IntVar(store, "x" + i, new IntervalDomain(lo, hi))
                : new IntVar(store, "x" + i, lo, hi);
      }
      store.impose(new HybridTable(x, tuples));
      for (int dive = 0; dive < 6; dive++) {
        dive(store, x, tuples, random, "trial " + trial);
      }
    }
  }

  /** It goes down a random branch, checking GAC and the restoration of the domains. */
  private static void dive(Store store, IntVar[] x, int[][] tuples, Random random, String what) {
    int[][] expected = supportedByGround(x, tuples);
    boolean consistent = store.consistency();
    if (expected == null) {
      assertThat(consistent).as("fails %s", what).isFalse();
      return;
    }
    assertThat(consistent).as("consistent %s", what).isTrue();
    int[][] after = current(x);
    assertThat(after).as("GAC %s", what).isDeepEqualTo(expected);
    List<Integer> open = new ArrayList<>();
    for (int i = 0; i < x.length; i++) {
      if (!x[i].singleton()) {
        open.add(i);
      }
    }
    if (open.isEmpty()) {
      return;
    }
    int pick = open.get(random.nextInt(open.size()));
    int[] values = after[pick];
    int level = store.level;
    store.setLevel(level + 1);
    switch (random.nextInt(3)) {
      case 0 -> {
        int v = values[random.nextInt(values.length)];
        x[pick].domain.in(store.level, x[pick], v, v);
      }
      case 1 -> x[pick].domain.inComplement(store.level, x[pick], values[0]);
      default -> {
        // Many values at once, so that many tuples go and many classes lose their supports.
        int a = random.nextInt(values.length);
        int b = random.nextInt(values.length);
        int from = Math.min(a, b);
        int to = Math.min(Math.max(a, b), from == 0 ? values.length - 2 : values.length - 1);
        x[pick].domain.inComplement(store.level, x[pick], values[from], values[to]);
      }
    }
    dive(store, x, tuples, random, what);
    store.removeLevel(level + 1);
    store.setLevel(level);
    assertThat(current(x)).as("restored %s", what).isDeepEqualTo(after);
  }

  @Test
  void shortTableWithAHugeDomain() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", -1_000_000, 1_000_000);
    IntVar b = new IntVar(store, "b", -1_000_000, 1_000_000);
    int star = Integer.MIN_VALUE;
    store.impose(new HybridTable(new IntVar[] {a, b}, new int[][] {{5, star}, {star, 7}}, star));
    assertThat(store.consistency()).isTrue();
    assertThat(a.getSize()).isEqualTo(2_000_001);
    store.setLevel(1);
    a.domain.inComplement(1, a, 5);
    assertThat(store.consistency()).isTrue();
    assertThat(b.singleton(7)).isTrue();
    store.removeLevel(1);
    store.setLevel(0);
    assertThat(b.getSize()).isEqualTo(2_000_001);
  }

  @Test
  void boundsAndColumnsOnAHugeDomain() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 1_000_000);
    IntVar b = new IntVar(store, "b", 0, 1_000_000);
    store.impose(
        new HybridTable(
            new IntVar[] {a, b},
            new Restriction[][] {
              {Restriction.ge(500_000), Restriction.column(Relation.LT, 0, -10)},
            }));
    assertThat(store.consistency()).isTrue();
    assertThat(a.min()).isEqualTo(500_000);
    assertThat(b.max()).isEqualTo(1_000_000 - 11);
    store.setLevel(1);
    b.domain.in(1, b, 999_000, 999_000);
    assertThat(store.consistency()).isTrue();
    assertThat(a.min()).isEqualTo(999_011);
  }

  @Test
  void expansionUsesTheDomainsAtImposition() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 3);
    IntVar b = new IntVar(store, "b", 0, 3);
    // Built while a is fixed to 1, imposed after backtracking: b = a + 1 must allow every a.
    store.setLevel(1);
    a.domain.in(1, a, 1, 1);
    HybridTable table =
        new HybridTable(
            new IntVar[] {a, b},
            new Restriction[][] {{Restriction.any(), Restriction.column(Relation.EQ, 0, 1)}});
    store.removeLevel(1);
    store.setLevel(0);
    store.impose(table);
    assertThat(store.consistency()).isTrue();
    assertThat(a.dom()).hasToString("{0..2}");
    assertThat(b.dom()).hasToString("{1..3}");
  }

  @Test
  void emptyTableFails() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 3);
    store.impose(new HybridTable(new IntVar[] {a}, new Restriction[0][]));
    assertThat(store.consistency()).isFalse();
  }

  @Test
  void rejectsWrongColumns() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 3);
    IntVar b = new IntVar(store, "b", 0, 3);
    IntVar[] x = {a, b};
    Restriction[][] selfReference = {{Restriction.column(Relation.EQ, 0), Restriction.any()}};
    Restriction[][] tooShort = {{Restriction.any()}};
    assertThatThrownBy(() -> new HybridTable(x, selfReference))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new HybridTable(x, tooShort))
        .isInstanceOf(IllegalArgumentException.class);
    assertThat(IntDomain.MAX_INT).isPositive();
  }

  /**
   * Revising the tuples with restrictions between columns can remove the only support of a value of
   * the one column that lost a live class, which the propagation then skipped: x[2] = 4 and 5 had
   * only the second tuple, removed with x[1] = 3 since x[1] != x[0] = 3, and were accepted.
   */
  @Test
  void revisedColumnTuplesRecheckTheChangedColumn() {
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 1, 3), new IntVar(store, "x1", 0, 3), new IntVar(store, "x2", 1, 5)
    };
    Restriction[][] tuples = {
      {Restriction.eq(3), Restriction.column(Relation.NE, 0), Restriction.ne(2)},
      {Restriction.any(), Restriction.ge(0), Restriction.le(3)}
    };
    store.impose(new XneqC(x[2], 0));
    store.impose(new XneqY(x[2], x[1]));
    store.impose(new HybridTable(x, tuples, false));
    List<int[]> found = new ArrayList<>();
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            found.add(Arrays.stream(x).mapToInt(IntVar::value).toArray());
            return result;
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, new SplitSelect<>(x, new SmallestDomain<>(), new IndomainMiddle<>()));

    for (int[] s : found) {
      assertThat(Arrays.stream(tuples).anyMatch(t -> HybridTable.accepts(t, s)))
          .as(Arrays.toString(s))
          .isTrue();
    }
    assertThat(found).hasSize(33);
  }
}
