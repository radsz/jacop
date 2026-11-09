/*
 * LinearizationsTest.java
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
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.function.Function;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.constraints.lp.LpColumn;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.LinearForm;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/**
 * Tests the rows of {@link Linearizations} against enumeration: for random small instances of each
 * constraint, every solution of the constraint alone must meet every row made from it before
 * search.
 */
class LinearizationsTest {

  private static final String[] RELATIONS = {"==", "!=", "<", "<=", ">", ">="};

  @Test
  void knapsackGivesItsWeightAndProfitRows() {
    Store store = new Store();
    IntVar[] q = new IntVar[3];
    for (int i = 0; i < q.length; i++) {
      q[i] = new IntVar(store, "q" + i, 0, 1);
    }
    IntVar capacity = new IntVar(store, "capacity", 0, 9);
    IntVar profit = new IntVar(store, "profit", 0, 20);
    Knapsack k = new Knapsack(new int[] {4, 5, 6}, new int[] {3, 4, 5}, q, capacity, profit);
    List<LinearForm> rows = Linearizations.of(k);
    assertThat(rows).hasSize(2);
    // 3 q0 + 4 q1 + 5 q2 - capacity = 0 and 4 q0 + 5 q1 + 6 q2 - profit = 0
    assertThat(rows.get(0).relation()).isEqualTo(LinearForm.EQ);
    assertThat(rows.get(1).relation()).isEqualTo(LinearForm.EQ);
  }

  @Test
  void rowsHoldForEverySolution() {
    Random rnd = new Random(7);
    int rows = 0;
    for (int run = 0; run < 4200; run++) {
      int kind = run % 21;
      Store store = new Store();
      IntVar[] x = new IntVar[4];
      for (int i = 0; i < x.length; i++) {
        int lo = rnd.nextInt(7) - 3;
        x[i] = new IntVar(store, "x" + i, lo, lo + rnd.nextInt(5));
      }
      IntVar b = new IntVar(store, "b", 0, 1);
      IntVar[] bs = new IntVar[3];
      for (int i = 0; i < bs.length; i++) {
        bs[i] = new IntVar(store, "b" + i, 0, 1);
      }
      int[] w = {rnd.nextInt(7) - 3, rnd.nextInt(7) - 3, 1 + rnd.nextInt(3)};
      String rel = RELATIONS[rnd.nextInt(RELATIONS.length)];
      int k = rnd.nextInt(9) - 4;
      List<Constraint> cs = new ArrayList<>();
      List<LinearForm> made = new ArrayList<>();
      IntVar[] scope;
      switch (kind) {
        case 0 -> {
          cs.add(new Reified(new LinearInt(new IntVar[] {x[0], x[1], x[2]}, w, rel, k), b));
          scope = new IntVar[] {x[0], x[1], x[2], b};
        }
        case 1 -> {
          cs.add(new Implies(b, new LinearInt(new IntVar[] {x[0], x[1], x[2]}, w, rel, k)));
          scope = new IntVar[] {x[0], x[1], x[2], b};
        }
        case 2 -> {
          cs.add(new Reified(new XeqC(x[0], k), b));
          scope = new IntVar[] {x[0], b};
        }
        case 3 -> {
          cs.add(new XplusClteqZImplied(b, x[0], k, x[1]));
          scope = new IntVar[] {x[0], x[1], b};
        }
        case 4 -> {
          cs.add(new AndBoolSimple(bs[0], bs[1], b));
          scope = new IntVar[] {bs[0], bs[1], b};
        }
        case 5 -> {
          cs.add(rnd.nextBoolean() ? new OrBoolVector(bs, b) : new AndBoolVector(bs, b));
          scope = new IntVar[] {bs[0], bs[1], bs[2], b};
        }
        case 6 -> {
          cs.add(new XmulYeqZ(x[0], x[1], x[2]));
          scope = new IntVar[] {x[0], x[1], x[2]};
        }
        case 7 -> {
          cs.add(new XmulYeqZ(x[0], x[0], x[2]));
          scope = new IntVar[] {x[0], x[2]};
        }
        case 8 -> {
          IntVar[] l = {x[0], x[1], x[2]};
          cs.add(rnd.nextBoolean() ? new Max(l, x[3]) : new Min(l, x[3]));
          scope = x;
        }
        case 9 -> {
          cs.add(
              rnd.nextBoolean()
                  ? new MaxSimple(x[0], x[1], x[2])
                  : new MinSimple(x[0], x[1], x[2]));
          scope = new IntVar[] {x[0], x[1], x[2]};
        }
        case 10 -> {
          cs.add(new AbsXeqY(x[0], x[1]));
          scope = new IntVar[] {x[0], x[1]};
        }
        case 11 -> {
          IntVar[] l = {x[0], x[1], x[2]};
          cs.add(rnd.nextBoolean() ? new Alldistinct(l) : new Alldiff(l));
          scope = l;
        }
        case 12 -> {
          int lo = x[0].min();
          cs.add(new ChannelReif(x[0], bs, new int[] {lo, lo + 1, lo + 2}));
          scope = new IntVar[] {x[0], bs[0], bs[1], bs[2]};
        }
        case 13 -> {
          IntVar index = new IntVar(store, "i", 1, 3);
          IntVar value = new IntVar(store, "v", -5, 5);
          int[] list = {rnd.nextInt(11) - 5, rnd.nextInt(11) - 5, rnd.nextInt(11) - 5};
          cs.add(new ChannelReif(index, bs, new int[] {1, 2, 3}));
          cs.add(new ElementInteger(index, list, value, 0));
          scope = new IntVar[] {index, value, bs[0], bs[1], bs[2]};
        }
        case 15 -> {
          // element over an index without value Booleans, with holes in its domain
          IntVar index = new IntVar(store, "i", 0, 6);
          index.domain.inComplement(0, index, 1 + rnd.nextInt(5));
          IntVar value = new IntVar(store, "v", -20, 20);
          int[] list = new int[5 + rnd.nextInt(3)];
          for (int i = 0; i < list.length; i++) {
            list[i] = rnd.nextInt(21) - 10;
          }
          int offset = rnd.nextInt(2) - 1;
          cs.add(
              rnd.nextBoolean()
                  ? new ElementInteger(index, list, value, offset)
                  : new ElementIntegerFast(index, list, value, offset));
          scope = new IntVar[] {index, value};
        }
        case 16 -> {
          int d = (1 + rnd.nextInt(4)) * (rnd.nextBoolean() ? 1 : -1);
          IntVar z = new IntVar(store, "z", -10, 10);
          cs.add(new XdivYeqZ(x[0], new IntVar(store, "d", d, d), z));
          scope = new IntVar[] {x[0], z};
        }
        case 17 -> {
          // the last condition may be fixed to 1 and a value fixed, as the FlatZinc if_then_else
          // gives them
          IntVar last = rnd.nextBoolean() ? bs[2] : new IntVar(store, "one", 1, 1);
          IntVar second = rnd.nextBoolean() ? x[1] : new IntVar(store, "k", k, k);
          IntVar[] conditions = {bs[0], bs[1], last};
          IntVar[] values = {x[0], second, x[2]};
          cs.add(new ConditionalSelect(conditions, values, x[3]));
          scope = new IntVar[] {bs[0], bs[1], last, x[0], second, x[2], x[3]};
        }
        case 18 -> {
          int lo = x[0].min() + rnd.nextInt(3) - 1;
          cs.add(new Reified(new In(x[0], new IntervalDomain(lo, lo + rnd.nextInt(3))), b));
          scope = new IntVar[] {x[0], b};
        }
        case 19 -> {
          // x = c (or x != c) reified with b or implied by b, as the FlatZinc constraints give them
          int c = x[0].min() + rnd.nextInt(x[0].getSize());
          boolean both = rnd.nextBoolean();
          boolean equal = rnd.nextBoolean();
          PrimitiveConstraint p = equal ? new XeqC(x[0], c) : new XneqC(x[0], c);
          cs.add(both ? new Reified(p, b) : new Implies(b, p));
          made.addAll(Linearizations.valueRows(x[0], c, b, both, equal));
          scope = new IntVar[] {x[0], b};
        }
        case 20 -> {
          cs.add(new Implies(b, new XeqY(x[0], x[1])));
          made.addAll(
              Linearizations.implied(
                  new LinearForm(new IntVar[] {x[0], x[1]}, new long[] {1, -1}, 0, LinearForm.EQ),
                  b,
                  false));
          scope = new IntVar[] {x[0], x[1], b};
        }
        default -> {
          int lo = x[0].min();
          cs.add(new Reified(new XeqC(x[0], lo), bs[0]));
          cs.add(new Reified(new XeqC(x[0], lo + 1), bs[1]));
          cs.add(new ChannelImply(x[0], new IntVar[] {bs[2]}, new int[] {lo + 2}));
          scope = new IntVar[] {x[0], bs[0], bs[1], bs[2]};
        }
      }
      for (Constraint c : cs) {
        made.addAll(Linearizations.of(c));
      }
      made.addAll(Linearizations.encodings(cs));
      rows += made.size();
      for (Constraint c : cs) {
        store.impose(c);
      }
      for (long[] solution : solutions(store, scope)) {
        for (LinearForm f : made) {
          assertThat(holds(f, scope, solution))
              .as("run %d %s at %s", run, f, java.util.Arrays.toString(solution))
              .isTrue();
        }
      }
    }
    assertThat(rows).isGreaterThan(5000);
  }

  @Test
  void tableCliquesHoldForEverySolutionAndKeepThemAll() {
    Random rnd = new Random(11);
    int rows = 0;
    for (int run = 0; run < 400; run++) {
      Store store = new Store();
      int n = 3 + rnd.nextInt(3);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 1 + rnd.nextInt(3));
        if (rnd.nextInt(3) == 0 && x[i].max() > 1) {
          x[i].domain.inComplement(0, x[i], 1);
        }
      }
      // some values already have the model's Boolean
      for (int i = 0; i < n; i++) {
        if (rnd.nextBoolean()) {
          store.impose(new Reified(new XeqC(x[i], 0), new IntVar(store, "r" + i, 0, 1)));
        }
      }
      List<TableCliques.Table> tables = new ArrayList<>();
      for (int t = 0; t < n + 1; t++) {
        int i = rnd.nextInt(n);
        int j = rnd.nextInt(n);
        if (i == j) {
          continue;
        }
        List<int[]> allowed = new ArrayList<>();
        for (int a = x[i].min(); a <= x[i].max(); a++) {
          for (int b = x[j].min(); b <= x[j].max(); b++) {
            if (rnd.nextInt(3) > 0) {
              allowed.add(new int[] {a, b});
            }
          }
        }
        if (allowed.isEmpty()) {
          continue;
        }
        int[][] tuples = allowed.toArray(new int[0][]);
        store.impose(new HybridTable(new IntVar[] {x[i], x[j]}, tuples));
        tables.add(new TableCliques.Table(new IntVar[] {x[i], x[j]}, tuples));
      }
      long before = count(x, tables, new int[n], 0);
      TableCliques.Result r = TableCliques.rows(tables);
      List<IntVar> scope = new ArrayList<>(List.of(x));
      for (LinearForm f : r.rows()) {
        for (IntVar v : f.vars()) {
          if (!(v instanceof LpColumn) && !scope.contains(v)) {
            scope.add(v);
          }
        }
      }
      IntVar[] all = scope.toArray(new IntVar[0]);
      List<long[]> after = solutions(store, all);
      assertThat(after).hasSize((int) before);
      for (long[] a : after) {
        for (LinearForm f : r.rows()) {
          assertThat(holds(f, all, a)).as("%s", f).isTrue();
        }
      }
      rows += r.rows().size();
    }
    assertThat(rows).isGreaterThan(300);
  }

  @Test
  void tableCliquesMergeConflictsIntoOneRowAndReuseTheModelsBooleans() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 1);
    IntVar y = new IntVar(store, "y", 0, 1);
    IntVar z = new IntVar(store, "z", 0, 1);
    IntVar notX = new IntVar(store, "notX", 0, 1);
    store.impose(new Reified(new XeqC(x, 0), notX));
    // at most one of x, y and z is 1: three tables that forbid (1, 1)
    int[][] tuples = {{0, 0}, {0, 1}, {1, 0}};
    List<TableCliques.Table> tables =
        List.of(
            new TableCliques.Table(new IntVar[] {x, y}, tuples),
            new TableCliques.Table(new IntVar[] {y, z}, tuples),
            new TableCliques.Table(new IntVar[] {x, z}, tuples));
    int before = store.size();
    TableCliques.Result r = TableCliques.rows(tables);
    // x = 0 has the model's Boolean; x = 1, y = 0, y = 1, z = 0 and z = 1 get LP-only columns,
    // and nothing is added to the store
    assertThat(r.columns()).isEqualTo(5);
    assertThat(store.size()).isEqualTo(before);
    List<LinearForm> cliques =
        r.rows().stream().filter(f -> f.relation() == LinearForm.LE).toList();
    assertThat(cliques).hasSize(1);
    assertThat(cliques.get(0).vars()).hasSize(3).doesNotContain(notX);
    assertThat(cliques.get(0).vars()).allMatch(v -> v instanceof LpColumn c && c.value() == 1);
    // each variable has sum b = 1 and x = sum v b, x over the model's Boolean for 0
    assertThat(r.rows()).hasSize(7);
    assertThat(r.rows().stream().filter(f -> Arrays.asList(f.vars()).contains(notX))).hasSize(2);
  }

  /**
   * The value encodings over LP-only columns: for random all-different-except constraints and
   * reified comparisons, every row holds in every solution with each column at the indicator of its
   * value.
   */
  @Test
  void valueColumnsHoldForEverySolution() {
    Random rnd = new Random(13);
    int rows = 0;
    int columns = 0;
    for (int run = 0; run < 600; run++) {
      Store store = new Store();
      int n = 3 + rnd.nextInt(3);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        int lo = rnd.nextInt(3) == 0 ? -1 : 0;
        x[i] = new IntVar(store, "x" + i, lo, lo + 2 + rnd.nextInt(3));
        if (rnd.nextBoolean()) {
          x[i].domain.inComplement(0, x[i], x[i].min() + 1 + rnd.nextInt(x[i].getSize() - 1));
        }
      }
      List<Constraint> cs = new ArrayList<>();
      for (int a = 0; a < 2; a++) {
        List<IntVar> pool = new ArrayList<>(List.of(x));
        IntVar[] list = new IntVar[2 + rnd.nextInt(n - 1)];
        for (int i = 0; i < list.length; i++) {
          list[i] = pool.remove(rnd.nextInt(pool.size()));
        }
        cs.add(
            switch (rnd.nextInt(3)) {
              case 0 -> new AlldifferentExceptZero(list);
              case 1 -> new AlldifferentExcept(list, new IntervalDomain(1, 1));
              default -> new AlldifferentExcept(list, new IntervalDomain(0, 1));
            });
      }
      List<IntVar> scope = new ArrayList<>(List.of(x));
      for (int r = 0; r < 4; r++) {
        IntVar b = new IntVar(store, "b" + r, 0, 1);
        scope.add(b);
        IntVar y = x[rnd.nextInt(n)];
        int c = rnd.nextInt(5) - 1;
        PrimitiveConstraint cmp =
            switch (rnd.nextInt(6)) {
              case 0 -> new XeqC(y, c);
              case 1 -> new XneqC(y, c);
              case 2 -> new XltC(y, c);
              case 3 -> new XlteqC(y, c);
              case 4 -> new XgtC(y, c);
              default -> new XgteqC(y, c);
            };
        cs.add(rnd.nextBoolean() ? new Reified(cmp, b) : new Implies(b, cmp));
      }
      List<LinearForm> made = Linearizations.valueColumns(cs);
      rows += made.size();
      for (LinearForm f : made) {
        for (IntVar v : f.vars()) {
          columns += v instanceof LpColumn ? 1 : 0;
        }
      }
      for (Constraint c : cs) {
        store.impose(c);
      }
      IntVar[] all = scope.toArray(new IntVar[0]);
      for (long[] solution : solutions(store, all)) {
        for (LinearForm f : made) {
          assertThat(holds(f, all, solution))
              .as("run %d %s at %s", run, f, Arrays.toString(solution))
              .isTrue();
        }
      }
    }
    assertThat(rows).isGreaterThan(3000);
    assertThat(columns).isGreaterThan(3000);
  }

  /**
   * The cliques of tables over three variables, from their projections on pairs: every row holds in
   * every solution of the tables with each column at the indicator of its value.
   */
  @Test
  void tableCliquesOfTernaryTablesHoldForEverySolution() {
    Random rnd = new Random(29);
    int rows = 0;
    for (int run = 0; run < 300; run++) {
      Store store = new Store();
      int n = 4;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 1 + rnd.nextInt(2));
      }
      List<TableCliques.Table> tables = new ArrayList<>();
      for (int t = 0; t < 2; t++) {
        List<IntVar> pool = new ArrayList<>(List.of(x));
        IntVar[] v = new IntVar[3];
        for (int k = 0; k < 3; k++) {
          v[k] = pool.remove(rnd.nextInt(pool.size()));
        }
        List<int[]> allowed = new ArrayList<>();
        for (int a = v[0].min(); a <= v[0].max(); a++) {
          for (int b = v[1].min(); b <= v[1].max(); b++) {
            for (int c = v[2].min(); c <= v[2].max(); c++) {
              if (rnd.nextInt(3) == 0) {
                allowed.add(new int[] {a, b, c});
              }
            }
          }
        }
        if (allowed.isEmpty()) {
          continue;
        }
        int[][] tuples = allowed.toArray(new int[0][]);
        store.impose(new HybridTable(v, tuples));
        tables.add(new TableCliques.Table(v, tuples));
      }
      TableCliques.Result r = TableCliques.rows(tables);
      for (long[] a : solutions(store, x)) {
        for (LinearForm f : r.rows()) {
          assertThat(holds(f, x, a)).as("run %d %s", run, f).isTrue();
        }
      }
      rows += r.rows().size();
    }
    assertThat(rows).isGreaterThan(1000);
  }

  /**
   * The value encodings of counting, all-different and element constraints over LP-only columns:
   * for random constraints of each kind, every row holds in every solution with each column at the
   * indicator of its value.
   */
  @Test
  void valueEncodingsHoldForEverySolution() {
    boolean binpacking = Linearizations.binpackingRows;
    // the bin packing rows are off by default
    Linearizations.binpackingRows = true;
    try {
      Random rnd = new Random(17);
      int rows = 0;
      int columns = 0;
      for (int run = 0; run < 600; run++) {
        Store store = new Store();
        int n = 3 + rnd.nextInt(2);
        IntVar[] x = new IntVar[n];
        for (int i = 0; i < n; i++) {
          int lo = rnd.nextInt(3) - 1;
          x[i] = new IntVar(store, "x" + i, lo, lo + 1 + rnd.nextInt(3));
          if (rnd.nextBoolean() && x[i].getSize() > 2) {
            // a hole inside the domain
            x[i].domain.inComplement(0, x[i], x[i].min() + 1 + rnd.nextInt(x[i].getSize() - 2));
          }
        }
        List<IntVar> scope = new ArrayList<>(List.of(x));
        List<Constraint> cs = new ArrayList<>();
        for (int k = 0; k < 2; k++) {
          List<IntVar> pool = new ArrayList<>(List.of(x));
          IntVar[] list = new IntVar[2 + rnd.nextInt(n - 1)];
          for (int i = 0; i < list.length; i++) {
            list[i] = pool.remove(rnd.nextInt(pool.size()));
          }
          IntervalDomain union = new IntervalDomain();
          for (IntVar v : list) {
            union.unionAdapt(v.dom());
          }
          switch (rnd.nextInt(8)) {
            case 0 -> cs.add(new Alldiff(list));
            case 5 -> {
              int[] w = new int[list.length];
              int total = 0;
              for (int i = 0; i < w.length; i++) {
                w[i] = rnd.nextInt(4);
                total += w[i];
              }
              IntVar[] loads = new IntVar[union.max() - union.min() + 1];
              for (int v = 0; v < loads.length; v++) {
                loads[v] = new IntVar(store, "l" + k + "_" + v, 0, total);
                scope.add(loads[v]);
              }
              cs.add(new Binpacking(list, loads, w, union.min()));
            }
            case 1 -> cs.add(new Alldistinct(list));
            case 2 -> {
              IntVar[] counters = new IntVar[union.getSize()];
              for (int v = 0; v < counters.length; v++) {
                counters[v] = new IntVar(store, "g" + k + "_" + v, 0, list.length);
                scope.add(counters[v]);
              }
              cs.add(new GCC(list, counters));
            }
            case 3 -> {
              int[] values = {union.min(), union.max()};
              IntVar[] counters = new IntVar[2];
              for (int v = 0; v < 2; v++) {
                counters[v] = new IntVar(store, "v" + k + "_" + v, 0, list.length);
                scope.add(counters[v]);
              }
              cs.add(new CountValues(list, counters, values));
            }
            case 4 -> {
              IntVar counter = new IntVar(store, "n" + k, 0, list.length);
              scope.add(counter);
              cs.add(
                  new Count(
                      list, counter, union.min() + rnd.nextInt(union.max() - union.min() + 1)));
            }
            default -> {
              IntVar index = list[0];
              int[] table = new int[index.max() - index.min() + 1];
              for (int i = 0; i < table.length; i++) {
                table[i] = rnd.nextInt(7) - 3;
              }
              IntVar y = new IntVar(store, "y" + k, -3, 3);
              scope.add(y);
              int offset = index.min() - 1;
              cs.add(
                  rnd.nextBoolean()
                      ? new ElementInteger(index, table, y, offset)
                      : new ElementIntegerFast(index, table, y, offset));
            }
          }
        }
        for (int r = 0; r < 2; r++) {
          IntVar b = new IntVar(store, "b" + r, 0, 1);
          scope.add(b);
          IntVar y = x[rnd.nextInt(n)];
          int c = rnd.nextInt(5) - 1;
          PrimitiveConstraint cmp = rnd.nextBoolean() ? new XlteqC(y, c) : new XeqC(y, c);
          cs.add(rnd.nextBoolean() ? new Reified(cmp, b) : new Implies(b, cmp));
        }
        List<LinearForm> made = Linearizations.valueRows(cs, List.of()).tried();
        rows += made.size();
        for (LinearForm f : made) {
          for (IntVar v : f.vars()) {
            columns += v instanceof LpColumn ? 1 : 0;
          }
        }
        for (Constraint c : cs) {
          store.impose(c);
        }
        IntVar[] all = scope.toArray(new IntVar[0]);
        for (long[] solution : solutions(store, all)) {
          for (LinearForm f : made) {
            assertThat(holds(f, all, solution))
                .as("run %d %s at %s", run, f, Arrays.toString(solution))
                .isTrue();
          }
        }
      }
      assertThat(rows).isGreaterThan(3000);
      assertThat(columns).isGreaterThan(3000);
    } finally {
      Linearizations.binpackingRows = binpacking;
    }
  }

  // the assignments of x[k..] in the domains of x that every table allows, given a[0..k)
  private static long count(IntVar[] x, List<TableCliques.Table> tables, int[] a, int k) {
    if (k == x.length) {
      for (TableCliques.Table t : tables) {
        int i = Arrays.asList(x).indexOf(t.x()[0]);
        int j = Arrays.asList(x).indexOf(t.x()[1]);
        if (Arrays.stream(t.tuples()).noneMatch(u -> u[0] == a[i] && u[1] == a[j])) {
          return 0;
        }
      }
      return 1;
    }
    long c = 0;
    for (ValueEnumeration e = x[k].domain.valueEnumeration(); e.hasMoreElements(); ) {
      a[k] = e.nextElement();
      c += count(x, tables, a, k + 1);
    }
    return c;
  }

  private static boolean holds(LinearForm f, IntVar[] scope, long[] value) {
    Function<IntVar, Long> v =
        aVar -> {
          if (aVar instanceof LpColumn c) {
            // [x = v], from the value of x
            for (int i = 0; i < scope.length; i++) {
              if (scope[i] == c.variable()) {
                return (long) c.valueIn((int) value[i]);
              }
            }
          }
          for (int i = 0; i < scope.length; i++) {
            if (scope[i] == aVar) {
              return value[i];
            }
          }
          throw new IllegalStateException(aVar + " outside the scope");
        };
    long sum = 0;
    for (int i = 0; i < f.vars().length; i++) {
      sum += f.weights()[i] * v.apply(f.vars()[i]);
    }
    return switch (f.relation()) {
      case LinearForm.LE -> sum <= f.c();
      case LinearForm.GE -> sum >= f.c();
      case LinearForm.EQ -> sum == f.c();
      default -> sum != f.c();
    };
  }

  private static List<long[]> solutions(Store store, IntVar[] scope) {
    List<long[]> found = new ArrayList<>();
    if (!store.consistency()) {
      return found;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            long[] a = new long[scope.length];
            for (int i = 0; i < scope.length; i++) {
              a[i] = scope[i].value();
            }
            found.add(a);
            return super.executeAfterSolution(s, select);
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, new SimpleSelect<>(scope, null, new IndomainMin<>()));
    return found;
  }

  /**
   * x != c with c inside the domain of x gives no rows: they would be the big-M pair of !b -> x = c
   * alone, which raised the nodes of still_life_no_border slnb7x7 from 22k to 32k. At a bound of x,
   * x != c is linear and keeps its rows.
   */
  @Test
  void notEqualRowsOnlyAtTheBounds() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 8);
    IntVar b = new IntVar(store, "b", 0, 1);
    assertThat(Linearizations.valueRows(x, 3, b, true, false)).isEmpty();
    assertThat(Linearizations.valueRows(x, 3, b, false, false)).isEmpty();
    assertThat(Linearizations.valueRows(x, 0, b, true, false)).isNotEmpty();
    assertThat(Linearizations.valueRows(x, 8, b, false, false)).isNotEmpty();
    assertThat(Linearizations.valueRows(x, 3, b, true, true)).isNotEmpty();
  }
}
