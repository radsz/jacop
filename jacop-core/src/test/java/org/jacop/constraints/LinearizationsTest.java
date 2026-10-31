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
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.IntVar;
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
  void rowsHoldForEverySolution() {
    Random rnd = new Random(7);
    int rows = 0;
    for (int run = 0; run < 3000; run++) {
      int kind = run % 15;
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
        default -> {
          int lo = x[0].min();
          cs.add(new Reified(new XeqC(x[0], lo), bs[0]));
          cs.add(new Reified(new XeqC(x[0], lo + 1), bs[1]));
          cs.add(new ChannelImply(x[0], new IntVar[] {bs[2]}, new int[] {lo + 2}));
          scope = new IntVar[] {x[0], bs[0], bs[1], bs[2]};
        }
      }
      List<LinearForm> made = new ArrayList<>();
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
      TableCliques.Result r = TableCliques.rows(store, tables);
      List<IntVar> scope = new ArrayList<>(List.of(x));
      for (LinearForm f : r.rows()) {
        for (IntVar v : f.vars()) {
          if (!scope.contains(v)) {
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
    TableCliques.Result r = TableCliques.rows(store, tables);
    // x = 0 has the model's Boolean; x = 1, y = 0, y = 1, z = 0 and z = 1 get new ones
    assertThat(r.booleans()).isEqualTo(5);
    assertThat(r.rows()).hasSize(1);
    assertThat(r.rows().get(0).vars()).hasSize(3);
    assertThat(r.rows().get(0).vars()).doesNotContain(notX);
    assertThat(Linearizations.valueBooleans(List.copyOf(x.dom().constraints())).get(x))
        .containsEntry(0, notX);
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
        var -> {
          for (int i = 0; i < scope.length; i++) {
            if (scope[i] == var) {
              return value[i];
            }
          }
          throw new IllegalStateException(var + " outside the scope");
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
}
