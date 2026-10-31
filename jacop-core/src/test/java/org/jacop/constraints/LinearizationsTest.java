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
import java.util.List;
import java.util.Random;
import java.util.function.Function;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
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
      int kind = run % 18;
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
        case 15 -> {
          // an index with holes and values outside the list removed by propagation first
          IntVar index = new IntVar(store, "i", 1, 6);
          index.domain.subtract(1 + rnd.nextInt(6));
          IntVar value = new IntVar(store, "v", -20, 20);
          int[] list = new int[6];
          for (int i = 0; i < list.length; i++) {
            list[i] = rnd.nextInt(21) - 10;
          }
          cs.add(new ElementInteger(index, list, value, 0));
          scope = new IntVar[] {index, value};
        }
        case 16 -> {
          IntVar[] bin = new IntVar[3];
          for (int i = 0; i < bin.length; i++) {
            bin[i] = new IntVar(store, "bin" + i, 1, 2);
          }
          IntVar[] load = {new IntVar(store, "l1", 0, 9), new IntVar(store, "l2", 0, 9)};
          int[] ws = {1 + rnd.nextInt(4), 1 + rnd.nextInt(4), rnd.nextInt(4)};
          cs.add(new org.jacop.constraints.binpacking.Binpacking(bin, load, ws));
          scope = new IntVar[] {bin[0], bin[1], bin[2], load[0], load[1]};
        }
        case 17 -> {
          IntVar[] succ = new IntVar[4];
          for (int i = 0; i < succ.length; i++) {
            succ[i] = new IntVar(store, "s" + i, 1, 4);
          }
          cs.add(rnd.nextBoolean() ? new Circuit(succ) : new Subcircuit(succ));
          scope = succ;
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
  void elementGetsTheFacetsOfTheHullOfItsPoints() {
    // y = [0, 10, 0][x]: the upper hull is y <= 10 x - 10 and y <= 30 - 10 x; the lower one is flat
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 3);
    IntVar y = new IntVar(store, "y", -20, 20);
    List<LinearForm> rows = Linearizations.of(new ElementInteger(x, new int[] {0, 10, 0}, y, 0));
    assertThat(rows).hasSize(2);
    for (LinearForm f : rows) {
      assertThat(f.relation()).isEqualTo(LinearForm.LE);
      assertThat(holds(f, new IntVar[] {x, y}, new long[] {2, 10})).isTrue();
      assertThat(holds(f, new IntVar[] {x, y}, new long[] {2, 11})).isFalse();
    }
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
