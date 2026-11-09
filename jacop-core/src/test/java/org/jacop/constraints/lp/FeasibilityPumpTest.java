/*
 * CapacityCutsTest.java
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

package org.jacop.constraints.lp;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.CountValuesBounds;
import org.jacop.constraints.Implies;
import org.jacop.constraints.In;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Linearizations;
import org.jacop.constraints.Reified;
import org.jacop.constraints.TableCliques;
import org.jacop.constraints.table.Table;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
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
 * Tests the feasibility pump on small car sequencing models, and the value encodings it relies on:
 * the rows of {@link CountValuesBounds} and of {@code b <-> x in S} over value columns, and the
 * table hulls keyed by a variable of more than 16 values, must hold on every solution.
 */
class FeasibilityPumpTest {

  // a car sequencing model: classes with demands, options with "at most cap in a window of size"
  private static final class Cars {
    final Store store = new Store();
    final IntVar[] slot;
    final IntVar[][] option;

    Cars(Random rnd, int slots, int classes, int options, boolean table) {
      slot = new IntVar[slots];
      for (int s = 0; s < slots; s++) {
        slot[s] = new IntVar(store, "slot" + s, 0, classes - 1);
      }
      // demands that add up to the slots
      int[] demand = new int[classes];
      for (int s = 0; s < slots; s++) {
        demand[s < classes ? s : rnd.nextInt(classes)]++;
      }
      int[] values = new int[classes];
      for (int c = 0; c < classes; c++) {
        values[c] = c;
      }
      store.impose(new CountValuesBounds(slot, demand, demand, values));
      boolean[][] requires = new boolean[classes][options];
      for (boolean[] r : requires) {
        for (int o = 0; o < options; o++) {
          r[o] = rnd.nextInt(3) == 0;
        }
      }
      option = new IntVar[slots][options];
      for (int s = 0; s < slots; s++) {
        for (int o = 0; o < options; o++) {
          option[s][o] = new IntVar(store, "o" + s + "_" + o, 0, 1);
        }
        if (table) {
          // the option bits of a slot as a function of its class, as merged elements give
          int[][] tuples = new int[classes][options + 1];
          for (int c = 0; c < classes; c++) {
            tuples[c][0] = c;
            for (int o = 0; o < options; o++) {
              tuples[c][o + 1] = requires[c][o] ? 1 : 0;
            }
          }
          IntVar[] x = new IntVar[options + 1];
          x[0] = slot[s];
          System.arraycopy(option[s], 0, x, 1, options);
          store.impose(new Table(x, tuples));
          tables.add(new TableCliques.Table(x, tuples));
        } else {
          for (int o = 0; o < options; o++) {
            IntDomain with = new IntervalDomain();
            for (int c = 0; c < classes; c++) {
              if (requires[c][o]) {
                with.unionAdapt(c, c);
              }
            }
            if (with.isEmpty()) {
              with.unionAdapt(-1, -1);
            }
            store.impose(new Reified(new In(slot[s], with), option[s][o]));
          }
        }
      }
      for (int o = 0; o < options; o++) {
        int size = 2 + rnd.nextInt(2);
        int cap = 1 + rnd.nextInt(size - 1);
        for (int s = 0; s + size <= slots; s++) {
          IntVar[] window = new IntVar[size];
          for (int k = 0; k < size; k++) {
            window[k] = option[s + k][o];
          }
          int[] ones = new int[size];
          Arrays.fill(ones, 1);
          store.impose(new LinearInt(window, ones, "<=", cap));
        }
      }
    }

    final List<TableCliques.Table> tables = new ArrayList<>();

    List<LinearForm> tableRows() {
      return tables.isEmpty()
          ? List.of()
          : TableCliques.rows(tables, java.util.Map.of(), FeasibilityPump.HULL_DOMAIN).all();
    }

    boolean solvable() {
      store.setLevel(store.level + 1);
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      search.setTimeOut(5);
      boolean found =
          store.consistency()
              && search.labeling(store, new SimpleSelect<>(slot, null, new IndomainMin<>()));
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
      return found;
    }

    // whether the values are a solution: fixed in the store, propagation holds
    boolean solution(IntVar[] vars, int[] values) {
      store.setLevel(store.level + 1);
      boolean ok = true;
      try {
        for (int i = 0; i < vars.length && ok; i++) {
          vars[i].domain.in(store.level, vars[i], values[i], values[i]);
          ok = store.consistency();
        }
        for (IntVar s : slot) {
          ok &= s.singleton();
        }
      } catch (org.jacop.core.FailException e) {
        ok = false;
      }
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
      return ok;
    }
  }

  @Test
  void pumpFindsCarSequences() {
    int integral = 0;
    int solved = 0;
    int models = 0;
    for (int run = 0; run < 40; run++) {
      Random rnd = new Random(run);
      Cars cars =
          new Cars(rnd, 10 + rnd.nextInt(6), 3 + rnd.nextInt(18), 2 + rnd.nextInt(2), run % 2 == 0);
      if (!cars.store.consistency() || !cars.solvable()) {
        continue;
      }
      models++;
      String before = Arrays.toString(cars.slot);
      FeasibilityPump pump = FeasibilityPump.of(cars.store, cars.tableRows(), List.of());
      assertThat(pump).as("seed %d", run).isNotNull();
      FeasibilityPump.Result r = pump.run(200, Long.MAX_VALUE, new Random(run));
      assertThat(r).as("seed %d", run).isNotNull();
      // the pump changes nothing in the store
      assertThat(Arrays.toString(cars.slot)).isEqualTo(before);
      for (int i = 0; i < r.vars().length; i++) {
        assertThat(r.vars()[i].domain.contains(r.values()[i])).isTrue();
      }
      if (r.integral()) {
        integral++;
        // the rows tie every option bit to the class of its slot: an integral point is a solution
        assertThat(cars.solution(r.vars(), r.values())).as("seed %d", run).isTrue();
        solved++;
      }
    }
    assertThat(models).isGreaterThan(10);
    assertThat(integral).as("%d of %d models", integral, models).isGreaterThan(models / 2);
    assertThat(solved).isEqualTo(integral);
  }

  @Test
  void encodingRowsHoldOnEverySolution() {
    for (int run = 0; run < 60; run++) {
      Random rnd = new Random(run);
      Cars cars =
          new Cars(rnd, 5 + rnd.nextInt(3), 2 + rnd.nextInt(18), 1 + rnd.nextInt(2), run % 3 == 0);
      Store store = cars.store;
      // implications as well as equivalences
      IntVar b = new IntVar(store, "b", 0, 1);
      store.impose(new Implies(b, new In(cars.slot[0], new IntervalDomain(0, rnd.nextInt(3)))));
      List<Constraint> constraints = new ArrayList<>(LinearRelaxation.constraintsOf(store));
      List<LinearForm> extra = new ArrayList<>(cars.tableRows());
      Linearizations.ValueRows rows = Linearizations.valueRows(constraints, extra, true, true);
      List<LinearForm> all = new ArrayList<>(extra);
      all.addAll(rows.kept());
      all.addAll(rows.tried());
      assertThat(all).as("seed %d", run).isNotEmpty();
      List<String> broken = new ArrayList<>();
      int[] found = {0};
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      search.setSolutionListener(
          new SimpleSolutionListener<>() {
            @Override
            public boolean executeAfterSolution(
                Search<IntVar> s, SelectChoicePoint<IntVar> select) {
              found[0]++;
              for (LinearForm f : all) {
                if (f.relation() != LinearForm.NE && !holds(f)) {
                  broken.add(f.toString());
                }
              }
              return super.executeAfterSolution(s, select);
            }
          });
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      List<IntVar> vars = new ArrayList<>(Arrays.asList(cars.slot));
      for (IntVar[] o : cars.option) {
        vars.addAll(Arrays.asList(o));
      }
      vars.add(b);
      if (store.consistency()) {
        search.labeling(
            store, new SimpleSelect<>(vars.toArray(new IntVar[0]), null, new IndomainMin<>()));
      }
      assertThat(broken).as("seed %d, %d solutions", run, found[0]).isEmpty();
    }
  }

  // a row under a solution, with the value columns at the indicators of the values
  private static boolean holds(LinearForm f) {
    long sum = 0;
    for (int k = 0; k < f.vars().length; k++) {
      IntVar v = f.vars()[k];
      long value;
      if (v instanceof LpColumn c && !c.isFree() && !c.isArc()) {
        value = c.variable().value() == c.value() ? 1 : 0;
      } else if (v instanceof LpColumn) {
        // a tuple or free column has no value in the store: the row is not checked
        return true;
      } else {
        value = v.value();
      }
      sum += f.weights()[k] * value;
    }
    return switch (f.relation()) {
      case LinearForm.LE -> sum <= f.c();
      case LinearForm.GE -> sum >= f.c();
      default -> sum == f.c();
    };
  }
}
