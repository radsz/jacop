/*
 * LcgBindControlsTest.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.lcg;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XlteqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.junit.jupiter.api.Test;

/**
 * Binding the controls of value reifications {@code b <-> [x = c]} to the literals of their atoms
 * ({@link LcgSolver#bindValueControls}): on random models of channels, clauses over the controls,
 * controls of other reified constraints and sums over the controls, the optimum with checked
 * explanations must be the one of enumerating every assignment, in each binding mode.
 */
class LcgBindControlsTest {

  private static final int RUNS = Integer.getInteger("lcg.bind.runs", 400);

  private static final String[] MODES = {"all", "clauses", "controls", "off"};

  // a control b <-> [x[var] = value]
  private record Item(IntVar b, int var, int value) {}

  // a clause over controls: item indices with signs (+1 for b, -1 for not b)
  private record Clause(int[] items, int[] signs) {}

  // b <-> [x[var] <= value]
  private record OrderControl(int item, int var, int value) {}

  // sum of controls <= bound
  private record ControlSum(int[] items, int bound) {}

  @Test
  void boundControlsKeepTheOptimum() {
    long bound = 0;
    long removed = 0;
    for (int run = 0; run < RUNS; run++) {
      Random rnd = new Random(run);
      String mode = MODES[run % MODES.length];
      Store store = new Store();
      int n = 2 + rnd.nextInt(3);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 4);
        if (rnd.nextInt(3) == 0) {
          x[i].domain.inComplement(store.level, x[i], 1 + rnd.nextInt(3));
        }
      }
      List<Item> items = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        int k = 1 + rnd.nextInt(4);
        List<Integer> values = new ArrayList<>(List.of(0, 1, 2, 3, 4));
        java.util.Collections.shuffle(values, rnd);
        IntVar[] bs = new IntVar[k];
        int[] vs = new int[k];
        for (int j = 0; j < k; j++) {
          bs[j] = new IntVar(store, "b" + i + "_" + values.get(j), 0, 1);
          vs[j] = values.get(j);
          items.add(new Item(bs[j], i, vs[j]));
        }
        store.impose(new ChannelReif(x[i], bs, vs));
      }
      List<Clause> clauses = new ArrayList<>();
      for (int c = rnd.nextInt(6); c > 0; c--) {
        int size = 1 + rnd.nextInt(3);
        int[] is = new int[size];
        int[] signs = new int[size];
        for (int j = 0; j < size; j++) {
          is[j] = rnd.nextInt(items.size());
          signs[j] = rnd.nextBoolean() ? 1 : -1;
        }
        clauses.add(new Clause(is, signs));
      }
      List<OrderControl> orders = new ArrayList<>();
      for (int c = rnd.nextInt(3); c > 0; c--) {
        OrderControl o =
            new OrderControl(rnd.nextInt(items.size()), rnd.nextInt(n), rnd.nextInt(5));
        orders.add(o);
        store.impose(new Reified(new XlteqC(x[o.var], o.value), items.get(o.item).b));
      }
      List<ControlSum> sums = new ArrayList<>();
      if (rnd.nextBoolean()) {
        int size = 2 + rnd.nextInt(2);
        int[] is = new int[size];
        IntVar[] bs = new IntVar[size];
        int[] ones = new int[size];
        for (int j = 0; j < size; j++) {
          is[j] = rnd.nextInt(items.size());
          bs[j] = items.get(is[j]).b;
          ones[j] = 1;
        }
        ControlSum s = new ControlSum(is, rnd.nextInt(size));
        sums.add(s);
        store.impose(new LinearInt(bs, ones, "<=", s.bound));
      }
      List<int[]> fixed = new ArrayList<>();
      if (rnd.nextInt(4) == 0) {
        // a control fixed by a constraint of its own
        int[] f = {rnd.nextInt(items.size()), rnd.nextInt(2)};
        fixed.add(f);
        store.impose(new XeqC(items.get(f[0]).b, f[1]));
      }
      int[] w = new int[n + 1];
      for (int i = 0; i < n; i++) {
        w[i] = rnd.nextInt(7) - 3;
      }
      w[n] = -1;
      IntVar cost = new IntVar(store, "cost", -100, 100);
      IntVar[] terms = java.util.Arrays.copyOf(x, n + 1);
      terms[n] = cost;
      store.impose(new LinearInt(terms, w, "==", 0));

      long best = minimum(x, items, clauses, orders, sums, w, fixed);

      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.setSeed(run % 3);
      long now = solver.bindValueControls(mode, cost);
      bound += now;
      removed += solver.channelsBound;
      if ("off".equals(mode)) {
        assertThat(now).isZero();
      }
      for (Clause c : clauses) {
        List<IntVar> pos = new ArrayList<>();
        List<IntVar> neg = new ArrayList<>();
        for (int j = 0; j < c.items.length; j++) {
          (c.signs[j] > 0 ? pos : neg).add(items.get(c.items[j]).b);
        }
        if (!pos.isEmpty() || !neg.isEmpty()) {
          solver.addClause(pos.toArray(new IntVar[0]), neg.toArray(new IntVar[0]));
        }
      }
      int status = solver.minimize(cost);
      String where = "run " + run + " mode " + mode;
      if (best == Long.MAX_VALUE) {
        assertThat(status).as(where).isEqualTo(CdclSolver.UNSAT);
        continue;
      }
      assertThat(status).as(where).isEqualTo(CdclSolver.SAT);
      assertThat((long) solver.value(cost)).as(where).isEqualTo(best);
      int[] t = new int[n];
      for (int i = 0; i < n; i++) {
        t[i] = solver.value(x[i]);
      }
      for (Item it : items) {
        assertThat(solver.value(it.b))
            .as(where + ": " + it.b)
            .isEqualTo(t[it.var] == it.value ? 1 : 0);
      }
      assertThat(holds(t, items, clauses, orders, sums)).as(where).isTrue();
    }
    System.out.printf(
        "lcg bind controls: %d controls bound, %d channels removed%n", bound, removed);
    assertThat(bound).isPositive();
  }

  private static long minimum(
      IntVar[] x,
      List<Item> items,
      List<Clause> clauses,
      List<OrderControl> orders,
      List<ControlSum> sums,
      int[] w,
      List<int[]> fixedControls) {
    int n = x.length;
    int[] t = new int[n];
    long best = Long.MAX_VALUE;
    int total = 1;
    for (int i = 0; i < n; i++) {
      total *= 5;
    }
    for (int code = 0; code < total; code++) {
      int c = code;
      boolean in = true;
      long sum = 0;
      for (int i = 0; i < n; i++) {
        t[i] = c % 5;
        c /= 5;
        in &= x[i].domain.contains(t[i]);
        sum += (long) w[i] * t[i];
      }
      if (!in || sum < -100 || sum > 100 || !holds(t, items, clauses, orders, sums)) {
        continue;
      }
      boolean fixedOk = true;
      for (int[] f : fixedControls) {
        Item it = items.get(f[0]);
        fixedOk &= (t[it.var] == it.value ? 1 : 0) == f[1];
      }
      if (fixedOk) {
        best = Math.min(best, sum);
      }
    }
    return best;
  }

  private static boolean holds(
      int[] t,
      List<Item> items,
      List<Clause> clauses,
      List<OrderControl> orders,
      List<ControlSum> sums) {
    for (Clause c : clauses) {
      boolean sat = false;
      for (int j = 0; j < c.items.length; j++) {
        Item it = items.get(c.items[j]);
        boolean on = t[it.var] == it.value;
        sat |= on == c.signs[j] > 0;
      }
      if (!sat) {
        return false;
      }
    }
    for (OrderControl o : orders) {
      Item it = items.get(o.item);
      if ((t[it.var] == it.value) != (t[o.var] <= o.value)) {
        return false;
      }
    }
    for (ControlSum s : sums) {
      int count = 0;
      for (int k : s.items) {
        Item it = items.get(k);
        count += t[it.var] == it.value ? 1 : 0;
      }
      if (count > s.bound) {
        return false;
      }
    }
    return true;
  }
}
