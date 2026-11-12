/*
 * SequenceMddTest.java
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.SequenceMdd;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Tests {@link SequenceMdd} against the enumeration of all circuits of small random instances with
 * time windows and arc costs: an exact diagram (width large enough) keeps exactly the successor
 * values of the feasible circuits (no costlier than the cost's maximum) and gives the earliest
 * return time and the least cost; a narrow one keeps at least those, and every time of their
 * earliest schedules.
 */
public class SequenceMddTest {

  private static final int TRIALS = Integer.getInteger("sequenceMdd.trials", 1000);

  private static final int OFFSET = 3;

  private record Instance(
      int n, int[][] travel, int[] delta, int[][] inWin, int[][] outWin, int[][] costs) {}

  private static Instance random(Random r) {
    int n = 3 + r.nextInt(4);
    int[][] travel = new int[n][n];
    int[] delta = new int[n];
    int[][] inWin = new int[n][2];
    int[][] outWin = new int[n][2];
    int[][] costs = new int[n][n];
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        travel[i][j] = r.nextInt(8) == 0 ? SequenceMdd.NONE : r.nextInt(10);
        costs[i][j] = r.nextInt(20);
      }
      delta[i] = r.nextInt(6) == 0 ? SequenceMdd.NONE : r.nextInt(4);
      int a = r.nextInt(25);
      inWin[i][0] = a;
      inWin[i][1] = a + r.nextInt(30);
      int b = r.nextInt(25);
      outWin[i][0] = b;
      outWin[i][1] = b + r.nextInt(35);
    }
    delta[0] = SequenceMdd.NONE;
    outWin[0][0] = 0;
    outWin[0][1] = 0;
    inWin[0][0] = 0;
    inWin[0][1] = 200;
    return new Instance(n, travel, delta, inWin, outWin, costs);
  }

  // one feasible circuit from node 0: its order, earliest schedule (in then out) and cost
  private record Circuit(int[] order, long[] times, long cost) {}

  private static List<Circuit> enumerate(Instance p) {
    int n = p.n;
    List<Circuit> result = new ArrayList<>();
    int[] perm = new int[n - 1];
    for (int i = 0; i < n - 1; i++) {
      perm[i] = i + 1;
    }
    do {
      long t = p.outWin[0][0];
      long[] times = new long[2 * n];
      times[n] = t;
      long c = 0;
      int last = 0;
      boolean ok = true;
      for (int k = 0; k < n && ok; k++) {
        int j = k < n - 1 ? perm[k] : 0;
        c += p.costs[last][j];
        long a = p.inWin[j][0];
        if (p.travel[last][j] != SequenceMdd.NONE) {
          a = Math.max(a, t + p.travel[last][j]);
        }
        if (a > p.inWin[j][1]) {
          ok = false;
        } else if (j == 0) {
          times[0] = a;
        } else {
          times[j] = a;
          long d = p.outWin[j][0];
          if (p.delta[j] != SequenceMdd.NONE) {
            d = Math.max(d, a + p.delta[j]);
          }
          ok = d <= p.outWin[j][1];
          times[n + j] = d;
          t = d;
          last = j;
        }
      }
      if (ok) {
        result.add(new Circuit(perm.clone(), times, c));
      }
    } while (next(perm));
    return result;
  }

  private static boolean next(int[] a) {
    int i = a.length - 2;
    while (i >= 0 && a[i] >= a[i + 1]) {
      i--;
    }
    if (i < 0) {
      return false;
    }
    int j = a.length - 1;
    while (a[j] <= a[i]) {
      j--;
    }
    int t = a[i];
    a[i] = a[j];
    a[j] = t;
    for (int l = i + 1, r = a.length - 1; l < r; l++, r--) {
      t = a[l];
      a[l] = a[r];
      a[r] = t;
    }
    return true;
  }

  // costMode: -1 no cost, 0 a cost without bound, 1 a cost at most the least one
  private static void check(Instance p, boolean pred, int width, boolean exact, int costMode) {
    int n = p.n;
    List<Circuit> all = enumerate(p);
    long least = Long.MAX_VALUE;
    for (Circuit c : all) {
      least = Math.min(least, c.cost);
    }
    long budget = costMode == 1 ? least : Long.MAX_VALUE;
    List<Circuit> kept = new ArrayList<>();
    long best = Long.MAX_VALUE;
    boolean[][] supported = new boolean[n][n];
    for (Circuit c : all) {
      if (c.cost <= budget) {
        kept.add(c);
        best = Math.min(best, c.times[0]);
        int prev = 0;
        for (int j : c.order) {
          supported[prev][j] = true;
          prev = j;
        }
        supported[prev][0] = true;
      }
    }
    Store store = new Store();
    IntVar[] arcs = new IntVar[n];
    IntVar[] in = new IntVar[n];
    IntVar[] out = new IntVar[n];
    for (int i = 0; i < n; i++) {
      arcs[i] = new IntVar(store, "x" + i, 1, n);
      in[i] = new IntVar(store, "in" + i, p.inWin[i][0], p.inWin[i][1]);
      out[i] = new IntVar(store, "out" + i, p.outWin[i][0], p.outWin[i][1]);
    }
    IntVar cost = null;
    if (costMode < 0) {
      store.impose(new SequenceMdd(arcs, pred, 1, in, out, p.travel, p.delta, 0, width));
    } else {
      long hi = costMode == 1 && least != Long.MAX_VALUE ? least + OFFSET : 10_000;
      cost = new IntVar(store, "cost", 0, (int) hi);
      store.impose(
          new SequenceMdd(
              arcs, pred, 1, in, out, p.travel, p.delta, 0, width, p.costs, cost, OFFSET));
    }
    boolean consistent = store.consistency();
    if (kept.isEmpty()) {
      if (exact) {
        assertFalse(consistent, "exact diagram keeps an infeasible instance");
      }
      return;
    }
    assertTrue(consistent, "a feasible instance failed");
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (i == j) {
          continue;
        }
        boolean has = pred ? arcs[j].domain.contains(i + 1) : arcs[i].domain.contains(j + 1);
        if (supported[i][j]) {
          assertTrue(has, "removed the arc " + i + "->" + j + " of a feasible circuit");
        } else if (exact) {
          assertFalse(has, "exact diagram kept the arc " + i + "->" + j);
        }
      }
    }
    for (Circuit c : kept) {
      for (int j = 0; j < n; j++) {
        assertTrue(in[j].domain.contains((int) c.times[j]), "cut a feasible arrival at " + j);
        assertTrue(
            out[j].domain.contains((int) c.times[n + j]), "cut a feasible departure at " + j);
      }
    }
    assertTrue(in[0].min() <= best, "return time bound above the optimum");
    if (exact && costMode < 0) {
      assertEquals(best, in[0].min(), "exact diagram return time");
    }
    if (cost != null) {
      assertTrue(cost.min() <= least + OFFSET, "cost bound above the optimum");
      if (exact) {
        assertEquals(least + OFFSET, cost.min(), "exact diagram cost");
      }
    }
  }

  @Test
  public void exactDiagramMatchesEnumeration() {
    Random r = new Random(17);
    for (int t = 0; t < TRIALS; t++) {
      check(random(r), t % 2 == 0, 1000, true, -1);
    }
  }

  @Test
  public void narrowDiagramIsARelaxation() {
    Random r = new Random(23);
    for (int t = 0; t < TRIALS; t++) {
      check(random(r), t % 2 == 1, 1 + r.nextInt(3), false, -1);
    }
  }

  // with times and costs the earliest time and the least cost of a (set, last) may come from
  // different paths, so the diagram is exact for costs only when no arc carries a time
  @Test
  public void exactDiagramWithCosts() {
    Random r = new Random(29);
    for (int t = 0; t < TRIALS; t++) {
      Instance p = random(r);
      for (int[] row : p.travel) {
        Arrays.fill(row, SequenceMdd.NONE);
      }
      check(p, t % 2 == 0, 1000, true, t % 3 == 0 ? 0 : 1);
    }
  }

  @Test
  public void narrowDiagramWithCostsIsARelaxation() {
    Random r = new Random(31);
    for (int t = 0; t < TRIALS; t++) {
      check(random(r), t % 2 == 1, 1 + r.nextInt(3), false, t % 3 == 0 ? 0 : 1);
    }
  }

  // the relation on a complete assignment, written independently of the constraint
  private static boolean holds(Instance p, boolean pred, int[] x, int[] in, int[] out) {
    int n = p.n;
    int[] succ = new int[n];
    Arrays.fill(succ, -1);
    for (int i = 0; i < n; i++) {
      int v = x[i] - 1;
      if (pred) {
        if (succ[v] >= 0) {
          return false;
        }
        succ[v] = i;
      } else {
        succ[i] = v;
      }
    }
    boolean[] seen = new boolean[n];
    int i = 0;
    for (int k = 0; k < n; k++) {
      if (succ[i] < 0 || seen[i]) {
        return false;
      }
      seen[i] = true;
      int j = succ[i];
      if (p.travel[i][j] != SequenceMdd.NONE && in[j] < out[i] + p.travel[i][j]) {
        return false;
      }
      i = j;
    }
    if (i != 0) {
      return false;
    }
    for (int j = 0; j < n; j++) {
      if (p.delta[j] != SequenceMdd.NONE && out[j] < in[j] + p.delta[j]) {
        return false;
      }
    }
    return true;
  }

  private static int bruteCount(Instance p, boolean pred, int[] x, int[] in, int[] out, int k) {
    int n = p.n;
    if (k == 3 * n) {
      return holds(p, pred, x, in, out) ? 1 : 0;
    }
    int[] a = k < n ? x : k < 2 * n ? in : out;
    int j = k % n;
    int lo = k < n ? 1 : k < 2 * n ? p.inWin[j][0] : p.outWin[j][0];
    int hi = k < n ? n : k < 2 * n ? p.inWin[j][1] : p.outWin[j][1];
    int c = 0;
    for (int v = lo; v <= hi; v++) {
      a[j] = v;
      c += bruteCount(p, pred, x, in, out, k + 1);
    }
    return c;
  }

  // the constraint alone is a checker: a search over all its variables finds exactly the
  // assignments of the relation, also with narrow diagrams whose calls back off
  @Test
  public void searchFindsExactlyTheRelation() {
    Random r = new Random(37);
    for (int t = 0; t < TRIALS / 4; t++) {
      int n = 3 + r.nextInt(2);
      int[][] travel = new int[n][n];
      int[] delta = new int[n];
      int[][] inWin = new int[n][2];
      int[][] outWin = new int[n][2];
      for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
          travel[i][j] = r.nextInt(6) == 0 ? SequenceMdd.NONE : r.nextInt(4);
        }
        delta[i] = r.nextInt(5) == 0 ? SequenceMdd.NONE : r.nextInt(3);
        inWin[i][0] = r.nextInt(8);
        inWin[i][1] = inWin[i][0] + r.nextInt(2);
        outWin[i][0] = r.nextInt(8);
        outWin[i][1] = outWin[i][0] + r.nextInt(2);
      }
      delta[0] = SequenceMdd.NONE;
      Instance p = new Instance(n, travel, delta, inWin, outWin, new int[n][n]);
      boolean pred = t % 2 == 0;
      int expected = bruteCount(p, pred, new int[n], new int[n], new int[n], 0);
      Store store = new Store();
      IntVar[] vars = new IntVar[3 * n];
      IntVar[] arcs = new IntVar[n];
      IntVar[] in = new IntVar[n];
      IntVar[] out = new IntVar[n];
      for (int i = 0; i < n; i++) {
        arcs[i] = new IntVar(store, "x" + i, 1, n);
        in[i] = new IntVar(store, "in" + i, inWin[i][0], inWin[i][1]);
        out[i] = new IntVar(store, "out" + i, outWin[i][0], outWin[i][1]);
        vars[i] = arcs[i];
        vars[n + i] = in[i];
        vars[2 * n + i] = out[i];
      }
      SequenceMdd c = new SequenceMdd(arcs, pred, 1, in, out, travel, delta, 0, 1 + r.nextInt(2));
      store.impose(c);
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      int found = 0;
      if (store.consistency()) {
        search.labeling(store, new SimpleSelect<>(vars, null, new IndomainMin<>()));
        found = search.getSolutionListener().solutionsNo();
      }
      assertEquals(expected, found, "solutions of instance " + t + ", " + (pred ? "pred" : "succ"));
      for (int k = 0; k < 20; k++) {
        int[] xs = new int[n];
        int[] ins = new int[n];
        int[] outs = new int[n];
        Store ground = new Store();
        IntVar[] gx = new IntVar[n];
        IntVar[] gin = new IntVar[n];
        IntVar[] gout = new IntVar[n];
        for (int i = 0; i < n; i++) {
          xs[i] = 1 + r.nextInt(n);
          ins[i] = inWin[i][0] + r.nextInt(inWin[i][1] - inWin[i][0] + 1);
          outs[i] = outWin[i][0] + r.nextInt(outWin[i][1] - outWin[i][0] + 1);
          gx[i] = new IntVar(ground, xs[i], xs[i]);
          gin[i] = new IntVar(ground, ins[i], ins[i]);
          gout[i] = new IntVar(ground, outs[i], outs[i]);
        }
        SequenceMdd g = new SequenceMdd(gx, pred, 1, gin, gout, travel, delta, 0, 2);
        assertEquals(holds(p, pred, xs, ins, outs), g.satisfied(), "satisfied() of instance " + t);
      }
    }
  }
}
