/*
 * CostNetworkBoundTest.java
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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Random;
import org.jacop.constraints.cfn.CostNetwork;
import org.jacop.constraints.cfn.CostNetworkBound;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.ExplanationChecker;
import org.junit.jupiter.api.Test;

/**
 * Checks of {@link CostNetwork} and {@link CostNetworkBound} on small random networks against brute
 * force: the bound never passes the optimum, propagation keeps every assignment whose cost fits the
 * objective, and the reasons imply their atoms.
 */
class CostNetworkBoundTest {

  // -Dcostnetwork.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("costnetwork.instances", 600);

  private static final long HARD = CostNetwork.HARD;

  /** A random network and its costs kept aside, since solving changes the network. */
  private record Instance(int[][] values, long[][] unary, long[][][] binary, long constant) {

    CostNetwork network() {
      CostNetwork net = new CostNetwork(values);
      net.addConstant(constant);
      for (int i = 0; i < values.length; i++) {
        for (int a = 0; a < values[i].length; a++) {
          net.addUnary(i, a, unary[i][a]);
        }
      }
      for (int i = 0; i < values.length; i++) {
        for (int j = i + 1; j < values.length; j++) {
          if (binary[i][j] != null) {
            net.addBinary(i, j, binary[i][j]);
          }
        }
      }
      return net;
    }

    // the cost of an assignment by value indexes, HARD when a function forbids it
    long cost(int[] at) {
      long s = constant;
      for (int i = 0; i < values.length; i++) {
        if (unary[i][at[i]] == HARD) {
          return HARD;
        }
        s += unary[i][at[i]];
      }
      for (int i = 0; i < values.length; i++) {
        for (int j = i + 1; j < values.length; j++) {
          if (binary[i][j] != null) {
            long c = binary[i][j][at[i] * values[j].length + at[j]];
            if (c == HARD) {
              return HARD;
            }
            s += c;
          }
        }
      }
      return s;
    }

    // the least cost of an assignment within the domains (by value), HARD when none
    long optimum(IntDomain[] domains, int fixVar, int fixValue) {
      int n = values.length;
      int[] at = new int[n];
      long best = HARD;
      while (true) {
        boolean inside = true;
        for (int i = 0; i < n && inside; i++) {
          int v = values[i][at[i]];
          inside = (domains == null || domains[i].contains(v)) && (i != fixVar || v == fixValue);
        }
        if (inside) {
          best = Math.min(best, cost(at));
        }
        int k = 0;
        while (k < n && ++at[k] == values[k].length) {
          at[k] = 0;
          k++;
        }
        if (k == n) {
          return best;
        }
      }
    }
  }

  private static Instance random(Random rnd) {
    int n = 2 + rnd.nextInt(4);
    int[][] values = new int[n][];
    for (int i = 0; i < n; i++) {
      int d = 1 + rnd.nextInt(4);
      values[i] = new int[d];
      int v = rnd.nextInt(3) - 1;
      for (int a = 0; a < d; a++) {
        v += 1 + rnd.nextInt(2);
        values[i][a] = v;
      }
    }
    long[][] unary = new long[n][];
    for (int i = 0; i < n; i++) {
      unary[i] = new long[values[i].length];
      for (int a = 0; a < unary[i].length; a++) {
        unary[i][a] = rnd.nextInt(8) == 0 ? HARD : rnd.nextInt(7) - (rnd.nextInt(6) == 0 ? 3 : 0);
      }
    }
    long[][][] binary = new long[n][n][];
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        int kind = rnd.nextInt(4);
        if (kind == 0) {
          continue;
        }
        int di = values[i].length;
        int dj = values[j].length;
        long[] c = new long[di * dj];
        if (kind == 1 && di == dj) {
          // a hard bijection, sometimes partial, with costs on its pairs
          int shift = rnd.nextInt(di);
          java.util.Arrays.fill(c, HARD);
          for (int a = 0; a < di; a++) {
            if (rnd.nextInt(5) != 0) {
              c[a * dj + (a + shift) % dj] = rnd.nextInt(3);
            }
          }
        } else {
          for (int k = 0; k < c.length; k++) {
            c[k] = rnd.nextInt(6) == 0 ? HARD : rnd.nextInt(10);
          }
        }
        binary[i][j] = c;
      }
    }
    return new Instance(values, unary, binary, rnd.nextInt(5) - 2);
  }

  @Test
  void boundIsAtMostTheOptimum() {
    Random rnd = new Random(5);
    int infeasible = 0;
    int tight = 0;
    for (int instance = 0; instance < INSTANCES; instance++) {
      Instance inst = random(rnd);
      long opt = inst.optimum(null, -1, 0);
      CostNetwork.Solution s = inst.network().solve(Long.MAX_VALUE, 200);
      long b = s.bound();
      if (opt == HARD) {
        infeasible++;
        continue;
      }
      assertTrue(b != HARD, "infeasible bound on a feasible network " + instance);
      long lb = Math.ceilDiv(b, s.scale);
      assertTrue(lb <= opt, "bound " + lb + " above the optimum " + opt + " in " + instance);
      if (lb == opt) {
        tight++;
      }
    }
    assertTrue(infeasible > 0 && tight > INSTANCES / 4, infeasible + " infeasible, tight " + tight);
  }

  @Test
  void hardBijectionsAreMerged() {
    int[][] values = {{0, 1, 2}, {5, 6, 7}, {0, 1}};
    CostNetwork net = new CostNetwork(values);
    long[] bij = {HARD, 3, HARD, HARD, HARD, 0, 1, HARD, HARD};
    net.addBinary(0, 1, bij);
    // y = 5 is cheap only when z = 1, and y = 5 means x = 2
    net.addBinary(1, 2, new long[] {4, 0, 2, 2, 2, 2});
    CostNetwork.Solution s = net.solve(Long.MAX_VALUE, 100);
    assertEquals(1, s.mergedCount());
    // the optimum: x = 2, y = 5, z = 1 costs 1 + 0; x = 0, y = 6 costs 3 + 2
    assertEquals(1, Math.ceilDiv(s.bound(), s.scale));
  }

  // a store with the network's variables (holes where values are not consecutive) and cost z
  private static IntVar[] variables(Store store, Instance inst) {
    int n = inst.values().length;
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      IntervalDomain d = new IntervalDomain();
      for (int v : inst.values()[i]) {
        d.unionAdapt(v, v);
      }
      x[i] = new IntVar(store, "x" + i, d);
    }
    return x;
  }

  @Test
  void propagationKeepsEveryAssignmentThatFits() {
    Random rnd = new Random(17);
    int removed = 0;
    for (int instance = 0; instance < INSTANCES; instance++) {
      Instance inst = random(rnd);
      boolean maximize = rnd.nextBoolean();
      Store store = new Store();
      IntVar[] x = variables(store, inst);
      IntVar z = new IntVar(store, "z", -60, 60);
      store.impose(new CostNetworkBound(z, maximize, x, inst.network()));
      boolean consistent = store.consistency();
      for (int step = 0; step < 6; step++) {
        IntDomain[] before = new IntDomain[x.length];
        for (int i = 0; i < x.length; i++) {
          before[i] = x[i].dom().cloneLight();
        }
        long top = maximize ? -(long) z.min() : z.max();
        long opt = inst.optimum(before, -1, 0);
        if (!consistent) {
          assertTrue(opt == HARD || opt > top, "failed with an assignment of cost " + opt);
          break;
        }
        // the objective bound holds for the cheapest assignment
        long low = maximize ? -(long) z.max() : z.min();
        assertTrue(opt == HARD || low <= opt, "bound " + low + " above " + opt);
        store.setLevel(store.level + 1);
        try {
          if (rnd.nextInt(3) == 0) {
            int b = (int) Math.min(60, Math.max(-60, opt == HARD ? 0 : opt + rnd.nextInt(3) - 1));
            if (maximize) {
              z.domain.inMin(store.level, z, -b);
            } else {
              z.domain.inMax(store.level, z, b);
            }
          } else {
            int i = rnd.nextInt(x.length);
            x[i].domain.inComplement(store.level, x[i], x[i].min() + rnd.nextInt(2));
          }
        } catch (FailException _) {
          // the change itself emptied a domain
          break;
        }
        IntDomain[] now = new IntDomain[x.length];
        for (int i = 0; i < x.length; i++) {
          now[i] = x[i].dom().cloneLight();
        }
        long fits = inst.optimum(now, -1, 0);
        long limit = maximize ? -(long) z.min() : z.max();
        try {
          consistent = store.consistency();
        } catch (FailException _) {
          consistent = false;
        }
        if (fits == HARD || fits > limit) {
          continue;
        }
        assertTrue(consistent, "failed although an assignment of cost " + fits + " fits");
        // every value removed has no assignment within the limit
        for (int i = 0; i < x.length; i++) {
          for (int v : inst.values()[i]) {
            if (now[i].contains(v) && !x[i].domain.contains(v)) {
              removed++;
              long with = inst.optimum(now, i, v);
              assertTrue(with == HARD || with > limit, "removed " + v + " of cost " + with);
            }
          }
        }
      }
    }
    assertTrue(removed > 50, "values removed: " + removed);
  }

  @Test
  void backtrackingKeepsTheBound() {
    Random rnd = new Random(23);
    int raised = 0;
    for (int instance = 0; instance < INSTANCES / 2; instance++) {
      Instance inst = random(rnd);
      boolean maximize = rnd.nextBoolean();
      Store store = new Store();
      IntVar[] x = variables(store, inst);
      IntVar z = new IntVar(store, "z", -60, 60);
      CostNetworkBound c = new CostNetworkBound(z, maximize, x, inst.network());
      store.impose(c);
      if (!store.consistency()) {
        continue;
      }
      int root = store.level;
      for (int step = 0; step < 30; step++) {
        if (store.level > root && rnd.nextInt(3) == 0) {
          // back to a random earlier level
          int to = root + rnd.nextInt(store.level - root);
          while (store.level > to) {
            store.removeLevel(store.level);
            store.setLevel(store.level - 1);
          }
        }
        store.setLevel(store.level + 1);
        int i = rnd.nextInt(x.length);
        boolean consistent;
        try {
          if (rnd.nextBoolean()) {
            x[i].domain.in(store.level, x[i], x[i].min(), x[i].min());
          } else {
            x[i].domain.inComplement(store.level, x[i], x[i].min());
          }
          consistent = store.consistency();
        } catch (FailException _) {
          consistent = false;
        }
        if (!consistent) {
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
          continue;
        }
        // the propagated bound is the one of the current domains, computed afresh
        long fresh = c.currentBound();
        long low = maximize ? -(long) z.max() : z.min();
        assertTrue(low >= Math.min(fresh, 61), "bound " + low + " below the fresh " + fresh);
        long opt = inst.optimum(domains(x), -1, 0);
        assertTrue(opt == HARD || low <= opt, "bound " + low + " above " + opt);
        if (fresh > -60) {
          raised++;
        }
      }
    }
    assertTrue(raised > 100, "bounds raised: " + raised);
  }

  private static IntDomain[] domains(IntVar[] x) {
    IntDomain[] d = new IntDomain[x.length];
    for (int i = 0; i < x.length; i++) {
      d[i] = x[i].dom().cloneLight();
    }
    return d;
  }

  @Test
  void reasonsImplyTheirAtoms() {
    Random rnd = new Random(29);
    int checked = 0;
    for (int instance = 0; instance < INSTANCES / 2; instance++) {
      Instance inst = random(rnd);
      boolean maximize = rnd.nextBoolean();
      Store store = new Store();
      IntVar[] x = variables(store, inst);
      IntVar z = new IntVar(store, "z", -60, 60);
      AtomicTrail trail = new AtomicTrail(store);
      store.impose(new CostNetworkBound(z, maximize, x, inst.network()));
      boolean consistent;
      try {
        consistent = store.consistency();
      } catch (FailException _) {
        consistent = false;
      }
      for (int step = 0; consistent && step < 8; step++) {
        store.setLevel(store.level + 1);
        try {
          if (rnd.nextInt(3) == 0) {
            int v = z.min() + rnd.nextInt(z.max() - z.min() + 1);
            if (maximize) {
              z.domain.inMin(store.level, z, v);
            } else {
              z.domain.inMax(store.level, z, v);
            }
          } else {
            IntVar y = x[rnd.nextInt(x.length)];
            y.domain.inComplement(store.level, y, y.min() + rnd.nextInt(y.max() - y.min() + 1));
          }
          consistent = store.consistency();
        } catch (FailException _) {
          consistent = false;
        }
      }
      ExplanationChecker checker = new ExplanationChecker(trail);
      for (int e = 0; e < trail.size(); e++) {
        if (trail.reason(e) instanceof CostNetworkBound) {
          EntryList reason = new EntryList();
          assertTrue(trail.explain(e, reason), "no reason for " + trail.atomString(e));
          assertNull(checker.checkReason(e, reason));
          checked++;
        }
      }
      trail.detach();
    }
    assertTrue(checked > 100, "reasons checked: " + checked);
  }
}
