/*
 * UnaryEarlinessTardinessTest.java
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

import static org.assertj.core.api.Assertions.assertThatThrownBy;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Or;
import org.jacop.constraints.UnaryEarlinessTardiness;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Checks of {@link UnaryEarlinessTardiness}: the unit costs of every task stay within its cost, the
 * bound over random boxes stays below the brute-force minimum over the non-overlapping schedules,
 * the dual and primal values of each transportation problem agree, and optima of random one- and
 * two-machine earliness/tardiness problems match the decomposition.
 */
class UnaryEarlinessTardinessTest {

  // -Dunaryet.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("unaryet.instances", 1000);

  @Test
  void unitCostsStayWithinTheTaskCost() {
    HashMap<Long, Long> cache = new HashMap<>();
    for (long p = 1; p <= 30; p++) {
      for (long e = 0; e <= 6; e++) {
        for (long t = 0; t <= 6; t++) {
          long w2 = UnaryEarlinessTardiness.flat(p, e, t, cache);
          assertTrue(w2 >= 0 && w2 <= Math.max(0, p - 1), "w2 " + w2 + " for p " + p);
          for (long s = -4 * p - 3; s <= 4 * p + 3; s++) {
            long sum = 0;
            for (long u = s; u < s + p; u++) {
              sum += UnaryEarlinessTardiness.hinge2(p, e, t, w2, 2 * u);
            }
            long f = e * Math.max(0, -s) + t * Math.max(0, s);
            assertTrue(sum <= 2 * p * f, "p " + p + " e " + e + " t " + t + " s " + s);
          }
          // the flat part is the smallest: one less breaks a start next to the due date
          if (w2 > 0) {
            boolean broken = false;
            for (long s = -p; s <= p && !broken; s++) {
              long sum = 0;
              for (long u = s; u < s + p; u++) {
                sum += UnaryEarlinessTardiness.hinge2(p, e, t, w2 - 1, 2 * u);
              }
              broken = sum > 2 * p * (e * Math.max(0, -s) + t * Math.max(0, s));
            }
            assertTrue(broken, "flat part not minimal for p " + p + " e " + e + " t " + t);
          }
        }
      }
    }
  }

  @Test
  void twoTasksWithOneDueDate() {
    // two tasks of length 3 due at 5 on one machine: one of them is 3 early or 3 late
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 20);
    IntVar b = new IntVar(store, "b", 0, 20);
    IntVar c = new IntVar(store, "c", 0, 100);
    UnaryEarlinessTardiness et =
        new UnaryEarlinessTardiness(
            new IntVar[] {a, b},
            new int[] {3, 3},
            new int[] {5, 5},
            new int[] {1, 1},
            new int[] {1, 1},
            c);
    store.impose(et);
    assertTrue(store.consistency());
    assertTrue(c.min() >= 1 && c.min() <= 3, c.toString());
  }

  @Test
  void failsWhenTheMachineIsOverloaded() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 2);
    IntVar b = new IntVar(store, "b", 0, 2);
    IntVar c = new IntVar(store, "c", 0, 100);
    store.impose(
        new UnaryEarlinessTardiness(
            new IntVar[] {a, b},
            new int[] {3, 3},
            new int[] {0, 0},
            new int[] {1, 1},
            new int[] {1, 1},
            c));
    assertFalse(store.consistency());
  }

  @Test
  void rejectsBadArguments() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 5);
    IntVar b = new IntVar(store, "b", 0, 5);
    IntVar c = new IntVar(store, "c", 0, 5);
    IntVar[] s = {a, b};
    int[][] none = new int[0][];
    int[][] one = {{0, 1}};
    assertThatThrownBy(
            () -> new UnaryEarlinessTardiness(s, new int[] {1, 0}, one, new int[2], none, c))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new UnaryEarlinessTardiness(
                    s, new int[] {1, 1}, new int[][] {{0}}, new int[] {0, 0}, none, c))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new UnaryEarlinessTardiness(
                    s, new int[] {1, 1}, one, new int[2], new int[][] {{0, 1, -1, 0}}, c))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new UnaryEarlinessTardiness(
                    new IntVar[] {a, a}, new int[] {1, 1}, one, new int[2], none, c))
        .isInstanceOf(IllegalArgumentException.class);
  }

  /** Random tasks on one or two machines, with earliness and tardiness terms and boxes. */
  static final class Problem {
    final int n;
    final int[] p;
    final int[][] machines;
    final int[] owner;
    final int[][] terms;
    final int[] lo;
    final int[] hi;

    Problem(int n, int[] p, int[][] machines, int[] owner, int[][] terms, int[] lo, int[] hi) {
      this.n = n;
      this.p = p;
      this.machines = machines;
      this.owner = owner;
      this.terms = terms;
      this.lo = lo;
      this.hi = hi;
    }

    static Problem random(Random r, int maxTasks, int horizon, int maxDuration) {
      int n = 1 + r.nextInt(maxTasks);
      int[] p = new int[n];
      for (int i = 0; i < n; i++) {
        p[i] = 1 + r.nextInt(maxDuration);
      }
      int count = 1 + r.nextInt(2);
      List<List<Integer>> on = new ArrayList<>();
      for (int m = 0; m < count; m++) {
        on.add(new ArrayList<>());
      }
      int[] owner = new int[n];
      for (int i = 0; i < n; i++) {
        int kind = r.nextInt(6);
        if (kind == 0) {
          // on no machine
          owner[i] = -1;
          continue;
        }
        int m = r.nextInt(count);
        on.get(m).add(i);
        owner[i] = m;
        if (count == 2 && kind == 1) {
          // on both machines, owned by one
          on.get(1 - m).add(i);
        } else if (kind == 2) {
          // on its machine without counting its cost there
          owner[i] = -1;
        }
      }
      int[][] machines = new int[count][];
      for (int m = 0; m < count; m++) {
        machines[m] = on.get(m).stream().mapToInt(Integer::intValue).toArray();
      }
      List<int[]> terms = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        for (int k = r.nextInt(3); k > 0; k--) {
          terms.add(new int[] {i, r.nextInt(horizon + 4) - 2, r.nextInt(5), r.nextInt(5)});
        }
      }
      int[] lo = new int[n];
      int[] hi = new int[n];
      for (int i = 0; i < n; i++) {
        lo[i] = r.nextInt(horizon / 2 + 1);
        hi[i] = lo[i] + r.nextInt(horizon / 2 + 1);
      }
      return new Problem(n, p, machines, owner, terms.toArray(new int[0][]), lo, hi);
    }

    long cost(int[] s) {
      long total = 0;
      for (int[] t : terms) {
        total +=
            (long) t[2] * Math.max(0, t[1] - s[t[0]]) + (long) t[3] * Math.max(0, s[t[0]] - t[1]);
      }
      return total;
    }

    boolean feasible(int[] s) {
      for (int[] m : machines) {
        for (int a = 0; a < m.length; a++) {
          for (int b = a + 1; b < m.length; b++) {
            int i = m[a];
            int j = m[b];
            if (s[i] < s[j] + p[j] && s[j] < s[i] + p[i]) {
              return false;
            }
          }
        }
      }
      return true;
    }

    long bruteMinimum() {
      int[] s = lo.clone();
      long best = Long.MAX_VALUE;
      while (true) {
        if (feasible(s)) {
          best = Math.min(best, cost(s));
        }
        int k = 0;
        while (k < n && s[k] == hi[k]) {
          s[k] = lo[k];
          k++;
        }
        if (k == n) {
          return best;
        }
        s[k]++;
      }
    }

    UnaryEarlinessTardiness post(Store store, IntVar[] s, IntVar cost) {
      UnaryEarlinessTardiness c = new UnaryEarlinessTardiness(s, p, machines, owner, terms, cost);
      store.impose(c);
      return c;
    }

    @Override
    public String toString() {
      return "p="
          + Arrays.toString(p)
          + " machines="
          + Arrays.deepToString(machines)
          + " owner="
          + Arrays.toString(owner)
          + " terms="
          + Arrays.deepToString(terms)
          + " lo="
          + Arrays.toString(lo)
          + " hi="
          + Arrays.toString(hi);
    }
  }

  private static void checkBound(Problem p, String what) {
    Store store = new Store();
    IntVar[] s = new IntVar[p.n];
    for (int i = 0; i < p.n; i++) {
      s[i] = new IntVar(store, "s" + i, p.lo[i], p.hi[i]);
    }
    IntVar c = new IntVar(store, "c", 0, 1_000_000);
    UnaryEarlinessTardiness et =
        new UnaryEarlinessTardiness(s, p.p, p.machines, p.owner, p.terms, c);
    long[] lo = Arrays.stream(p.lo).asLongStream().toArray();
    long[] hi = Arrays.stream(p.hi).asLongStream().toArray();
    long bound = et.boundFor(lo, hi);
    long brute = p.bruteMinimum();
    if (bound != Long.MAX_VALUE) {
      assertTrue(bound <= brute, what + ": bound " + bound + " above " + brute + " for " + p);
      for (int m = 0; m < p.machines.length; m++) {
        assertEquals(et.primalValue(m), et.dualValue(m), what + ": duality gap on " + p);
      }
    }
  }

  @Test
  void boundStaysBelowTheMinimum() {
    Random r = new Random(1);
    for (int t = 0; t < 4 * INSTANCES; t++) {
      checkBound(Problem.random(r, 5, 10, 4), "instance " + t);
    }
  }

  @Test
  void boundOverBlocksStaysBelowTheMinimum() {
    // windows longer than the number of blocks, so slots are grouped
    Random r = new Random(3);
    for (int t = 0; t < INSTANCES / 4; t++) {
      Problem q = Problem.random(r, 3, 300, 40);
      int[] hi = q.hi.clone();
      for (int i = 0; i < q.n; i++) {
        hi[i] = Math.min(hi[i], q.lo[i] + 60);
      }
      checkBound(new Problem(q.n, q.p, q.machines, q.owner, q.terms, q.lo, hi), "blocks " + t);
    }
  }

  /**
   * The reduced-cost filtering keeps every start value of a schedule that fits on the machines with
   * a cost at most the maximum, and removes some: the maximum is the brute-force minimum plus a
   * small margin.
   */
  @Test
  void filteringKeepsEverySupportedStart() {
    Random r = new Random(4);
    long prunings = 0;
    for (int t = 0; t < INSTANCES; t++) {
      Problem q = Problem.random(r, 5, 12, 4);
      long best = q.bruteMinimum();
      if (best == Long.MAX_VALUE) {
        continue;
      }
      long max = best + r.nextInt(4);
      boolean[][] supported = new boolean[q.n][];
      for (int i = 0; i < q.n; i++) {
        supported[i] = new boolean[q.hi[i] - q.lo[i] + 1];
      }
      int[] x = q.lo.clone();
      while (true) {
        if (q.feasible(x) && q.cost(x) <= max) {
          for (int i = 0; i < q.n; i++) {
            supported[i][x[i] - q.lo[i]] = true;
          }
        }
        int k = 0;
        while (k < q.n && x[k] == q.hi[k]) {
          x[k] = q.lo[k];
          k++;
        }
        if (k == q.n) {
          break;
        }
        x[k]++;
      }
      Store store = new Store();
      IntVar[] s = new IntVar[q.n];
      for (int i = 0; i < q.n; i++) {
        s[i] = new IntVar(store, "s" + i, q.lo[i], q.hi[i]);
      }
      IntVar c = new IntVar(store, "c", 0, (int) max);
      UnaryEarlinessTardiness et = q.post(store, s, c);
      assertTrue(store.consistency(), "instance " + t + " max " + max + ": " + q);
      for (int i = 0; i < q.n; i++) {
        for (int v = q.lo[i]; v <= q.hi[i]; v++) {
          if (supported[i][v - q.lo[i]]) {
            assertTrue(
                s[i].domain.contains(v),
                "instance " + t + " max " + max + ": s" + i + " = " + v + " removed for " + q);
          }
        }
      }
      prunings += et.filterStatistics()[0];
    }
    assertTrue(prunings > 0, "the filtering never pruned");
  }

  // random precedences {i, j, d} between tasks i < j
  private static int[][] randomPrecedences(Random r, Problem q) {
    List<int[]> list = new ArrayList<>();
    for (int i = 0; i < q.n; i++) {
      for (int j = i + 1; j < q.n; j++) {
        if (r.nextInt(3) == 0) {
          list.add(new int[] {i, j, r.nextInt(q.p[i] + 2)});
        }
      }
    }
    return list.toArray(new int[0][]);
  }

  private static boolean precedencesHold(int[][] precedences, int[] x) {
    for (int[] q : precedences) {
      if (x[q[1]] < x[q[0]] + q[2]) {
        return false;
      }
    }
    return true;
  }

  /**
   * With precedences the bound stays below the brute-force minimum over the schedules that fit and
   * keep the precedences, for random multipliers and for the ones of the subgradient search, and
   * the propagation keeps every start of a schedule within the maximum.
   */
  @Test
  void lagrangianBoundStaysBelowTheMinimum() {
    Random r = new Random(6);
    int raised = 0;
    for (int t = 0; t < INSTANCES; t++) {
      Problem q = Problem.random(r, 5, 12, 4);
      int[][] precedences = randomPrecedences(r, q);
      if (precedences.length == 0) {
        continue;
      }
      long best = Long.MAX_VALUE;
      boolean[][] supported = new boolean[q.n][];
      for (int i = 0; i < q.n; i++) {
        supported[i] = new boolean[q.hi[i] - q.lo[i] + 1];
      }
      int[] x = q.lo.clone();
      List<int[]> schedules = new ArrayList<>();
      while (true) {
        if (q.feasible(x) && precedencesHold(precedences, x)) {
          best = Math.min(best, q.cost(x));
          schedules.add(x.clone());
        }
        int k = 0;
        while (k < q.n && x[k] == q.hi[k]) {
          x[k] = q.lo[k];
          k++;
        }
        if (k == q.n) {
          break;
        }
        x[k]++;
      }
      String what = "instance " + t + " " + q + " precedences " + Arrays.deepToString(precedences);
      long[] low = Arrays.stream(q.lo).asLongStream().toArray();
      long[] high = Arrays.stream(q.hi).asLongStream().toArray();
      if (best == Long.MAX_VALUE) {
        continue;
      }
      long max = best + r.nextInt(3);
      for (int[] y : schedules) {
        if (q.cost(y) <= max) {
          for (int i = 0; i < q.n; i++) {
            supported[i][y[i] - q.lo[i]] = true;
          }
        }
      }
      Store scratch = new Store();
      IntVar[] f = new IntVar[q.n];
      for (int i = 0; i < q.n; i++) {
        f[i] = new IntVar(scratch, "s" + i, q.lo[i], q.hi[i]);
      }
      UnaryEarlinessTardiness probe =
          new UnaryEarlinessTardiness(
              f, q.p, q.machines, q.owner, q.terms, precedences, new IntVar(scratch, 0, 100_000));
      long plain = probe.boundFor(low, high);
      for (int rep = 0; rep < 3; rep++) {
        long[] lambda = new long[precedences.length];
        for (int k = 0; k < lambda.length; k++) {
          lambda[k] = r.nextInt(4) == 0 ? 0 : r.nextInt(80);
        }
        probe.setMultipliers(lambda);
        long b = probe.boundFor(low, high);
        assertTrue(
            b == Long.MAX_VALUE || b <= best,
            what + " lambda " + Arrays.toString(lambda) + ": " + b + " > " + best);
      }
      Store store = new Store();
      IntVar[] s = new IntVar[q.n];
      for (int i = 0; i < q.n; i++) {
        s[i] = new IntVar(store, "s" + i, q.lo[i], q.hi[i]);
      }
      IntVar c = new IntVar(store, "c", 0, (int) max);
      UnaryEarlinessTardiness et =
          new UnaryEarlinessTardiness(s, q.p, q.machines, q.owner, q.terms, precedences, c);
      store.impose(et);
      assertTrue(store.consistency(), what + " max " + max);
      for (int i = 0; i < q.n; i++) {
        for (int v = q.lo[i]; v <= q.hi[i]; v++) {
          if (supported[i][v - q.lo[i]]) {
            assertTrue(
                s[i].domain.contains(v), what + " max " + max + ": s" + i + " = " + v + " removed");
          }
        }
      }
      et.setMultipliers(et.multipliers());
      if (et.boundFor(low, high) > plain) {
        raised++;
      }
    }
    assertTrue(raised > 0, "the multipliers never raised the bound");
  }

  /** The optimum with the constraint alone (and the disjunctions), the decomposition, and both. */
  @Test
  void optimaMatchDecomposition() {
    Random r = new Random(2);
    for (int t = 0; t < INSTANCES; t++) {
      Problem p = Problem.random(r, 6, 14, 4);
      long plain = optimum(p, false);
      long global = optimum(p, true);
      assertEquals(plain, global, "instance " + t + ": " + p);
    }
  }

  // the minimum cost, -1 when there is no schedule
  private static long optimum(Problem p, boolean global) {
    Store store = new Store();
    IntVar[] s = new IntVar[p.n];
    for (int i = 0; i < p.n; i++) {
      s[i] = new IntVar(store, "s" + i, p.lo[i], p.hi[i]);
    }
    IntVar cost = new IntVar(store, "cost", 0, 100_000);
    for (int[] m : p.machines) {
      for (int a = 0; a < m.length; a++) {
        for (int b = a + 1; b < m.length; b++) {
          int i = m[a];
          int j = m[b];
          store.impose(
              new Or(new XplusClteqZ(s[i], p.p[i], s[j]), new XplusClteqZ(s[j], p.p[j], s[i])));
        }
      }
    }
    IntVar[] vars = new IntVar[2 * p.terms.length + 1];
    int[] w = new int[vars.length];
    for (int k = 0; k < p.terms.length; k++) {
      int[] term = p.terms[k];
      IntVar early = new IntVar(store, "e" + k, 0, 1000);
      IntVar late = new IntVar(store, "l" + k, 0, 1000);
      store.impose(
          new LinearInt(new IntVar[] {early, s[term[0]]}, new int[] {1, 1}, ">=", term[1]));
      store.impose(
          new LinearInt(new IntVar[] {late, s[term[0]]}, new int[] {1, -1}, ">=", -term[1]));
      vars[2 * k] = early;
      w[2 * k] = term[2];
      vars[2 * k + 1] = late;
      w[2 * k + 1] = term[3];
    }
    vars[vars.length - 1] = cost;
    w[w.length - 1] = -1;
    store.impose(new LinearInt(vars, w, "<=", 0));
    if (global) {
      p.post(store, s, cost);
    }
    Search<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    IntVar[] all = Arrays.copyOf(s, p.n + 1);
    all[p.n] = cost;
    SelectChoicePoint<IntVar> select = new SimpleSelect<>(all, null, new IndomainMin<>());
    boolean found = search.labeling(store, select, cost);
    return found ? search.getCostValue() : -1;
  }
}
