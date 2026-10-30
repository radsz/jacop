/*
 * LcgSolverTest.java
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
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

import java.time.Duration;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.IntPredicate;
import java.util.function.Predicate;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.AlldifferentExcept;
import org.jacop.constraints.AlldifferentExceptZero;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.AtLeast;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.CountValues;
import org.jacop.constraints.CountValuesBounds;
import org.jacop.constraints.CountVar;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementVariable;
import org.jacop.constraints.ExtensionalSupportMdd;
import org.jacop.constraints.GCC;
import org.jacop.constraints.GlobalCardinality;
import org.jacop.constraints.IncreasingNValue;
import org.jacop.constraints.IncreasingSum;
import org.jacop.constraints.LexChain;
import org.jacop.constraints.LexOrder;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Max;
import org.jacop.constraints.MaxSimple;
import org.jacop.constraints.Member;
import org.jacop.constraints.Min;
import org.jacop.constraints.MinSimple;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SeqPrecedeChain;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.Xor;
import org.jacop.constraints.XorBool;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.cumulative.UnaryTransition;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.NetworkFlow;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.constraints.regular.Regular;
import org.jacop.constraints.table.HybridTable;
import org.jacop.constraints.table.Restriction;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.lcg.ValueIndicator;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMax;
import org.jacop.search.IndomainMiddle;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.jacop.search.SplitSelect;
import org.jacop.search.lns.AdaptiveLns;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;
import org.junit.jupiter.api.Test;

/**
 * Tests lazy clause generation against brute force: random small problems of several constraints
 * must be found satisfiable exactly when some assignment satisfies every relation, and the solution
 * found must satisfy them.
 */
class LcgSolverTest {

  private record Relation(Constraint constraint, Predicate<int[]> test) {}

  private static IntVar newVar(Store store, String name, Random rnd) {
    IntVar x = new IntVar(store, name, rnd.nextInt(2) - 1, 3 + rnd.nextInt(3));
    if (rnd.nextInt(3) == 0) {
      x.domain.subtractAdapt(x.min() + 1 + rnd.nextInt(x.max() - x.min() - 1));
      x.refreshBounds();
    }
    return x;
  }

  private static int pick(Random rnd, int n, int... not) {
    while (true) {
      int k = rnd.nextInt(n);
      boolean ok = true;
      for (int m : not) {
        ok &= m != k;
      }
      if (ok) {
        return k;
      }
    }
  }

  private static Relation relation(IntVar[] x, Random rnd) {
    int n = x.length;
    int i = pick(rnd, n);
    int j = pick(rnd, n, i);
    int k = pick(rnd, n, i, j);
    return switch (rnd.nextInt(8)) {
      case 0 -> {
        int c = rnd.nextInt(5);
        yield new Relation(
            new LinearInt(new IntVar[] {x[i], x[j], x[k]}, new int[] {2, -1, 3}, "<=", c),
            t -> 2 * t[i] - t[j] + 3 * t[k] <= c);
      }
      case 1 -> {
        int c = rnd.nextInt(6);
        yield new Relation(
            new LinearInt(new IntVar[] {x[i], x[j], x[k]}, new int[] {1, 1, -1}, "==", c),
            t -> t[i] + t[j] - t[k] == c);
      }
      case 2 -> new Relation(new XplusYeqZ(x[i], x[j], x[k]), t -> t[i] + t[j] == t[k]);
      case 3 -> new Relation(new XmulYeqZ(x[i], x[j], x[k]), t -> t[i] * t[j] == t[k]);
      case 4 -> new Relation(new XneqY(x[i], x[j]), t -> t[i] != t[j]);
      case 6 -> {
        int[] d = {1 + rnd.nextInt(3), 1 + rnd.nextInt(3), 1 + rnd.nextInt(3)};
        int[] r = {1 + rnd.nextInt(2), 1 + rnd.nextInt(2), 1 + rnd.nextInt(2)};
        int limit = 2 + rnd.nextInt(2);
        Store store = x[i].getStore();
        IntVar[] durations = new IntVar[3];
        IntVar[] resources = new IntVar[3];
        for (int k2 = 0; k2 < 3; k2++) {
          durations[k2] = new IntVar(store, d[k2], d[k2]);
          resources[k2] = new IntVar(store, r[k2], r[k2]);
        }
        int[] at = {i, j, k};
        yield new Relation(
            new Cumulative(
                new IntVar[] {x[i], x[j], x[k]},
                durations,
                resources,
                new IntVar(store, limit, limit)),
            t -> {
              for (int time = -8; time < 12; time++) {
                int load = 0;
                for (int k2 = 0; k2 < 3; k2++) {
                  if (t[at[k2]] <= time && time < t[at[k2]] + d[k2]) {
                    load += r[k2];
                  }
                }
                if (load > limit) {
                  return false;
                }
              }
              return true;
            });
      }
      case 5 -> {
        int[] list = {rnd.nextInt(5), rnd.nextInt(5), rnd.nextInt(5), rnd.nextInt(5)};
        yield new Relation(
            new ElementInteger(x[i], list, x[j], 0),
            t -> t[i] >= 1 && t[i] <= list.length && list[t[i] - 1] == t[j]);
      }
      default ->
          new Relation(
              new Alldistinct(new IntVar[] {x[i], x[j], x[k]}),
              t -> t[i] != t[j] && t[j] != t[k] && t[i] != t[k]);
    };
  }

  private static boolean bruteForce(IntVar[] x, List<Relation> relations, int[] t, int i) {
    if (i == x.length) {
      return relations.stream().allMatch(r -> r.test.test(t));
    }
    for (int v = x[i].min(); v <= x[i].max(); v++) {
      if (x[i].domain.contains(v)) {
        t[i] = v;
        if (bruteForce(x, relations, t, i + 1)) {
          return true;
        }
      }
    }
    return false;
  }

  @Test
  void agreesWithBruteForce() {
    Random rnd = new Random(11);
    int sat = 0;
    int unsat = 0;
    long lifted = 0;
    for (int instance = 0; instance < 3000; instance++) {
      Store store = new Store();
      int n = 4 + rnd.nextInt(3);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 2 + rnd.nextInt(4); c > 0; c--) {
        relations.add(relation(x, rnd));
      }
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.sat().setSeed(instance);
      int status = solver.solve();
      lifted += solver.liftedLiterals;
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[n];
        for (int i = 0; i < n; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
    }
    assertThat(sat).isGreaterThan(300);
    assertThat(unsat).isGreaterThan(300);
    // lifted bounds cite weaker literals the solver has, which the checker verifies
    assertThat(lifted).isGreaterThan(0);
  }

  /**
   * The SAT solver's own decisions on literals with phase false (LITERALS; AUTO, which falls back
   * to activity until a first solution; and ALTERNATE, which takes turns with activity and with an
   * annotation) find the brute-force optimum of a weighted sum. A variable that no constraint
   * mentions has no literal, so the last decisions are on it.
   */
  @Test
  void literalBranchingAgreesWithBruteForce() {
    Random rnd = new Random(23);
    int proved = 0;
    for (int instance = 0; instance < 1500; instance++) {
      LcgSolver.Branching branching =
          switch (instance % 4) {
            case 0 -> LcgSolver.Branching.LITERALS;
            case 1 -> LcgSolver.Branching.AUTO;
            default -> LcgSolver.Branching.ALTERNATE;
          };
      Store store = new Store();
      int n = 4 + rnd.nextInt(3);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 1 + rnd.nextInt(3); c > 0; c--) {
        relations.add(relation(Arrays.copyOf(x, n - 1), rnd));
      }
      int[] w = new int[n];
      for (int i = 0; i < n - 1; i++) {
        w[i] = rnd.nextInt(7) - 3;
      }
      long best = minimum(x, relations, w, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      IntVar cost = new IntVar(store, "cost", -1000, 1000);
      IntVar[] terms = Arrays.copyOf(x, n);
      terms[n - 1] = cost; // x[n - 1] is in no constraint
      int[] weights = Arrays.copyOf(w, n);
      weights[n - 1] = -1;
      store.impose(new LinearInt(terms, weights, "==", 0));
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.setBranching(branching);
      if (instance % 4 == 3) {
        solver.setAnnotation(new SimpleSelect<>(x, null, new IndomainMin<>()), true);
      }
      solver.sat().setInitialPhase(false);
      solver.setBooleansFirstTurns(instance % 8 >= 4);
      solver.setKeepImprovingRun(instance / 8 % 2 == 1);
      solver.setSeed(instance % 3);
      int status = solver.minimize(cost);
      if (best == Long.MAX_VALUE) {
        assertThat(status).as("instance %d", instance).isEqualTo(CdclSolver.UNSAT);
        continue;
      }
      assertThat(status).as("instance %d", instance).isEqualTo(CdclSolver.SAT);
      assertThat((long) solver.value(cost)).as("instance %d", instance).isEqualTo(best);
      int[] t = new int[n];
      long sum = 0;
      for (int i = 0; i < n; i++) {
        t[i] = solver.value(x[i]);
        sum += (long) w[i] * t[i];
      }
      for (Relation r : relations) {
        assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
      }
      assertThat(sum).as("instance %d", instance).isEqualTo(best);
      proved++;
    }
    assertThat(proved).isGreaterThan(300);
  }

  // the smallest weighted sum over the assignments of x that satisfy the relations
  private static long minimum(IntVar[] x, List<Relation> relations, int[] w, int[] t, int i) {
    if (i == x.length) {
      if (!relations.stream().allMatch(r -> r.test.test(t))) {
        return Long.MAX_VALUE;
      }
      long sum = 0;
      for (int k = 0; k < x.length; k++) {
        sum += (long) w[k] * t[k];
      }
      return sum;
    }
    long best = Long.MAX_VALUE;
    for (int v = x[i].min(); v <= x[i].max(); v++) {
      if (x[i].domain.contains(v)) {
        t[i] = v;
        best = Math.min(best, minimum(x, relations, w, t, i + 1));
      }
    }
    return best;
  }

  /**
   * Random hybrid tables with unary restrictions against brute force; the table explains its
   * prunings itself.
   */
  @Test
  void hybridTablesAgreeWithBruteForce() {
    long[] counts = checkHybridTables(new Random(SEED + 17), TABLE_TRIALS, false);
    assertThat(counts[0]).isGreaterThan(100);
    assertThat(counts[1]).isGreaterThan(100);
    assertThat(counts[2]).isGreaterThan(counts[3]);
  }

  /**
   * Random hybrid tables with restrictions between columns, kept as they are, against brute force.
   * A tuple whose restriction between columns is violated by the bounds is explained by them.
   */
  @Test
  void hybridTablesBetweenColumnsAgreeWithBruteForce() {
    long[] counts = checkHybridTables(new Random(SEED + 29), TABLE_TRIALS, true);
    assertThat(counts[0]).isGreaterThan(100);
    assertThat(counts[1]).isGreaterThan(100);
    assertThat(counts[2]).isGreaterThan(4 * counts[3]);
  }

  /**
   * Returns the satisfiable and unsatisfiable instances and the HybridTable explanations of its own
   * and generic.
   */
  /** Instances of the hybrid table checks, and the seed added to their random seeds. */
  private static final int TABLE_TRIALS = Integer.getInteger("lcg.table.trials", 1500);

  private static final int SEED = Integer.getInteger("lcg.table.seed", 0);

  /** Instances of the scheduling checks against search; the {@code min} profile lowers it. */
  private static final int SCHEDULING_INSTANCES =
      Integer.getInteger("lcg.scheduling.instances", 400);

  private static long[] checkHybridTables(Random rnd, int instances, boolean betweenColumns) {
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < instances; instance++) {
      Store store = new Store();
      int n = 4 + rnd.nextInt(2);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 3 + rnd.nextInt(3); c > 0; c--) {
        relations.add(
            c == 1 && rnd.nextBoolean() ? relation(x, rnd) : tableRelation(x, rnd, betweenColumns));
      }
      boolean expected = solveAndCheck(store, x, relations, "instance " + instance);
      if (expected) {
        sat++;
      } else {
        unsat++;
      }
      LcgSolver solver = lastSolver;
      long[] counts = solver.explanationStatistics().get("HybridTable");
      if (counts != null) {
        own += counts[0] - counts[1] + counts[3] - counts[4];
        generic += counts[1] + counts[4];
      }
    }
    System.out.printf(
        "hybrid tables%s: %d sat, %d unsat, %d own and %d generic explanations%n",
        betweenColumns ? " between columns" : "", sat, unsat, own, generic);
    return new long[] {sat, unsat, own, generic};
  }

  private static LcgSolver lastSolver;

  /**
   * Solves with lazy clause generation, explanations checked, and compares with brute force; a
   * solution must satisfy every relation. Returns whether the model is satisfiable.
   */
  private static boolean solveAndCheck(
      Store store, IntVar[] x, List<Relation> relations, String name) {
    int n = x.length;
    boolean expected = bruteForce(x, relations, new int[n], 0);
    for (Relation r : relations) {
      store.impose(r.constraint);
    }
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    lastSolver = solver;
    int status = solver.solve();
    assertThat(status).as(name).isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
    if (expected) {
      int[] t = new int[n];
      for (int i = 0; i < n; i++) {
        t[i] = solver.value(x[i]);
      }
      for (Relation r : relations) {
        assertThat(r.test.test(t)).as("%s: %s", name, r.constraint).isTrue();
      }
    }
    return expected;
  }

  /**
   * A passed deadline stops the search at the next decision. The solver checked the clock only
   * every 1024 decisions, and LCG decisions can take milliseconds each: city-position ran 166 s on
   * a 60 s limit.
   */
  @Test
  void passedDeadlineStopsTheNextDecision() {
    Store store = new Store();
    IntVar[] x = new IntVar[20];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 9);
      if (i > 0) {
        store.impose(new XlteqY(x[i - 1], x[i]));
      }
    }
    LcgSolver solver = new LcgSolver(store);
    solver.sat().setDeadline(System.nanoTime() - 1);
    assertThat(solver.solve()).isEqualTo(CdclSolver.UNKNOWN);
    solver.sat().setDeadline(Long.MAX_VALUE);
    assertThat(solver.solve()).isEqualTo(CdclSolver.SAT);
  }

  /**
   * Large ground tables over a key variable with many values, a few tuples per value, so that the
   * tables keep sparse supports and the explanations pick among many dead tuples. Each table
   * explains everything itself.
   */
  @Test
  void largeTablesAgreeWithBruteForce() {
    Random rnd = new Random(SEED + 31);
    int sat = 0;
    int unsat = 0;
    for (int instance = 0; instance < TABLE_TRIALS / 10; instance++) {
      Store store = new Store();
      IntVar[] x = new IntVar[4];
      x[0] = new IntVar(store, "key", 0, 149);
      for (int v = 0; v < 150; v++) {
        if (rnd.nextInt(5) == 0) {
          x[0].domain.subtractAdapt(v);
          x[0].refreshBounds();
        }
      }
      for (int i = 1; i < x.length; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 2 + rnd.nextInt(2); c > 0; c--) {
        relations.add(keyTableRelation(x, rnd));
      }
      relations.add(tableRelation(x, rnd, false));
      if (solveAndCheck(store, x, relations, "instance " + instance)) {
        sat++;
      } else {
        unsat++;
      }
      long[] counts = lastSolver.explanationStatistics().get("HybridTable");
      if (counts != null) {
        assertThat(counts[1] + counts[4]).as("instance %d: generic", instance).isZero();
      }
    }
    System.out.printf("large tables: %d sat, %d unsat%n", sat, unsat);
    assertThat(sat).isGreaterThan(20);
    assertThat(unsat).isGreaterThan(20);
  }

  /** A ground table over the key x[0] and two other variables, its tuples sorted by key. */
  private static Relation keyTableRelation(IntVar[] x, Random rnd) {
    int a = 1 + rnd.nextInt(x.length - 1);
    int b = 1 + pick(rnd, x.length - 1, a - 1);
    List<int[]> tuples = new ArrayList<>();
    Set<Long> allowed = new HashSet<>();
    for (int key = 0; key < 150; key++) {
      for (int k = rnd.nextInt(5); k > 0; k--) {
        int u = rnd.nextInt(7) - 1;
        int w = rnd.nextInt(7) - 1;
        if (allowed.add(((long) key * 64 + u + 1) * 64 + w + 1)) {
          tuples.add(new int[] {key, u, w});
        }
      }
    }
    IntVar[] vars = {x[0], x[a], x[b]};
    return new Relation(
        new HybridTable(vars, tuples.toArray(new int[0][])),
        t -> allowed.contains(((long) t[0] * 64 + t[a] + 1) * 64 + t[b] + 1));
  }

  @Test
  void diffnAgreesWithBruteForce() {
    Random rnd = new Random(23);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 4;
      // per rectangle its x and y origins, then its widths and heights
      IntVar[] x = new IntVar[4 * n];
      int side = 1 + rnd.nextInt(3);
      for (int i = 0; i < 2 * n; i++) {
        x[i] = new IntVar(store, "o" + i, 0, side);
        if (rnd.nextInt(4) == 0) {
          x[i].domain.subtractAdapt(rnd.nextInt(side + 1));
          x[i].refreshBounds();
        }
      }
      for (int i = 2 * n; i < 4 * n; i++) {
        int c = 1 + rnd.nextInt(3);
        x[i] = rnd.nextInt(3) == 0 ? new IntVar(store, "l" + i, 1, 3) : new IntVar(store, c, c);
      }
      IntVar[] ox = new IntVar[n];
      IntVar[] oy = new IntVar[n];
      IntVar[] lx = new IntVar[n];
      IntVar[] ly = new IntVar[n];
      for (int i = 0; i < n; i++) {
        ox[i] = x[2 * i];
        oy[i] = x[2 * i + 1];
        lx[i] = x[2 * n + 2 * i];
        ly[i] = x[2 * n + 2 * i + 1];
      }
      List<Relation> relations = new ArrayList<>();
      relations.add(
          new Relation(
              new Diffn(ox, oy, lx, ly, rnd.nextBoolean()),
              t -> {
                for (int i = 0; i < n; i++) {
                  for (int j = i + 1; j < n; j++) {
                    boolean apartX =
                        t[2 * i] + t[2 * n + 2 * i] <= t[2 * j]
                            || t[2 * j] + t[2 * n + 2 * j] <= t[2 * i];
                    boolean apartY =
                        t[2 * i + 1] + t[2 * n + 2 * i + 1] <= t[2 * j + 1]
                            || t[2 * j + 1] + t[2 * n + 2 * j + 1] <= t[2 * i + 1];
                    if (!apartX && !apartY) {
                      return false;
                    }
                  }
                }
                return true;
              }));
      if (rnd.nextBoolean()) {
        relations.add(relation(Arrays.copyOf(x, 2 * n), rnd));
      }
      boolean expected = bruteForce(x, relations, new int[x.length], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[x.length];
        for (int i = 0; i < x.length; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
      long[] counts = solver.explanationStatistics().get("Diffn");
      if (counts != null) {
        own += counts[0] - counts[1] + counts[3] - counts[4];
        generic += counts[1] + counts[4];
      }
    }
    System.out.printf(
        "diffn: %d sat, %d unsat, %d own and %d generic explanations%n", sat, unsat, own, generic);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(own).isGreaterThan(generic);
  }

  /**
   * Bin packing with items sharing bin variables, items of weight zero, bin variables reaching
   * outside the bins, loads with holes and an extra relation on the bins: the LCG answer agrees
   * with enumerating the bins, every explanation is checked, and almost all are the constraint's
   * own.
   */
  @Test
  void binpackingAgreesWithBruteForce() {
    Random rnd = new Random(31);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int bins = 2 + rnd.nextInt(2);
      int minBin = rnd.nextInt(2);
      int n = 6 + rnd.nextInt(3);
      List<IntVar> distinct = new ArrayList<>();
      int[] at = new int[n];
      int[] w = new int[n];
      for (int k = 0; k < n; k++) {
        if (k > 0 && rnd.nextInt(5) == 0) {
          at[k] = at[rnd.nextInt(k)];
        } else {
          IntVar b =
              new IntVar(
                  store, "b" + k, minBin - rnd.nextInt(2), minBin + bins - 1 + rnd.nextInt(2));
          if (rnd.nextInt(3) == 0) {
            b.domain.subtractAdapt(b.min() + rnd.nextInt(b.max() - b.min() + 1));
            b.refreshBounds();
          }
          at[k] = distinct.size();
          distinct.add(b);
        }
        w[k] = rnd.nextInt(6) == 0 ? 0 : 1 + rnd.nextInt(5);
      }
      IntVar[] x = distinct.toArray(new IntVar[0]);
      IntVar[] item = new IntVar[n];
      for (int k = 0; k < n; k++) {
        item[k] = x[at[k]];
      }
      IntVar[] load = new IntVar[bins];
      for (int i = 0; i < bins; i++) {
        int lo = rnd.nextInt(6);
        load[i] = new IntVar(store, "l" + i, lo, lo + 2 + rnd.nextInt(12));
        for (int h = rnd.nextInt(3); h > 0 && load[i].getSize() > 2; h--) {
          load[i].domain.subtractAdapt(load[i].min() + 1 + rnd.nextInt(load[i].getSize() - 2));
          load[i].refreshBounds();
        }
      }
      List<Relation> relations = new ArrayList<>();
      relations.add(
          new Relation(
              new Binpacking(item, load, w, minBin, rnd.nextInt(4) != 0)
                  .cardinalityReasoning(rnd.nextInt(3) == 0),
              t -> {
                int[] sum = new int[bins];
                for (int k = 0; k < n; k++) {
                  int i = t[at[k]] - minBin;
                  if (i < 0 || i >= bins) {
                    return false;
                  }
                  sum[i] += w[k];
                }
                for (int i = 0; i < bins; i++) {
                  if (!load[i].domain.contains(sum[i])) {
                    return false;
                  }
                }
                return true;
              }));
      if (x.length >= 3 && rnd.nextBoolean()) {
        relations.add(relation(x, rnd));
      }
      // loads are read from their domains before search, so the test may refer to them
      boolean expected = bruteForce(x, relations, new int[x.length], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[x.length];
        for (int i = 0; i < x.length; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        int[] sum = new int[bins];
        for (int k = 0; k < n; k++) {
          sum[t[at[k]] - minBin] += w[k];
        }
        for (int i = 0; i < bins; i++) {
          assertThat(solver.value(load[i]))
              .as("instance %d load %d", instance, i)
              .isEqualTo(sum[i]);
        }
        sat++;
      } else {
        unsat++;
      }
      long[] counts = solver.explanationStatistics().get("Binpacking");
      if (counts != null) {
        own += counts[0] - counts[1] + counts[3] - counts[4];
        generic += counts[1] + counts[4];
      }
    }
    System.out.printf(
        "binpacking: %d sat, %d unsat, %d own and %d generic explanations%n",
        sat, unsat, own, generic);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(own).isGreaterThan(20 * generic);
  }

  /**
   * Graph colouring under a value precedence chain, with and without a value chain, over domains
   * with holes and values outside the chain, minimising the largest value: LCG finds the optimum
   * depth-first search finds, every explanation is checked, and almost all are the constraint's
   * own.
   */
  @Test
  void seqPrecedeChainColouringAgreesWithSearch() {
    long own = 0;
    long generic = 0;
    int unsat = 0;
    for (int instance = 0; instance < 400; instance++) {
      int[] optimum = new int[2];
      for (int mode = 0; mode < 2; mode++) {
        Random rnd = new Random(41 + instance);
        Store store = new Store();
        int n = 7 + rnd.nextInt(4);
        IntVar[] x = new IntVar[n];
        for (int i = 0; i < n; i++) {
          x[i] = new IntVar(store, "x" + i, -1, 5);
          if (rnd.nextInt(3) == 0) {
            x[i].domain.subtractAdapt(rnd.nextInt(7) - 1);
            x[i].refreshBounds();
          }
        }
        int[] chain = null;
        if (rnd.nextInt(3) != 0) {
          List<Integer> values = new ArrayList<>(List.of(-1, 0, 1, 2, 3, 4, 5));
          java.util.Collections.shuffle(values, rnd);
          chain = values.subList(0, 3 + rnd.nextInt(5)).stream().mapToInt(i -> i).toArray();
        }
        store.impose(new SeqPrecedeChain(x, chain));
        for (int i = 0; i < n; i++) {
          for (int j = i + 1; j < n; j++) {
            if (rnd.nextInt(100) < 45) {
              store.impose(new XneqY(x[i], x[j]));
            }
          }
        }
        IntVar largest = new IntVar(store, "largest", -1, 5);
        store.impose(new Max(x, largest));
        if (mode == 0) {
          DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
          search.setPrintInfo(false);
          optimum[0] =
              search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()), largest)
                  ? search.getCostValue()
                  : -2;
        } else {
          LcgSolver solver = new LcgSolver(store);
          solver.setChecking(true);
          int status = solver.minimize(largest);
          optimum[1] = status == CdclSolver.SAT ? solver.value(largest) : -2;
          long[] counts = solver.explanationStatistics().get("SeqPrecedeChain");
          if (counts != null) {
            own += counts[0] - counts[1] - counts[6] + counts[3] - counts[4] - counts[7];
            generic += counts[1] + counts[4] + counts[6] + counts[7];
          }
        }
      }
      assertThat(optimum[1]).as("instance %d", instance).isEqualTo(optimum[0]);
      unsat += optimum[0] == -2 ? 1 : 0;
    }
    System.out.printf(
        "seq precede chain colouring: %d unsat, %d own and %d generic or replayed explanations%n",
        unsat, own, generic);
    assertThat(own).isGreaterThan(1000);
    assertThat(own).isGreaterThan(20 * generic);
  }

  /**
   * Lexicographically ordered rows of a small matrix (strict or not), with a sum and differences
   * across rows, minimising a weighted sum: LCG finds the optimum depth-first search finds, every
   * explanation is checked, and most are the constraint's own.
   */
  @Test
  void lexChainAgreesWithSearch() {
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 300; instance++) {
      int[] optimum = new int[2];
      for (int mode = 0; mode < 2; mode++) {
        Random rnd = new Random(43 + instance);
        Store store = new Store();
        int rows = 3 + rnd.nextInt(3);
        int columns = 2 + rnd.nextInt(2);
        boolean strict = rnd.nextBoolean();
        IntVar[][] x = new IntVar[rows][columns];
        List<IntVar> all = new ArrayList<>();
        for (int i = 0; i < rows; i++) {
          for (int j = 0; j < columns; j++) {
            x[i][j] = new IntVar(store, "x" + i + j, 0, 2 + rnd.nextInt(2));
            if (rnd.nextInt(4) == 0) {
              x[i][j].domain.subtractAdapt(1 + rnd.nextInt(x[i][j].max() - 1));
              x[i][j].refreshBounds();
            }
            all.add(x[i][j]);
          }
        }
        store.impose(new LexChain(x, strict));
        IntVar[] v = all.toArray(new IntVar[0]);
        for (int k = 2 + rnd.nextInt(4); k > 0; k--) {
          int a = rnd.nextInt(v.length);
          int b = rnd.nextInt(v.length);
          if (a != b) {
            store.impose(new XneqY(v[a], v[b]));
          }
        }
        int[] w = new int[v.length];
        for (int k = 0; k < v.length; k++) {
          w[k] = rnd.nextInt(5) - 2;
        }
        IntVar cost = new IntVar(store, "cost", -100, 100);
        int[] wc = Arrays.copyOf(w, v.length + 1);
        wc[v.length] = -1;
        IntVar[] vc = Arrays.copyOf(v, v.length + 1);
        vc[v.length] = cost;
        store.impose(new LinearInt(vc, wc, "==", 0));
        if (mode == 0) {
          DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
          search.setPrintInfo(false);
          optimum[0] =
              search.labeling(store, new SimpleSelect<>(v, null, new IndomainMin<>()), cost)
                  ? search.getCostValue()
                  : -1000;
        } else {
          LcgSolver solver = new LcgSolver(store);
          solver.setChecking(true);
          int status = solver.minimize(cost);
          optimum[1] = status == CdclSolver.SAT ? solver.value(cost) : -1000;
          long[] counts = solver.explanationStatistics().get("LexChain");
          if (counts != null) {
            own += counts[0] - counts[1] - counts[6] + counts[3] - counts[4] - counts[7];
            generic += counts[1] + counts[4] + counts[6] + counts[7];
          }
        }
      }
      assertThat(optimum[1]).as("instance %d", instance).isEqualTo(optimum[0]);
    }
    System.out.printf("lex chain: %d own and %d generic or replayed explanations%n", own, generic);
    assertThat(own).isGreaterThan(1000);
    assertThat(own).isGreaterThan(generic);
  }

  @Test
  void unaryTransitionAgreesWithBruteForce() {
    Random rnd = new Random(31);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 800; instance++) {
      Store store = new Store();
      int n = 4;
      boolean optional = rnd.nextInt(3) == 0;
      boolean variable = !optional && rnd.nextBoolean();
      List<IntVar> all = new ArrayList<>();
      IntVar[] s = new IntVar[n];
      IntVar[] d = new IntVar[n];
      IntVar[] o = optional ? new IntVar[n] : null;
      int horizon = 5 + rnd.nextInt(4);
      for (int i = 0; i < n; i++) {
        s[i] = new IntVar(store, "s" + i, rnd.nextInt(2), horizon);
        if (rnd.nextInt(4) == 0) {
          s[i].domain.subtractAdapt(s[i].min() + 1 + rnd.nextInt(s[i].max() - s[i].min() - 1));
          s[i].refreshBounds();
        }
        all.add(s[i]);
      }
      for (int i = 0; i < n; i++) {
        int c = rnd.nextInt(4);
        d[i] =
            variable
                ? new IntVar(store, "d" + i, Math.max(0, c - 1), c + 1)
                : new IntVar(store, c, c);
        if (variable) {
          all.add(d[i]);
        }
      }
      if (optional) {
        for (int i = 0; i < n; i++) {
          o[i] = new IntVar(store, "o" + i, 0, 1);
          all.add(o[i]);
        }
      }
      int f = 1 + rnd.nextInt(3);
      int[] family = new int[n];
      for (int i = 0; i < n; i++) {
        family[i] = rnd.nextInt(f);
      }
      int[][] tt = new int[f][f];
      for (int[] row : tt) {
        for (int g = 0; g < f; g++) {
          row[g] = rnd.nextInt(3);
        }
      }
      IntVar[] x = all.toArray(IntVar[]::new);
      List<Relation> relations = new ArrayList<>();
      relations.add(
          new Relation(
              new UnaryTransition(s, d, family, tt, o),
              t -> {
                for (int i = 0; i < n; i++) {
                  for (int j = i + 1; j < n; j++) {
                    if (optional && (t[n + i] == 0 || t[n + j] == 0)) {
                      continue;
                    }
                    int di = variable ? t[n + i] : d[i].value();
                    int dj = variable ? t[n + j] : d[j].value();
                    if (t[i] + di + tt[family[i]][family[j]] > t[j]
                        && t[j] + dj + tt[family[j]][family[i]] > t[i]) {
                      return false;
                    }
                  }
                }
                return true;
              }));
      if (rnd.nextBoolean()) {
        relations.add(relation(s, rnd));
      }
      // t holds the starts, then the durations when variable or the presences when optional
      int[] t = new int[x.length];
      boolean expected = bruteForce(x, relations, t, 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] u = new int[x.length];
        for (int i = 0; i < x.length; i++) {
          u[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(u)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
      long[] counts = solver.explanationStatistics().get("UnaryTransition");
      if (counts != null) {
        own += counts[0] - counts[1] + counts[3] - counts[4];
        generic += counts[1] + counts[4];
      }
    }
    System.out.printf(
        "unary transition: %d sat, %d unsat, %d own and %d generic explanations%n",
        sat, unsat, own, generic);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(own).isGreaterThan(20 * generic);
  }

  /**
   * Random global cardinality and count constraints, with fixed bounds or with counters that are
   * variables of the problem (counted themselves or not), against brute force. Their explanations
   * are cuts of the flow network, which check that the negated atom makes it infeasible.
   */
  @Test
  void cardinalityAgreesWithBruteForce() {
    Random rnd = new Random(43);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 5 + rnd.nextInt(2);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 1 + rnd.nextInt(2); c > 0; c--) {
        relations.add(cardinality(x, rnd));
      }
      if (rnd.nextBoolean()) {
        relations.add(relation(x, rnd));
      }
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[n];
        for (int i = 0; i < n; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
      for (String name : new String[] {"GCC", "GlobalCardinality", "CountValues"}) {
        long[] counts = solver.explanationStatistics().get(name);
        if (counts != null) {
          own += counts[0] - counts[1] + counts[3] - counts[4];
          generic += counts[1] + counts[4];
        }
      }
    }
    System.out.printf(
        "cardinality: %d sat, %d unsat, %d own and %d generic explanations%n",
        sat, unsat, own, generic);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(own).isGreaterThan(1000);
    assertThat(own).isGreaterThan(50 * generic);
  }

  /**
   * Random knapsacks over the variables, with a capacity and a profit that are variables of the
   * problem, against brute force. Knapsack explains the bounds of its linear relaxation by
   * surrogate rows, which are checked to imply the atom; prunings of its dynamic program keep the
   * generic reason.
   */
  @Test
  void knapsackAgreesWithBruteForce() {
    Random rnd = new Random(47);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 6;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      int k = 3 + rnd.nextInt(2);
      int[] w = new int[k];
      int[] p = new int[k];
      IntVar[] q = new IntVar[k];
      for (int i = 0; i < k; i++) {
        w[i] = 1 + rnd.nextInt(4);
        p[i] = 1 + rnd.nextInt(4);
        q[i] = x[i];
        // quantities are not negative
        q[i].domain.in(store.level, q[i], 0, Math.min(q[i].max(), 1 + rnd.nextInt(2)));
      }
      int c = k;
      int f = k + 1;
      for (IntVar v : new IntVar[] {x[c], x[f]}) {
        v.domain.in(store.level, v, 0, v.max() + 3 * rnd.nextInt(3));
      }
      List<Relation> relations = new ArrayList<>();
      relations.add(
          new Relation(
              new Knapsack(p, w, q, x[c], x[f]),
              t -> {
                long weight = 0;
                long profit = 0;
                for (int i = 0; i < k; i++) {
                  weight += (long) w[i] * t[i];
                  profit += (long) p[i] * t[i];
                }
                return weight == t[c] && profit == t[f];
              }));
      if (rnd.nextBoolean()) {
        relations.add(relation(x, rnd));
      }
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[n];
        for (int i = 0; i < n; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
      long[] counts = solver.explanationStatistics().get("Knapsack");
      if (counts != null) {
        own += counts[0] - counts[1] + counts[3] - counts[4];
        generic += counts[1] + counts[4];
      }
    }
    System.out.printf(
        "knapsack: %d sat, %d unsat, %d own and %d generic explanations%n",
        sat, unsat, own, generic);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(own).isGreaterThan(100);
  }

  /**
   * A constraint without an explanation of its own, {@link IncreasingNValue}, is explained by
   * replaying a copy of it: the answers agree with brute force, every reason is checked, and the
   * reasons come from the replay rather than the generic reason.
   */
  @Test
  void replayedExplanationsAgreeWithBruteForce() {
    Random rnd = new Random(53);
    int sat = 0;
    int unsat = 0;
    long replayed = 0;
    long generic = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 6;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      relations.add(
          new Relation(
              new IncreasingNValue(new IntVar[] {x[0], x[1], x[2], x[3], x[4]}, x[5]),
              t -> {
                int distinct = 1;
                for (int i = 1; i < 5; i++) {
                  if (t[i] < t[i - 1]) {
                    return false;
                  }
                  distinct += t[i] > t[i - 1] ? 1 : 0;
                }
                return t[5] == distinct;
              }));
      for (int c = 1 + rnd.nextInt(3); c > 0; c--) {
        relations.add(relation(x, rnd));
      }
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[n];
        for (int i = 0; i < n; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
      long[] counts = solver.explanationStatistics().get("IncreasingNValue");
      if (counts != null) {
        replayed += counts[6] + counts[7];
        generic += counts[1] + counts[4];
      }
    }
    System.out.printf(
        "replay: %d sat, %d unsat, %d replayed and %d generic explanations%n",
        sat, unsat, replayed, generic);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(replayed).isGreaterThan(100);
    assertThat(generic).isLessThan(replayed / 10);
  }

  // (a, b) before (c, d) lexicographically
  private static boolean lexBefore(int a, int b, int c, int d, boolean strict) {
    return a < c || a == c && (strict ? b < d : b <= d);
  }

  /**
   * {@link NetworkFlow} explains its cost pruning by the duals of a minimum cost flow and its
   * feasibility pruning by a cut: the answers agree with brute force, every reason is checked, and
   * on flows without holes few are generic or replayed.
   */
  @Test
  void networkFlowExplanationsAgreeWithBruteForce() {
    Random rnd = new Random(61);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long other = 0;
    // arcs s->a, s->b, a->t, b->t, a->b on x0..x4, the cost on x5
    int[][] arcs = {{0, 1}, {0, 2}, {1, 3}, {2, 3}, {1, 2}};
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 6;
      IntVar[] x = new IntVar[n];
      // flows over intervals: the flow bounds explain the pruning, holes would not
      for (int i = 0; i < n - 1; i++) {
        x[i] = new IntVar(store, "x" + i, rnd.nextInt(2) - 1, 2 + rnd.nextInt(3));
      }
      x[n - 1] = new IntVar(store, "cost", 0, 4 + rnd.nextInt(12));
      int supply = 1 + rnd.nextInt(4);
      int[] weight = new int[arcs.length];
      NetworkBuilder net = new NetworkBuilder();
      Node[] node = {
        net.addNode("s", supply),
        net.addNode("a", 0),
        net.addNode("b", 0),
        net.addNode("t", -supply)
      };
      for (int k = 0; k < arcs.length; k++) {
        weight[k] = rnd.nextInt(4);
        net.addArc(node[arcs[k][0]], node[arcs[k][1]], weight[k], x[k]);
      }
      net.setCostVariable(x[n - 1]);
      List<Relation> relations = new ArrayList<>();
      relations.add(
          new Relation(
              new NetworkFlow(net),
              t -> {
                long cost = 0;
                for (int k = 0; k < arcs.length; k++) {
                  cost += (long) weight[k] * t[k];
                }
                return t[0] + t[1] == supply
                    && t[2] + t[4] == t[0]
                    && t[3] == t[1] + t[4]
                    && cost == t[5];
              }));
      for (int c = rnd.nextInt(3); c > 0; c--) {
        relations.add(relation(x, rnd));
      }
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[n];
        for (int i = 0; i < n; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
      long[] counts = solver.explanationStatistics().get("NetworkFlow");
      if (counts != null) {
        long notOwn = counts[1] + counts[4] + counts[6] + counts[7];
        own += counts[0] + counts[3] - notOwn;
        other += notOwn;
      }
    }
    System.out.printf(
        "network flow: %d sat, %d unsat, %d own and %d generic or replayed explanations%n",
        sat, unsat, own, other);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(own).isGreaterThan(10 * other);
  }

  /**
   * {@link IncreasingSum}, {@link LexOrder} and {@link CountVar} (also reified) explain their own
   * pruning: the answers agree with brute force, every reason is checked, and none is generic or
   * replayed.
   */
  @Test
  void sumOrderAndCountExplanationsAgreeWithBruteForce() {
    Random rnd = new Random(59);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long other = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 6;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n - 1; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      x[n - 1] = new IntVar(store, "b", 0, 1);
      boolean strict = rnd.nextBoolean();
      List<Relation> relations = new ArrayList<>();
      switch (rnd.nextInt(3)) {
        case 0 ->
            relations.add(
                new Relation(
                    new IncreasingSum(new IntVar[] {x[0], x[1], x[2]}, x[3], strict),
                    t ->
                        (strict ? t[0] < t[1] && t[1] < t[2] : t[0] <= t[1] && t[1] <= t[2])
                            && t[0] + t[1] + t[2] == t[3]));
        case 1 ->
            relations.add(
                new Relation(
                    new LexOrder(new IntVar[] {x[0], x[1]}, new IntVar[] {x[2], x[3]}, strict),
                    t -> lexBefore(t[0], t[1], t[2], t[3], strict)));
        default -> {
          CountVar count = new CountVar(new IntVar[] {x[0], x[1], x[2]}, x[3], x[4]);
          Predicate<int[]> counted =
              t -> (t[0] == t[4] ? 1 : 0) + (t[1] == t[4] ? 1 : 0) + (t[2] == t[4] ? 1 : 0) == t[3];
          relations.add(
              strict
                  ? new Relation(new Reified(count, x[5]), t -> counted.test(t) == (t[5] == 1))
                  : new Relation(count, counted));
        }
      }
      for (int c = 1 + rnd.nextInt(3); c > 0; c--) {
        relations.add(relation(x, rnd));
      }
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[n];
        for (int i = 0; i < n; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
      for (String name : new String[] {"IncreasingSum", "LexOrder", "CountVar", "Reified"}) {
        long[] counts = solver.explanationStatistics().get(name);
        if (counts != null) {
          long notOwn = counts[1] + counts[4] + counts[6] + counts[7];
          own += counts[0] + counts[3] - notOwn;
          other += notOwn;
        }
      }
    }
    System.out.printf(
        "sum, order and count: %d sat, %d unsat, %d own and %d generic or replayed explanations%n",
        sat, unsat, own, other);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(own).isGreaterThan(10 * other);
  }

  // a cardinality constraint over 3 or 4 of the variables
  private static Relation cardinality(IntVar[] x, Random rnd) {
    int n = x.length;
    int[] at = new int[3 + rnd.nextInt(2)];
    for (int k = 0; k < at.length; k++) {
      at[k] = pick(rnd, n, Arrays.copyOf(at, k));
    }
    IntVar[] q = new IntVar[at.length];
    for (int k = 0; k < at.length; k++) {
      q[k] = x[at[k]];
    }
    int kind = rnd.nextInt(4);
    int[] values =
        kind == 2
            ? new int[] {2, 0, 3}
            : kind == 3 ? new int[] {-1, 0, 1, 2, 3} : new int[] {0, 1, 2, 3};
    // counters: variables of the problem, possibly counted too
    int[] counterAt = new int[values.length];
    IntVar[] counters = new IntVar[values.length];
    for (int k = 0; k < values.length; k++) {
      counterAt[k] = rnd.nextInt(n);
      counters[k] = x[counterAt[k]];
    }
    int[] low = new int[values.length];
    int[] up = new int[values.length];
    for (int k = 0; k < values.length; k++) {
      low[k] = rnd.nextInt(2);
      up[k] = low[k] + rnd.nextInt(3);
    }
    boolean fixed = kind == 0;
    boolean closed = kind == 3;
    Constraint constraint =
        switch (kind) {
          case 0 -> new GlobalCardinality(q, values, low, up);
          case 1 -> new GlobalCardinality(q, values, counters);
          case 2 -> new CountValues(q, counters, values);
          default -> new GCC(q, counters, -1);
        };
    return new Relation(
        constraint,
        t -> {
          int[] count = new int[values.length];
          for (int k : at) {
            int a = -1;
            for (int j = 0; j < values.length; j++) {
              if (values[j] == t[k]) {
                a = j;
              }
            }
            if (a >= 0) {
              count[a]++;
            } else if (closed) {
              return false;
            }
          }
          for (int j = 0; j < values.length; j++) {
            if (fixed ? count[j] < low[j] || count[j] > up[j] : count[j] != t[counterAt[j]]) {
              return false;
            }
          }
          return true;
        });
  }

  @Test
  void allDifferentAgreesWithBruteForce() {
    Random rnd = new Random(29);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 5 + rnd.nextInt(2);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 1 + rnd.nextInt(2); c > 0; c--) {
        IntVar[] q = new IntVar[3 + rnd.nextInt(n - 2)];
        int[] at = new int[q.length];
        for (int k = 0; k < q.length; k++) {
          at[k] = pick(rnd, n, Arrays.copyOf(at, k));
          q[k] = x[at[k]];
        }
        int kind = rnd.nextInt(5);
        Constraint constraint =
            switch (kind) {
              case 0 -> new Alldifferent(q);
              case 1 -> new Alldiff(q);
              case 2 -> new Alldistinct(q);
              case 3 -> new AlldifferentExcept(q, new IntervalDomain(0, 1));
              default -> new AlldifferentExceptZero(q);
            };
        int shared = kind == 3 ? 1 : kind == 4 ? 0 : Integer.MIN_VALUE;
        relations.add(
            new Relation(
                constraint,
                t -> {
                  for (int k = 0; k < at.length; k++) {
                    for (int m = k + 1; m < at.length; m++) {
                      int v = t[at[k]];
                      boolean exception = v == shared || kind == 3 && v == 0;
                      if (v == t[at[m]] && !exception) {
                        return false;
                      }
                    }
                  }
                  return true;
                }));
      }
      for (int c = 1 + rnd.nextInt(2); c > 0; c--) {
        relations.add(relation(x, rnd));
      }
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[n];
        for (int i = 0; i < n; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
      for (String name :
          new String[] {
            "Alldifferent", "Alldiff", "Alldistinct", "AlldifferentExcept", "AlldifferentExceptZero"
          }) {
        long[] counts = solver.explanationStatistics().get(name);
        if (counts != null) {
          own += counts[0] - counts[1] + counts[3] - counts[4];
          generic += counts[1] + counts[4];
        }
      }
    }
    System.out.printf(
        "all different: %d sat, %d unsat, %d own and %d generic explanations%n",
        sat, unsat, own, generic);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(generic).isZero();
    assertThat(own).isGreaterThan(1000);
  }

  /**
   * Random subcircuits with a least number of nodes and a cost bound, against brute force.
   * Subcircuit explains its prunings by cuts of its successor graph, with the dominator pruning run
   * at every call, so its reasons are checked on every kind of pruning.
   */
  @Test
  void subcircuitAgreesWithBruteForce() {
    String skip = System.getProperty("sub_circuit_dominance_skip");
    System.setProperty("sub_circuit_dominance_skip", "0");
    try {
      Random rnd = new Random(41);
      int sat = 0;
      int unsat = 0;
      long own = 0;
      long generic = 0;
      for (int instance = 0; instance < 1500; instance++) {
        Store store = new Store();
        int n = 6 + rnd.nextInt(3);
        IntVar[] x = new IntVar[n];
        for (int i = 0; i < n; i++) {
          x[i] = new IntVar(store, "x" + i, 1, n);
          for (int w = 1; w <= n; w++) {
            if (w != i + 1 && rnd.nextInt(3) == 0) {
              x[i].domain.subtractAdapt(w);
              x[i].refreshBounds();
            }
          }
        }
        List<Relation> relations = new ArrayList<>();
        relations.add(new Relation(new Subcircuit(x), t -> isSubcircuit(t)));
        int[] cost = new int[n];
        for (int i = 0; i < n; i++) {
          cost[i] = rnd.nextInt(4);
        }
        IntVar[] in = new IntVar[n];
        for (int i = 0; i < n; i++) {
          in[i] = new IntVar(store, "in" + i, 0, 1);
          relations.add(new Relation(new Reified(new XneqC(x[i], i + 1), in[i]), t -> true));
        }
        int limit = n / 2 + rnd.nextInt(n);
        relations.add(
            new Relation(
                new LinearInt(in, cost, "<=", limit),
                t -> {
                  int sum = 0;
                  for (int i = 0; i < n; i++) {
                    sum += t[i] != i + 1 ? cost[i] : 0;
                  }
                  return sum <= limit;
                }));
        int least = 2 + rnd.nextInt(n - 2);
        int[] ones = new int[n];
        Arrays.fill(ones, 1);
        relations.add(
            new Relation(
                new LinearInt(in, ones, ">=", least),
                t -> {
                  int count = 0;
                  for (int i = 0; i < n; i++) {
                    count += t[i] != i + 1 ? 1 : 0;
                  }
                  return count >= least;
                }));
        boolean expected = bruteForce(x, relations, new int[n], 0);
        for (Relation r : relations) {
          store.impose(r.constraint);
        }
        LcgSolver solver = new LcgSolver(store);
        solver.setChecking(true);
        int status = solver.solve();
        assertThat(status)
            .as("instance %d", instance)
            .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
        if (expected) {
          int[] t = new int[n];
          for (int i = 0; i < n; i++) {
            t[i] = solver.value(x[i]);
          }
          for (Relation r : relations) {
            assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
          }
          sat++;
        } else {
          unsat++;
        }
        long[] counts = solver.explanationStatistics().get("Subcircuit");
        if (counts != null) {
          own += counts[0] - counts[1] + counts[3] - counts[4];
          generic += counts[1] + counts[4];
        }
      }
      System.out.printf(
          "subcircuit: %d sat, %d unsat, %d own and %d generic explanations%n",
          sat, unsat, own, generic);
      assertThat(sat).isGreaterThan(100);
      assertThat(unsat).isGreaterThan(100);
      assertThat(own).isGreaterThan(1000);
      assertThat(generic).isLessThan(own / 50);
    } finally {
      if (skip == null) {
        System.clearProperty("sub_circuit_dominance_skip");
      } else {
        System.setProperty("sub_circuit_dominance_skip", skip);
      }
    }
  }

  /**
   * Random circuits, numbered from 0 or 1, with a bound on a weighted sum of the successors,
   * against brute force. Circuit explains its prunings itself: cuts of its successor graph, and the
   * fixed arcs of a chain for the arc that would close it early.
   */
  @Test
  void circuitAgreesWithBruteForce() {
    Random rnd = new Random(43);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 5 + rnd.nextInt(3);
      int offset = rnd.nextInt(2);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, offset, offset + n - 1);
        for (int w = 0; w < n; w++) {
          if (w != i && rnd.nextInt(4) == 0) {
            x[i].domain.subtractAdapt(offset + w);
            x[i].refreshBounds();
          }
        }
      }
      List<Relation> relations = new ArrayList<>();
      relations.add(
          new Relation(
              new Circuit(x, offset),
              t -> {
                int v = 0;
                for (int k = 1; k < n; k++) {
                  v = t[v] - offset;
                  if (v < 0 || v >= n || v == 0) {
                    return false;
                  }
                }
                return t[v] - offset == 0;
              }));
      int[] weight = new int[n];
      for (int i = 0; i < n; i++) {
        weight[i] = rnd.nextInt(3) - 1;
      }
      int limit = rnd.nextInt(n) - n / 2;
      relations.add(
          new Relation(
              new LinearInt(x, weight, "<=", limit + offset * Arrays.stream(weight).sum()),
              t -> {
                int sum = 0;
                for (int i = 0; i < n; i++) {
                  sum += weight[i] * (t[i] - offset);
                }
                return sum <= limit;
              }));
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[n];
        for (int i = 0; i < n; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
      long[] counts = solver.explanationStatistics().get("Circuit");
      if (counts != null) {
        own += counts[0] - counts[1] + counts[3] - counts[4];
        generic += counts[1] + counts[4];
      }
    }
    System.out.printf(
        "circuit: %d sat, %d unsat, %d own and %d generic explanations%n",
        sat, unsat, own, generic);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(own).isGreaterThan(1000);
    assertThat(generic).isLessThan(own / 50);
  }

  // the nodes not pointing to themselves form one cycle
  private static boolean isSubcircuit(int[] t) {
    int n = t.length;
    int start = -1;
    int inCircuit = 0;
    boolean[] seen = new boolean[n + 1];
    for (int v = 0; v < n; v++) {
      if (seen[t[v]]) {
        return false;
      }
      seen[t[v]] = true;
      if (t[v] != v + 1) {
        start = v;
        inCircuit++;
      }
    }
    if (inCircuit == 0) {
      return true;
    }
    int length = 0;
    int v = start;
    do {
      v = t[v] - 1;
      length++;
    } while (v != start && length <= inCircuit);
    return v == start && length == inCircuit;
  }

  @Test
  void absoluteValueAgreesWithBruteForce() {
    Random rnd = new Random(37);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 2000; instance++) {
      Store store = new Store();
      int n = 5;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        // signed values, with up to two holes
        x[i] = new IntVar(store, "x" + i, -1 - rnd.nextInt(5), 1 + rnd.nextInt(5));
        for (int h = rnd.nextInt(3); h > 0; h--) {
          int v = x[i].min() + 1 + rnd.nextInt(x[i].max() - x[i].min() - 1);
          if (x[i].getSize() > 2) {
            x[i].domain.subtractAdapt(v);
            x[i].refreshBounds();
          }
        }
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 1 + rnd.nextInt(3); c > 0; c--) {
        int i = pick(rnd, n);
        int j = pick(rnd, n, i);
        relations.add(
            new Relation(new AbsXeqY(x[i], x[j], rnd.nextBoolean()), t -> Math.abs(t[i]) == t[j]));
      }
      for (int c = 1 + rnd.nextInt(2); c > 0; c--) {
        relations.add(relation(x, rnd));
      }
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[n];
        for (int i = 0; i < n; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
      long[] counts = solver.explanationStatistics().get("AbsXeqY");
      if (counts != null) {
        own += counts[0] - counts[1] + counts[3] - counts[4];
        generic += counts[1] + counts[4];
      }
    }
    System.out.printf(
        "absolute value: %d sat, %d unsat, %d own and %d generic explanations%n",
        sat, unsat, own, generic);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(generic).isZero();
    assertThat(own).isGreaterThan(500);
  }

  @Test
  void maxAndMinAgreeWithBruteForce() {
    Random rnd = new Random(37);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 5 + rnd.nextInt(2);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 2 + rnd.nextInt(3); c > 0; c--) {
        boolean simple = rnd.nextInt(3) == 0;
        IntVar[] q = new IntVar[simple ? 2 : 2 + rnd.nextInt(n - 2)];
        int[] at = new int[q.length];
        for (int k = 0; k < q.length; k++) {
          at[k] = pick(rnd, n, Arrays.copyOf(at, k));
          q[k] = x[at[k]];
        }
        // the maximum is one of the list half of the time, as in y[k] = max(y)
        int r = rnd.nextBoolean() ? at[rnd.nextInt(at.length)] : pick(rnd, n, at);
        boolean isMax = rnd.nextBoolean();
        Constraint constraint;
        if (simple) {
          constraint = isMax ? new MaxSimple(q[0], q[1], x[r]) : new MinSimple(q[0], q[1], x[r]);
        } else {
          constraint = isMax ? new Max(q, x[r]) : new Min(q, x[r]);
        }
        relations.add(
            new Relation(
                constraint,
                t -> {
                  int best = t[at[0]];
                  for (int k : at) {
                    best = isMax ? Math.max(best, t[k]) : Math.min(best, t[k]);
                  }
                  return t[r] == best;
                }));
      }
      relations.add(relation(x, rnd));
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[n];
        for (int i = 0; i < n; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
      for (String name : new String[] {"Max", "Min", "MaxSimple", "MinSimple"}) {
        long[] counts = solver.explanationStatistics().get(name);
        if (counts != null) {
          own += counts[0] - counts[1] + counts[3] - counts[4];
          generic += counts[1] + counts[4];
        }
      }
    }
    System.out.printf(
        "max and min: %d sat, %d unsat, %d own and %d generic explanations%n",
        sat, unsat, own, generic);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(generic).isZero();
    assertThat(own).isGreaterThan(1000);
  }

  @Test
  void layeredGraphsAgreeWithBruteForce() {
    Random rnd = new Random(31);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 5;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 1 + rnd.nextInt(2); c > 0; c--) {
        relations.add(rnd.nextBoolean() ? regularRelation(x, rnd) : mddRelation(x, rnd));
      }
      relations.add(relation(x, rnd));
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[n];
        for (int i = 0; i < n; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
      for (String name : new String[] {"Regular", "ExtensionalSupportMdd"}) {
        long[] counts = solver.explanationStatistics().get(name);
        if (counts != null) {
          own += counts[0] - counts[1] + counts[3] - counts[4];
          generic += counts[1] + counts[4];
        }
      }
    }
    System.out.printf(
        "layered graphs: %d sat, %d unsat, %d own and %d generic explanations%n",
        sat, unsat, own, generic);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(generic).isZero();
    assertThat(own).isGreaterThan(300);
  }

  /**
   * CountValuesBounds over random lists, some with a variable twice, and random values and bounds,
   * with every explanation checked; every reason and failure must be the constraint's own.
   */
  @Test
  void countValuesBoundsAgreesWithBruteForce() {
    Random rnd = new Random(37);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 5 + rnd.nextInt(2);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 2 + rnd.nextInt(2); c > 0; c--) {
        int[] at = new int[3 + rnd.nextInt(n - 2)];
        for (int k = 0; k < at.length; k++) {
          at[k] = pick(rnd, n, Arrays.copyOf(at, k));
        }
        if (rnd.nextInt(4) == 0) {
          at[at.length - 1] = at[0];
        }
        IntVar[] q = new IntVar[at.length];
        for (int k = 0; k < at.length; k++) {
          q[k] = x[at[k]];
        }
        int[] values = new int[1 + rnd.nextInt(3)];
        for (int k = 0; k < values.length; k++) {
          values[k] = rnd.nextInt(6) - 1;
          for (int l = 0; l < k; l++) {
            if (values[l] == values[k]) {
              k--;
              break;
            }
          }
        }
        int[] lb = new int[values.length];
        int[] ub = new int[values.length];
        for (int k = 0; k < values.length; k++) {
          lb[k] = rnd.nextInt(3);
          ub[k] = lb[k] + rnd.nextInt(2);
        }
        relations.add(
            new Relation(
                new CountValuesBounds(q, lb, ub, values),
                t -> {
                  for (int k = 0; k < values.length; k++) {
                    int count = 0;
                    for (int i : at) {
                      if (t[i] == values[k]) {
                        count++;
                      }
                    }
                    if (count < lb[k] || count > ub[k]) {
                      return false;
                    }
                  }
                  return true;
                }));
      }
      for (int c = rnd.nextInt(2); c > 0; c--) {
        relations.add(relation(x, rnd));
      }
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[n];
        for (int i = 0; i < n; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
      long[] counts = solver.explanationStatistics().get("CountValuesBounds");
      if (counts != null) {
        own += counts[0] - counts[1] + counts[3] - counts[4];
        generic += counts[1] + counts[4];
      }
    }
    System.out.printf(
        "count values bounds: %d sat, %d unsat, %d own and %d generic explanations%n",
        sat, unsat, own, generic);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(generic).isZero();
    assertThat(own).isGreaterThan(1000);
  }

  /** An automaton of three states, its transitions on small ranges, over 3 or 4 variables. */
  private static Relation regularRelation(IntVar[] x, Random rnd) {
    int[] at = new int[3 + rnd.nextInt(2)];
    for (int k = 0; k < at.length; k++) {
      at[k] = pick(rnd, x.length, Arrays.copyOf(at, k));
    }
    int states = 3;
    // next[s][v + 1] is the state after reading v in state s, or -1
    int[][] next = new int[states][7];
    boolean[] accepting = new boolean[states];
    FsmState[] state = new FsmState[states];
    Fsm fsm = new Fsm();
    for (int s = 0; s < states; s++) {
      state[s] = new FsmState();
      fsm.allStates.add(state[s]);
      Arrays.fill(next[s], -1);
    }
    fsm.initState = state[0];
    for (int s = 0; s < states; s++) {
      accepting[s] = rnd.nextInt(3) > 0;
      if (accepting[s]) {
        fsm.finalStates.add(state[s]);
      }
      for (int v = -1; v <= 5; v++) {
        if (rnd.nextInt(3) > 0) {
          int t = rnd.nextInt(states);
          next[s][v + 1] = t;
          state[s].addTransition(new FsmTransition(new IntervalDomain(v, v), state[t]));
        }
      }
    }
    IntVar[] vars = new IntVar[at.length];
    for (int k = 0; k < at.length; k++) {
      vars[k] = x[at[k]];
    }
    return new Relation(
        new Regular(fsm, vars),
        t -> {
          int s = 0;
          for (int k : at) {
            s = next[s][t[k] + 1];
            if (s < 0) {
              return false;
            }
          }
          return accepting[s];
        });
  }

  /** A table of random tuples on 3 variables, as a decision diagram. */
  private static Relation mddRelation(IntVar[] x, Random rnd) {
    int[] at = {pick(rnd, x.length), 0, 0};
    at[1] = pick(rnd, x.length, at[0]);
    at[2] = pick(rnd, x.length, at[0], at[1]);
    int[][] tuples = new int[4 + rnd.nextInt(12)][3];
    for (int[] t : tuples) {
      for (int k = 0; k < 3; k++) {
        t[k] = rnd.nextInt(6) - 1;
      }
    }
    return new Relation(
        new ExtensionalSupportMdd(new IntVar[] {x[at[0]], x[at[1]], x[at[2]]}, tuples),
        t -> {
          for (int[] tuple : tuples) {
            if (tuple[0] == t[at[0]] && tuple[1] == t[at[1]] && tuple[2] == t[at[2]]) {
              return true;
            }
          }
          return false;
        });
  }

  /** A hybrid table over 2 or 3 of the variables with random unary restrictions. */
  private static Relation tableRelation(IntVar[] x, Random rnd, boolean betweenColumns) {
    int arity = 2 + rnd.nextInt(2);
    int[] col = new int[arity];
    for (int k = 0; k < arity; k++) {
      col[k] = pick(rnd, x.length, Arrays.copyOf(col, k));
    }
    int rows = 2 + rnd.nextInt(6);
    Restriction[][] tuples = new Restriction[rows][arity];
    List<List<IntPredicate>> accepts = new ArrayList<>();
    List<int[]> columnRestrictions = new ArrayList<>();
    for (int r = 0; r < rows; r++) {
      List<IntPredicate> row = new ArrayList<>();
      for (int k = 0; k < arity; k++) {
        int v = rnd.nextInt(6) - 1;
        int w = rnd.nextInt(6) - 1;
        int other = (k + 1 + rnd.nextInt(arity - 1)) % arity;
        int offset = rnd.nextInt(3) - 1;
        // mostly constants, so that the tables prune
        switch (rnd.nextInt(betweenColumns ? 17 : 14)) {
          case 0 -> {
            tuples[r][k] = Restriction.any();
            row.add(u -> true);
          }
          case 1 -> {
            tuples[r][k] = Restriction.ne(v);
            row.add(u -> u != v);
          }
          case 2 -> {
            tuples[r][k] = Restriction.le(v);
            row.add(u -> u <= v);
          }
          case 3 -> {
            tuples[r][k] = Restriction.ge(v);
            row.add(u -> u >= v);
          }
          case 4 -> {
            tuples[r][k] = Restriction.in(v, w);
            row.add(u -> u == v || u == w);
          }
          case 5 -> {
            tuples[r][k] = Restriction.notIn(v, w);
            row.add(u -> u != v && u != w);
          }
          case 14, 15, 16 -> {
            Restriction.Relation rel = Restriction.Relation.values()[rnd.nextInt(6)];
            tuples[r][k] = Restriction.column(rel, other, offset);
            row.add(null); // checked on the whole tuple
            columnRestrictions.add(new int[] {r, k, other, offset, rel.ordinal()});
          }
          default -> {
            tuples[r][k] = Restriction.eq(v);
            row.add(u -> u == v);
          }
        }
      }
      accepts.add(row);
    }
    IntVar[] vars = new IntVar[arity];
    for (int k = 0; k < arity; k++) {
      vars[k] = x[col[k]];
    }
    return new Relation(
        new HybridTable(vars, tuples, !betweenColumns),
        t -> {
          for (int r = 0; r < rows; r++) {
            List<IntPredicate> row = accepts.get(r);
            boolean all = true;
            for (int k = 0; k < arity && all; k++) {
              all = row.get(k) == null || row.get(k).test(t[col[k]]);
            }
            for (int[] c : columnRestrictions) {
              if (all && c[0] == r) {
                long u = t[col[c[1]]];
                long w = (long) t[col[c[2]]] + c[3];
                all =
                    switch (Restriction.Relation.values()[c[4]]) {
                      case LT -> u < w;
                      case LE -> u <= w;
                      case EQ -> u == w;
                      case NE -> u != w;
                      case GE -> u >= w;
                      case GT -> u > w;
                    };
              }
            }
            if (all) {
              return true;
            }
          }
          return false;
        });
  }

  private static Relation booleanRelation(IntVar[] x, int ints, Random rnd) {
    int i = pick(rnd, ints);
    int j = pick(rnd, ints, i);
    int b = ints + pick(rnd, x.length - ints);
    int c = ints + pick(rnd, x.length - ints, b - ints);
    BooleanVar bv = (BooleanVar) x[b];
    return switch (rnd.nextInt(4)) {
      case 0 ->
          new Relation(new Reified(new XlteqY(x[i], x[j]), bv), t -> (t[i] <= t[j]) == (t[b] == 1));
      case 1 -> {
        int v = rnd.nextInt(4);
        yield new Relation(new Reified(new XeqC(x[i], v), bv), t -> (t[i] == v) == (t[b] == 1));
      }
      case 2 ->
          new Relation(
              new LinearInt(new IntVar[] {x[b], x[c], x[i]}, new int[] {2, 1, -1}, "==", 0),
              t -> 2 * t[b] + t[c] == t[i]);
      default -> new Relation(new XneqY(x[b], x[c]), t -> t[b] != t[c]);
    };
  }

  /** Models mixing integer and boolean variables (BooleanVar, which has no store index). */
  @Test
  void booleanModelsAgreeWithBruteForce() {
    Random rnd = new Random(13);
    int sat = 0;
    int unsat = 0;
    for (int instance = 0; instance < 1000; instance++) {
      Store store = new Store();
      int ints = 3 + rnd.nextInt(2);
      int n = ints + 2 + rnd.nextInt(2);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = i < ints ? newVar(store, "x" + i, rnd) : new BooleanVar(store, "b" + i);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 2 + rnd.nextInt(3); c > 0; c--) {
        relations.add(relation(Arrays.copyOf(x, ints), rnd));
      }
      for (int c = 2 + rnd.nextInt(4); c > 0; c--) {
        relations.add(booleanRelation(x, ints, rnd));
      }
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.sat().setSeed(instance);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
        int[] t = new int[n];
        for (int i = 0; i < n; i++) {
          t[i] = solver.value(x[i]);
        }
        for (Relation r : relations) {
          assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
        }
        sat++;
      } else {
        unsat++;
      }
    }
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
  }

  /**
   * Random small scheduling problems (precedences and a cumulative resource) against JaCoP's
   * depth-first search: larger than brute force allows, so that the solver interleaves its own
   * propagation with the store's.
   */
  @Test
  void schedulingAgreesWithSearch() {
    Random rnd = new Random(5);
    int sat = 0;
    int unsat = 0;
    for (int instance = 0; instance < SCHEDULING_INSTANCES; instance++) {
      int n = 7 + rnd.nextInt(4);
      int horizon = 8 + rnd.nextInt(8);
      int[] d = new int[n];
      int[] r = new int[n];
      for (int i = 0; i < n; i++) {
        d[i] = 1 + rnd.nextInt(4);
        r[i] = 1 + rnd.nextInt(3);
      }
      int limit = 3 + rnd.nextInt(2);
      int[][] prec = new int[n][2];
      int np = rnd.nextInt(n);
      for (int p = 0; p < np; p++) {
        int a = rnd.nextInt(n - 1);
        prec[p] = new int[] {a, a + 1 + rnd.nextInt(n - a - 1)};
      }
      Boolean[] answer = new Boolean[2];
      int[] starts = null;
      for (int mode = 0; mode < 2; mode++) {
        Store store = new Store();
        IntVar[] s = new IntVar[n];
        IntVar[] durations = new IntVar[n];
        IntVar[] resources = new IntVar[n];
        for (int i = 0; i < n; i++) {
          s[i] = new IntVar(store, "s" + i, 0, Math.max(0, horizon - d[i]));
          durations[i] = new IntVar(store, d[i], d[i]);
          resources[i] = new IntVar(store, r[i], r[i]);
        }
        for (int p = 0; p < np; p++) {
          store.impose(new XplusClteqZ(s[prec[p][0]], d[prec[p][0]], s[prec[p][1]]));
        }
        store.impose(new Cumulative(s, durations, resources, new IntVar(store, limit, limit)));
        if (mode == 0) {
          DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
          search.setPrintInfo(false);
          answer[0] = search.labeling(store, new SimpleSelect<>(s, null, new IndomainMin<>()));
        } else {
          LcgSolver solver = new LcgSolver(store);
          solver.setChecking(true);
          int status = solver.solve();
          answer[1] = status == CdclSolver.SAT;
          assertThat(status).isNotEqualTo(CdclSolver.UNKNOWN);
          if (answer[1]) {
            starts = new int[n];
            for (int i = 0; i < n; i++) {
              starts[i] = solver.value(s[i]);
            }
          }
        }
      }
      assertThat(answer[1]).as("instance %d", instance).isEqualTo(answer[0]);
      if (answer[1]) {
        for (int p = 0; p < np; p++) {
          assertThat(starts[prec[p][0]] + d[prec[p][0]]).isLessThanOrEqualTo(starts[prec[p][1]]);
        }
        for (int time = 0; time < horizon; time++) {
          int load = 0;
          for (int i = 0; i < n; i++) {
            assertThat(starts[i] + d[i]).isLessThanOrEqualTo(Math.max(horizon, d[i]));
            if (starts[i] <= time && time < starts[i] + d[i]) {
              load += r[i];
            }
          }
          assertThat(load).as("instance %d load at %d", instance, time).isLessThanOrEqualTo(limit);
        }
        sat++;
      } else {
        unsat++;
      }
    }
    assertThat(sat).isGreaterThan(SCHEDULING_INSTANCES / 8);
    assertThat(unsat).isGreaterThan(SCHEDULING_INSTANCES / 8);
  }

  /**
   * Random unary resources with release times, deadlines and precedences, minimising the makespan:
   * the optimum agrees with depth-first search, and every explanation of the unary rules
   * (precedences found by detectable precedences, edge finding and not-first) is checked.
   */
  @Test
  void unaryMakespanAgreesWithSearch() {
    Random rnd = new Random(17);
    long unaryReasons = 0;
    for (int instance = 0; instance < SCHEDULING_INSTANCES / 8; instance++) {
      int n = 6 + rnd.nextInt(4);
      int[] d = new int[n];
      int[] release = new int[n];
      int horizon = 0;
      for (int i = 0; i < n; i++) {
        d[i] = 1 + rnd.nextInt(9);
        horizon += d[i];
      }
      for (int i = 0; i < n; i++) {
        release[i] = rnd.nextInt(horizon / 2);
      }
      horizon += horizon / 4;
      int[][] prec = new int[rnd.nextInt(3)][];
      for (int p = 0; p < prec.length; p++) {
        int a = rnd.nextInt(n - 1);
        prec[p] = new int[] {a, a + 1 + rnd.nextInt(n - a - 1)};
      }
      int[] optimum = new int[2];
      for (int mode = 0; mode < 2; mode++) {
        Store store = new Store();
        IntVar[] s = new IntVar[n];
        IntVar[] durations = new IntVar[n];
        IntVar[] resources = new IntVar[n];
        IntVar makespan = new IntVar(store, "makespan", 0, horizon);
        for (int i = 0; i < n; i++) {
          s[i] = new IntVar(store, "s" + i, release[i], horizon - d[i]);
          durations[i] = new IntVar(store, d[i], d[i]);
          resources[i] = new IntVar(store, 1, 1);
          store.impose(new XplusClteqZ(s[i], d[i], makespan));
        }
        for (int[] p : prec) {
          store.impose(new XplusClteqZ(s[p[0]], d[p[0]], s[p[1]]));
        }
        store.impose(new CumulativeUnary(s, durations, resources, new IntVar(store, 1, 1)));
        if (mode == 0) {
          DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
          search.setPrintInfo(false);
          optimum[0] =
              search.labeling(store, new SimpleSelect<>(s, null, new IndomainMin<>()), makespan)
                  ? search.getCostValue()
                  : -1;
        } else {
          LcgSolver solver = new LcgSolver(store);
          solver.setChecking(true);
          int status = solver.minimize(makespan);
          optimum[1] = status == CdclSolver.SAT ? solver.value(makespan) : -1;
          long[] counts = solver.explanationStatistics().get("CumulativeUnary");
          unaryReasons += counts == null ? 0 : counts[0];
        }
      }
      assertThat(optimum[1]).as("instance %d", instance).isEqualTo(optimum[0]);
    }
    assertThat(unaryReasons).isPositive();
  }

  /**
   * Long tasks, as in the largescheduling benchmark: the time table made holes of thousands of
   * start values in one go, each an atom with a literal of its own, and the solver ran out of
   * memory before a first solution; a start with no value left was explained by every atom of the
   * constraint. Under LCG the time table now keeps to the bounds of the starts, and such a failure
   * has an explanation of its own.
   */
  @Test
  void longTasksKeepTheTimeTableToTheBounds() {
    Random rnd = new Random(11);
    int n = 30;
    Store store = new Store();
    IntVar[] s = new IntVar[n];
    IntVar[] durations = new IntVar[n];
    IntVar[] resources = new IntVar[n];
    int[] d = new int[n];
    int[] r = new int[n];
    int horizon = 0;
    for (int i = 0; i < n; i++) {
      d[i] = 5000 + rnd.nextInt(15000);
      r[i] = 1 + rnd.nextInt(40);
      horizon += d[i];
    }
    IntVar makespan = new IntVar(store, "makespan", 0, horizon);
    for (int i = 0; i < n; i++) {
      s[i] = new IntVar(store, "s" + i, 0, horizon);
      durations[i] = new IntVar(store, d[i], d[i]);
      resources[i] = new IntVar(store, r[i], r[i]);
      store.impose(new XplusClteqZ(s[i], d[i], makespan));
    }
    int limit = 50;
    store.impose(new Cumulative(s, durations, resources, new IntVar(store, limit, limit)));
    LcgSolver solver = new LcgSolver(store);
    solver.sat().setConflictLimit(2000);
    solver.minimize(makespan);

    int end = solver.value(makespan);
    for (int i = 0; i < n; i++) {
      assertThat(solver.value(s[i]) + d[i]).isLessThanOrEqualTo(end);
    }
    for (int i = 0; i < n; i++) {
      // the load where a task starts is the highest it reaches while that task runs
      int time = solver.value(s[i]);
      int load = 0;
      for (int k = 0; k < n; k++) {
        if (solver.value(s[k]) <= time && time < solver.value(s[k]) + d[k]) {
          load += r[k];
        }
      }
      assertThat(load).isLessThanOrEqualTo(limit);
    }
    assertThat(solver.sat().conflicts).isPositive();
    // one hole of a long task alone was thousands of literals
    assertThat(solver.sat().numVars()).isLessThan(100_000);
    long[] counts = solver.explanationStatistics().get("Cumulative");
    assertThat(counts[3]).as("failures of the cumulative").isPositive();
    assertThat(counts[4]).as("failures explained generically").isZero();
  }

  /**
   * CountValues prunes with an internal variable for the number of variables equal to no counted
   * value. The variable was not among the constraint's arguments, so the generic reason left out
   * its atoms, among them the solver's own decisions on it, and the learnt clauses cut off the
   * optimum.
   */
  @Test
  void countValuesExplainsWithItsInternalCounter() {
    int[] optimum = new int[2];
    for (int mode = 0; mode < 2; mode++) {
      Store store = new Store();
      IntVar[] x = new IntVar[6];
      for (int i = 0; i < 4; i++) {
        x[i] = new IntVar(store, "x" + i, -1, 3);
      }
      x[2].domain.unionAdapt(4, 4);
      x[2].refreshBounds();
      x[4] = new IntVar(store, "x4", 1, 3);
      x[5] = new IntVar(store, "x5", 1, 3);
      IntVar objective = new IntVar(store, "obj", -30, 30);
      store.impose(
          new CountValues(
              new IntVar[] {x[3], x[2], x[4], x[5]}, new IntVar[] {x[0], x[5]}, new int[] {0, 1}));
      store.impose(new ElementVariable(x[1], new IntVar[] {x[3], x[2], x[1], x[0]}, x[0], 0));
      store.impose(
          new LinearInt(
              new IntVar[] {x[3], x[4], x[5], objective}, new int[] {1, -1, 1, -1}, "==", 0));
      if (mode == 0) {
        DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
        search.setPrintInfo(false);
        assertThat(
                search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()), objective))
            .isTrue();
        optimum[0] = search.getCostValue();
      } else {
        LcgSolver solver = new LcgSolver(store);
        solver.setChecking(true);
        assertThat(solver.minimize(objective)).isEqualTo(CdclSolver.SAT);
        optimum[1] = solver.value(objective);
      }
    }
    assertThat(optimum[1]).isEqualTo(optimum[0]);
  }

  /**
   * x3 * x2 = x0 leaves only x2 = x3 = -1 and x2 = x3 = 2, which alldistinct rules out, though root
   * propagation does not see it (LCG fuzz seed 228750). The explanations of a conflict found in
   * search held on the root domains, so the conflict clause was empty, and the solver threw instead
   * of answering UNSAT.
   */
  @Test
  void conflictTrueOnTheRootDomainsProvesUnsatisfiable() {
    Store store = new Store();
    IntVar x0 = new IntVar(store, "x0", 1, 1);
    x0.domain.unionAdapt(3, 4);
    x0.refreshBounds();
    IntVar x1 = new IntVar(store, "x1", -1, 4);
    IntVar x2 = new IntVar(store, "x2", -1, 0);
    x2.domain.unionAdapt(2, 2);
    x2.refreshBounds();
    IntVar x3 = new IntVar(store, "x3", -1, 3);
    IntVar x4 = new IntVar(store, "x4", 1, 1);
    x4.domain.unionAdapt(3, 3);
    x4.refreshBounds();
    IntVar x5 = new IntVar(store, "x5", 1, 2);
    BooleanVar b0 = new BooleanVar(store, "b0");
    BooleanVar b1 = new BooleanVar(store, "b1");
    BooleanVar b2 = new BooleanVar(store, "b2");
    store.impose(new XmulYeqZ(x3, x2, x0));
    store.impose(
        new Xor(new LinearInt(new IntVar[] {x4, x5, x3}, new int[] {1, 2, -1}, "<=", 4), b2));
    store.impose(new AtLeast(new IntVar[] {x2, x1}, 1, 0));
    store.impose(new Member(new IntVar[] {x3, x2, x4}, x0));
    store.impose(new XorBool(new IntVar[] {b0, b2}, b0));
    store.impose(new Alldistinct(new IntVar[] {x2, x1, x3}));
    IntVar[] vars = {x0, x1, x2, x3, x4, x5, b0, b1, b2};
    List<SelectChoicePoint<IntVar>> annotations = new ArrayList<>();
    annotations.add(null);
    annotations.add(new SimpleSelect<>(vars, null, new IndomainMin<>()));
    annotations.add(new SimpleSelect<>(vars, new SmallestDomain<>(), new IndomainMax<>()));
    annotations.add(new SimpleSelect<>(vars, null, new IndomainMiddle<>()));
    annotations.add(new SplitSelect<>(vars, null, new IndomainMiddle<>()));
    for (SelectChoicePoint<IntVar> annotation : annotations) {
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.sat().setExternalReasonKeep(1);
      if (annotation != null) {
        solver.setAnnotation(annotation, false);
      }
      assertThat(solver.solve()).isEqualTo(CdclSolver.UNSAT);
    }
  }

  /**
   * Free search branches on the 0/1 variables before the others, as CP-SAT does: here the integer
   * variable y is first on the heap, and only branching on b first ([b <= 0], then y above 50)
   * gives b = 0 and y = 51. With the property off, y goes first ([y <= 50] makes b = 1, then y =
   * 0).
   */
  @Test
  void freeSearchBranchesOnBooleansFirst() {
    for (boolean first : new boolean[] {true, false}) {
      Store store = new Store();
      IntVar y = new IntVar(store, "y", 0, 100);
      BooleanVar b = new BooleanVar(store, "b");
      store.impose(new Reified(new XlteqC(y, 50), b));
      if (!first) {
        System.setProperty("jacop.lcg.booleansFirst", "false");
      }
      LcgSolver solver;
      try {
        solver = new LcgSolver(store);
      } finally {
        System.clearProperty("jacop.lcg.booleansFirst");
      }
      solver.setChecking(true);
      assertThat(solver.solve()).isEqualTo(CdclSolver.SAT);
      assertThat(new int[] {solver.value(b), solver.value(y)})
          .as("Booleans first: %s", first)
          .containsExactly(first ? new int[] {0, 51} : new int[] {1, 0});
    }
  }

  @Test
  void freeSearchWithoutBooleansFirstKeepsOneActivityOrder() {
    // with Booleans first off, every variable is in one order of activity again, as before the two
    // heaps: at equal activity the first variable goes first, here the 0/1 variable b, not the
    // wider y (skill-allocation 1m_2 took twice the nodes when y won such ties)
    Store store = new Store();
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar y = new IntVar(store, "y", 0, 100);
    store.impose(new Reified(new XlteqC(y, 50), b));
    System.setProperty("jacop.lcg.booleansFirst", "false");
    LcgSolver solver;
    try {
      solver = new LcgSolver(store);
    } finally {
      System.clearProperty("jacop.lcg.booleansFirst");
    }
    solver.setChecking(true);
    assertThat(solver.solve()).isEqualTo(CdclSolver.SAT);
    assertThat(new int[] {solver.value(b), solver.value(y)}).containsExactly(0, 51);
  }

  /**
   * Booleans first set after the solver is made moves the variables between the two orders: off
   * gives y first, as with the property off; on again gives b first.
   */
  @Test
  void booleansFirstSetAfterConstructionMovesTheVariables() {
    for (boolean[] settings : new boolean[][] {{false}, {false, true}}) {
      Store store = new Store();
      IntVar y = new IntVar(store, "y", 0, 100);
      BooleanVar b = new BooleanVar(store, "b");
      store.impose(new Reified(new XlteqC(y, 50), b));
      LcgSolver solver = new LcgSolver(store);
      for (boolean first : settings) {
        solver.setBooleansFirst(first);
      }
      solver.setChecking(true);
      boolean first = settings[settings.length - 1];
      assertThat(solver.booleansFirst()).isEqualTo(first);
      assertThat(solver.solve()).isEqualTo(CdclSolver.SAT);
      assertThat(new int[] {solver.value(b), solver.value(y)})
          .as("Booleans first: %s", first)
          .containsExactly(first ? new int[] {0, 51} : new int[] {1, 0});
    }
  }

  /** With turns, each restart into activity branching switches Booleans first. */
  @Test
  void booleansFirstTurnsSwitchAtRestarts() {
    Store store = new Store();
    IntVar y = new IntVar(store, "y", 0, 100);
    BooleanVar b = new BooleanVar(store, "b");
    store.impose(new Reified(new XlteqC(y, 50), b));
    LcgSolver solver = new LcgSolver(store);
    solver.setBranching(LcgSolver.Branching.ACTIVITY);
    solver.setBooleansFirstTurns(true);
    solver.notifyRestart();
    assertThat(solver.booleansFirst()).isFalse();
    solver.notifyRestart();
    assertThat(solver.booleansFirst()).isTrue();
    solver.notifyRestart();
    solver.setChecking(true);
    assertThat(solver.solve()).isEqualTo(CdclSolver.SAT);
    assertThat(new int[] {solver.value(b), solver.value(y)}).containsExactly(1, 0);
  }

  /** The literal map against a TreeMap, under random insertions and lookups. */
  /**
   * Semantic minimisation of a long group of literals on one variable (city-position learnt clauses
   * of thousands, which the pairwise check took quadratic time on) keeps the clause's set of values
   * and the asserting literal, and leaves no literal implied by another.
   */
  @Test
  void semanticMinimisationOfLongGroupsKeepsTheClause() {
    Random rnd = new Random(11);
    for (int instance = 0; instance < 500; instance++) {
      Store store = new Store();
      IntVar x = new IntVar(store, "x", 0, 60);
      LcgSolver solver = new LcgSolver(store);
      int i = solver.index(x);
      int n = 17 + rnd.nextInt(30);
      Set<Integer> lits = new LinkedHashSet<>();
      while (lits.size() < n) {
        int v = 1 + rnd.nextInt(59);
        int lit = rnd.nextInt(3) == 0 ? solver.eqLiteral(i, v) : solver.geLiteral(i, v);
        lits.add(rnd.nextBoolean() ? lit : -lit);
      }
      int[] clause = lits.stream().mapToInt(Integer::intValue).toArray();
      int[] original = clause.clone();
      int size = solver.minimizeLearnt(clause, clause.length);
      assertThat(clause[0]).as("instance %d", instance).isEqualTo(original[0]);
      assertThat(covered(solver, i, clause, size))
          .as("instance %d", instance)
          .isEqualTo(covered(solver, i, original, original.length));
      for (int a = 1; a < size; a++) {
        for (int b = 0; b < size; b++) {
          if (a != b) {
            BitSet va = covered(solver, i, new int[] {clause[a]}, 1);
            BitSet vb = covered(solver, i, new int[] {clause[b]}, 1);
            va.andNot(vb);
            assertThat(va.isEmpty()).as("instance %d: %d implies %d", instance, a, b).isFalse();
          }
        }
      }
    }
  }

  /**
   * Forty thousand {@code !=} literals of one variable, none implied by another, in linear time.
   */
  @Test
  void semanticMinimisationOfManyHolesIsFast() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 100_000);
    LcgSolver solver = new LcgSolver(store);
    int i = solver.index(x);
    int n = 40_000;
    int[] clause = new int[n + 1];
    clause[0] = solver.geLiteral(i, 99_000);
    for (int k = 1; k <= n; k++) {
      clause[k] = -solver.eqLiteral(i, 2 * k);
    }
    int size =
        assertTimeoutPreemptively(
            Duration.ofSeconds(2), () -> solver.minimizeLearnt(clause, clause.length));
    // [x >= 99,000] implies x != v for the holes below it, and stays as the asserting literal
    assertThat(size).isEqualTo(n + 1);
  }

  // the values of x in 0..60 that satisfy some literal of the clause
  private static BitSet covered(LcgSolver solver, int i, int[] clause, int size) {
    BitSet values = new BitSet();
    for (int k = 0; k < size; k++) {
      for (int v = 0; v <= 60; v++) {
        if (solver.holds(clause[k], i, v)) {
          values.set(v);
        }
      }
    }
    return values;
  }

  @Test
  void literalMapAgreesWithTreeMap() {
    Random rnd = new Random(3);
    for (int instance = 0; instance < 400; instance++) {
      // a narrow root domain becomes indexed by value as it fills; a wide one stays sorted
      int span = instance % 2 == 0 ? 60 : 2 * LiteralMap.DENSE_SPAN;
      LiteralMap map = new LiteralMap(-30, span - 31);
      TreeMap<Integer, Integer> reference = new TreeMap<>();
      for (int step = 0; step < 100; step++) {
        int v = rnd.nextInt(70) - 35;
        if (v >= -30 && v < 30 && rnd.nextInt(3) == 0 && !reference.containsKey(v)) {
          map.put(v, step + 1);
          reference.put(v, step + 1);
        } else if (rnd.nextInt(4) == 0 && reference.containsKey(v)) {
          map.remove(v);
          reference.remove(v);
        }
        Integer lower = reference.lowerKey(v);
        Integer higher = reference.higherKey(v);
        assertThat(map.get(v)).isEqualTo(reference.getOrDefault(v, LiteralMap.NONE));
        assertThat(map.lower(v)).isEqualTo(lower == null ? LiteralMap.NONE : reference.get(lower));
        assertThat(map.higher(v))
            .isEqualTo(higher == null ? LiteralMap.NONE : reference.get(higher));
      }
    }
  }

  /**
   * Random small scheduling problems minimising the makespan, against JaCoP's search: LCG with its
   * default search, with objective lower-bound search, and following the start-time annotation as
   * fixed search and as free search. Conflict analysis stops at semantic UIPs on some of them.
   */
  @Test
  void makespanAgreesWithSearch() {
    Random rnd = new Random(9);
    long atomLiterals = 0;
    long atomLiteralsLearnt = 0;
    long lowerBoundRuns = 0;
    long lowerBoundRaised = 0;
    long annotationDecisions = 0;
    long semanticUips = 0;
    long released = 0;
    for (int instance = 0; instance < SCHEDULING_INSTANCES * 3 / 8; instance++) {
      int n = 6 + rnd.nextInt(4);
      int horizon = 25;
      int[] d = new int[n];
      int[] r = new int[n];
      for (int i = 0; i < n; i++) {
        d[i] = 1 + rnd.nextInt(4);
        r[i] = 1 + rnd.nextInt(3);
      }
      int limit = 3 + rnd.nextInt(2);
      int np = rnd.nextInt(n);
      int[][] prec = new int[np][];
      for (int p = 0; p < np; p++) {
        int a = rnd.nextInt(n - 1);
        prec[p] = new int[] {a, a + 1 + rnd.nextInt(n - a - 1)};
      }
      int[] optimum = new int[6];
      for (int mode = 0; mode < 6; mode++) {
        Store store = new Store();
        IntVar[] s = new IntVar[n];
        IntVar[] ends = new IntVar[n];
        IntVar[] durations = new IntVar[n];
        IntVar[] resources = new IntVar[n];
        for (int i = 0; i < n; i++) {
          s[i] = new IntVar(store, "s" + i, 0, horizon - d[i]);
          ends[i] = new IntVar(store, "e" + i, d[i], horizon);
          store.impose(new XplusCeqZ(s[i], d[i], ends[i]));
          durations[i] = new IntVar(store, d[i], d[i]);
          resources[i] = new IntVar(store, r[i], r[i]);
        }
        IntVar makespan = new IntVar(store, "makespan", 0, horizon);
        store.impose(new Max(ends, makespan));
        for (int[] p : prec) {
          store.impose(new XplusClteqZ(s[p[0]], d[p[0]], s[p[1]]));
        }
        store.impose(new Cumulative(s, durations, resources, new IntVar(store, limit, limit)));
        if (mode == 0) {
          DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
          search.setPrintInfo(false);
          assertThat(
                  search.labeling(
                      store, new SimpleSelect<>(s, null, new IndomainMin<>()), makespan))
              .isTrue();
          optimum[0] = search.getCostValue();
        } else {
          LcgSolver solver = new LcgSolver(store);
          solver.setChecking(true);
          if (mode == 2 || mode == 4) {
            solver.setLowerBoundSearch(1, 1);
          }
          if (mode == 3 || mode == 4) {
            solver.setAnnotation(new SimpleSelect<>(s, null, new IndomainMin<>()), mode == 4);
            solver.sat().setRestarts(mode == 4);
          }
          if (mode == 5) {
            // the ends and the makespan follow from the starts
            List<IntVar> late = new ArrayList<>(Arrays.asList(ends));
            late.add(makespan);
            solver.setLateVariables(late);
          }
          assertThat(solver.minimize(makespan)).isEqualTo(CdclSolver.SAT);
          optimum[mode] = solver.value(makespan);
          assertThat(solver.atomLiteralsLearnt).isLessThanOrEqualTo(solver.atomLiterals);
          atomLiterals += solver.atomLiterals;
          atomLiteralsLearnt += solver.atomLiteralsLearnt;
          lowerBoundRuns += solver.lowerBoundRuns;
          lowerBoundRaised += solver.lowerBoundRaised;
          annotationDecisions += solver.annotationDecisions;
          semanticUips += solver.sat().semanticUips;
          released += solver.literalsReleased;
          if (mode == 5) {
            // every start fixed fixes the ends and the makespan: no decision is left for them
            assertThat(solver.lateDecisions).as("instance %d", instance).isZero();
          }
        }
      }
      for (int mode = 1; mode < 6; mode++) {
        assertThat(optimum[mode]).as("instance %d, mode %d", instance, mode).isEqualTo(optimum[0]);
      }
    }
    // the learnt clauses use some of the atoms pushed, not all
    assertThat(atomLiteralsLearnt).isPositive().isLessThan(atomLiterals);
    assertThat(lowerBoundRaised).isPositive().isLessThan(lowerBoundRuns);
    assertThat(annotationDecisions).isPositive();
    // conflict analysis stops at some semantic UIPs, and the optima above still agree
    assertThat(semanticUips).isPositive();
    // literals created only to push a bound are released, their variables given to new literals
    assertThat(released).isPositive();
  }

  /**
   * Makespan problems whose tasks trade duration for resource use (d + r fixed per task), so that
   * the cumulative prunes upper bounds of durations and resource uses. The optimum agrees with
   * depth-first search, every explanation is checked, and the cumulative explains every bound it
   * prunes itself.
   */
  @Test
  void variableTasksAgreeWithSearch() {
    Random rnd = new Random(13);
    long reasons = 0;
    long generic = 0;
    for (int instance = 0; instance < SCHEDULING_INSTANCES / 8; instance++) {
      int n = 5 + rnd.nextInt(3);
      int horizon = 20;
      int limit = 4 + rnd.nextInt(2);
      int[] c = new int[n];
      for (int i = 0; i < n; i++) {
        c[i] = 3 + rnd.nextInt(4);
      }
      int[] optimum = new int[2];
      for (int mode = 0; mode < 2; mode++) {
        Store store = new Store();
        IntVar[] s = new IntVar[n];
        IntVar[] ends = new IntVar[n];
        IntVar[] durations = new IntVar[n];
        IntVar[] resources = new IntVar[n];
        for (int i = 0; i < n; i++) {
          s[i] = new IntVar(store, "s" + i, 0, horizon);
          durations[i] = new IntVar(store, "d" + i, 1, c[i] - 1);
          resources[i] = new IntVar(store, "r" + i, 1, Math.min(limit, c[i] - 1));
          ends[i] = new IntVar(store, "e" + i, 0, horizon);
          store.impose(new XplusYeqC(durations[i], resources[i], c[i]));
          store.impose(new XplusYeqZ(s[i], durations[i], ends[i]));
        }
        IntVar makespan = new IntVar(store, "makespan", 0, horizon);
        store.impose(new Max(ends, makespan));
        store.impose(new Cumulative(s, durations, resources, new IntVar(store, limit, limit)));
        if (mode == 0) {
          DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
          search.setPrintInfo(false);
          IntVar[] vars = new IntVar[2 * n];
          System.arraycopy(durations, 0, vars, 0, n);
          System.arraycopy(s, 0, vars, n, n);
          assertThat(
                  search.labeling(
                      store, new SimpleSelect<>(vars, null, new IndomainMin<>()), makespan))
              .isTrue();
          optimum[0] = search.getCostValue();
        } else {
          LcgSolver solver = new LcgSolver(store);
          solver.setChecking(true);
          assertThat(solver.minimize(makespan)).isEqualTo(CdclSolver.SAT);
          optimum[1] = solver.value(makespan);
          long[] counts = solver.explanationStatistics().get("Cumulative");
          reasons += counts[0];
          generic += counts[1];
        }
      }
      assertThat(optimum[1]).as("instance %d", instance).isEqualTo(optimum[0]);
    }
    assertThat(reasons).isPositive();
    assertThat(generic).as("generic reasons of %d", reasons).isZero();
  }

  /**
   * An equality, decided during search, between a variable of a million values and one of five
   * (liner-sf-repositioning fm3_5): the large variable takes only the bounds of the small one, not
   * a million holes, each a {@code !=} atom with its own literals.
   */
  @Test
  void equalityWithASparseDomainKeepsTheBoundsOfALargeOne() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 1_000_000);
    IntVar y = new IntVar(store, "y", new IntervalDomain(0, 0));
    for (int v = 250_000; v <= 1_000_000; v += 250_000) {
      y.domain.unionAdapt(v, v);
      y.refreshBounds();
    }
    BooleanVar b = new BooleanVar(store, "b");
    IntVar cost = new IntVar(store, "cost", 0, 3_000_000);
    store.impose(new Reified(new XeqY(x, y), b));
    store.impose(
        new LinearInt(new IntVar[] {x, b, cost}, new int[] {1, -1_000_000, -1}, "==", -1_000_000));
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    assertThat(solver.minimize(cost)).isEqualTo(CdclSolver.SAT);
    assertThat(solver.value(cost)).isEqualTo(250_000);
    assertThat(solver.atomLiterals).isLessThan(1_000);
  }

  /**
   * Runs in large neighbourhoods between the runs of branch and bound assume the values of the best
   * solution outside each neighbourhood; the optimum and its proof must not change.
   */
  @Test
  void largeNeighbourhoodRunsKeepTheOptimum() {
    Random rnd = new Random(23);
    long runs = 0;
    for (int k = 0; k < 60; k++) {
      Store store = new Store();
      int n = 6;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 5);
      }
      List<int[]> neq = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          if (rnd.nextInt(3) == 0) {
            neq.add(new int[] {i, j});
            store.impose(new XneqY(x[i], x[j]));
          }
        }
      }
      int[] w = new int[n + 1];
      for (int i = 0; i < n; i++) {
        w[i] = rnd.nextInt(11) - 3;
      }
      w[n] = -1;
      IntVar cost = new IntVar(store, "cost", -1000, 1000);
      IntVar[] terms = Arrays.copyOf(x, n + 1);
      terms[n] = cost;
      store.impose(new LinearInt(terms, w, "==", 0));
      int best = Integer.MAX_VALUE;
      int[] v = new int[n];
      for (int code = 0; code < 46656; code++) {
        int c = code;
        int sum = 0;
        for (int i = 0; i < n; i++) {
          v[i] = c % 6;
          c /= 6;
          sum += w[i] * v[i];
        }
        boolean ok = true;
        for (int[] e : neq) {
          ok &= v[e[0]] != v[e[1]];
        }
        if (ok) {
          best = Math.min(best, sum);
        }
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.setLowerBoundSearch(0.5, 2);
      solver.setLns(new AdaptiveLns(store, x, cost, new Random(k)), 4.0, 2);
      assertThat(solver.minimize(cost)).isEqualTo(CdclSolver.SAT);
      assertThat(solver.value(cost)).isEqualTo(best);
      runs += solver.lnsRuns;
    }
    assertThat(runs).isPositive();
  }

  @Test
  void coreGuidedSearchAgreesWithSearch() {
    Random rnd = new Random(17);
    long cores = 0;
    long proved = 0;
    long hardened = 0;
    int unsat = 0;
    for (int instance = 0; instance < 300; instance++) {
      long seed = rnd.nextLong();
      Integer expected = coreModelOptimum(seed, -1, new long[3]);
      for (int mode = 0; mode < 4; mode++) {
        // mode 0: core-guided search alone; 1: a few conflicts, then branch and bound; 2: the
        // objective maximised through its negation; 3: a few conflicts of branch and bound first
        long[] stats = new long[3];
        Integer found = coreModelOptimum(seed, mode, stats);
        assertThat(found)
            .as("instance %d (seed %d), mode %d", instance, seed, mode)
            .isEqualTo(expected);
        cores += stats[0];
        proved += stats[1];
        hardened += stats[2];
      }
      if (expected == null) {
        unsat++;
      }
    }
    assertThat(cores).isPositive();
    // core-guided search alone proves some optima
    assertThat(proved).isPositive();
    // soft literals heavier than the gap to the best solution are made hard
    assertThat(hardened).isPositive();
    assertThat(unsat).isPositive();
  }

  @Test
  void coreGuidedSearchWithAtMostOneGroupsAgreesWithSearch() {
    Random rnd = new Random(29);
    long groups = 0;
    long expanded = 0;
    long proved = 0;
    for (int instance = 0; instance < 200; instance++) {
      long seed = rnd.nextLong();
      Integer expected = selectionOptimum(seed, false, new long[3]);
      long[] stats = new long[3];
      Integer found = selectionOptimum(seed, true, stats);
      assertThat(found).as("instance %d (seed %d)", instance, seed).isEqualTo(expected);
      groups += stats[0];
      expanded += stats[1];
      proved += stats[2];
    }
    assertThat(groups).isPositive();
    assertThat(expanded).isPositive();
    assertThat(proved).isPositive();
  }

  /** {@code b <=> x = c}, which core-guided search reads as an indicator of the value. */
  private static final class Indicator extends Reified implements ValueIndicator {
    private final IntVar b;
    private final IntVar x;
    private final int c;

    Indicator(IntVar x, int c, IntVar b) {
      super(new XeqC(x, c), b);
      this.b = b;
      this.x = x;
      this.c = c;
    }

    @Override
    public IntVar indicator() {
      return b;
    }

    @Override
    public IntVar variable() {
      return x;
    }

    @Override
    public int value() {
      return c;
    }
  }

  /**
   * A random selection problem as spot5: each x[i] is 0 (not selected) or one of a few values,
   * binary tables forbid pairs of values, and the objective is the weight of the variables at 0,
   * through indicators. Minimised by depth-first search, or by LCG with core-guided search alone;
   * stats gets the at-most-one groups, the terms seen through their values, and whether core-guided
   * search proved the optimum.
   */
  private static Integer selectionOptimum(long seed, boolean lcg, long[] stats) {
    Random rnd = new Random(seed);
    Store store = new Store();
    int n = 5 + rnd.nextInt(6);
    IntVar[] x = new IntVar[n];
    IntVar[] b = new IntVar[n];
    int[] w = new int[n + 1];
    int sum = 0;
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1 + rnd.nextInt(3));
      b[i] = new IntVar(store, "b" + i, 0, 1);
      store.impose(new Indicator(x[i], 0, b[i]));
      w[i] = 1 + rnd.nextInt(3);
      sum += w[i];
    }
    int pairs = n + rnd.nextInt(2 * n);
    for (int k = 0; k < pairs; k++) {
      int i = rnd.nextInt(n);
      int j = (i + 1 + rnd.nextInt(n - 1)) % n;
      List<int[]> allowed = new ArrayList<>();
      for (int u = 0; u <= x[i].max(); u++) {
        for (int v = 0; v <= x[j].max(); v++) {
          // a forbidden pair of selected values, or all of them
          boolean conflict = u > 0 && v > 0 && (rnd.nextInt(3) > 0 || u == v);
          if (!conflict) {
            allowed.add(new int[] {u, v});
          }
        }
      }
      store.impose(new HybridTable(new IntVar[] {x[i], x[j]}, allowed.toArray(new int[0][])));
    }
    IntVar cost = new IntVar(store, "cost", 0, sum);
    IntVar[] terms = Arrays.copyOf(b, n + 1);
    terms[n] = cost;
    w[n] = -1;
    store.impose(new LinearInt(terms, w, "==", 0));
    if (!lcg) {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      boolean found =
          search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()), cost);
      return found ? search.getCostValue() : null;
    }
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    solver.setCoreSearch(1, 1_000_000, 100_000);
    int status = solver.minimize(cost);
    assertThat(status).isNotEqualTo(CdclSolver.UNKNOWN);
    if (solver.coreSearch() != null) {
      stats[0] += solver.coreSearch().amoGroups;
      stats[1] += solver.coreSearch().expandedTerms;
      stats[2] += solver.coreSearch().proved ? 1 : 0;
    }
    return status == CdclSolver.SAT ? solver.value(cost) : null;
  }

  @Test
  void atMostOneGroupKeepsTheNextLevelsOfIntegerTerms() {
    // x0 = 0 forces x1 >= 4 and x1 = 0 forces x0 >= 4, so [x0 >= 1] and [x1 >= 1] form a group;
    // the levels above 1 must still cost their weight, or a solution with every soft literal false
    // (x0 = 4, x1 = 0, cost 8) ends the core-guided phase above its lower bound without a proof
    Store store = new Store();
    IntVar x0 = new IntVar(store, "x0", 0, 5);
    IntVar x1 = new IntVar(store, "x1", 0, 5);
    IntVar obj = new IntVar(store, "obj", 0, 25);
    store.impose(new LinearInt(new IntVar[] {x0, x1}, new int[] {1, 1}, ">=", 4));
    store.impose(new LinearInt(new IntVar[] {x0, x1, obj}, new int[] {2, 3, -1}, "==", 0));
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    solver.setCoreSearch(1, 1_000_000, 100_000);
    assertThat(solver.minimize(obj)).isEqualTo(CdclSolver.SAT);
    assertThat(solver.value(obj)).isEqualTo(8);
    assertThat(solver.coreSearch().amoGroups).isEqualTo(1);
    assertThat(solver.coreSearch().proved).isTrue();
  }

  @Test
  void coreGuidedSearchReadsThroughPartialSumsWithoutGroups() {
    // obj = s1 + s2 with s1 = x0 + x1 and s2 = x2 + x3, and no two terms exclude each other: the
    // terms are still the x's (trucking lost its proofs when the block sums were kept)
    Store store = new Store();
    IntVar[] x = new IntVar[4];
    for (int i = 0; i < 4; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 3);
    }
    IntVar s1 = new IntVar(store, "s1", 0, 6);
    IntVar s2 = new IntVar(store, "s2", 0, 6);
    IntVar obj = new IntVar(store, "obj", 0, 12);
    store.impose(new LinearInt(new IntVar[] {x[0], x[1], s1}, new int[] {1, 1, -1}, "==", 0));
    store.impose(new LinearInt(new IntVar[] {x[2], x[3], s2}, new int[] {1, 1, -1}, "==", 0));
    store.impose(new LinearInt(new IntVar[] {s1, s2, obj}, new int[] {1, 1, -1}, "==", 0));
    store.impose(new LinearInt(x, new int[] {1, 1, 1, 1}, ">=", 2));
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    solver.setCoreSearch(1, 1_000_000, 100_000);
    assertThat(solver.minimize(obj)).isEqualTo(CdclSolver.SAT);
    assertThat(solver.value(obj)).isEqualTo(2);
    assertThat(solver.coreSearch().amoGroups).isZero();
    assertThat(solver.coreSearch().termCount()).isEqualTo(4);
  }

  @Test
  void coreGuidedSearchReadsThroughPartialSums() {
    // obj = s1 + s2 with s1 = 2 * x0 + x1 and s2 = x2 + 3 * x3, as --lcg splits a long sum into
    // blocks; the terms of the core-guided phase are the x's, not the block sums
    Store store = new Store();
    IntVar[] x = new IntVar[4];
    for (int i = 0; i < 4; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 3);
    }
    IntVar s1 = new IntVar(store, "s1", 0, 9);
    IntVar s2 = new IntVar(store, "s2", 0, 12);
    IntVar obj = new IntVar(store, "obj", 0, 21);
    store.impose(new LinearInt(new IntVar[] {x[0], x[1], s1}, new int[] {2, 1, -1}, "==", 0));
    store.impose(new LinearInt(new IntVar[] {x[2], x[3], s2}, new int[] {1, 3, -1}, "==", 0));
    store.impose(new LinearInt(new IntVar[] {s1, s2, obj}, new int[] {1, 1, -1}, "==", 0));
    store.impose(new LinearInt(new IntVar[] {x[0], x[2]}, new int[] {1, 1}, ">=", 3));
    store.impose(new LinearInt(new IntVar[] {x[1], x[3]}, new int[] {1, 1}, ">=", 2));
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    solver.setCoreSearch(1, 1_000_000, 100_000);
    assertThat(solver.minimize(obj)).isEqualTo(CdclSolver.SAT);
    // x2 = 3 and x1 = 2: 3 + 2
    assertThat(solver.value(obj)).isEqualTo(5);
    assertThat(solver.coreSearch().termCount()).isEqualTo(4);
    assertThat(solver.coreSearch().proved).isTrue();
  }

  @Test
  void coreGuidedSearchJumpsOverHolesOfTheTerms() {
    // cost variables of two values, 0 and 10, as jp-encoding's: a soft literal per level would
    // need a core for each of the ten levels; one for the whole hole needs one
    Store store = new Store();
    IntVar[] x = new IntVar[4];
    for (int i = 0; i < 4; i++) {
      IntervalDomain dom = new IntervalDomain(0, 0);
      dom.unionAdapt(10, 10);
      x[i] = new IntVar(store, "x" + i, dom);
    }
    IntVar obj = new IntVar(store, "obj", 0, 40);
    store.impose(
        new LinearInt(
            new IntVar[] {x[0], x[1], x[2], x[3], obj}, new int[] {1, 1, 1, 1, -1}, "==", 0));
    store.impose(new LinearInt(new IntVar[] {x[0], x[1]}, new int[] {1, 1}, ">=", 1));
    store.impose(new LinearInt(new IntVar[] {x[2], x[3]}, new int[] {1, 1}, ">=", 1));
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    solver.setCoreSearch(1, 1_000_000, 100_000);
    assertThat(solver.minimize(obj)).isEqualTo(CdclSolver.SAT);
    assertThat(solver.value(obj)).isEqualTo(20);
    assertThat(solver.coreSearch().proved).isTrue();
    assertThat(solver.coreSearch().cores).isLessThanOrEqualTo(2);
  }

  @Test
  void coreGuidedSearchTakesTheDefinitionWithTheHigherRootBound() {
    // obj = a + b with a, b in 0..10, and obj = y0 + y1 with y0, y1 in {3, 5}, as presolve adds the
    // objective over cost variables next to its definition: the y's bound obj by 6 at the root
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 10);
    IntVar b = new IntVar(store, "b", 0, 10);
    IntVar[] y = new IntVar[2];
    for (int i = 0; i < 2; i++) {
      IntervalDomain dom = new IntervalDomain(3, 3);
      dom.unionAdapt(5, 5);
      y[i] = new IntVar(store, "y" + i, dom);
    }
    IntVar obj = new IntVar(store, "obj", 0, 20);
    store.impose(new LinearInt(new IntVar[] {a, b, obj}, new int[] {1, 1, -1}, "==", 0));
    store.impose(new LinearInt(new IntVar[] {y[0], y[1], obj}, new int[] {1, 1, -1}, "==", 0));
    store.impose(new XneqY(y[0], y[1]));
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    solver.setCoreSearch(1, 1_000_000, 100_000);
    assertThat(solver.minimize(obj)).isEqualTo(CdclSolver.SAT);
    assertThat(solver.value(obj)).isEqualTo(8);
    assertThat(solver.coreSearch().proved).isTrue();
    assertThat(solver.coreSearch().cores).isLessThanOrEqualTo(1);
  }

  @Test
  void coreGuidedSearchStratifiesByHalvingTheWeight() {
    // sixteen distinct weights: a stratum per weight costs a solution each, halving the threshold
    // gives five strata
    Store store = new Store();
    IntVar[] x = new IntVar[16];
    int[] w = new int[17];
    for (int i = 0; i < 16; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
      w[i] = 100 + i;
    }
    IntVar obj = new IntVar(store, "obj", 0, 2000);
    IntVar[] terms = Arrays.copyOf(x, 17);
    terms[16] = obj;
    w[16] = -1;
    store.impose(new LinearInt(terms, w, "==", 0));
    for (int i = 0; i < 16; i += 2) {
      store.impose(new LinearInt(new IntVar[] {x[i], x[i + 1]}, new int[] {1, 1}, ">=", 1));
    }
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    solver.setCoreSearch(1, 1_000_000, 100_000);
    assertThat(solver.minimize(obj)).isEqualTo(CdclSolver.SAT);
    assertThat(solver.value(obj)).isEqualTo(856);
    assertThat(solver.coreSearch().proved).isTrue();
    assertThat(solver.coreSearch().stratumSolutions).isLessThan(8);
  }

  /**
   * Builds a random model with a weighted sum objective and minimises it: by depth-first search
   * (mode -1) or by LCG with core-guided search (modes 0 to 3). Returns the optimum, or null when
   * there is no solution; stats gets the cores, whether core-guided search proved the optimum and
   * the soft literals it made hard.
   */
  private static Integer coreModelOptimum(long seed, int mode, long[] stats) {
    Random rnd = new Random(seed);
    Store store = new Store();
    int n = 4 + rnd.nextInt(5);
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      int lo = rnd.nextInt(3) - 1;
      // a few wider domains, for terms that must move far above their bounds
      x[i] = new IntVar(store, "x" + i, lo, lo + 1 + rnd.nextInt(i < 2 ? 10 : 4));
    }
    int m = 2 + rnd.nextInt(2 * n);
    for (int k = 0; k < m; k++) {
      int a = rnd.nextInt(n);
      int b = (a + 1 + rnd.nextInt(n - 1)) % n;
      switch (rnd.nextInt(5)) {
        case 0 -> store.impose(new XneqY(x[a], x[b]));
        case 3 -> {
          // x[a] >= high or x[a] >= low by a 0/1 choice: x[a] >= low holds in every solution but
          // not at the root, so core-guided search proves it by probing
          int low = 2 + rnd.nextInt(3);
          int high = low + 1 + rnd.nextInt(3);
          IntVar choice = new IntVar(store, "c" + k, 0, 1);
          store.impose(new LinearInt(new IntVar[] {x[a], choice}, new int[] {1, -high}, ">=", 0));
          store.impose(new LinearInt(new IntVar[] {x[a], choice}, new int[] {1, low}, ">=", low));
        }
        case 1 -> store.impose(new XlteqY(x[a], x[b]));
        case 2 -> store.impose(new XplusClteqZ(x[a], rnd.nextInt(3) - 1, x[b]));
        default -> {
          // x[a] + x[b] + x[c] >= c: pushes costs up
          int c = rnd.nextInt(n);
          store.impose(
              new LinearInt(
                  new IntVar[] {x[a], x[b], x[c]}, new int[] {1, 1, 1}, ">=", rnd.nextInt(6)));
        }
      }
    }
    int[] w = new int[n + 1];
    IntVar[] terms = Arrays.copyOf(x, n + 1);
    int lo = 0;
    int hi = 0;
    for (int i = 0; i < n; i++) {
      w[i] = rnd.nextInt(4) == 0 ? -1 - rnd.nextInt(2) : 1 + rnd.nextInt(5);
      lo += Math.min(w[i] * x[i].min(), w[i] * x[i].max());
      hi += Math.max(w[i] * x[i].min(), w[i] * x[i].max());
    }
    IntVar objective = new IntVar(store, "obj", lo, hi);
    terms[n] = objective;
    w[n] = -1;
    store.impose(new LinearInt(terms, w, "==", 0));
    IntVar cost = objective;
    if (mode == 2) {
      // as fz2jacop maximises: the negation of a variable that is minus the sum
      IntVar negated = new IntVar(store, "neg", -hi, -lo);
      store.impose(new XplusYeqZ(objective, negated, new IntVar(store, 0, 0)));
      IntVar max = new IntVar(store, "max", lo, hi);
      store.impose(new XplusYeqC(max, negated, 0));
      cost = max;
    }
    if (mode < 0) {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      boolean found =
          search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()), cost);
      return found ? search.getCostValue() : null;
    }
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    solver.setCoreSearch(
        1, mode == 1 ? 1 + rnd.nextInt(10) : 1_000_000, mode == 1 ? 1 + rnd.nextInt(5) : 100_000);
    if (mode == 3) {
      // a few conflicts of branch and bound, after a few of core-guided search or none, then the
      // core-guided phase picks up where it stopped
      solver.setCoreDelay(1, 1 + rnd.nextInt(5), rnd.nextInt(2));
    }
    int status = solver.minimize(cost);
    assertThat(status).isNotEqualTo(CdclSolver.UNKNOWN);
    if (solver.coreSearch() != null) {
      stats[0] += solver.coreSearch().cores;
      stats[1] += solver.coreSearch().proved ? 1 : 0;
      stats[2] += solver.coreSearch().hardened;
    }
    return status == CdclSolver.SAT ? solver.value(cost) : null;
  }
}
