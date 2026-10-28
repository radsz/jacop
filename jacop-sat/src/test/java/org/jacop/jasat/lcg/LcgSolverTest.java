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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
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
import org.jacop.constraints.Constraint;
import org.jacop.constraints.CountValues;
import org.jacop.constraints.CountValuesBounds;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementVariable;
import org.jacop.constraints.ExtensionalSupportMdd;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Max;
import org.jacop.constraints.MaxSimple;
import org.jacop.constraints.Member;
import org.jacop.constraints.Min;
import org.jacop.constraints.MinSimple;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.Xor;
import org.jacop.constraints.XorBool;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.UnaryTransition;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.constraints.regular.Regular;
import org.jacop.constraints.table.HybridTable;
import org.jacop.constraints.table.Restriction;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMax;
import org.jacop.search.IndomainMiddle;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.jacop.search.SplitSelect;
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
        }
      }
      List<Relation> relations = new ArrayList<>();
      relations.add(
          new Relation(
              new Binpacking(item, load, w, minBin, rnd.nextInt(4) != 0),
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
    for (int instance = 0; instance < 400; instance++) {
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
    assertThat(sat).isGreaterThan(50);
    assertThat(unsat).isGreaterThan(50);
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
    IntVar x1 = new IntVar(store, "x1", -1, 4);
    IntVar x2 = new IntVar(store, "x2", -1, 0);
    x2.domain.unionAdapt(2, 2);
    IntVar x3 = new IntVar(store, "x3", -1, 3);
    IntVar x4 = new IntVar(store, "x4", 1, 1);
    x4.domain.unionAdapt(3, 3);
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

  /** The literal map against a TreeMap, under random insertions and lookups. */
  @Test
  void literalMapAgreesWithTreeMap() {
    Random rnd = new Random(3);
    for (int instance = 0; instance < 200; instance++) {
      LiteralMap map = new LiteralMap();
      TreeMap<Integer, Integer> reference = new TreeMap<>();
      for (int step = 0; step < 100; step++) {
        int v = rnd.nextInt(60) - 30;
        if (rnd.nextInt(3) == 0 && !reference.containsKey(v)) {
          map.put(v, step + 1);
          reference.put(v, step + 1);
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
    for (int instance = 0; instance < 150; instance++) {
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
      int[] optimum = new int[5];
      for (int mode = 0; mode < 5; mode++) {
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
          if (mode >= 3) {
            solver.setAnnotation(new SimpleSelect<>(s, null, new IndomainMin<>()), mode == 4);
            solver.sat().setRestarts(mode == 4);
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
        }
      }
      for (int mode = 1; mode < 5; mode++) {
        assertThat(optimum[mode]).as("instance %d, mode %d", instance, mode).isEqualTo(optimum[0]);
      }
    }
    // the learnt clauses use some of the atoms pushed, not all
    assertThat(atomLiteralsLearnt).isPositive().isLessThan(atomLiterals);
    assertThat(lowerBoundRaised).isPositive().isLessThan(lowerBoundRuns);
    assertThat(annotationDecisions).isPositive();
    // conflict analysis stops at some semantic UIPs, and the optima above still agree
    assertThat(semanticUips).isPositive();
  }
}
