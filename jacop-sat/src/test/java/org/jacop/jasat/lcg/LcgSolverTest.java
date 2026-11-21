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
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.IntPredicate;
import java.util.function.Predicate;
import java.util.function.ToLongBiFunction;
import java.util.stream.IntStream;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.AlldifferentExcept;
import org.jacop.constraints.AlldifferentExceptZero;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Among;
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
import org.jacop.constraints.Implies;
import org.jacop.constraints.Increasing;
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
import org.jacop.constraints.Or;
import org.jacop.constraints.OverlappingAlldiff;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Routes;
import org.jacop.constraints.SeqPrecedeChain;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.Values;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XgteqC;
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
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.cumulative.Cumulatives;
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
import org.jacop.search.SimpleSolutionListener;
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

  /**
   * A solution given by setIncumbent is the best one of minimize: only better solutions are
   * reported, and an optimal incumbent is the answer without any report.
   */
  @Test
  void incumbentIsTheFirstSolution() {
    for (int start = 0; start <= 4; start++) {
      Store store = new Store();
      IntVar x = new IntVar(store, "x", 0, 5);
      IntVar y = new IntVar(store, "y", 0, 5);
      IntVar cost = new IntVar(store, "cost", 0, 100);
      store.impose(new LinearInt(new IntVar[] {x, y}, new int[] {1, 1}, ">=", 4));
      store.impose(new LinearInt(new IntVar[] {x, y, cost}, new int[] {2, 3, -1}, "==", 0));
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      // x + y = 4 with y = start: cost 8 + start, optimal for start 0
      int given = 8 + start;
      solver.setIncumbent(new IntVar[] {x, y, cost}, new int[] {4 - start, start, given});
      List<Integer> reported = new ArrayList<>();
      solver.onSolution(() -> reported.add(cost.value()));
      assertThat(solver.minimize(cost)).isEqualTo(CdclSolver.SAT);
      assertThat(solver.value(cost)).isEqualTo(8);
      assertThat(reported).allMatch(c -> c < given);
      if (start == 0) {
        assertThat(reported).isEmpty();
        assertThat(solver.value(x)).isEqualTo(4);
      }
    }
  }

  /**
   * An incumbent leaves the core-guided phase as without it: with its bound before the phase every
   * stratum had to improve on it, and the phase found no core (MaxSAT 2024 upgradeability rand653
   * and warehouses cap91 lost their proofs). Weighted vertex covers, from the cheapest cover above
   * the optimum.
   */
  @Test
  void incumbentKeepsTheCoreGuidedPhase() {
    Random rnd = new Random(71);
    long cores = 0;
    for (int instance = 0; instance < 20; instance++) {
      Store store = new Store();
      int n = 10;
      IntVar[] b = new IntVar[n];
      int[] w = new int[n];
      for (int i = 0; i < n; i++) {
        b[i] = new IntVar(store, "b" + i, 0, 1);
        w[i] = 1 + rnd.nextInt(9);
      }
      List<int[]> edges = new ArrayList<>();
      for (int e = 0; e < 2 * n; e++) {
        int i = rnd.nextInt(n);
        int j = rnd.nextInt(n);
        if (i != j) {
          edges.add(new int[] {i, j});
          store.impose(new LinearInt(new IntVar[] {b[i], b[j]}, new int[] {1, 1}, ">=", 1));
        }
      }
      IntVar cost = new IntVar(store, "cost", 0, 100);
      IntVar[] terms = Arrays.copyOf(b, n + 1);
      terms[n] = cost;
      int[] coefficients = Arrays.copyOf(w, n + 1);
      coefficients[n] = -1;
      store.impose(new LinearInt(terms, coefficients, "==", 0));
      // the optimum, and the cheapest cover above it as the incumbent
      int optimum = Integer.MAX_VALUE;
      int[] covers = new int[1 << n];
      for (int mask = 0; mask < 1 << n; mask++) {
        final int m = mask;
        covers[mask] = Integer.MAX_VALUE;
        if (edges.stream().allMatch(e -> ((m >> e[0]) & 1) + ((m >> e[1]) & 1) >= 1)) {
          int c = 0;
          for (int i = 0; i < n; i++) {
            c += ((mask >> i) & 1) * w[i];
          }
          covers[mask] = c;
          optimum = Math.min(optimum, c);
        }
      }
      int given = (1 << n) - 1;
      for (int mask = 0; mask < 1 << n; mask++) {
        if (covers[mask] > optimum
            && covers[mask] < Integer.MAX_VALUE
            && covers[mask] < covers[given]) {
          given = mask;
        }
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.setCoreSearch(1, 1_000_000, 100_000);
      int[] values = new int[n + 1];
      for (int i = 0; i < n; i++) {
        values[i] = (given >> i) & 1;
      }
      values[n] = covers[given];
      solver.setIncumbent(terms, values);
      assertThat(solver.minimize(cost)).as("instance %d", instance).isEqualTo(CdclSolver.SAT);
      assertThat(solver.value(cost)).as("instance %d", instance).isEqualTo(optimum);
      cores += solver.coreSearch().cores;
    }
    assertThat(cores).isPositive();
  }

  @Test
  void deferredValueRemovalsAgreeWithBruteForce() {
    // with no literal budget every value removal without a literal stays out of the solver, and
    // clauses cite its explanation instead (the out-of-memory of a 4096-variable alldiff)
    Random rnd = new Random(67);
    int sat = 0;
    int unsat = 0;
    long deferred = 0;
    long conflicts = 0;
    for (int instance = 0; instance < 2000; instance++) {
      Store store = new Store();
      int n = 5 + rnd.nextInt(2);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      IntVar[] distinct = Arrays.copyOf(x, 3 + rnd.nextInt(n - 2));
      relations.add(
          new Relation(
              rnd.nextBoolean() ? new Alldiff(distinct) : new Alldistinct(distinct),
              t -> Arrays.stream(t, 0, distinct.length).distinct().count() == distinct.length));
      for (int c = 1 + rnd.nextInt(3); c > 0; c--) {
        relations.add(relation(x, rnd));
      }
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.setLiteralBudget(0);
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
      deferred += solver.deferredAtoms;
      conflicts += solver.sat().conflicts;
    }
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(deferred).isGreaterThan(1000);
    assertThat(conflicts).isGreaterThan(300);
  }

  @Test
  void lazyCountersAgreeWithPigeonhole() {
    // pigeons in holes: rows and columns are SumBool counts, which become unary counters at a
    // restart once they explained a conflict (lazy decomposition); n + 1 pigeons do not fit
    long encoded = 0;
    for (int n = 4; n <= 6; n++) {
      for (int pigeons = n; pigeons <= n + 1; pigeons++) {
        Store store = new Store();
        IntVar[][] x = new IntVar[pigeons][n];
        for (int p = 0; p < pigeons; p++) {
          for (int h = 0; h < n; h++) {
            x[p][h] = new IntVar(store, "x" + p + "_" + h, 0, 1);
          }
          store.impose(new SumBool(x[p], "==", new IntVar(store, 1, 1)));
        }
        for (int h = 0; h < n; h++) {
          IntVar[] column = new IntVar[pigeons];
          for (int p = 0; p < pigeons; p++) {
            column[p] = x[p][h];
          }
          store.impose(new SumBool(column, "<=", new IntVar(store, 0, 1)));
        }
        LcgSolver solver = new LcgSolver(store);
        solver.setChecking(true);
        solver.setLazyCounterUses(1);
        int status = solver.solve();
        assertThat(status)
            .as("%d pigeons, %d holes", pigeons, n)
            .isEqualTo(pigeons > n ? CdclSolver.UNSAT : CdclSolver.SAT);
        if (status == CdclSolver.SAT) {
          int[] perHole = new int[n];
          for (int p = 0; p < pigeons; p++) {
            int sum = 0;
            for (int h = 0; h < n; h++) {
              sum += solver.value(x[p][h]);
              perHole[h] += solver.value(x[p][h]);
            }
            assertThat(sum).isEqualTo(1);
          }
          assertThat(Arrays.stream(perHole).max().getAsInt()).isLessThanOrEqualTo(1);
        }
        encoded += solver.lazyCountersEncoded;
      }
    }
    assertThat(encoded).isGreaterThan(0);
  }

  @Test
  void wideTablesAgreeWithBruteForce() {
    // tables of an index and many 0/1 columns, as merged element groups of a constant matrix
    // (minimal-decision-sets), two of them sharing columns, next to other constraints: their
    // explanations stop scanning columns once a fixed column kills a tuple with one atom
    Random rnd = new Random(97);
    int sat = 0;
    int unsat = 0;
    for (int instance = 0; instance < 600; instance++) {
      Store store = new Store();
      int columns = 6 + rnd.nextInt(5);
      IntVar[] x = new IntVar[columns + 2];
      for (int i = 0; i < columns; i++) {
        x[i] = new IntVar(store, "b" + i, 0, 1);
      }
      List<Relation> relations = new ArrayList<>();
      int[][] first = null;
      for (int g = 0; g < 2; g++) {
        int rows = 2 + rnd.nextInt(4);
        x[columns + g] = new IntVar(store, "i" + g, 1, rows);
        IntVar[] scope = new IntVar[columns + 1];
        System.arraycopy(x, 0, scope, 0, columns);
        scope[columns] = x[columns + g];
        int[][] tuples = new int[rows][columns + 1];
        for (int r = 0; r < rows; r++) {
          for (int k = 0; k < columns; k++) {
            // the second table mostly repeats rows of the first, so that the two often agree
            tuples[r][k] =
                first != null && rnd.nextInt(8) != 0 ? first[r % first.length][k] : rnd.nextInt(2);
          }
          tuples[r][columns] = r + 1;
        }
        first = tuples;
        int index = columns + g;
        relations.add(
            new Relation(
                new HybridTable(scope, tuples),
                t ->
                    Arrays.stream(tuples)
                        .anyMatch(
                            row ->
                                row[columns] == t[index]
                                    && IntStream.range(0, columns).allMatch(k -> row[k] == t[k]))));
      }
      for (int c = 1 + rnd.nextInt(2); c > 0; c--) {
        relations.add(relation(x, rnd));
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
    }
    assertThat(sat).isGreaterThan(30);
    assertThat(unsat).isGreaterThan(50);
  }

  @Test
  void tablesAsClausesAgreeWithBruteForce() {
    // tables of 2 to 4 columns, some over a fixed variable, written as clauses (support or
    // direct, jacop.lcg.tableClauses) next to other constraints; tuples may name values outside
    // the domains
    Random rnd = new Random(83);
    String[] modes = {"support", "direct", "binary"};
    long[] encoded = new long[modes.length];
    int sat = 0;
    int unsat = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 4 + rnd.nextInt(2);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      if (rnd.nextInt(4) == 0) {
        x[0] = new IntVar(store, "c", 2, 2);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 1 + rnd.nextInt(3); c > 0; c--) {
        IntVar[] scope = Arrays.copyOf(x, 2 + rnd.nextInt(3));
        Collections.shuffle(Arrays.asList(scope), rnd);
        int[][] tuples = new int[1 + rnd.nextInt(12)][scope.length];
        for (int[] tuple : tuples) {
          for (int k = 0; k < tuple.length; k++) {
            tuple[k] = rnd.nextInt(7) - 1;
          }
        }
        int[] position = new int[scope.length];
        for (int k = 0; k < scope.length; k++) {
          position[k] = Arrays.asList(x).indexOf(scope[k]);
        }
        relations.add(
            new Relation(
                new HybridTable(scope, tuples),
                t ->
                    Arrays.stream(tuples)
                        .anyMatch(
                            row ->
                                IntStream.range(0, row.length)
                                    .allMatch(k -> row[k] == t[position[k]]))));
      }
      if (rnd.nextBoolean()) {
        relations.add(relation(x, rnd));
      }
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      int mode = instance % modes.length;
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.setTableClauses(modes[mode]);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d (%s)", instance, modes[mode])
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
      encoded[mode] += solver.tablesAsClauses;
    }
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    for (long e : encoded) {
      assertThat(e).isGreaterThan(20);
    }
  }

  @Test
  void booleanTablesAsPrimeImplicatesAgreeWithBruteForce() {
    // tables of 2 to 6 columns over two-valued variables (some {0, 1}, some two other values, one
    // possibly fixed), written as the clauses of their prime implicates next to other
    // constraints; tuples may name values outside the domains
    Random rnd = new Random(91);
    long encoded = 0;
    int sat = 0;
    int unsat = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 4 + rnd.nextInt(4);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        int lo = rnd.nextInt(3) == 0 ? rnd.nextInt(3) - 1 : 0;
        int hi = lo + 1 + (rnd.nextInt(3) == 0 ? rnd.nextInt(3) : 0);
        x[i] = new IntVar(store, "x" + i, lo, lo);
        x[i].domain.unionAdapt(hi, hi);
        x[i].refreshBounds();
      }
      if (rnd.nextInt(5) == 0) {
        x[0] = new IntVar(store, "c", 1, 1);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 1 + rnd.nextInt(3); c > 0; c--) {
        IntVar[] scope = Arrays.copyOf(x, 2 + rnd.nextInt(n - 1));
        Collections.shuffle(Arrays.asList(scope), rnd);
        int[][] tuples = new int[1 + rnd.nextInt(3 << scope.length)][scope.length];
        for (int[] tuple : tuples) {
          for (int k = 0; k < tuple.length; k++) {
            tuple[k] =
                rnd.nextInt(8) == 0
                    ? 7
                    : scope[k].min() + rnd.nextInt(2) * (scope[k].max() - scope[k].min());
          }
        }
        IntVar[] sc = scope;
        int[] position = new int[scope.length];
        for (int k = 0; k < scope.length; k++) {
          position[k] = Arrays.asList(x).indexOf(scope[k]);
        }
        relations.add(
            new Relation(
                new HybridTable(sc, tuples),
                t ->
                    Arrays.stream(tuples)
                        .anyMatch(
                            row ->
                                IntStream.range(0, row.length)
                                    .allMatch(k -> row[k] == t[position[k]]))));
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
      solver.setTableClauses("none");
      solver.setCompressedTableClauses(false);
      solver.setBooleanTableClauses(true);
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
      encoded += solver.booleanTablesAsClauses;
    }
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(encoded).isGreaterThan(500);
  }

  @Test
  void primeCubesOfForbiddenPoints() {
    // x0 + x1 + x2 != 1: the forbidden points 001, 010, 100 merge with no other, three primes
    boolean[] allowed = new boolean[8];
    for (int p = 0; p < 8; p++) {
      allowed[p] = Integer.bitCount(p) != 1;
    }
    assertThat(LcgSolver.forbiddenPrimeCubes(allowed, 3, 100).orElseThrow()).hasSize(3);
    // x0 or x1 (x2 free): one prime cube, x0 = 0 and x1 = 0
    for (int p = 0; p < 8; p++) {
      allowed[p] = (p & 3) != 0;
    }
    List<long[]> primes = LcgSolver.forbiddenPrimeCubes(allowed, 3, 100).orElseThrow();
    assertThat(primes).hasSize(1);
    assertThat(primes.get(0)).containsExactly(3, 0);
    // the limit
    for (int p = 0; p < 8; p++) {
      allowed[p] = Integer.bitCount(p) % 2 == 0;
    }
    assertThat(LcgSolver.forbiddenPrimeCubes(allowed, 3, 3)).isEmpty();
    assertThat(LcgSolver.forbiddenPrimeCubes(allowed, 3, 4).orElseThrow()).hasSize(4);
  }

  @Test
  void rootActionWaitsForItsTimeOverEarlierRestarts() {
    // the action of atRootAfter runs at a restart to the root once its time has come, not at the
    // first restart before it: under free search, which restarts at once, a relaxation suspended
    // for a probe of 200 ms came back at the first restart
    Store store = new Store();
    IntVar[] x = new IntVar[9];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 8);
    }
    for (int i = 0; i < x.length; i++) {
      for (int j = i + 1; j < x.length; j++) {
        store.impose(new XneqY(x[i], x[j]));
      }
    }
    LcgSolver solver = new LcgSolver(store);
    boolean[] ran = {false};
    solver.atRootAfter(3_600_000_000_000L, () -> ran[0] = true);
    assertThat(solver.solve()).isEqualTo(CdclSolver.UNSAT);
    assertThat(solver.sat().restarts).isGreaterThan(0);
    assertThat(ran[0]).isFalse();
    assertThat(solver.rootActionPending()).isTrue();
  }

  @Test
  void detachOnAStoreLevelOfItsOwnLeavesTheModelAsItWas() {
    // a solver built on a store level that the caller removes after detach: the backtrack restores
    // the table the solver took as clauses, which is in the store once (release imposes it again)
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 3);
    }
    int[][] tuples = {{0, 1, 2}, {1, 2, 3}, {2, 3, 0}, {3, 0, 1}};
    store.impose(new HybridTable(x, tuples));
    store.impose(new XneqY(x[0], x[1]));
    assertThat(store.consistency()).isTrue();
    int[] before = new int[x.length];
    for (int i = 0; i < x.length; i++) {
      before[i] = x[i].dom().sizeConstraints();
    }
    store.setLevel(store.level + 1);
    LcgSolver solver = new LcgSolver(store);
    solver.setTableClauses("support");
    assertThat(solver.solve()).isEqualTo(CdclSolver.SAT);
    assertThat(solver.tablesAsClauses).isGreaterThan(0);
    // changes on the solver's level that no consistency followed: the table queued their columns
    x[0].domain.in(store.level, x[0], 0, 2);
    x[1].domain.in(store.level, x[1], 1, 3);
    solver.detach();
    store.removeLevel(store.level);
    store.setLevel(store.level - 1);
    for (int i = 0; i < x.length; i++) {
      assertThat(x[i].dom().sizeConstraints()).as("x%d", i).isEqualTo(before[i]);
      assertThat(x[i].min()).isZero();
      assertThat(x[i].max()).isEqualTo(3);
    }
    // the model is whole: every solution of plain search is a tuple of the table
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(true);
    assertThat(search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()))).isTrue();
    assertThat(search.getSolutionListener().solutionsNo()).isEqualTo(tuples.length);
  }

  @Test
  void compressedTablesAsClausesAgreeWithBruteForce() {
    // tables that are unions of one to three boxes of value sets, so they compress to a few
    // tuples, written as the clauses of their compressed form
    // (jacop.lcg.tableClauses.compressed) next to other constraints
    Random rnd = new Random(89);
    long encoded = 0;
    int sat = 0;
    int unsat = 0;
    for (int instance = 0; instance < 600; instance++) {
      Store store = new Store();
      int n = 4 + rnd.nextInt(2);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 1 + rnd.nextInt(3); c > 0; c--) {
        IntVar[] scope = Arrays.copyOf(x, 2 + rnd.nextInt(3));
        Collections.shuffle(Arrays.asList(scope), rnd);
        Set<List<Integer>> rows = new LinkedHashSet<>();
        for (int box = 1 + rnd.nextInt(3); box > 0; box--) {
          int[][] sets = new int[scope.length][];
          for (int k = 0; k < scope.length; k++) {
            sets[k] = rnd.ints(1 + rnd.nextInt(3), -1, 6).distinct().toArray();
          }
          addProduct(rows, sets, new ArrayList<>());
        }
        int[][] tuples =
            rows.stream()
                .map(r -> r.stream().mapToInt(Integer::intValue).toArray())
                .toArray(int[][]::new);
        int[] position = new int[scope.length];
        for (int k = 0; k < scope.length; k++) {
          position[k] = Arrays.asList(x).indexOf(scope[k]);
        }
        relations.add(
            new Relation(
                new HybridTable(scope, tuples),
                t ->
                    Arrays.stream(tuples)
                        .anyMatch(
                            row ->
                                IntStream.range(0, row.length)
                                    .allMatch(k -> row[k] == t[position[k]]))));
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
      solver.setCompressedTableClauses(true);
      // two-valued tables would go to the prime implicate encoding first
      solver.setBooleanTableClauses(false);
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
      encoded += solver.compressedTablesAsClauses;
    }
    assertThat(sat).isGreaterThan(50);
    assertThat(unsat).isGreaterThan(50);
    assertThat(encoded).isGreaterThan(50);
  }

  private static void addProduct(Set<List<Integer>> rows, int[][] sets, List<Integer> prefix) {
    if (prefix.size() == sets.length) {
      rows.add(new ArrayList<>(prefix));
      return;
    }
    for (int v : sets[prefix.size()]) {
      prefix.add(v);
      addProduct(rows, sets, prefix);
      prefix.remove(prefix.size() - 1);
    }
  }

  @Test
  void largeAlldiffStaysWithinTheLiteralBudget() {
    // each value fixed removes it from every other variable: n * n / 2 removals on one branch,
    // which made a solver variable each and filled the heap on debruijn_binary_04_06 (n = 4096)
    Store store = new Store();
    int n = 300;
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      // different minimums, so a value fixed is a hole in the variables with smaller ones
      x[i] = new IntVar(store, "x" + i, i / 2, n - 1);
    }
    store.impose(new Alldiff(x));
    LcgSolver solver = new LcgSolver(store);
    solver.setLiteralBudget(2000);
    assertThat(solver.solve()).isEqualTo(CdclSolver.SAT);
    assertThat(Arrays.stream(x).mapToInt(solver::value).distinct().count()).isEqualTo(n);
    assertThat(solver.deferredAtoms).isGreaterThan(10000);
    assertThat(solver.sat().numVars()).isLessThan(5000);
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

  /**
   * Restarts under a fixed search annotation (each run replays it, or runs take turns with activity
   * branching, from the start or from the first solution) keep the brute-force optimum of a
   * weighted sum under random side constraints.
   */
  @Test
  void fixedRestartsAgreeWithBruteForce() {
    Random rnd = new Random(31);
    int proved = 0;
    long restarts = 0;
    for (int instance = 0; instance < 600; instance++) {
      LcgSolver.FixedRestarts mode =
          instance % 2 == 0 ? LcgSolver.FixedRestarts.REPLAY : LcgSolver.FixedRestarts.ALTERNATE;
      Store store = new Store();
      int n = 5 + rnd.nextInt(3);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 2 + rnd.nextInt(3); c > 0; c--) {
        relations.add(relation(x, rnd));
      }
      int[] w = new int[n];
      for (int i = 0; i < n; i++) {
        w[i] = rnd.nextInt(9) - 4;
      }
      long best = minimum(x, relations, w, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      IntVar cost = new IntVar(store, "cost", -1000, 1000);
      IntVar[] terms = Arrays.copyOf(x, n + 1);
      terms[n] = cost;
      int[] weights = Arrays.copyOf(w, n + 1);
      weights[n] = -1;
      store.impose(new LinearInt(terms, weights, "==", 0));
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      // the annotation covers part of the variables: activity completes the assignment
      IntVar[] annotated = Arrays.copyOf(x, n - instance % 3);
      solver.setAnnotation(new SimpleSelect<>(annotated, null, new IndomainMin<>()), false);
      solver.setFixedRestarts(mode, instance % 4 >= 2);
      solver.setSeed(instance % 3);
      int status = solver.minimize(cost);
      restarts += solver.sat().restarts;
      if (best == Long.MAX_VALUE) {
        assertThat(status).as("instance %d", instance).isEqualTo(CdclSolver.UNSAT);
        continue;
      }
      assertThat(status).as("instance %d", instance).isEqualTo(CdclSolver.SAT);
      assertThat((long) solver.value(cost)).as("instance %d", instance).isEqualTo(best);
      int[] t = new int[n];
      for (int i = 0; i < n; i++) {
        t[i] = solver.value(x[i]);
      }
      for (Relation r : relations) {
        assertThat(r.test.test(t)).as("instance %d: %s", instance, r.constraint).isTrue();
      }
      proved++;
    }
    assertThat(proved).isGreaterThan(100);
    // the optimum of n pairwise different values from 0 takes many conflicts to prove: the runs
    // restart and keep it
    for (int k = 0; k < 2; k++) {
      Store store = new Store();
      int n = 8;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, n + 1);
      }
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          store.impose(new XneqY(x[i], x[j]));
        }
      }
      IntVar cost = new IntVar(store, "cost", 0, 1000);
      store.impose(new SumInt(x, "==", cost));
      LcgSolver solver = new LcgSolver(store);
      solver.setAnnotation(new SimpleSelect<>(x, null, new IndomainMin<>()), false);
      solver.setFixedRestarts(
          k == 0 ? LcgSolver.FixedRestarts.REPLAY : LcgSolver.FixedRestarts.ALTERNATE, k == 1);
      assertThat(solver.minimize(cost)).as("run %d", k).isEqualTo(CdclSolver.SAT);
      assertThat(solver.value(cost)).as("run %d", k).isEqualTo(n * (n - 1) / 2);
      restarts += solver.sat().restarts;
      System.out.println(
          "restarts " + k + " " + solver.sat().restarts + " " + solver.sat().conflicts);
    }
    assertThat(restarts).isPositive();
  }

  /**
   * Presolving the root again at every restart that learnt a root fact, which leaves out the
   * constraints the root satisfies, keeps the optimum: random weighted sums over a permutation with
   * random side constraints, solved with and without it.
   */
  @Test
  void restartPresolveKeepsTheOptimum() {
    Random rnd = new Random(29);
    long represolves = 0;
    for (int instance = 0; instance < 20; instance++) {
      long seed = rnd.nextLong();
      int[] optimum = new int[2];
      int[] status = new int[2];
      for (int run = 0; run < 2; run++) {
        Random r = new Random(seed);
        Store store = new Store();
        int n = 9;
        IntVar[] x = new IntVar[n];
        for (int i = 0; i < n; i++) {
          x[i] = new IntVar(store, "x" + i, 0, n - 1);
        }
        store.impose(new Alldistinct(x));
        for (int c = 0; c < 4; c++) {
          int[] a = new int[n];
          for (int i = 0; i < n; i++) {
            a[i] = r.nextInt(7) - 3;
          }
          store.impose(new LinearInt(x, a, "<=", r.nextInt(10)));
        }
        IntVar cost = new IntVar(store, "cost", -10_000, 10_000);
        IntVar[] terms = Arrays.copyOf(x, n + 1);
        terms[n] = cost;
        int[] weights = new int[n + 1];
        for (int i = 0; i < n; i++) {
          weights[i] = r.nextInt(41) - 20;
        }
        weights[n] = -1;
        store.impose(new LinearInt(terms, weights, "==", 0));
        LcgSolver solver = new LcgSolver(store);
        solver.setChecking(true);
        solver.setRestartPresolve(run == 0 ? 0 : 1e-9);
        status[run] = solver.minimize(cost);
        if (status[run] == CdclSolver.SAT) {
          optimum[run] = solver.value(cost);
        }
        if (run == 1) {
          represolves += solver.represolves;
        }
      }
      assertThat(status[1]).as("instance %d", instance).isEqualTo(status[0]);
      assertThat(optimum[1]).as("instance %d", instance).isEqualTo(optimum[0]);
    }
    assertThat(represolves).isGreaterThan(0);
  }

  /**
   * Dichotomic bound search keeps the optimum, never reports a bound above it, and raises the bound
   * by proofs of its probes: the sum of pairwise different values with random linear side
   * constraints is minimised by plain branch and bound and by bisection down to a zero gap.
   */
  @Test
  void bisectionKeepsTheOptimumAndProvesBounds() {
    Random rnd = new Random(59);
    long raised = 0;
    for (int instance = 0; instance < 8; instance++) {
      long seed = rnd.nextLong();
      int[] status = new int[2];
      int[] optimum = new int[2];
      for (int run = 0; run < 2; run++) {
        Random r = new Random(seed);
        Store store = new Store();
        int n = 8;
        IntVar[] x = new IntVar[n];
        for (int i = 0; i < n; i++) {
          x[i] = new IntVar(store, "x" + i, 0, 2 * n);
        }
        store.impose(new Alldistinct(x));
        for (int c = 0; c < 2; c++) {
          int[] a = new int[n];
          for (int i = 0; i < n; i++) {
            a[i] = r.nextInt(5) - 2;
          }
          store.impose(new LinearInt(x, a, "<=", r.nextInt(6)));
        }
        IntVar cost = new IntVar(store, "cost", 0, 1000);
        IntVar[] terms = Arrays.copyOf(x, n + 1);
        terms[n] = cost;
        int[] weights = new int[n + 1];
        for (int i = 0; i < n; i++) {
          weights[i] = 1 + r.nextInt(5);
        }
        weights[n] = -1;
        store.impose(new LinearInt(terms, weights, "==", 0));
        if (!store.consistency()) {
          break;
        }
        LcgSolver solver = new LcgSolver(store);
        solver.setChecking(true);
        solver.setSeed(instance);
        if (run == 1) {
          // probes of a few conflicts, so that some run out and move towards the lower bound
          solver.setLowerBoundSearch(0, 3);
          solver.setBisection(1e-9);
        }
        List<Long> bounds = new ArrayList<>();
        solver.onBound(bounds::add);
        status[run] = solver.minimize(cost);
        if (status[run] == CdclSolver.SAT) {
          optimum[run] = solver.value(cost);
          for (long b : bounds) {
            assertThat(b).as("instance %d", instance).isLessThanOrEqualTo(optimum[run]);
          }
        }
        if (run == 1) {
          raised += solver.bisectRaised;
        }
      }
      assertThat(status[1]).as("instance %d", instance).isEqualTo(status[0]);
      assertThat(optimum[1]).as("instance %d", instance).isEqualTo(optimum[0]);
    }
    assertThat(raised).isPositive();
  }

  /**
   * An objective that the core-guided phase cannot take (the maximum of pairwise different values,
   * no linear sum) is bisected to closure when core-guided search and lower-bound runs are on, as
   * under free search, at once or after a few conflicts: it keeps the optimum of plain branch and
   * bound and proves it.
   */
  @Test
  void anUncoredObjectiveIsBisectedToClosure() {
    Random rnd = new Random(61);
    int bisected = 0;
    for (int instance = 0; instance < 8; instance++) {
      long seed = rnd.nextLong();
      int[] status = new int[2];
      int[] optimum = new int[2];
      for (int run = 0; run < 2; run++) {
        Random r = new Random(seed);
        Store store = new Store();
        int n = 7;
        IntVar[] x = new IntVar[n];
        for (int i = 0; i < n; i++) {
          x[i] = new IntVar(store, "x" + i, 0, 3 * n);
        }
        store.impose(new Alldistinct(x));
        for (int c = 0; c < 3; c++) {
          int[] a = new int[n];
          for (int i = 0; i < n; i++) {
            a[i] = r.nextInt(5) - 2;
          }
          store.impose(new LinearInt(x, a, ">=", r.nextInt(6)));
        }
        IntVar max = new IntVar(store, "max", 0, 3 * n);
        store.impose(new Max(x, max));
        if (!store.consistency()) {
          break;
        }
        LcgSolver solver = new LcgSolver(store);
        solver.setChecking(true);
        solver.setSeed(instance);
        if (run == 1) {
          solver.setCoreSearch(0.5, 1000, 100);
          solver.setLowerBoundSearch(0.5, 3);
          // half of them after a few conflicts of branch and bound with lower-bound runs
          solver.setUncoredBisectionDelay(instance % 2 == 0 ? 0 : 5);
        }
        status[run] = solver.minimize(max);
        if (status[run] == CdclSolver.SAT) {
          optimum[run] = solver.value(max);
        }
        if (run == 1 && solver.uncoredBisection()) {
          bisected++;
        }
      }
      assertThat(status[1]).as("instance %d", instance).isEqualTo(status[0]);
      assertThat(optimum[1]).as("instance %d", instance).isEqualTo(optimum[0]);
    }
    assertThat(bisected).isPositive();
  }

  /**
   * Objective shaving keeps the optimum and raises the lower bound by steps of more than one: the
   * sum of pairwise different values, whose root bound is far below the optimum, is minimised with
   * and without shaving, on random linear side constraints, and both find the same optimum.
   */
  @Test
  void shavingKeepsTheOptimumAndRaisesTheBoundInSteps() {
    Random rnd = new Random(53);
    int jumps = 0;
    for (int instance = 0; instance < 8; instance++) {
      long seed = rnd.nextLong();
      int[] status = new int[2];
      int[] optimum = new int[2];
      for (int run = 0; run < 2; run++) {
        Random r = new Random(seed);
        Store store = new Store();
        int n = 7;
        IntVar[] x = new IntVar[n];
        for (int i = 0; i < n; i++) {
          x[i] = new IntVar(store, "x" + i, 0, 2 * n);
        }
        store.impose(new Alldistinct(x));
        for (int c = 0; c < 2; c++) {
          int[] a = new int[n];
          for (int i = 0; i < n; i++) {
            a[i] = r.nextInt(5) - 2;
          }
          store.impose(new LinearInt(x, a, "<=", r.nextInt(6)));
        }
        IntVar cost = new IntVar(store, "cost", 0, 1000);
        IntVar[] terms = Arrays.copyOf(x, n + 1);
        terms[n] = cost;
        int[] weights = new int[n + 1];
        for (int i = 0; i < n; i++) {
          weights[i] = 1 + r.nextInt(5);
        }
        weights[n] = -1;
        store.impose(new LinearInt(terms, weights, "==", 0));
        if (!store.consistency()) {
          break;
        }
        LcgSolver solver = new LcgSolver(store);
        solver.setChecking(true);
        solver.setSeed(instance);
        solver.setLowerBoundSearch(1, 5);
        solver.setShaving(run == 1);
        solver.setLowerBoundGrowth(run == 1 ? 2 : 1);
        List<Long> bounds = new ArrayList<>();
        solver.onBound(bounds::add);
        status[run] = solver.minimize(cost);
        if (status[run] == CdclSolver.SAT) {
          optimum[run] = solver.value(cost);
          for (long b : bounds) {
            assertThat(b).as("instance %d", instance).isLessThanOrEqualTo(optimum[run]);
          }
        }
        for (int k = 1; run == 1 && k < bounds.size(); k++) {
          if (bounds.get(k) > bounds.get(k - 1) + 1) {
            jumps++;
          }
        }
      }
      assertThat(status[1]).as("instance %d", instance).isEqualTo(status[0]);
      assertThat(optimum[1]).as("instance %d", instance).isEqualTo(optimum[0]);
    }
    assertThat(jumps).isGreaterThan(0);
  }

  /**
   * The lower-bound runs start before the first solution. Every solution has the cost 0, and a cost
   * above 0 leaves nine pigeons for eight holes, which branch and bound refutes only after many
   * conflicts; the run that assumes the cost at its lower bound finds a solution at once.
   */
  @Test
  void lowerBoundRunsStartBeforeTheFirstSolution() {
    Store store = new Store();
    int n = 10;
    IntVar[] z = new IntVar[n];
    for (int i = 0; i < n; i++) {
      z[i] = new BooleanVar(store, "z" + i);
    }
    IntVar cost = new IntVar(store, "cost", 0, n);
    IntVar[] terms = Arrays.copyOf(z, n + 1);
    terms[n] = cost;
    int[] weights = new int[n + 1];
    Arrays.fill(weights, 1);
    store.impose(new LinearInt(terms, weights, "==", n));
    BooleanVar crowded = new BooleanVar(store, "crowded");
    store.impose(new Reified(new XgteqC(cost, 1), crowded));
    IntVar[] pigeon = new IntVar[9];
    for (int i = 0; i < pigeon.length; i++) {
      pigeon[i] = new IntVar(store, "p" + i, 0, 8);
      // a cost above 0 closes the ninth hole
      store.impose(new Implies(crowded, new XlteqC(pigeon[i], 7)));
      for (int j = 0; j < i; j++) {
        store.impose(new XneqY(pigeon[i], pigeon[j]));
      }
    }
    assertThat(store.consistency()).isTrue();
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    // fixed search, each z at 0 first: the cost goes up and the pigeons are crowded
    IntVar[] order = Arrays.copyOf(z, n + pigeon.length);
    System.arraycopy(pigeon, 0, order, n, pigeon.length);
    solver.setAnnotation(new SimpleSelect<>(order, null, new IndomainMin<>()), false);
    solver.setLowerBoundSearch(0.5, 20);
    solver.setTimeLimit(20_000);
    assertThat(solver.minimize(cost)).isEqualTo(CdclSolver.SAT);
    assertThat(solver.value(cost)).isZero();
    assertThat(solver.lowerBoundRuns).isPositive();
  }

  /**
   * The bounds minimize reports at its restarts hold: none is above the optimum, and on most
   * instances learning raises one above the root's. Stopping in the action ends minimize with a
   * best solution within the gap of the bound, as fzn's --gap does.
   */
  @Test
  void boundsAtRestartsHoldAndStopAtTheGap() {
    Random rnd = new Random(31);
    int raised = 0;
    int stopped = 0;
    for (int instance = 0; instance < 24; instance++) {
      long seed = rnd.nextLong();
      for (int run = 0; run < 2; run++) {
        Random r = new Random(seed);
        Store store = new Store();
        int n = 9;
        IntVar[] x = new IntVar[n];
        for (int i = 0; i < n; i++) {
          x[i] = new IntVar(store, "x" + i, 0, n - 1);
        }
        store.impose(new Alldistinct(x));
        for (int c = 0; c < 4; c++) {
          int[] a = new int[n];
          for (int i = 0; i < n; i++) {
            a[i] = r.nextInt(7) - 3;
          }
          store.impose(new LinearInt(x, a, "<=", r.nextInt(10)));
        }
        IntVar cost = new IntVar(store, "cost", -10_000, 10_000);
        IntVar[] terms = Arrays.copyOf(x, n + 1);
        terms[n] = cost;
        int[] weights = new int[n + 1];
        for (int i = 0; i < n; i++) {
          weights[i] = r.nextInt(41) - 20;
        }
        weights[n] = -1;
        store.impose(new LinearInt(terms, weights, "==", 0));
        if (!store.consistency()) {
          break;
        }
        int root = cost.min();
        LcgSolver solver = new LcgSolver(store);
        solver.setChecking(true);
        solver.setSeed(instance);
        if (instance % 2 == 1) {
          solver.setLowerBoundSearch(0.5, 50);
          // objective shaving in half of them
          solver.setShaving(instance % 8 >= 4);
          solver.setLowerBoundGrowth(instance % 16 >= 8 ? 2 : 1);
        }
        if (instance % 4 >= 2) {
          solver.setCoreSearch(0.5, 10_000, 500);
        }
        List<Long> bounds = new ArrayList<>();
        boolean stop = run == 1;
        solver.onBound(
            lower -> {
              bounds.add(lower);
              long best = solver.bestObjective();
              if (stop && best != Long.MAX_VALUE && best - lower <= 0.2 * Math.abs(best)) {
                solver.stop();
              }
            });
        int status = solver.minimize(cost);
        if (run == 0) {
          if (status != CdclSolver.SAT) {
            break; // no solution: nothing to compare with
          }
          int optimum = solver.value(cost);
          for (long b : bounds) {
            assertThat(b).as("instance %d", instance).isLessThanOrEqualTo(optimum);
          }
          if (bounds.stream().anyMatch(b -> b > root)) {
            raised++;
          }
        } else if (status == CdclSolver.UNKNOWN) {
          long best = solver.value(cost); // the best solution found
          long last = bounds.stream().mapToLong(Long::longValue).max().orElseThrow();
          assertThat(best - last)
              .as("instance %d", instance)
              .isLessThanOrEqualTo((long) Math.floor(0.2 * Math.abs(best)));
          stopped++;
        }
      }
    }
    assertThat(raised).isGreaterThan(0);
    assertThat(stopped).isGreaterThan(0);
  }

  /**
   * Without restarts, as under a fixed search annotation, the bounds come from the backjumps to the
   * root: each must hold (never above the optimum), they must rise, and some must rise above the
   * root's bound before the search ends.
   */
  @Test
  void boundsWithoutRestartsComeFromBackjumpsToTheRoot() {
    Random rnd = new Random(37);
    int raised = 0;
    for (int instance = 0; instance < 24; instance++) {
      Store store = new Store();
      int n = 9;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, n - 1);
      }
      store.impose(new Alldistinct(x));
      for (int c = 0; c < 4; c++) {
        int[] a = new int[n];
        for (int i = 0; i < n; i++) {
          a[i] = rnd.nextInt(7) - 3;
        }
        store.impose(new LinearInt(x, a, "<=", rnd.nextInt(10)));
      }
      IntVar cost = new IntVar(store, "cost", -10_000, 10_000);
      IntVar[] terms = Arrays.copyOf(x, n + 1);
      terms[n] = cost;
      int[] weights = new int[n + 1];
      for (int i = 0; i < n; i++) {
        weights[i] = rnd.nextInt(41) - 20;
      }
      weights[n] = -1;
      store.impose(new LinearInt(terms, weights, "==", 0));
      if (!store.consistency()) {
        continue;
      }
      int root = cost.min();
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.setSeed(instance);
      solver.setAnnotation(new SimpleSelect<>(x, null, new IndomainMin<>()), false);
      solver.sat().setRestarts(false);
      List<Long> bounds = new ArrayList<>();
      solver.onBound(bounds::add);
      int status = solver.minimize(cost);
      assertThat(solver.sat().restarts).isZero();
      if (status != CdclSolver.SAT) {
        continue;
      }
      int optimum = solver.value(cost);
      for (int k = 0; k < bounds.size(); k++) {
        assertThat(bounds.get(k)).as("instance %d", instance).isLessThanOrEqualTo(optimum);
        if (k > 0) {
          assertThat(bounds.get(k)).isGreaterThan(bounds.get(k - 1));
        }
      }
      if (bounds.stream().anyMatch(b -> b > root)) {
        raised++;
      }
    }
    assertThat(raised).isGreaterThan(0);
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
    // the profile and area rules are explained by the bounds of all rectangles, never generically
    assertThat(own).isPositive();
    assertThat(generic).isZero();
  }

  private static IntVar constant(Store store, int c) {
    return new IntVar(store, c, c);
  }

  /**
   * Packings of more and larger rectangles than {@link #diffnAgreesWithBruteForce}, with origin
   * domains full of holes, so that the profile and area rules prune: every explanation is checked,
   * none is generic (all origin holes), and the LCG answer agrees with depth-first search.
   */
  @Test
  void diffnProfileReasonsAreBoundsOnly() {
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 1000; instance++) {
      Store[] stores = new Store[2];
      IntVar[][] all = new IntVar[2][];
      for (int copy = 0; copy < 2; copy++) {
        Random rnd = new Random(41 + instance);
        Store store = new Store();
        int n = 7 + rnd.nextInt(4);
        int side = 5 + rnd.nextInt(3);
        IntVar[] ox = new IntVar[n];
        IntVar[] oy = new IntVar[n];
        IntVar[] lx = new IntVar[n];
        IntVar[] ly = new IntVar[n];
        for (int i = 0; i < n; i++) {
          ox[i] = new IntVar(store, "x" + i, 0, side - 1);
          oy[i] = new IntVar(store, "y" + i, 0, side - 1);
          for (IntVar o : new IntVar[] {ox[i], oy[i]}) {
            for (int h = rnd.nextInt(3); h > 0; h--) {
              o.domain.subtractAdapt(rnd.nextInt(side));
            }
            o.refreshBounds();
          }
          lx[i] =
              rnd.nextInt(4) == 0 ? new IntVar(store, 1, 3) : constant(store, 1 + rnd.nextInt(3));
          ly[i] =
              rnd.nextInt(4) == 0 ? new IntVar(store, 1, 3) : constant(store, 1 + rnd.nextInt(3));
          // inside a side x side square
          store.impose(new XplusYlteqZ(ox[i], lx[i], constant(store, side)));
          store.impose(new XplusYlteqZ(oy[i], ly[i], constant(store, side)));
        }
        store.impose(new Diffn(ox, oy, lx, ly, rnd.nextBoolean()));
        stores[copy] = store;
        IntVar[] vars = new IntVar[4 * n];
        for (int i = 0; i < n; i++) {
          vars[4 * i] = ox[i];
          vars[4 * i + 1] = oy[i];
          vars[4 * i + 2] = lx[i];
          vars[4 * i + 3] = ly[i];
        }
        all[copy] = vars;
      }
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      boolean expected =
          stores[0].consistency()
              && search.labeling(stores[0], new SimpleSelect<>(all[0], null, new IndomainMin<>()));
      LcgSolver solver = new LcgSolver(stores[1]);
      solver.setChecking(true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (expected) {
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
        "diffn profile: %d sat, %d unsat, %d own and %d generic explanations%n",
        sat, unsat, own, generic);
    assertThat(sat).isPositive();
    assertThat(unsat).isPositive();
    assertThat(own).isPositive();
    assertThat(generic).isZero();
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
   * Bin packing with the number of items of each bin as variables (bin packing with cardinality),
   * over three or four bins so that the rules on groups of bins run, with items of weight 0 and
   * items sharing a bin variable: the LCG answer agrees with enumerating the bins, every
   * explanation is checked, and almost all are the constraint's own.
   */
  @Test
  void binpackingWithCardinalityAgreesWithBruteForce() {
    Random rnd = new Random(37);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    for (int instance = 0; instance < 600; instance++) {
      Store store = new Store();
      int bins = 3 + rnd.nextInt(2);
      int n = 6 + rnd.nextInt(3);
      List<IntVar> distinct = new ArrayList<>();
      int[] at = new int[n];
      int[] w = new int[n];
      for (int k = 0; k < n; k++) {
        if (k > 0 && rnd.nextInt(8) == 0) {
          at[k] = at[rnd.nextInt(k)];
        } else {
          IntVar b = new IntVar(store, "b" + k, 0, bins - 1);
          if (rnd.nextInt(3) == 0) {
            b.domain.subtractAdapt(rnd.nextInt(bins));
            b.refreshBounds();
          }
          at[k] = distinct.size();
          distinct.add(b);
        }
        w[k] = rnd.nextInt(8) == 0 ? 0 : 1 + rnd.nextInt(5);
      }
      IntVar[] x = distinct.toArray(new IntVar[0]);
      IntVar[] item = new IntVar[n];
      for (int k = 0; k < n; k++) {
        item[k] = x[at[k]];
      }
      IntVar[] load = new IntVar[bins];
      IntVar[] card = new IntVar[bins];
      for (int i = 0; i < bins; i++) {
        int lo = rnd.nextInt(6);
        load[i] = new IntVar(store, "l" + i, lo, lo + 3 + rnd.nextInt(8));
        int c = rnd.nextInt(3);
        card[i] = new IntVar(store, "c" + i, c, c + 1 + rnd.nextInt(2));
      }
      List<Relation> relations = new ArrayList<>();
      relations.add(
          new Relation(
              new Binpacking(item, load, w, 0, rnd.nextBoolean(), card),
              t -> {
                int[] sum = new int[bins];
                int[] count = new int[bins];
                for (int k = 0; k < n; k++) {
                  int i = t[at[k]];
                  sum[i] += w[k];
                  count[i]++;
                }
                for (int i = 0; i < bins; i++) {
                  if (!load[i].domain.contains(sum[i]) || !card[i].domain.contains(count[i])) {
                    return false;
                  }
                }
                return true;
              }));
      if (x.length >= 3 && rnd.nextInt(3) == 0) {
        relations.add(relation(x, rnd));
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
      long[] counts = solver.explanationStatistics().get("Binpacking");
      if (counts != null) {
        own += counts[0] - counts[1] + counts[3] - counts[4];
        generic += counts[1] + counts[4];
      }
    }
    System.out.printf(
        "binpacking with cardinality: %d sat, %d unsat, %d own and %d generic explanations%n",
        sat, unsat, own, generic);
    assertThat(sat).isGreaterThan(50);
    assertThat(unsat).isGreaterThan(50);
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
    // about 800 since reasons cite the earliest bound beyond a value (shorter searches)
    assertThat(own).isGreaterThan(500);
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

  /**
   * {@link Increasing}, {@link Among}, {@link OverlappingAlldiff} and {@link Values} explain their
   * own pruning: the answers agree with brute force, every reason is checked, and almost none is
   * generic or replayed.
   */
  @Test
  void increasingAmongAndOverlappingAlldiffExplanationsAgreeWithBruteForce() {
    Random rnd = new Random(61);
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long other = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 6;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      boolean strict = rnd.nextBoolean();
      List<Relation> relations = new ArrayList<>();
      switch (rnd.nextInt(4)) {
        case 3 ->
            relations.add(
                new Relation(
                    new Values(new IntVar[] {x[0], x[1], x[2], x[3]}, x[4]),
                    t -> Arrays.stream(t, 0, 4).distinct().count() == t[4]));
        case 0 ->
            relations.add(
                new Relation(
                    new Increasing(new IntVar[] {x[0], x[1], x[2], x[3]}, strict),
                    t ->
                        strict
                            ? t[0] < t[1] && t[1] < t[2] && t[2] < t[3]
                            : t[0] <= t[1] && t[1] <= t[2] && t[2] <= t[3]));
        case 1 -> {
          IntervalDomain k = new IntervalDomain(0, 1);
          k.unionAdapt(3, 3);
          relations.add(
              new Relation(
                  new Among(new IntVar[] {x[0], x[1], x[2], x[3]}, k, x[4]),
                  t -> {
                    int c = 0;
                    for (int i = 0; i < 4; i++) {
                      c += k.contains(t[i]) ? 1 : 0;
                    }
                    return c == t[4];
                  }));
        }
        default -> {
          IntVar[] s1 = {x[0], x[1], x[2], x[3]};
          IntVar[] s2 = {x[1], x[2], x[3], x[4]};
          relations.add(
              new Relation(
                  new OverlappingAlldiff(s1, s2),
                  t -> distinct(t, 0, 1, 2, 3) && distinct(t, 1, 2, 3, 4)));
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
      for (String name : new String[] {"Increasing", "Among", "OverlappingAlldiff", "Values"}) {
        long[] counts = solver.explanationStatistics().get(name);
        if (counts != null) {
          long notOwn = counts[1] + counts[4] + counts[6] + counts[7];
          own += counts[0] + counts[3] - notOwn;
          other += notOwn;
        }
      }
    }
    System.out.printf(
        "increasing, among, overlapping alldiff and values: %d sat, %d unsat, %d own and %d generic or"
            + " replayed explanations%n",
        sat, unsat, own, other);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(own).isGreaterThan(10 * other);
  }

  private static boolean distinct(int[] t, int... at) {
    for (int a = 0; a < at.length; a++) {
      for (int b = a + 1; b < at.length; b++) {
        if (t[at[a]] == t[at[b]]) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * Permutations over the terms of the objective's sum become clauses too (sudoku_opt of the
   * MiniZinc Challenge 2022): on a 3x3 Latin square minimising a signed sum of its cells, split
   * into two blocks as the FlatZinc front end splits long sums, all six rows and columns become
   * clauses and the optimum is the one of brute force.
   */
  @Test
  void permutationsOverObjectiveTermsBecomeClauses() {
    int n = 3;
    Store store = new Store();
    IntVar[] x = new IntVar[n * n];
    int[] sign = new int[n * n];
    for (int k = 0; k < x.length; k++) {
      x[k] = new IntVar(store, "x" + k, 1, n);
      sign[k] = (k / n + k % n) % 2 == 0 ? 1 : -1;
    }
    for (int i = 0; i < n; i++) {
      IntVar[] row = new IntVar[n];
      IntVar[] col = new IntVar[n];
      for (int j = 0; j < n; j++) {
        row[j] = x[i * n + j];
        col[j] = x[j * n + i];
      }
      store.impose(new Alldistinct(row));
      store.impose(new Alldistinct(col));
    }
    // b1 = the signed first row, b2 = the signed rest, obj = b1 + b2
    IntVar b1 = new IntVar(store, "b1", -n * n, n * n);
    IntVar b2 = new IntVar(store, "b2", -n * n * n, n * n * n);
    IntVar obj = new IntVar(store, "obj", -n * n * n, n * n * n);
    IntVar[] first = new IntVar[n + 1];
    int[] w1 = new int[n + 1];
    IntVar[] rest = new IntVar[n * n - n + 1];
    int[] w2 = new int[n * n - n + 1];
    for (int k = 0; k < n * n; k++) {
      if (k < n) {
        first[k] = x[k];
        w1[k] = sign[k];
      } else {
        rest[k - n] = x[k];
        w2[k - n] = sign[k];
      }
    }
    first[n] = b1;
    w1[n] = -1;
    rest[n * n - n] = b2;
    w2[n * n - n] = -1;
    store.impose(new LinearInt(first, w1, "==", 0));
    store.impose(new LinearInt(rest, w2, "==", 0));
    store.impose(new LinearInt(new IntVar[] {b1, b2, obj}, new int[] {1, 1, -1}, "==", 0));
    // brute force over all assignments of the cells
    int best = Integer.MAX_VALUE;
    int[] t = new int[n * n];
    for (int code = 0; code < Math.pow(n, n * n); code++) {
      int c = code;
      for (int k = 0; k < t.length; k++) {
        t[k] = 1 + c % n;
        c /= n;
      }
      if (latin(t, n)) {
        int sum = 0;
        for (int k = 0; k < t.length; k++) {
          sum += sign[k] * t[k];
        }
        best = Math.min(best, sum);
      }
    }
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    solver.setAnnotation(new SimpleSelect<>(x, null, new IndomainMin<>()), true);
    assertThat(solver.minimize(obj)).isEqualTo(CdclSolver.SAT);
    assertThat(solver.value(obj)).isEqualTo(best);
    assertThat(solver.permutationsAsClauses).isEqualTo(2L * n);
  }

  private static boolean latin(int[] t, int n) {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        for (int k = j + 1; k < n; k++) {
          if (t[i * n + j] == t[i * n + k] || t[j * n + i] == t[k * n + i]) {
            return false;
          }
        }
      }
    }
    return true;
  }

  /**
   * An all different over as many values as variables gets the clauses that each value is taken,
   * and the answers still agree with brute force.
   */
  @Test
  void permutationAlldiffGetsCoverClauses() {
    Random rnd = new Random(67);
    int sat = 0;
    int unsat = 0;
    long clauses = 0;
    for (int instance = 0; instance < 600; instance++) {
      Store store = new Store();
      int n = 5;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, n - 1);
        if (rnd.nextInt(3) == 0) {
          x[i].domain.subtractAdapt(rnd.nextInt(n));
          x[i].refreshBounds();
        }
      }
      List<Relation> relations = new ArrayList<>();
      Constraint alldiff =
          switch (rnd.nextInt(3)) {
            case 0 -> new Alldiff(x);
            case 1 -> new Alldistinct(x);
            default -> new Alldifferent(x);
          };
      relations.add(new Relation(alldiff, t -> distinct(t, 0, 1, 2, 3, 4)));
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
      clauses += solver.impliedClauses;
    }
    System.out.printf("cover clauses: %d sat, %d unsat, %d clauses%n", sat, unsat, clauses);
    assertThat(sat).isGreaterThan(50);
    assertThat(unsat).isGreaterThan(50);
    assertThat(clauses).isGreaterThan(600);
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
    layeredGraphsAgreeWithBruteForce(false);
  }

  /**
   * The same models with every graph explained as a large one: the far cuts found from the reached
   * nodes or the nodes reaching the last level, and failures from the labels of each node, give the
   * same reasons as the walks (the same number of atoms).
   */
  @Test
  void layeredGraphCutsOfLargeGraphsAreTheWalkedOnes() {
    System.setProperty("jacop.lcg.graphCutsLargeNodes", "0");
    try {
      layeredGraphsAgreeWithBruteForce(false);
    } finally {
      System.clearProperty("jacop.lcg.graphCutsLargeNodes");
    }
  }

  /**
   * Regular (some automata nondeterministic) and decision diagrams given to the solver as clauses
   * against brute force: no explanation is left to the constraints, which are out of the store.
   */
  @Test
  void layeredGraphClausesAgreeWithBruteForce() {
    layeredGraphsAgreeWithBruteForce(true);
  }

  /**
   * Free search of a 0/1 model whose regular constraints all become clauses leaves the decisions to
   * the SAT solver, and still agrees with brute force; with one variable of three values, or with a
   * constraint left in the store, it keeps its own branching.
   */
  @Test
  void pureClauseModelsLeaveDecisionsToTheSatSolver() {
    Random rnd = new Random(53);
    int pure = 0;
    int kept = 0;
    int sat = 0;
    int unsat = 0;
    for (int instance = 0; instance < 600; instance++) {
      int kind = instance % 3; // 0: pure 0/1, 1: one variable 0..2, 2: a constraint left
      Store store = new Store();
      int n = 6;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, kind == 1 && i == 0 ? 2 : 1);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 1 + rnd.nextInt(2); c > 0; c--) {
        relations.add(regularRelation(x, rnd));
      }
      if (kind == 2) {
        relations.add(new Relation(new XneqY(x[0], x[1]), t -> t[0] != t[1]));
      }
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      // the root propagation builds the graphs, as the FlatZinc front end does before solving; it
      // may take value 2 from x0, which makes the model 0/1
      if (!store.consistency()) {
        assertThat(expected).as("instance %d", instance).isFalse();
        unsat++;
        continue;
      }
      boolean wide = kind == 1 && x[0].getSize() > 2;
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.setGraphClauses(true);
      solver.setBranching(LcgSolver.Branching.ALTERNATE);
      solver.setAnnotation(new SimpleSelect<>(x, null, new IndomainMin<>()), true);
      int status = solver.solve();
      assertThat(status)
          .as("instance %d", instance)
          .isEqualTo(expected ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (kind == 2 || wide) {
        assertThat(solver.pureClauses).as("instance %d", instance).isFalse();
        kept++;
      } else if (solver.pureClauses) {
        pure++;
      } else if (expected) {
        System.out.println(
            "DBG "
                + kind
                + " enc="
                + solver.graphConstraintsEncoded
                + " left="
                + store.getConstraints());
      }
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
    System.out.printf("pure clauses: %d pure, %d kept, %d sat, %d unsat%n", pure, kept, sat, unsat);
    assertThat(pure).isGreaterThan(100);
    assertThat(kept).isGreaterThan(80);
    assertThat(sat).isGreaterThan(50);
    assertThat(unsat).isGreaterThan(50);
  }

  private static void layeredGraphsAgreeWithBruteForce(boolean clauses) {
    Random rnd = new Random(clauses ? 41 : 31);
    long encoded = 0;
    int sat = 0;
    int unsat = 0;
    long own = 0;
    long generic = 0;
    long atoms = 0;
    for (int instance = 0; instance < 1500; instance++) {
      Store store = new Store();
      int n = 5;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = newVar(store, "x" + i, rnd);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 1 + rnd.nextInt(2); c > 0; c--) {
        relations.add(
            rnd.nextBoolean()
                ? clauses && rnd.nextBoolean() ? nfaRelation(x, rnd) : regularRelation(x, rnd)
                : mddRelation(x, rnd));
      }
      relations.add(relation(x, rnd));
      boolean expected = bruteForce(x, relations, new int[n], 0);
      for (Relation r : relations) {
        store.impose(r.constraint);
      }
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.setGraphClauses(clauses);
      int status = solver.solve();
      encoded += solver.graphConstraintsEncoded;
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
          atoms += counts[2] + counts[5];
        }
      }
    }
    System.out.printf(
        "layered graphs%s: %d sat, %d unsat, %d own and %d generic explanations, %d atoms%n",
        clauses ? " as clauses" : "", sat, unsat, own, generic, atoms);
    assertThat(sat).isGreaterThan(100);
    assertThat(unsat).isGreaterThan(100);
    assertThat(generic).isZero();
    if (clauses) {
      assertThat(encoded).isGreaterThan(1500);
      assertThat(own).isZero();
    } else {
      assertThat(own).isGreaterThan(300);
      // the cuts are found by one walk each way since the cut explanation of WordDesign2-words-mdd
      // (XCSP 2023) was made faster; the atoms are those of the four walks per cut before it
      assertThat(atoms).isEqualTo(751);
    }
  }

  /**
   * A nondeterministic automaton of three states over 3 or 4 variables: a value leads from a state
   * to none, one or two states.
   */
  private static Relation nfaRelation(IntVar[] x, Random rnd) {
    int[] at = new int[3 + rnd.nextInt(2)];
    for (int k = 0; k < at.length; k++) {
      at[k] = pick(rnd, x.length, Arrays.copyOf(at, k));
    }
    int states = 3;
    // next[s][v + 1] holds bit t when reading v in state s may lead to state t
    int[][] next = new int[states][7];
    boolean[] accepting = new boolean[states];
    FsmState[] state = new FsmState[states];
    Fsm fsm = new Fsm();
    for (int s = 0; s < states; s++) {
      state[s] = new FsmState();
      fsm.allStates.add(state[s]);
    }
    fsm.initState = state[0];
    for (int s = 0; s < states; s++) {
      accepting[s] = rnd.nextInt(3) > 0;
      if (accepting[s]) {
        fsm.finalStates.add(state[s]);
      }
      for (int v = -1; v <= 5; v++) {
        for (int k = rnd.nextInt(3); k > 0; k--) {
          int t = rnd.nextInt(states);
          if ((next[s][v + 1] & 1 << t) == 0) {
            next[s][v + 1] |= 1 << t;
            state[s].addTransition(new FsmTransition(new IntervalDomain(v, v), state[t]));
          }
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
          int current = 1;
          for (int k : at) {
            int reached = 0;
            for (int s = 0; s < states; s++) {
              if ((current & 1 << s) != 0) {
                reached |= next[s][t[k] + 1];
              }
            }
            current = reached;
          }
          for (int s = 0; s < states; s++) {
            if ((current & 1 << s) != 0 && accepting[s]) {
              return true;
            }
          }
          return false;
        });
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

  /**
   * Closed global cardinalities with fixed counts over variables of at most four values become
   * clauses before search ({@code jacop.lcg.gccClauses}); the answers must match brute force.
   */
  @Test
  void smallDomainGccAsClausesAgreesWithBruteForce() {
    Random rnd = new Random(53);
    int sat = 0;
    int unsat = 0;
    long encoded = 0;
    for (int instance = 0; instance < 400; instance++) {
      Store store = new Store();
      int n = 5 + rnd.nextInt(3);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, rnd.nextInt(4) == 0 ? 1 : 0, 3);
      }
      List<Relation> relations = new ArrayList<>();
      for (int c = 1 + rnd.nextInt(2); c > 0; c--) {
        int[] at = new int[3 + rnd.nextInt(n - 2)];
        for (int k = 0; k < at.length; k++) {
          at[k] = pick(rnd, n, Arrays.copyOf(at, k));
        }
        IntVar[] q = new IntVar[at.length];
        for (int k = 0; k < at.length; k++) {
          q[k] = x[at[k]];
        }
        // mostly closed GCCs (the counts add up to the list), which become clauses
        int[] values = {0, 1, 2, 3};
        int[] lb = new int[values.length];
        for (int k = 0; k < at.length; k++) {
          lb[rnd.nextInt(values.length)]++;
        }
        int[] ub = lb.clone();
        if (rnd.nextInt(4) == 0) {
          ub[rnd.nextInt(values.length)]++;
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
      encoded += solver.gccsAsClauses;
    }
    assertThat(sat).isGreaterThan(40);
    assertThat(unsat).isGreaterThan(40);
    assertThat(encoded).isGreaterThan(100);
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
   * A propagator that joins the search at the root once the search has started, as the linear
   * relaxation does after its probe (org.jacop.fz.lpProbe), can fail there on the root domains
   * while the solver has assigned nothing: miplib2003 disctom (PB 2025) threw "the constraints
   * failed on the root domains", since the conflict clause was empty and no assigned literal was
   * left to stand in for it. The empty clause now goes to the solver, which answers UNSAT.
   */
  @Test
  void failureResumedAtTheRootWithNothingAssignedProvesUnsatisfiable() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 10);
    IntVar y = new IntVar(store, "y", 0, 10);
    store.impose(new XplusYeqZ(x, y, new IntVar(store, "z", 0, 20)));
    Constraint gate = new FailsOnceOpened(x, y);
    store.impose(gate);
    LcgSolver solver = new LcgSolver(store);
    solver.atRootAfter(
        0,
        () -> {
          ((FailsOnceOpened) gate).open = true;
          store.addChanged(gate);
        });
    int result = assertTimeoutPreemptively(Duration.ofSeconds(10), () -> solver.solve());
    assertThat(result).isEqualTo(CdclSolver.UNSAT);
  }

  // a constraint without pruning until opened, then failing whatever the domains
  private static final class FailsOnceOpened extends Constraint {
    private static final AtomicInteger ID = new AtomicInteger();
    boolean open;

    FailsOnceOpened(IntVar... vars) {
      super(new IntVar[][] {vars});
      numberId = ID.incrementAndGet();
    }

    @Override
    public void consistency(Store store) {
      if (open) {
        throw Store.failException;
      }
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

  /**
   * A variable gets a literal map of a kind only with its first literal of that kind: three maps
   * for every variable from the start took 210 MB of XCSP 2022 RoomMate-sr0700, most of them never
   * used. The maps before the search are the one shared empty map, which answers like an empty map
   * of its own, and the solver still solves.
   */
  @Test
  void literalMapsAreMadeAtTheFirstLiteral() throws ReflectiveOperationException {
    Store store = new Store();
    int n = 50;
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 9);
    }
    store.impose(new LinearInt(new IntVar[] {x[0], x[1]}, new int[] {1, 1}, "==", 9));
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    Set<LiteralMap> before = Collections.newSetFromMap(new java.util.IdentityHashMap<>());
    for (String kind : new String[] {"ge", "eq", "linked"}) {
      java.lang.reflect.Field field = LcgSolver.class.getDeclaredField(kind);
      field.setAccessible(true);
      for (LiteralMap map : (LiteralMap[]) field.get(solver)) {
        if (map != null) {
          before.add(map);
        }
      }
    }
    assertThat(before).containsExactly(LiteralMap.NO_LITERALS);
    assertThat(LiteralMap.NO_LITERALS.get(0)).isEqualTo(LiteralMap.NONE);
    assertThat(LiteralMap.NO_LITERALS.lower(5)).isEqualTo(LiteralMap.NONE);
    assertThat(LiteralMap.NO_LITERALS.higher(-5)).isEqualTo(LiteralMap.NONE);
    assertThat(LiteralMap.NO_LITERALS.ceilingValue(-5)).isEqualTo(Long.MAX_VALUE);
    assertThat(LiteralMap.NO_LITERALS.floorValue(5)).isEqualTo(Long.MIN_VALUE);
    assertThat(solver.solve()).isEqualTo(CdclSolver.SAT);
    assertThat(solver.value(x[0]) + solver.value(x[1])).isEqualTo(9);
    assertThat(LiteralMap.NO_LITERALS.get(0)).isEqualTo(LiteralMap.NONE);
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
  /**
   * Cumulatives over two machines, with upper or lower bounds, negative heights and optional tasks:
   * LCG with the explanation checker on finds the same least sum of starts as depth-first search.
   * Without optional tasks its reasons are all its own.
   */
  @Test
  void cumulativesAgreeWithSearch() {
    Random rnd = new Random(17);
    long own = 0;
    for (int instance = 0; instance < 40; instance++) {
      int n = 4 + rnd.nextInt(3);
      boolean upper = rnd.nextBoolean();
      boolean optional = rnd.nextInt(3) == 0;
      int[] d = new int[n];
      int[] r = new int[n];
      for (int i = 0; i < n; i++) {
        d[i] = 1 + rnd.nextInt(3);
        r[i] = rnd.nextInt(5) - (upper ? 1 : 2);
      }
      int[] bound = {rnd.nextInt(3) - (upper ? 0 : 1), rnd.nextInt(3) - (upper ? 0 : 1)};
      Integer[] optimum = new Integer[2];
      for (int mode = 0; mode < 2; mode++) {
        Store store = new Store();
        IntVar[] s = new IntVar[n];
        IntVar[] m = new IntVar[n];
        IntVar[] p = optional ? new IntVar[n] : null;
        IntVar[] dur = new IntVar[n];
        IntVar[] res = new IntVar[n];
        for (int i = 0; i < n; i++) {
          s[i] = new IntVar(store, "s" + i, 0, 6);
          m[i] = new IntVar(store, "m" + i, 1, 2);
          dur[i] = new IntVar(store, d[i], d[i]);
          res[i] = new IntVar(store, r[i], r[i]);
          if (optional) {
            p[i] = new IntVar(store, "p" + i, i == 0 ? 1 : 0, 1);
          }
        }
        IntVar[] b = {new IntVar(store, bound[0], bound[0]), new IntVar(store, bound[1], bound[1])};
        store.impose(new Cumulatives(s, dur, res, m, b, upper, 1, p));
        IntVar cost = new IntVar(store, "cost", 0, 6 * n);
        store.impose(new SumInt(s, "==", cost));
        IntVar[] all = optional ? concat(concat(m, p), s) : concat(m, s);
        if (mode == 0) {
          DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
          search.setPrintInfo(false);
          if (search.labeling(store, new SimpleSelect<>(all, null, new IndomainMin<>()), cost)) {
            optimum[0] = search.getCostValue();
          }
        } else {
          LcgSolver solver = new LcgSolver(store);
          solver.setChecking(true);
          if (solver.minimize(cost) == CdclSolver.SAT) {
            optimum[1] = solver.value(cost);
          }
          long[] stats = solver.explanationStatistics().get("Cumulatives");
          if (stats != null) {
            // only an optional task that no machine can take is set absent by the generic reason
            if (!optional) {
              assertThat(stats[1] + stats[4]).as("instance %d generic", instance).isZero();
            }
            own += stats[0];
          }
        }
      }
      assertThat(optimum[1]).as("instance %d", instance).isEqualTo(optimum[0]);
    }
    assertThat(own).isPositive();
  }

  private static IntVar[] concat(IntVar[] a, IntVar[] b) {
    IntVar[] c = Arrays.copyOf(a, a.length + b.length);
    System.arraycopy(b, 0, c, a.length, b.length);
    return c;
  }

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

  /**
   * Neighbourhood runs pause while the best solution stops improving ({@link
   * LcgSolver#setLnsStall}), so that the time goes to the proof, and the optimum is still found and
   * proved. Under free search they took more than half of the time after the optimum on
   * java-routing trip_8_3 and fox-geese-corn 17 (MiniZinc Challenge), whose proofs then did not
   * come in 600 s.
   */
  @Test
  void lnsStallPausesNeighbourhoodRuns() {
    Random rnd = new Random(31);
    long runsPaused = 0;
    long runsAlways = 0;
    long skips = 0;
    for (int k = 0; k < 30; k++) {
      int n = 6;
      int[][] neq = new int[n * n][];
      int edges = 0;
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          if (rnd.nextInt(3) == 0) {
            neq[edges++] = new int[] {i, j};
          }
        }
      }
      int[] w = new int[n + 1];
      for (int i = 0; i < n; i++) {
        w[i] = rnd.nextInt(11) - 3;
      }
      w[n] = -1;
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
        for (int e = 0; e < edges; e++) {
          ok &= v[neq[e][0]] != v[neq[e][1]];
        }
        if (ok) {
          best = Math.min(best, sum);
        }
      }
      for (boolean pause : new boolean[] {false, true}) {
        Store store = new Store();
        IntVar[] x = new IntVar[n];
        for (int i = 0; i < n; i++) {
          x[i] = new IntVar(store, "x" + i, 0, 5);
        }
        for (int e = 0; e < edges; e++) {
          store.impose(new XneqY(x[neq[e][0]], x[neq[e][1]]));
        }
        IntVar cost = new IntVar(store, "cost", -1000, 1000);
        IntVar[] terms = Arrays.copyOf(x, n + 1);
        terms[n] = cost;
        store.impose(new LinearInt(terms, w, "==", 0));
        LcgSolver solver = new LcgSolver(store);
        solver.setChecking(true);
        solver.setLowerBoundSearch(0.5, 2);
        solver.setLns(new AdaptiveLns(store, x, cost, new Random(k)), 4.0, 2);
        // a pause as soon as any time passes without a better solution
        solver.setLnsStall(pause ? 1e-9 : 0, 0);
        assertThat(solver.minimize(cost)).isEqualTo(CdclSolver.SAT);
        assertThat(solver.value(cost)).isEqualTo(best);
        if (pause) {
          runsPaused += solver.lnsRuns;
          skips += solver.lnsStallSkips;
        } else {
          runsAlways += solver.lnsRuns;
          assertThat(solver.lnsStallSkips).isZero();
        }
      }
    }
    assertThat(skips).isPositive();
    assertThat(runsPaused).isLessThan(runsAlways);
  }

  /**
   * A stop during the runs in large neighbourhoods ends them: the runs that follow return at once
   * without a conflict and must not count as neighbourhoods too large. The slow-LCG hand-over of
   * free search stopped LCG in its runs on MaximumAgreementForest2-exact12 (XCSP 2026), which went
   * on for the rest of their share of the time: 7,000 runs shrank every neighbourhood to 2
   * variables.
   */
  @Test
  void stopEndsLargeNeighbourhoodRuns() {
    Random rnd = new Random(29);
    int stopped = 0;
    for (int k = 0; k < 60; k++) {
      Store store = new Store();
      int n = 8;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 5);
      }
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          if (rnd.nextInt(3) == 0) {
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
      LcgSolver solver = new LcgSolver(store);
      solver.setLowerBoundSearch(0.5, 2);
      AdaptiveLns lns = new AdaptiveLns(store, x, cost, new Random(k));
      solver.setLns(lns, 1000.0, 2);
      long[] runsAtStop = {-1};
      // the first better solution found in a neighbourhood stops the search
      solver.onSolution(
          () -> {
            if (solver.lnsRuns > 0 && runsAtStop[0] < 0) {
              runsAtStop[0] = solver.lnsRuns;
              solver.stop();
            }
          });
      String shares = lns.statistics();
      int result = solver.minimize(cost);
      if (runsAtStop[0] < 0) {
        continue;
      }
      stopped++;
      assertThat(result).isNotEqualTo(CdclSolver.UNSAT);
      // at most the run that the stop came in
      assertThat(solver.lnsRuns).isEqualTo(runsAtStop[0]);
      assertThat(lns.statistics()).doesNotContain("0.000");
      assertThat(shares).doesNotContain("0.000");
    }
    assertThat(stopped).isPositive();
  }

  /**
   * A solver that adds constraints to the shared model (symmetry breaking) reads the clauses of
   * solvers that added none or the same ones; its own reach only the latter.
   */
  @Test
  void sharedClausesStayWithinTheirModel() {
    SharedClauses pool = new SharedClauses();
    int plain = pool.newSource("");
    int plain2 = pool.newSource("");
    int lex = pool.newSource("lex[a,b,]");
    int lex2 = pool.newSource("lex[a,b,]");
    int other = pool.newSource("lex[b,a,]");
    for (int source : new int[] {plain, plain2, lex, lex2, other}) {
      pool.publish(List.of(new int[] {source, 1, pool.id("a"), SharedClauses.GE, 1}));
    }
    assertThat(sources(pool, plain)).containsExactly(plain2);
    assertThat(sources(pool, lex)).containsExactly(plain, plain2, lex2);
    assertThat(sources(pool, other)).containsExactly(plain, plain2);
  }

  private static List<Integer> sources(SharedClauses pool, int reader) {
    List<int[]> in = new ArrayList<>();
    assertThat(pool.read(0, reader, in)).isEqualTo(pool.size());
    return in.stream().map(c -> c[0]).toList();
  }

  /**
   * A solver of makespan problems stops after a few conflicts; a second one, of the same problem in
   * its own store, takes its learnt clauses (of any size and LBD, to share many), its root bounds
   * and its best cost as the bound, as portfolio threads do. Neither finds a solution better than
   * the optimum of depth-first search, and the better of their solutions is optimal.
   */
  @Test
  void sharedClausesKeepTheOptimum() {
    Random rnd = new Random(31);
    long imported = 0;
    for (int instance = 0; instance < SCHEDULING_INSTANCES / 4; instance++) {
      int n = 6 + rnd.nextInt(3);
      int[] d = new int[n];
      int[] r = new int[n];
      for (int i = 0; i < n; i++) {
        d[i] = 1 + rnd.nextInt(4);
        r[i] = 1 + rnd.nextInt(3);
      }
      int limit = 3 + rnd.nextInt(2);
      IntVar[][] starts = new IntVar[3][];
      IntVar[] makespans = new IntVar[3];
      Store[] stores = new Store[3];
      for (int k = 0; k < 3; k++) {
        stores[k] = new Store();
        starts[k] = new IntVar[n];
        IntVar[] durations = new IntVar[n];
        IntVar[] resources = new IntVar[n];
        IntVar[] ends = new IntVar[n];
        for (int i = 0; i < n; i++) {
          starts[k][i] = new IntVar(stores[k], "s" + i, 0, 20 - d[i]);
          ends[i] = new IntVar(stores[k], "e" + i, d[i], 20);
          stores[k].impose(new XplusCeqZ(starts[k][i], d[i], ends[i]));
          durations[i] = new IntVar(stores[k], d[i], d[i]);
          resources[i] = new IntVar(stores[k], r[i], r[i]);
        }
        makespans[k] = new IntVar(stores[k], "makespan", 0, 20);
        stores[k].impose(new Max(ends, makespans[k]));
        stores[k].impose(
            new Cumulative(starts[k], durations, resources, new IntVar(stores[k], limit, limit)));
      }
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      assertThat(
              search.labeling(
                  stores[0],
                  new SimpleSelect<>(starts[0], null, new IndomainMin<>()),
                  makespans[0]))
          .isTrue();
      int optimum = search.getCostValue();

      // the first solver stops after a few conflicts, the second takes its clauses and its best
      // solution's cost as the bound, as a portfolio thread does from another one
      SharedClauses pool = new SharedClauses();
      AtomicInteger bound = new AtomicInteger(Integer.MAX_VALUE);
      int[] found = {Integer.MAX_VALUE, Integer.MAX_VALUE, Integer.MAX_VALUE};
      int[] results = new int[3];
      for (int k = 1; k < 3; k++) {
        int w = k;
        LcgSolver solver = new LcgSolver(stores[k]);
        solver.setChecking(true);
        solver.setSharedClauses(pool, "", IntVar::id, 64, 64);
        solver.setSharedBound(bound::get);
        solver.onSolution(
            () -> {
              int cost = makespans[w].value();
              found[w] = Math.min(found[w], cost);
              bound.accumulateAndGet(cost, Math::min);
            });
        if (k == 1) {
          solver.sat().setConflictLimit(5 + rnd.nextInt(60));
        }
        results[k] = solver.minimize(makespans[k]);
        if (k == 2) {
          imported += solver.clausesImported;
        }
      }
      for (int k = 1; k < 3; k++) {
        assertThat(found[k])
            .as("instance %d, solver %d", instance, k)
            .isGreaterThanOrEqualTo(optimum);
      }
      // the second solver ends its search: the better of the two solutions is optimal
      assertThat(results[2]).as("instance %d", instance).isNotEqualTo(CdclSolver.UNKNOWN);
      assertThat(bound.get()).as("instance %d", instance).isEqualTo(optimum);
    }
    assertThat(imported).isPositive();
  }

  /**
   * Core-guided search proves the same optima with and without trimming its cores, and trimming
   * takes literals out of some of them.
   */
  @Test
  void trimmedCoresKeepTheOptimum() {
    Random rnd = new Random(23);
    long shrunk = 0;
    long untrimmed = 0;
    for (int instance = 0; instance < 300; instance++) {
      long seed = rnd.nextLong();
      Integer expected = coreModelOptimum(seed, -1, new long[3]);
      long[] trimmed = new long[6];
      assertThat(coreModelOptimum(seed, 0, trimmed))
          .as("instance %d (seed %d), trimmed", instance, seed)
          .isEqualTo(expected);
      long[] plain = new long[6];
      assertThat(coreModelOptimum(seed, 4, plain))
          .as("instance %d (seed %d), untrimmed", instance, seed)
          .isEqualTo(expected);
      shrunk += trimmed[5];
      untrimmed += plain[5];
    }
    assertThat(shrunk).isPositive();
    assertThat(untrimmed).isZero();
  }

  /**
   * Core-guided search proves the same optima of random partial MaxSAT models (3-literal hard
   * clauses, every variable a unit-cost soft) with and without core exhaustion, the optima of
   * search, and exhaustion proves totalizer outputs on some of them.
   */
  @Test
  void exhaustedCoresKeepTheOptimum() {
    Random rnd = new Random(29);
    long exhausted = 0;
    for (int instance = 0; instance < 150; instance++) {
      long seed = rnd.nextLong();
      long[] stats = new long[1];
      Integer expected = maxSatOptimum(seed, -1, stats);
      assertThat(maxSatOptimum(seed, 0, stats))
          .as("instance %d (seed %d), without exhaustion", instance, seed)
          .isEqualTo(expected);
      assertThat(stats[0]).isZero();
      assertThat(maxSatOptimum(seed, 1 + instance % 8, stats))
          .as("instance %d (seed %d), exhausted", instance, seed)
          .isEqualTo(expected);
      exhausted += stats[0];
    }
    assertThat(exhausted).isPositive();
  }

  /**
   * With a time limit the phases of the core-guided schedule have work limits: an exhaustion test
   * takes only a share of the work its phase has left, and one that refutes nothing gives its work
   * back. Neither may change the optimum.
   */
  @Test
  void cappedExhaustionKeepsTheOptimum() {
    Random rnd = new Random(37);
    long exhausted = 0;
    for (int instance = 0; instance < 60; instance++) {
      long seed = rnd.nextLong();
      long[] stats = new long[1];
      Integer expected = maxSatOptimum(seed, -1, stats);
      assertThat(maxSatOptimum(seed, DEFAULT_EXHAUST, stats, 1 + instance % 20))
          .as("instance %d (seed %d)", instance, seed)
          .isEqualTo(expected);
      exhausted += stats[0];
    }
    assertThat(exhausted).isPositive();
  }

  private static final int DEFAULT_EXHAUST = Integer.MAX_VALUE;

  /** Core exhaustion is on by default. */
  @Test
  void coresAreExhaustedByDefault() {
    Random rnd = new Random(31);
    long exhausted = 0;
    for (int instance = 0; instance < 40; instance++) {
      long seed = rnd.nextLong();
      long[] stats = new long[1];
      assertThat(maxSatOptimum(seed, DEFAULT_EXHAUST, stats))
          .as("instance %d (seed %d)", instance, seed)
          .isEqualTo(maxSatOptimum(seed, -1, stats));
      exhausted += stats[0];
    }
    assertThat(exhausted).isPositive();
  }

  /**
   * Minimises the number of true variables under random 3-literal clauses: by depth-first search
   * when {@code exhaust} is negative, otherwise by core-guided search with that many outputs
   * exhausted per core ({@link #DEFAULT_EXHAUST}: the solver's defaults); adds the exhausted
   * outputs to {@code stats[0]}.
   */
  private static Integer maxSatOptimum(long seed, int exhaust, long[] stats) {
    return maxSatOptimum(seed, exhaust, stats, 0);
  }

  /**
   * As {@link #maxSatOptimum(long, int, long[])}, with a time limit in milliseconds for the
   * core-guided schedule (0 = none): its phases then have work limits, which also cap each
   * exhaustion test, and the work of the tests that refute nothing is given back to the phase.
   */
  private static Integer maxSatOptimum(long seed, int exhaust, long[] stats, long timeLimit) {
    Random rnd = new Random(seed);
    Store store = new Store();
    int n = 14 + rnd.nextInt(8);
    IntVar[] x = new IntVar[n + 1];
    int[] w = new int[n + 1];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
      w[i] = 1;
    }
    int m = 2 * n + rnd.nextInt(2 * n);
    for (int k = 0; k < m; k++) {
      int a = rnd.nextInt(n);
      int b = (a + 1 + rnd.nextInt(n - 1)) % n;
      int c = rnd.nextInt(n);
      if (c == a || c == b) {
        continue;
      }
      // x[a] or x[b] or x[c], each literal negative with probability 1/3
      int[] coefficients = new int[3];
      int rhs = 1;
      for (int t = 0; t < 3; t++) {
        coefficients[t] = rnd.nextInt(3) == 0 ? -1 : 1;
        rhs -= coefficients[t] < 0 ? 1 : 0;
      }
      store.impose(new LinearInt(new IntVar[] {x[a], x[b], x[c]}, coefficients, ">=", rhs));
    }
    IntVar cost = new IntVar(store, "cost", 0, n);
    x[n] = cost;
    w[n] = -1;
    store.impose(new LinearInt(x, w, "==", 0));
    if (exhaust < 0) {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      boolean found =
          search.labeling(
              store, new SimpleSelect<>(Arrays.copyOf(x, n), null, new IndomainMin<>()), cost);
      return found ? search.getCostValue() : null;
    }
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    solver.setCoreSearch(1, 1_000_000, 100_000);
    if (exhaust != DEFAULT_EXHAUST) {
      solver.setCoreExhaust(exhaust);
    }
    solver.setTimeLimit(timeLimit);
    int status = solver.minimize(cost);
    assertThat(status).isNotEqualTo(CdclSolver.UNKNOWN);
    if (solver.coreSearch() != null) {
      stats[0] += solver.coreSearch().exhaustedOutputs;
    }
    return status == CdclSolver.SAT ? solver.value(cost) : null;
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
  void reportedLowerBoundsHold() {
    Random rnd = new Random(29);
    int reachedOptimum = 0;
    int checked = 0;
    for (int instance = 0; instance < 200; instance++) {
      long seed = rnd.nextLong();
      Integer optimum = coreModelOptimum(seed, -1, new long[3]);
      if (optimum == null) {
        continue;
      }
      checked++;
      for (int mode = 0; mode < 4; mode++) {
        long[] lower = new long[1];
        coreModelOptimum(seed, mode, new long[3], null, lower);
        assertThat(lower[0])
            .as("instance %d (seed %d), mode %d", instance, seed, mode)
            .isLessThanOrEqualTo(optimum);
        if (mode == 0 && lower[0] == optimum) {
          reachedOptimum++;
        }
        // a bound found elsewhere: no solution below it, so the bound reported may pass it, but
        // the smaller of the two never passes the optimum
        for (int shared : new int[] {optimum, optimum + 1}) {
          coreModelOptimum(seed, mode, new long[3], shared, lower);
          assertThat(Math.min(lower[0], shared))
              .as("instance %d (seed %d), mode %d, shared %d", instance, seed, mode, shared)
              .isLessThanOrEqualTo(optimum);
        }
      }
    }
    assertThat(checked).isPositive();
    // core-guided search raises its bound to the optimum on some instances
    assertThat(reachedOptimum).isPositive();
  }

  @Test
  void coreGuidedSearchStopsAtTheSharedBound() {
    Random rnd = new Random(23);
    int provedElsewhere = 0;
    int checked = 0;
    long[] alone = new long[4];
    long[] withBound = new long[4];
    for (int instance = 0; instance < 200; instance++) {
      long seed = rnd.nextLong();
      Integer optimum = coreModelOptimum(seed, -1, new long[3]);
      if (optimum == null) {
        continue;
      }
      checked++;
      coreModelOptimum(seed, 0, alone);
      // the optimum found elsewhere: the search ends with the proof that nothing is better, with
      // no solution of its own or one that is not better
      Integer found = coreModelOptimum(seed, 0, withBound, optimum);
      if (found == null || found > optimum) {
        provedElsewhere++;
      } else {
        assertThat(found).as("instance %d (seed %d)", instance, seed).isEqualTo(optimum);
      }
      // a worse solution found elsewhere: the optimum is still found here
      assertThat(coreModelOptimum(seed, 0, new long[3], optimum + 1))
          .as("instance %d (seed %d), bound above the optimum", instance, seed)
          .isEqualTo(optimum);
    }
    assertThat(checked).isPositive();
    // the cores stop once their lower bound meets the bound found elsewhere, mostly before they
    // find a solution of their own (55 of 82 instances; 5 when the cores ignore the bound)
    assertThat(provedElsewhere).isGreaterThan(checked / 4);
    assertThat(withBound[3]).isLessThanOrEqualTo(alone[3]);
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
  void coreScheduleUnderATimeLimitRepeats() {
    // under a time limit the probe, branch and bound and core-guided phases took shares of the
    // clock, so the cores found differed between runs (10 against 35 on the same instance); they
    // now take shares of the solver's work, and two runs take the same path
    long[] first = null;
    for (int run = 0; run < 3; run++) {
      Random rnd = new Random(7);
      Store store = new Store();
      int n = 24;
      IntVar[] x = new IntVar[n];
      int[] w = new int[n + 1];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 6);
        w[i] = 1 + rnd.nextInt(9);
      }
      for (int c = 0; c < 12; c++) {
        IntVar[] vs = new IntVar[5];
        int[] ws = new int[5];
        for (int k = 0; k < 5; k++) {
          vs[k] = x[rnd.nextInt(n)];
          ws[k] = 1 + rnd.nextInt(4);
        }
        store.impose(new LinearInt(vs, ws, ">=", 6 + rnd.nextInt(10)));
      }
      IntVar cost = new IntVar(store, "cost", 0, 10_000);
      IntVar[] terms = Arrays.copyOf(x, n + 1);
      terms[n] = cost;
      w[n] = -1;
      store.impose(new LinearInt(terms, w, "==", 0));
      LcgSolver solver = new LcgSolver(store);
      // with the fixpoint's atoms pushed before a conflict, branch and bound proves this instance
      // before the core-guided phase starts (3,186 conflicts, no core), which the test needs
      solver.setPushBeforeConflict(false);
      solver.setCoreSearch(0.5, 100_000, 5_000);
      solver.setTimeLimit(100); // 100 ms of work at the nominal rate
      // a deadline far away: only the work ends the phases
      solver.sat().setDeadline(System.nanoTime() + 3_600_000_000_000L);
      int status = solver.minimize(cost);
      assertThat(status).isNotEqualTo(CdclSolver.UNKNOWN);
      long[] trace = {
        solver.coreSearch().cores, solver.sat().conflicts, solver.value(cost), solver.clockStops
      };
      if (first == null) {
        first = trace;
      } else {
        assertThat(trace).containsExactly(first);
      }
    }
    assertThat(first[0]).isPositive();
    assertThat(first[3]).isZero();
  }

  @Test
  void heavySoftConflictsFormAtMostOneGroupsOnceHardened() {
    // a weighted MaxSAT independent set as frb_wt of the MaxSAT Evaluation: unit soft clauses of
    // weight 1 select vertices, and soft conflict clauses of a weight above all units together
    // forbid pairs, the groups' cliques among them. The conflicts become hard only once a solution
    // is known; the at-most-one groups are then looked for again, and the groups give the bound
    // without a core (there were one core per unit of the bound before)
    Random rnd = new Random(11);
    long proved = 0;
    for (int instance = 0; instance < 30; instance++) {
      long seed = rnd.nextLong();
      Integer expected = independentSetOptimum(seed, false, new long[3]);
      long[] stats = new long[3];
      Integer found = independentSetOptimum(seed, true, stats);
      assertThat(found).as("instance %d (seed %d)", instance, seed).isEqualTo(expected);
      assertThat(stats[0]).as("groups of instance %d", instance).isPositive();
      assertThat(stats[1]).as("regroups of instance %d", instance).isEqualTo(1);
      proved += stats[2];
    }
    assertThat(proved).isEqualTo(30);
  }

  /**
   * Minimises the units left out of a random independent set with soft conflicts, by depth-first
   * search or by LCG with core-guided search alone; stats gets the at-most-one groups, the regroups
   * and whether core-guided search proved the optimum.
   */
  private static Integer independentSetOptimum(long seed, boolean lcg, long[] stats) {
    Random rnd = new Random(seed);
    Store store = new Store();
    int groups = 3 + rnd.nextInt(3);
    int size = 3 + rnd.nextInt(2);
    int n = groups * size;
    int heavy = n + 1;
    IntVar[] v = new IntVar[n];
    List<IntVar> relax = new ArrayList<>();
    List<Integer> weight = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      v[i] = new IntVar(store, "v" + i, 0, 1);
      IntVar r = new IntVar(store, "u" + i, 0, 1);
      store.impose(new LinearInt(new IntVar[] {v[i], r}, new int[] {1, 1}, ">=", 1));
      relax.add(r);
      weight.add(1);
    }
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        boolean sameGroup = i / size == j / size;
        if (sameGroup || rnd.nextInt(4) == 0) {
          IntVar r = new IntVar(store, "c" + i + "_" + j, 0, 1);
          store.impose(new LinearInt(new IntVar[] {v[i], v[j], r}, new int[] {1, 1, -1}, "<=", 1));
          relax.add(r);
          weight.add(heavy);
        }
      }
    }
    int m = relax.size();
    IntVar cost = new IntVar(store, "cost", 0, n + heavy * (m - n));
    IntVar[] terms = relax.toArray(new IntVar[m + 1]);
    terms[m] = cost;
    int[] w = new int[m + 1];
    for (int k = 0; k < m; k++) {
      w[k] = weight.get(k);
    }
    w[m] = -1;
    store.impose(new LinearInt(terms, w, "==", 0));
    if (!lcg) {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      IntVar[] all = Arrays.copyOf(v, n + m);
      for (int k = 0; k < m; k++) {
        all[n + k] = relax.get(k);
      }
      boolean found =
          search.labeling(store, new SimpleSelect<>(all, null, new IndomainMin<>()), cost);
      return found ? search.getCostValue() : null;
    }
    LcgSolver solver = new LcgSolver(store);
    solver.setChecking(true);
    solver.setCoreSearch(1, 1_000_000, 100_000);
    int status = solver.minimize(cost);
    assertThat(status).isNotEqualTo(CdclSolver.UNKNOWN);
    stats[0] += solver.coreSearch().amoGroups;
    stats[1] += solver.coreSearch().regroups;
    stats[2] += solver.coreSearch().proved ? 1 : 0;
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

  /**
   * The core-guided phase gives its time to branch and bound when it has no solution of its own
   * after a third of its time, also when branch and bound before it found one. That solution made
   * the test pass before, so the phase always ran its whole share: city-position spent half of its
   * time on cores that raised the bound to 435 against an optimum of 3,493.
   */
  /**
   * A core that the assumptions meet at their first conflict ends the solver's call before it
   * checks its work limit, so the core-guided phase checks the limit itself between cores. Here
   * every core is one clause of three soft literals, all false under the assumptions: the phase
   * used to find all 300 of them, far past its share of the work, and now stops at that share.
   */
  @Test
  void corePhaseStopsAtItsWorkLimitWhenEveryCoreFailsAtOnce() {
    Store store = new Store();
    int n = 300;
    IntVar[] x = new IntVar[3 * n + 1];
    int[] w = new int[3 * n + 1];
    for (int i = 0; i < 3 * n; i++) {
      x[i] = new BooleanVar(store, "x" + i);
      w[i] = 1;
    }
    for (int i = 0; i < n; i++) {
      IntVar[] clause = {x[3 * i], x[3 * i + 1], x[3 * i + 2]};
      store.impose(new LinearInt(clause, new int[] {1, 1, 1}, ">=", 1));
    }
    IntVar cost = new IntVar(store, "cost", 0, 3 * n);
    x[3 * n] = cost;
    w[3 * n] = -1;
    store.impose(new LinearInt(x, w, "==", 0));
    LcgSolver solver = new LcgSolver(store);
    solver.setCoreSearch(0.5, 1_000_000, 100_000_000);
    // 100,000 units of work at the nominal rate: since the exhaustion tests that refute nothing are
    // left out of the phase's work (#837), the cores alone must take more than its share
    solver.setTimeLimit(50);
    // the deadline only ends branch and bound, which does not prove the bound of 300 in time
    solver.sat().setDeadline(System.nanoTime() + 1_000_000_000L);
    solver.minimize(cost);
    assertThat(solver.coreSearch().limitStops).isPositive();
    assertThat(solver.coreSearch().cores).isLessThan(n);
  }

  @Test
  void corePhaseWithoutItsOwnSolutionStopsAfterAThird() {
    // 12 pigeons; hole 0 takes any number of them and costs 1 each, holes 1 to 11 take one each.
    // Branch and bound finds solutions at once (all in hole 0, then fewer), while the first core
    // (no pigeon in hole 0) is a pigeonhole proof over disequalities, too hard for the phase
    Store store = new Store();
    int n = 12;
    IntVar[] p = new IntVar[n];
    BooleanVar[] c = new BooleanVar[n];
    for (int i = 0; i < n; i++) {
      p[i] = new IntVar(store, "p" + i, 0, n - 1);
      c[i] = new BooleanVar(store, "c" + i);
      store.impose(new Reified(new XeqC(p[i], 0), c[i]));
      for (int j = 0; j < i; j++) {
        store.impose(new Or(new XneqY(p[j], p[i]), new XeqC(p[i], 0)));
      }
    }
    IntVar obj = new IntVar(store, "obj", 0, n);
    store.impose(new SumBool(c, "==", obj));
    LcgSolver solver = new LcgSolver(store);
    // the annotation puts every pigeon in hole 0, the activity of the free search does not
    solver.setAnnotation(new SimpleSelect<>(p, null, new IndomainMin<>()), true);
    solver.setCoreSearch(0.5, 1_000_000, 100_000_000);
    solver.setCoreDelay(0.05, 1_000_000, 0);
    solver.sat().setDeadline(System.nanoTime() + 1_000_000_000L);
    solver.minimize(obj);
    assertThat(solver.coreSearch().stratumSolutions).isZero();
    assertThat(solver.coreSearch().noSolutionStops).isEqualTo(1);
  }

  /**
   * Branch and bound that improves the best solution by one at each solution stops after a few
   * solutions for jumps a doubling step below it, which reach the same optimum with fewer
   * solutions; without jumps it walks down one by one.
   */
  @Test
  void jumpsBelowTheBestSolution() {
    long[] found = new long[2];
    for (boolean jump : new boolean[] {false, true}) {
      Store store = new Store();
      IntVar[] x = new IntVar[5];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 30);
      }
      IntVar obj = new IntVar(store, "obj", 0, 150);
      store.impose(new LinearInt(x, new int[] {1, 1, 1, 1, 1}, ">=", 37));
      store.impose(
          new LinearInt(
              new IntVar[] {x[0], x[1], x[2], x[3], x[4], obj},
              new int[] {1, 1, 1, 1, 1, -1},
              "==",
              0));
      LcgSolver solver = new LcgSolver(store);
      solver.setAnnotation(new SimpleSelect<>(x, null, new IndomainMax<>()), true);
      solver.setJumps(jump);
      assertThat(solver.minimize(obj)).isEqualTo(CdclSolver.SAT);
      assertThat(solver.value(obj)).isEqualTo(37);
      assertThat(solver.jumpRuns > 0).isEqualTo(jump);
      found[jump ? 1 : 0] = solver.solutions;
    }
    assertThat(found[1]).isLessThan(found[0] / 2);
  }

  /**
   * When the objective's root bound is above the cores' lower bound, a short search for a solution
   * at that bound runs before the core-guided probe and ends the search with it: on nfc (Challenge
   * 2022) the linear relaxation's bound is the optimum, which the probe delayed by 0.67 % of the
   * time limit.
   */
  @Test
  void solutionAtTheRootBoundBeforeTheCoreProbe() {
    // dive = true runs with the default
    for (boolean dive : new boolean[] {true, false}) {
      Store store = new Store();
      IntVar[] x = new IntVar[4];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 5);
      }
      IntVar obj = new IntVar(store, "obj", 0, 20);
      store.impose(
          new LinearInt(
              new IntVar[] {x[0], x[1], x[2], x[3], obj}, new int[] {1, 1, 1, 1, -1}, "==", 0));
      // the root bound obj >= 7, as from a linear relaxation; the cores start at the terms'
      // minima, 0
      store.impose(new XgteqC(obj, 7));
      LcgSolver solver = new LcgSolver(store);
      solver.setAnnotation(new SimpleSelect<>(x, null, new IndomainMax<>()), true);
      solver.setCoreSearch(0.5, 1_000_000, 100_000_000);
      solver.setCoreDelay(0.05, 1_000_000, 0.02);
      if (!dive) {
        solver.setBoundDive(0);
      }
      solver.setTimeLimit(200);
      solver.sat().setDeadline(System.nanoTime() + 1_000_000_000L);
      assertThat(solver.minimize(obj)).isEqualTo(CdclSolver.SAT);
      assertThat(solver.value(obj)).isEqualTo(7);
      assertThat(solver.boundDives).isEqualTo(dive ? 1 : 0);
      assertThat(solver.boundDiveSolutions).isEqualTo(dive ? 1 : 0);
      // without the search, the probe's cores start from 0 and raise the bound first
      assertThat(solver.coreSearch().lowerBound > 0).isEqualTo(!dive);
    }
  }

  /**
   * When the probe of the core-guided phase stops without a solution of its own and branch and
   * bound after it finds one, the rest of the phase is skipped: it would stop the same way after a
   * third of its time (fast-food, gt-sort and city-position spent minutes on it before branch and
   * bound proved the optimum).
   */
  @Test
  void corePhaseSkippedWhenItsProbeFoundNoSolution() {
    // skip = true runs with the default
    for (boolean skip : new boolean[] {true, false}) {
      // the pigeons of corePhaseWithoutItsOwnSolutionStopsAfterAThird: the first core is too hard
      Store store = new Store();
      int n = 12;
      IntVar[] p = new IntVar[n];
      BooleanVar[] c = new BooleanVar[n];
      for (int i = 0; i < n; i++) {
        p[i] = new IntVar(store, "p" + i, 0, n - 1);
        c[i] = new BooleanVar(store, "c" + i);
        store.impose(new Reified(new XeqC(p[i], 0), c[i]));
        for (int j = 0; j < i; j++) {
          store.impose(new Or(new XneqY(p[j], p[i]), new XeqC(p[i], 0)));
        }
      }
      IntVar obj = new IntVar(store, "obj", 0, n);
      store.impose(new SumBool(c, "==", obj));
      LcgSolver solver = new LcgSolver(store);
      solver.setAnnotation(new SimpleSelect<>(p, null, new IndomainMin<>()), true);
      solver.setCoreSearch(0.5, 1_000_000, 100_000_000);
      solver.setCoreDelay(0.05, 1_000_000, 0.05);
      if (!skip) {
        solver.setCoreProbeSkip(false);
      }
      // shares as work, not as time, so that the probe's share does not depend on the machine
      solver.setTimeLimit(200);
      solver.sat().setDeadline(System.nanoTime() + 1_000_000_000L);
      solver.minimize(obj);
      assertThat(solver.coreSearch().stratumSolutions).isZero();
      assertThat(solver.probeSkips).isEqualTo(skip ? 1 : 0);
      // with the skip, the probe is the only core-guided run that stops without a solution
      assertThat(solver.coreSearch().noSolutionStops).isEqualTo(skip ? 1 : 2);
      assertThat(solver.value(obj)).isEqualTo(1);
    }
  }

  /**
   * 0-1 terms replace the sums of a split objective also when the sums span fewer levels than the
   * terms, up to twice: a long run's root propagation tightens the sums beyond their terms' bounds,
   * and on the sums the cores of xai-mindset2 iris (MaxSAT Evaluation 2024) had 3 assumptions and
   * reached 49 of 87 in 240 s, while on the terms the optimum is proved in 4 s. Wide terms keep the
   * sums when they span more.
   */
  @Test
  void zeroOneTermsReplaceTighterSums() {
    for (int width : new int[] {1, 3}) {
      Store store = new Store();
      IntVar[] x = new IntVar[6];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, 0, width);
      }
      // each sum spans two thirds of its terms' levels
      IntVar s1 = new IntVar(store, "s1", 0, 2 * width);
      IntVar s2 = new IntVar(store, "s2", 0, 2 * width);
      IntVar obj = new IntVar(store, "obj", 0, 4 * width);
      store.impose(
          new LinearInt(new IntVar[] {x[0], x[1], x[2], s1}, new int[] {1, 1, 1, -1}, "==", 0));
      store.impose(
          new LinearInt(new IntVar[] {x[3], x[4], x[5], s2}, new int[] {1, 1, 1, -1}, "==", 0));
      store.impose(new LinearInt(new IntVar[] {s1, s2, obj}, new int[] {1, 1, -1}, "==", 0));
      store.impose(new LinearInt(new IntVar[] {x[0], x[3]}, new int[] {1, 1}, ">=", 1));
      store.impose(new LinearInt(new IntVar[] {x[1], x[4]}, new int[] {1, 1}, ">=", 1));
      LcgSolver solver = new LcgSolver(store);
      solver.setChecking(true);
      solver.setCoreSearch(1, 1_000_000, 100_000);
      assertThat(solver.minimize(obj)).isEqualTo(CdclSolver.SAT);
      assertThat(solver.value(obj)).isEqualTo(2);
      assertThat(solver.coreSearch().proved).isTrue();
      assertThat(solver.coreSearch().termCount()).isEqualTo(width == 1 ? 6 : 2);
      assertThat(solver.coreSearch().termsBySpanRatio).isEqualTo(width == 1);
    }
  }

  /**
   * The core-guided phase is not skipped after a probe without a solution of its own when the probe
   * raised the lower bound at least as far as it is still below the solution of branch and bound:
   * the probe of xai-mindset2 iris (MaxSAT Evaluation 2024) took the bound from 0 to 77 of 87 in
   * 0.4 s, and the skip left it at 49 after 240 s.
   */
  @Test
  void corePhaseNotSkippedAfterAProbeHalfWay() {
    // the pigeons of corePhaseSkippedWhenItsProbeFoundNoSolution, whose core is too hard, and 16
    // pairs of Booleans of which one at least is true and costs 1, whose cores are easy: the probe
    // raises the bound to 16, and branch and bound finds solutions of 16 + the pigeons in hole 0
    Store store = new Store();
    int n = 12;
    int pairs = 16;
    IntVar[] p = new IntVar[n];
    BooleanVar[] c = new BooleanVar[n + 2 * pairs];
    for (int i = 0; i < n; i++) {
      p[i] = new IntVar(store, "p" + i, 0, n - 1);
      c[i] = new BooleanVar(store, "c" + i);
      store.impose(new Reified(new XeqC(p[i], 0), c[i]));
      for (int j = 0; j < i; j++) {
        store.impose(new Or(new XneqY(p[j], p[i]), new XeqC(p[i], 0)));
      }
    }
    for (int k = 0; k < pairs; k++) {
      c[n + 2 * k] = new BooleanVar(store, "a" + k);
      c[n + 2 * k + 1] = new BooleanVar(store, "b" + k);
      store.impose(
          new LinearInt(new IntVar[] {c[n + 2 * k], c[n + 2 * k + 1]}, new int[] {1, 1}, ">=", 1));
    }
    IntVar obj = new IntVar(store, "obj", 0, c.length);
    store.impose(new SumBool(c, "==", obj));
    LcgSolver solver = new LcgSolver(store);
    solver.setAnnotation(new SimpleSelect<>(p, null, new IndomainMin<>()), true);
    solver.setCoreSearch(0.5, 1_000_000, 100_000_000);
    solver.setCoreDelay(0.05, 1_000_000, 0.05);
    solver.setTimeLimit(200);
    // a clock cap of 1.5 times the probe's share of 3 s: the share of the work ends the probe, not
    // the clock of a cold JVM
    solver.sat().setDeadline(System.nanoTime() + 3_000_000_000L);
    solver.minimize(obj);
    assertThat(solver.coreSearch().lowerBound).isEqualTo(pairs);
    assertThat(solver.value(obj)).isBetween(pairs + 1, pairs + 12);
    assertThat(solver.coreSearch().noSolutionStops).isPositive();
    assertThat(solver.probeHalfWays).isEqualTo(1);
    assertThat(solver.probeSkips).isZero();
  }

  /**
   * Under fixed search the core-guided phase runs only when branch and bound under the annotation
   * found no solution in its share of the time (setCoresWithoutSolutionOnly): with one, branch and
   * bound keeps the time and proves the optimum without a core.
   */
  @Test
  void corePhaseOnlyWithoutASolutionOfBranchAndBound() {
    for (boolean annotationSolves : new boolean[] {true, false}) {
      Store store = new Store();
      int n = 6;
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, n - 1);
      }
      store.impose(new Alldistinct(x));
      IntVar obj = new IntVar(store, "obj", 0, n * n);
      store.impose(new LinearInt(x, IntStream.range(0, n).map(i -> i + 1).toArray(), "==", obj));
      LcgSolver solver = new LcgSolver(store);
      solver.setAnnotation(new SimpleSelect<>(x, null, new IndomainMin<>()), false);
      solver.setCoreSearch(0.5, 1_000_000, 100_000_000);
      // one conflict for branch and bound before the cores, or plenty
      solver.setCoreDelay(0.15, annotationSolves ? 1_000_000 : 1, 0);
      solver.setCoresWithoutSolutionOnly(true);
      assertThat(solver.minimize(obj)).isEqualTo(CdclSolver.SAT);
      // the optimum gives the largest weight the smallest value
      assertThat(solver.value(obj)).isEqualTo(35);
      if (annotationSolves) {
        assertThat(solver.coreSearch().cores).isZero();
      }
    }
  }

  /**
   * The core-guided phase also stops when its lower bound stalls over the second half of its work,
   * but only after a tenth of the run's work after its start: work-task-variation 2025 seed-8 rose
   * from a far initial bound, stalled for 20 s and then proved its optimum, while
   * community-detection 2026 and javarouting trip_7_2 stalled for good and kept the phase to the
   * end of the run (444 s and 566 s to their proofs at 600 s, 379 s and 428 s with the stop). The
   * rate since the start stays high after such a rise, so it never ends the phase.
   */
  @Test
  void corePhaseStopsWhenItsBoundStallsOverItsSecondHalf() {
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < 3; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 10);
    }
    IntVar obj = new IntVar(store, "obj", 0, 30);
    store.impose(
        new LinearInt(new IntVar[] {x[0], x[1], x[2], obj}, new int[] {1, 1, 1, -1}, "==", 0));
    LcgSolver solver = new LcgSolver(store);
    CoreSearch cores = CoreSearch.of(solver, obj);
    assertThat(cores).isNotNull();
    assertThat(CoreSearch.STALL).isEqualTo(0.1);
    long end = 1_000_000;
    cores.lowerBound = -1_000_000; // a far initial bound
    cores.start(0);
    cores.lowerBound = 60; // rises at once
    cores.sample(10_000);
    cores.sample(20_000);
    // flat since 10,000, but before a tenth of the run
    assertThat(cores.stalled(20_000, end, 248)).isFalse();
    cores.sample(99_000);
    assertThat(cores.stalled(99_000, end, 248)).isFalse();
    cores.sample(100_000);
    assertThat(cores.stalled(100_000, end, 248)).isTrue(); // flat since 50,000
    // a rise over the second half that could meet the best solution in the work left
    cores.lowerBound = 100;
    cores.sample(200_000);
    assertThat(cores.stalled(200_000, end, 248)).isFalse();
    assertThat(cores.stalled(200_000, Long.MAX_VALUE, 248)).isFalse(); // no end of the run
    // the same rise does not reach a far best solution: (100 - 60) / 100,000 per unit, three times
    // over 800,000 units is 960
    assertThat(cores.stalled(200_000, end, 100 + 960)).isFalse();
    assertThat(cores.stalled(200_000, end, 100 + 961)).isTrue();
  }

  /**
   * After {@link CoreSearch#DECAY_AFTER} of the phase's own work, a rate that falls from the third
   * to the fourth quarter of the phase is projected as a geometric series: on chessboard3 (2023)
   * each core cost more than the last, and the linear projection kept the phase for half of a 1200
   * s run while the bound stayed 13 below the optimum. Before that work, the linear test alone.
   */
  @Test
  void corePhaseStopsWhenItsBoundRateKeepsFalling() {
    CoreSearch cores = sumCores();
    long u = CoreSearch.DECAY_AFTER / 4; // a quarter of the work before a falling rate counts
    long end = 40 * u;
    cores.lowerBound = 0;
    cores.start(0);
    cores.lowerBound = 4;
    cores.sample(2 * u);
    cores.lowerBound = 6; // 2 over the third quarter
    cores.sample(3 * u);
    cores.lowerBound = 7; // 1 over the last: q = 1/2, at most 1 more in all
    cores.sample(4 * u);
    // linearly 1.5 per u, three times over 36 u reaches 162; the falling rate reaches 3 at most
    assertThat(cores.stalled(4 * u, end, 7 + 20)).isTrue();
    assertThat(cores.stalled(4 * u, end, 7 + 2)).isFalse();
    // the same quarters before DECAY_AFTER: the linear test only
    CoreSearch early = sumCores();
    early.lowerBound = 0;
    early.start(0);
    early.lowerBound = 4;
    early.sample(u);
    early.lowerBound = 6;
    early.sample(3 * u / 2);
    early.lowerBound = 7;
    early.sample(2 * u);
    assertThat(early.stalled(2 * u, 20 * u, 7 + 20)).isFalse();
  }

  /** The core-guided search of obj = x0 + x1 + x2 over 0..10 each, for the tests of its rates. */
  private static CoreSearch sumCores() {
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < 3; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 10);
    }
    IntVar obj = new IntVar(store, "obj", 0, 30);
    store.impose(
        new LinearInt(new IntVar[] {x[0], x[1], x[2], obj}, new int[] {1, 1, 1, -1}, "==", 0));
    CoreSearch cores = CoreSearch.of(new LcgSolver(store), obj);
    assertThat(cores).isNotNull();
    return cores;
  }

  /**
   * Whether the core-guided phase could reach the objective's root bound: at three times the rate
   * of its lower bound per unit of the solver's work since the mark, within the work given. Before
   * a mark, and once the bound is there, it could.
   */
  @Test
  void coreSearchReachesAValueAtThreeTimesItsRate() {
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < 3; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 10);
    }
    IntVar obj = new IntVar(store, "obj", 0, 30);
    store.impose(
        new LinearInt(new IntVar[] {x[0], x[1], x[2], obj}, new int[] {1, 1, 1, -1}, "==", 0));
    LcgSolver solver = new LcgSolver(store);
    CoreSearch cores = CoreSearch.of(solver, obj);
    assertThat(cores).isNotNull();
    long lb = cores.lowerBound;
    assertThat(cores.canReach(lb + 100, 0)).isTrue(); // nothing measured yet
    cores.mark();
    assertThat(cores.canReach(lb, 0)).isTrue();
    assertThat(cores.canReach(lb + 1, 1_000_000)).isFalse(); // the bound has not risen
    cores.lowerBound += 10; // in no work: a rate of 10 per unit
    assertThat(cores.canReach(lb + 10 + 30, 1)).isTrue();
    assertThat(cores.canReach(lb + 10 + 31, 1)).isFalse();
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
  void objectiveProbesOfTheCorePhaseKeepItsOptimaAndBounds() {
    // the probes of the objective's own bound after every core (32 cores by default): the optima
    // and the reported lower bounds stay those of search
    long saved = CoreSearch.objectiveProbeAfter;
    CoreSearch.objectiveProbeAfter = 1;
    try {
      Random rnd = new Random(31);
      int checked = 0;
      long probes = 0;
      for (int instance = 0; instance < 200; instance++) {
        long seed = rnd.nextLong();
        Integer expected = coreModelOptimum(seed, -1, new long[3]);
        for (int mode = 0; mode < 4; mode++) {
          long[] stats = new long[5];
          long[] lower = new long[1];
          Integer found = coreModelOptimum(seed, mode, stats, null, lower);
          assertThat(found)
              .as("instance %d (seed %d), mode %d", instance, seed, mode)
              .isEqualTo(expected);
          if (expected != null) {
            assertThat(lower[0])
                .as("instance %d (seed %d), mode %d", instance, seed, mode)
                .isLessThanOrEqualTo(expected);
          }
          probes += stats[4];
          checked++;
        }
      }
      assertThat(checked).isPositive();
      assertThat(probes).isPositive();
    } finally {
      CoreSearch.objectiveProbeAfter = saved;
    }
  }

  // the lowest value of the objective's domain in coreModelOptimum (tests that start it at the
  // optimum)
  private static int objectiveFloor = Integer.MIN_VALUE;

  @Test
  void objectiveProbeEndsWhenTheObjectiveIsAlreadyAtTheBestSolution() {
    // the objective's domain starts at the optimum, so its minimum meets the best solution while
    // the cores' bound, which counts only the soft literals, is still below it: each probe target
    // is then already implied, and the probe loop doubled its step until it overflowed and never
    // ended (MiniZinc Challenge 2023 roster-shifts-bool s100_e20_c8 under -f -t 240 s)
    long saved = CoreSearch.objectiveProbeAfter;
    CoreSearch.objectiveProbeAfter = 1;
    try {
      Random rnd = new Random(37);
      int checked = 0;
      long probes = 0;
      for (int instance = 0; instance < 2000; instance++) {
        long seed = rnd.nextLong();
        objectiveFloor = Integer.MIN_VALUE;
        Integer expected = coreModelOptimum(seed, -1, new long[3]);
        if (expected == null) {
          continue;
        }
        objectiveFloor = expected;
        for (int mode = 0; mode < 4; mode++) {
          int m = mode;
          long[] stats = new long[5];
          Integer found =
              assertTimeoutPreemptively(
                  Duration.ofSeconds(20), () -> coreModelOptimum(seed, m, stats, null, null));
          probes += stats[4];
          assertThat(found)
              .as("instance %d (seed %d), mode %d", instance, seed, mode)
              .isEqualTo(expected);
          checked++;
        }
      }
      assertThat(checked).isPositive();
      assertThat(probes).isPositive();
    } finally {
      objectiveFloor = Integer.MIN_VALUE;
      CoreSearch.objectiveProbeAfter = saved;
    }
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
    return coreModelOptimum(seed, mode, stats, null);
  }

  /** As above, with the objective value of a solution found elsewhere as a shared bound. */
  private static Integer coreModelOptimum(long seed, int mode, long[] stats, Integer shared) {
    return coreModelOptimum(seed, mode, stats, shared, null);
  }

  /** As above; lower[0] gets the largest lower bound the solver reports, if lower is given. */
  private static Integer coreModelOptimum(
      long seed, int mode, long[] stats, Integer shared, long[] lower) {
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
    IntVar objective = new IntVar(store, "obj", Math.max(lo, Math.min(hi, objectiveFloor)), hi);
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
    if (mode == 4) {
      // core-guided search alone, each core as the solver gives it
      solver.setCoreTrim(0);
    }
    if (mode == 3) {
      // a few conflicts of branch and bound, after a few of core-guided search or none, then the
      // core-guided phase picks up where it stopped
      solver.setCoreDelay(1, 1 + rnd.nextInt(5), rnd.nextInt(2));
      // or the core-guided phase only without a solution of that branch and bound
      solver.setCoresWithoutSolutionOnly(rnd.nextBoolean());
    }
    if (shared != null) {
      solver.setSharedBound(() -> shared);
    }
    if (lower != null) {
      lower[0] = Long.MIN_VALUE;
      solver.onBound(b -> lower[0] = Math.max(lower[0], b));
    }
    int status = solver.minimize(cost);
    assertThat(status).isNotEqualTo(CdclSolver.UNKNOWN);
    if (solver.coreSearch() != null) {
      stats[0] += solver.coreSearch().cores;
      stats[1] += solver.coreSearch().proved ? 1 : 0;
      stats[2] += solver.coreSearch().hardened;
    }
    if (stats.length > 3) {
      stats[3] += solver.solver().conflicts;
    }
    if (stats.length > 4 && solver.coreSearch() != null) {
      stats[4] += solver.coreSearch().objectiveProbes;
    }
    if (stats.length > 5 && solver.coreSearch() != null) {
      stats[5] += solver.coreSearch().coreShrunk;
    }
    return status == CdclSolver.SAT ? solver.value(cost) : null;
  }

  /**
   * A probe whose root propagation stops at the deadline backtracks to the root while root literals
   * it notified are not applied yet. They stay assigned and are not notified again, so they must
   * still reach the domains; ma-path-finding under -f threw "is not fixed in a model" when the core
   * phase found every literal assigned and a variable open.
   */
  @Test
  void rootLiteralsNotifiedBeforeABacktrackToTheRootReachTheDomains() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 1);
    IntVar y = new IntVar(store, "y", 0, 1);
    store.impose(new XneqY(x, y));
    LcgSolver lcg = new LcgSolver(store);
    int lit = lcg.geLiteral(lcg.index(x), 1);
    assertThat(lcg.solver().addClause(lit)).isTrue(); // [x >= 1] at the root
    lcg.notifyAssignment(lit, true);
    lcg.notifyBacktrack(0);
    lcg.propagate(); // applies the pending literals, then gives the first atom they imply
    assertThat(x.min()).isEqualTo(1);
    assertThat(y.max()).isZero();
  }

  /**
   * Routes without its own degrees (as the FlatZinc detector posts it, beside exactly-one rows)
   * explains a failure only by what it propagates itself: never by a node whose arcs out or in are
   * all 0, which only the rows rule out. The explanation checker copies the constraint alone, so
   * such a reason showed as wrong (2014 stochastic-vrp under --lcg). The optimum must match a
   * search with the degrees kept by Routes.
   */
  /**
   * A regular constraint that became clauses propagates again after the solver releases the store,
   * also when the solver was built above the root level, where removing a constraint only marks it
   * as entailed. Root probing with a solver of its own before the linear relaxation lost the
   * regular constraints of handball19 (elitserien 2014) this way, and the search then reported the
   * objective 0 as optimal against the optimum 3.
   */
  @Test
  void releasedRegularPropagatesAboveTheRoot() {
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
    }
    // no two 1s in a row: state 0 after a 0, state 1 after a 1
    Fsm fsm = new Fsm();
    FsmState zero = new FsmState();
    FsmState one = new FsmState();
    fsm.allStates.add(zero);
    fsm.allStates.add(one);
    fsm.initState = zero;
    fsm.finalStates.add(zero);
    fsm.finalStates.add(one);
    zero.addTransition(new FsmTransition(new IntervalDomain(0, 0), zero));
    zero.addTransition(new FsmTransition(new IntervalDomain(1, 1), one));
    one.addTransition(new FsmTransition(new IntervalDomain(0, 0), zero));
    store.impose(new Regular(fsm, x));
    store.setLevel(store.level + 1);
    LcgSolver solver = new LcgSolver(store);
    assertThat(solver.probeRoot(1_000_000_000L)).isTrue();
    assertThat(solver.graphConstraintsEncoded).isOne();
    solver.release();
    assertThat(store.consistency()).isTrue();
    store.setLevel(store.level + 1);
    x[0].domain.in(store.level, x[0], 1, 1);
    x[1].domain.in(store.level, x[1], 1, 1);
    assertThat(store.consistency()).isFalse();
  }

  @Test
  void routesWithoutDegreesExplainsOnlyItsOwnFailures() {
    Random rnd = new Random(20261109L);
    int routesFailures = 0;
    for (int instance = 0; instance < 150; instance++) {
      int n = 4 + rnd.nextInt(3);
      int[] demands = new int[n];
      for (int v = 1; v < n; v++) {
        demands[v] = 1 + rnd.nextInt(3);
      }
      int capacity = 3 + rnd.nextInt(4);
      int[][] weight = new int[n][n];
      for (int t = 0; t < n; t++) {
        for (int h = 0; h < n; h++) {
          weight[t][h] = rnd.nextInt(20);
        }
      }
      long best = routesOptimum(n, demands, capacity, weight, true, null);
      int seed = instance % 3;
      LcgSolver[] solver = new LcgSolver[1];
      long got =
          routesOptimum(
              n,
              demands,
              capacity,
              weight,
              false,
              (store, objective) -> {
                solver[0] = new LcgSolver(store);
                solver[0].setChecking(true);
                solver[0].setSeed(seed);
                int status = solver[0].minimize(objective);
                return status == CdclSolver.SAT ? solver[0].value(objective) : Long.MAX_VALUE;
              });
      assertThat(got).as("instance %d", instance).isEqualTo(best);
      long[] c = solver[0].explanationStatistics().get("Routes");
      if (c != null) {
        routesFailures += (int) c[3];
      }
    }
    assertThat(routesFailures).isGreaterThan(0);
  }

  // the cheapest routes over the complete graph of n nodes; degrees false posts exactly-one rows
  // and Routes without its degrees, and solves with lcg (DFS with null)
  private static long routesOptimum(
      int n,
      int[] demands,
      int capacity,
      int[][] weight,
      boolean degrees,
      ToLongBiFunction<Store, IntVar> lcg) {
    Store store = new Store();
    List<int[]> arcs = new ArrayList<>();
    for (int t = 0; t < n; t++) {
      for (int h = 0; h < n; h++) {
        if (t != h) {
          arcs.add(new int[] {t, h});
        }
      }
    }
    int m = arcs.size();
    int[] tails = new int[m];
    int[] heads = new int[m];
    int[] w = new int[m + 1];
    IntVar[] literals = new IntVar[m];
    for (int k = 0; k < m; k++) {
      tails[k] = arcs.get(k)[0];
      heads[k] = arcs.get(k)[1];
      w[k] = weight[tails[k]][heads[k]];
      literals[k] = new IntVar(store, "a" + tails[k] + "_" + heads[k], 0, 1);
    }
    Routes routes = new Routes(tails, heads, literals, demands, capacity);
    if (!degrees) {
      routes.setDegrees(false);
      IntVar one = new IntVar(store, 1, 1);
      for (int v = 1; v < n; v++) {
        List<IntVar> out = new ArrayList<>();
        List<IntVar> in = new ArrayList<>();
        for (int k = 0; k < m; k++) {
          if (tails[k] == v) {
            out.add(literals[k]);
          }
          if (heads[k] == v) {
            in.add(literals[k]);
          }
        }
        store.impose(new SumBool(out.toArray(new IntVar[0]), "==", one));
        store.impose(new SumBool(in.toArray(new IntVar[0]), "==", one));
      }
    }
    store.impose(routes);
    IntVar cost = new IntVar(store, "cost", 0, 1000);
    IntVar[] terms = Arrays.copyOf(literals, m + 1);
    terms[m] = cost;
    w[m] = -1;
    store.impose(new LinearInt(terms, w, "==", 0));
    if (lcg != null) {
      return lcg.applyAsLong(store, cost);
    }
    if (!store.consistency()) {
      return Long.MAX_VALUE;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(new SimpleSolutionListener<>());
    boolean found =
        search.labeling(store, new SimpleSelect<>(literals, null, new IndomainMin<>()), cost);
    return found ? cost.value() : Long.MAX_VALUE;
  }
}
