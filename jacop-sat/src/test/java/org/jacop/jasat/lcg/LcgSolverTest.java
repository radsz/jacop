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
import java.util.List;
import java.util.Random;
import java.util.function.Predicate;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Tests lazy clause generation against brute force: random small problems of several constraints
 * must be found satisfiable exactly when some assignment satisfies every relation, and the solution
 * found must satisfy them.
 */
class LcgSolverTest {

  private record Relation(Constraint constraint, Predicate<int[]> test) {}

  private static IntVar var(Store store, String name, Random rnd) {
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
              for (int time = -2; time < 12; time++) {
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
        x[i] = var(store, "x" + i, rnd);
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
}
