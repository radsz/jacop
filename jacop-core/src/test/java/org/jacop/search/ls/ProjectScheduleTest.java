/*
 * ProjectScheduleTest.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * preservation of specified reasonable legal notices and author attributions
 * in accordance with Section 7 of this License.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.search.ls;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.junit.jupiter.api.Test;

/**
 * Checks the project scheduling heuristic on small random projects: every schedule it reports keeps
 * the precedences and the capacities and has the makespan it claims, and it never reports a
 * makespan below the optimum found by depth-first search.
 */
class ProjectScheduleTest {

  private static final class Project {
    final Store store = new Store();
    final int n;
    final int[] d;
    final int[][] dem;
    final int[] cap;
    final List<int[]> arcs = new ArrayList<>();
    final IntVar[] s;
    final IntVar cost;

    Project(Random random, int n, int resources) {
      this.n = n;
      d = new int[n];
      int horizon = 0;
      for (int t = 0; t < n; t++) {
        d[t] = 1 + random.nextInt(4);
        horizon += d[t];
      }
      s = new IntVar[n];
      for (int t = 0; t < n; t++) {
        s[t] = new IntVar(store, "s" + t, 0, horizon);
      }
      cost = new IntVar(store, "cost", 0, horizon);
      cap = new int[resources];
      dem = new int[resources][n];
      for (int r = 0; r < resources; r++) {
        cap[r] = 1 + random.nextInt(4);
        IntVar[] ds = new IntVar[n];
        IntVar[] rs = new IntVar[n];
        for (int t = 0; t < n; t++) {
          dem[r][t] = random.nextInt(cap[r] + 1);
          ds[t] = new IntVar(store, d[t], d[t]);
          rs[t] = new IntVar(store, dem[r][t], dem[r][t]);
        }
        store.impose(new Cumulative(s, ds, rs, new IntVar(store, cap[r], cap[r])));
      }
      for (int a = 0; a < n; a++) {
        for (int b = a + 1; b < n; b++) {
          if (random.nextInt(4) == 0) {
            arcs.add(new int[] {a, b});
            store.impose(new XplusClteqZ(s[a], d[a], s[b]));
          }
        }
        store.impose(new XplusClteqZ(s[a], d[a], cost));
      }
    }

    // the makespan of a schedule that keeps every constraint, or -1
    int check(int[] start) {
      for (int[] a : arcs) {
        if (start[a[0]] + d[a[0]] > start[a[1]]) {
          return -1;
        }
      }
      int end = 0;
      for (int t = 0; t < n; t++) {
        end = Math.max(end, start[t] + d[t]);
      }
      for (int r = 0; r < cap.length; r++) {
        for (int u = 0; u < end; u++) {
          int load = 0;
          for (int t = 0; t < n; t++) {
            if (start[t] <= u && u < start[t] + d[t]) {
              load += dem[r][t];
            }
          }
          if (load > cap[r]) {
            return -1;
          }
        }
      }
      return end;
    }

    int optimum() {
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      IntVar[] all = new IntVar[n + 1];
      System.arraycopy(s, 0, all, 0, n);
      all[n] = cost;
      search.labeling(
          store, new SimpleSelect<>(all, new SmallestDomain<>(), new IndomainMin<>()), cost);
      return cost.value();
    }
  }

  @Test
  void schedulesKeepTheConstraints() {
    Random random = new Random(7);
    for (int trial = 0; trial < 60; trial++) {
      Project p = new Project(random, 4 + random.nextInt(5), 1 + random.nextInt(3));
      assertTrue(p.store.consistency());
      ProjectSchedule ps = ProjectSchedule.detect(p.cost, trial);
      assertNotNull(ps, "trial " + trial);
      IntVar[] starts = ps.starts();
      int[] best = {Integer.MAX_VALUE};
      ps.run(
          new ProjectSchedule.Listener() {
            @Override
            public boolean improved(int[] start, int makespan) {
              int[] byTask = new int[p.n];
              for (int k = 0; k < starts.length; k++) {
                for (int t = 0; t < p.n; t++) {
                  if (starts[k] == p.s[t]) {
                    byTask[t] = start[k];
                  }
                }
              }
              assertEquals(makespan, p.check(byTask));
              assertTrue(makespan < best[0]);
              best[0] = makespan;
              return true;
            }

            @Override
            public boolean stop() {
              return false;
            }
          },
          2000);
      int opt = p.optimum();
      assertTrue(best[0] >= opt, "trial " + trial + ": " + best[0] + " < optimum " + opt);
    }
  }

  @Test
  void costThatIsNotAMakespan() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 10);
    IntVar cost = new IntVar(store, "cost", 0, 10);
    store.impose(new XplusClteqZ(x, 1, cost));
    // no cumulative resource
    assertNull(ProjectSchedule.detect(cost, 1));
  }
}
