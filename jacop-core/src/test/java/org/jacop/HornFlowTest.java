/*
 * HornFlowTest.java
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

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Arrays;
import java.util.Random;
import java.util.TreeSet;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.HornFlow;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Checks {@link HornFlow} on random P|r_j, d_j| instances (unit resource uses, m machines) and on
 * random instances with resource uses above one: a failure must mean that no non-preemptive
 * schedule exists (brute force), the maximum flow must agree with the min-cut condition evaluated
 * over every union of elementary intervals, and adding the check to {@link Cumulative} must keep
 * every solution in a complete search. It also counts the instances the flow refutes at the root
 * while the cumulative constraint does not.
 */
class HornFlowTest {

  /** Random instances per test; the {@code min} profile lowers it. */
  private static final int TRIALS = Integer.getInteger("hornflow.trials", 2000);

  /** The fewest tasks of a large instance. */
  private static final int LARGE_TASKS = Integer.getInteger("hornflow.largeTasks", 6);

  private static final long SEED = Long.getLong("hornflow.seed", 20261106L);

  private record Instance(int[] release, int[] deadline, int[] p, int[] r, int capacity) {
    int n() {
      return p.length;
    }

    @Override
    public String toString() {
      return "release="
          + Arrays.toString(release)
          + " deadline="
          + Arrays.toString(deadline)
          + " p="
          + Arrays.toString(p)
          + " r="
          + Arrays.toString(r)
          + " capacity="
          + capacity;
    }
  }

  // tasks with windows [release, deadline) in a short horizon; tight enough that many are
  // infeasible. Large instances have 6 to 10 tasks on 2 to 4 machines with a load near the
  // capacity, where the time-table and the energy rules leave more to the flow.
  private static Instance random(Random rnd, boolean unit, boolean large) {
    int n = large ? LARGE_TASKS + rnd.nextInt(5) : 3 + rnd.nextInt(5);
    int capacity = unit ? (large ? 2 + rnd.nextInt(3) : 1 + rnd.nextInt(3)) : 2 + rnd.nextInt(3);
    int[] release = new int[n];
    int[] deadline = new int[n];
    int[] p = new int[n];
    int[] r = new int[n];
    int energy = 0;
    for (int j = 0; j < n; j++) {
      p[j] = 1 + rnd.nextInt(large ? 5 : 4);
      r[j] = unit ? 1 : 1 + rnd.nextInt(capacity);
      energy += p[j] * r[j];
    }
    int horizon =
        large
            ? Math.max(Arrays.stream(p).max().orElse(1), (energy + capacity - 1) / capacity)
                + rnd.nextInt(3)
            : 4 + rnd.nextInt(8);
    for (int j = 0; j < n; j++) {
      p[j] = Math.min(p[j], horizon);
      release[j] = rnd.nextInt(horizon - p[j] + 1);
      deadline[j] = release[j] + p[j] + rnd.nextInt(horizon - release[j] - p[j] + 1);
    }
    return new Instance(release, deadline, p, r, capacity);
  }

  private static final class Model {
    final Store store = new Store();
    final IntVar[] s;
    final IntVar[] d;
    final IntVar[] r;
    final IntVar limit;

    Model(Instance in) {
      int n = in.n();
      s = new IntVar[n];
      d = new IntVar[n];
      r = new IntVar[n];
      for (int j = 0; j < n; j++) {
        s[j] = new IntVar(store, "s" + j, in.release[j], in.deadline[j] - in.p[j]);
        d[j] = new IntVar(store, in.p[j], in.p[j]);
        r[j] = new IntVar(store, in.r[j], in.r[j]);
      }
      limit = new IntVar(store, in.capacity, in.capacity);
    }

    Cumulative cumulative(boolean allRules) {
      Cumulative c = new Cumulative(s, d, r, limit);
      if (allRules) {
        c.doEdgeFind(true);
        c.doHorizontallyElasticEdgeFind(true);
        c.doAdaptiveEnergyReasoning(false);
      }
      return c;
    }

    HornFlow flow(boolean compulsory) {
      HornFlow c = new HornFlow(s, d, r, limit);
      c.useCompulsoryParts(compulsory);
      return c;
    }

    boolean root(Constraint... cs) {
      for (Constraint c : cs) {
        store.impose(c);
      }
      return store.consistency();
    }
  }

  // a non-preemptive schedule exists
  private static boolean schedulable(Instance in) {
    int horizon = Arrays.stream(in.deadline).max().orElse(0);
    return place(in, 0, new int[horizon]);
  }

  private static boolean place(Instance in, int j, int[] load) {
    if (j == in.n()) {
      return true;
    }
    for (int t = in.release[j]; t + in.p[j] <= in.deadline[j]; t++) {
      boolean fits = true;
      for (int u = t; u < t + in.p[j] && fits; u++) {
        fits = load[u] + in.r[j] <= in.capacity;
      }
      if (!fits) {
        continue;
      }
      for (int u = t; u < t + in.p[j]; u++) {
        load[u] += in.r[j];
      }
      boolean ok = place(in, j + 1, load);
      for (int u = t; u < t + in.p[j]; u++) {
        load[u] -= in.r[j];
      }
      if (ok) {
        return true;
      }
    }
    return false;
  }

  /**
   * The min-cut condition over every union U of elementary intervals: each task needs r max(|cp &
   * U|, p - |W \ U|) in U (the compulsory part cp only with compulsory parts), at most C |U| in
   * total. By max-flow min-cut it holds if and only if the flow is full; null when there are too
   * many intervals to enumerate.
   */
  private static Boolean cutCondition(Instance in, boolean compulsory) {
    TreeSet<Integer> points = new TreeSet<>();
    for (int j = 0; j < in.n(); j++) {
      int lst = in.deadline[j] - in.p[j];
      int ect = in.release[j] + in.p[j];
      points.add(in.release[j]);
      points.add(in.deadline[j]);
      if (compulsory && lst < ect) {
        points.add(lst);
        points.add(ect);
      }
    }
    int[] t = points.stream().mapToInt(Integer::intValue).toArray();
    int k = t.length - 1;
    if (k > 16) {
      return null;
    }
    boolean[] inU = new boolean[t[k] + 1];
    for (int mask = 1; mask < (1 << k); mask++) {
      Arrays.fill(inU, false);
      int size = 0;
      for (int b = 0; b < k; b++) {
        if ((mask & (1 << b)) != 0) {
          for (int u = t[b]; u < t[b + 1]; u++) {
            inU[u] = true;
          }
          size += t[b + 1] - t[b];
        }
      }
      long need = 0;
      for (int j = 0; j < in.n(); j++) {
        int outside = 0;
        for (int u = in.release[j]; u < in.deadline[j]; u++) {
          outside += inU[u] ? 0 : 1;
        }
        int lst = in.deadline[j] - in.p[j];
        int ect = in.release[j] + in.p[j];
        int core = 0;
        if (compulsory) {
          for (int u = lst; u < ect; u++) {
            core += inU[u] ? 1 : 0;
          }
        }
        need += (long) in.r[j] * Math.max(0, Math.max(core, in.p[j] - outside));
      }
      if (need > (long) in.capacity * size) {
        return false;
      }
    }
    return true;
  }

  private static void check(boolean unit, boolean large) {
    Random rnd = new Random(SEED + (unit ? 0 : 1) + (large ? 2 : 0));
    int infeasible = 0;
    int[] flowFails = new int[2];
    int defaultFails = 0;
    int allRuleFails = 0;
    int[] extraOverDefault = new int[2];
    int[] extraOverAll = new int[2];
    int exactCompared = 0;
    int[] extraAfterFixpoint = new int[2];
    int[] extraAfterAllRules = new int[2];
    for (int trial = 0; trial < TRIALS; trial++) {
      Instance in = random(rnd, unit, large);
      boolean schedulable = schedulable(in);
      if (!schedulable) {
        infeasible++;
      }
      Model allModel = new Model(in);
      boolean allOk = allModel.root(allModel.cumulative(true));
      Model dm = new Model(in);
      boolean defaultOk = dm.root(dm.cumulative(false));
      defaultFails += defaultOk ? 0 : 1;
      allRuleFails += allOk ? 0 : 1;
      for (int c = 0; c < 2; c++) {
        boolean compulsory = c == 1;
        Model fm = new Model(in);
        boolean flowOk = fm.root(fm.flow(compulsory));
        String what = in + " compulsory=" + compulsory;
        // a failure must be a real infeasibility
        assertThat(flowOk || !schedulable).as("flow fails a schedulable " + what).isTrue();
        Boolean cut = cutCondition(in, compulsory);
        if (cut != null) {
          exactCompared++;
          assertThat(flowOk).as("flow and cut condition differ on " + what).isEqualTo(cut);
        }
        if (!flowOk) {
          flowFails[c]++;
          extraOverDefault[c] += defaultOk ? 1 : 0;
          extraOverAll[c] += allOk ? 1 : 0;
        }
        // the flow added to the cumulative never fails where the cumulative alone has a schedule
        Model both = new Model(in);
        boolean bothOk = both.root(both.cumulative(false), both.flow(compulsory));
        assertThat(bothOk || !schedulable).as("cumulative + flow fails " + what).isTrue();
        extraAfterFixpoint[c] += defaultOk && !bothOk ? 1 : 0;
        Model allBoth = new Model(in);
        boolean allBothOk = allBoth.root(allBoth.cumulative(true), allBoth.flow(compulsory));
        extraAfterAllRules[c] += allOk && !allBothOk ? 1 : 0;
      }
    }
    System.out.printf(
        "HornFlowTest %s: %d instances, %d infeasible, cumulative default fails %d, all rules %d;"
            + " Horn flow fails %d (%d not refuted by default, %d not by all rules);"
            + " flow with compulsory parts fails %d (%d / %d); %d exact cut comparisons;"
            + " added to the cumulative fixpoint it fails %d / %d more (Horn), %d / %d (compulsory)%n",
        (unit ? "P|r_j,d_j| unit uses" : "uses above one") + (large ? ", large" : ""),
        TRIALS,
        infeasible,
        defaultFails,
        allRuleFails,
        flowFails[0],
        extraOverDefault[0],
        extraOverAll[0],
        flowFails[1],
        extraOverDefault[1],
        extraOverAll[1],
        exactCompared,
        extraAfterFixpoint[0],
        extraAfterAllRules[0],
        extraAfterFixpoint[1],
        extraAfterAllRules[1]);
    // the flow with compulsory parts subsumes the time-table and overload checks
    assertThat(flowFails[1]).isGreaterThanOrEqualTo(flowFails[0]);
  }

  @Test
  void unitUsesAgainstBruteForce() {
    check(true, false);
  }

  @Test
  void largeUnitUsesAgainstBruteForce() {
    check(true, true);
  }

  @Test
  void largerUsesAgainstBruteForce() {
    check(false, false);
  }

  @Test
  void largeLargerUsesAgainstBruteForce() {
    check(false, true);
  }

  /** A complete search with the flow added to the cumulative finds the same solutions. */
  @Test
  void searchKeepsEverySolution() {
    Random rnd = new Random(SEED + 7);
    int trials = Math.max(50, TRIALS / 10);
    for (int trial = 0; trial < trials; trial++) {
      Instance in = random(rnd, rnd.nextBoolean(), false);
      long seed = rnd.nextLong();
      int base = solutions(in, false, false, seed);
      for (int c = 0; c < 2; c++) {
        assertThat(solutions(in, true, c == 1, seed))
            .as("solutions of " + in + " compulsory=" + (c == 1))
            .isEqualTo(base);
      }
      // the flow alone is a correct constraint: it has the solutions of the cumulative
      assertThat(solutionsFlowOnly(in, seed)).as("flow alone on " + in).isEqualTo(base);
    }
  }

  private static int solutions(Instance in, boolean flow, boolean compulsory, long seed) {
    Model m = new Model(in);
    m.store.impose(m.cumulative(false));
    if (flow) {
      m.store.impose(m.flow(compulsory));
    }
    return count(m, seed);
  }

  private static int solutionsFlowOnly(Instance in, long seed) {
    Model m = new Model(in);
    m.store.impose(m.flow(true));
    return count(m, seed);
  }

  private static int count(Model m, long seed) {
    if (!m.store.consistency()) {
      return 0;
    }
    Search<IntVar> search = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(m.s, null, new IndomainRandom<>((int) seed));
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.setPrintInfo(false);
    search.labeling(m.store, select);
    return search.getSolutionListener().solutionsNo();
  }

  /**
   * Solves large random instances (first solution or a proof that there is none) with the
   * cumulative alone and with the flow added, checks that both agree with the brute force, and
   * reports the nodes and the instances where the flow cut the search tree.
   */
  @Test
  void searchNodesOnLargeInstances() {
    for (boolean unit : new boolean[] {true, false}) {
      Random rnd = new Random(SEED + 13 + (unit ? 0 : 1));
      int trials = Math.max(50, TRIALS / 4);
      long[] nodes = new long[3];
      int[] fewer = new int[3];
      int[] more = new int[3];
      for (int trial = 0; trial < trials; trial++) {
        Instance in = random(rnd, unit, true);
        Boolean schedulable = LARGE_TASKS <= 10 ? schedulable(in) : null;
        long[] k = new long[3];
        for (int c = 0; c < 3; c++) {
          Model m = new Model(in);
          m.store.impose(m.cumulative(false));
          if (c > 0) {
            m.store.impose(m.flow(c == 2));
          }
          boolean ok = m.store.consistency();
          if (ok) {
            Search<IntVar> search = new DepthFirstSearch<>();
            search.setPrintInfo(false);
            ok =
                search.labeling(
                    m.store, new SimpleSelect<>(m.s, null, new org.jacop.search.IndomainMin<>()));
            k[c] = search.getNodes() + search.getWrongDecisions();
          }
          if (schedulable == null) {
            schedulable = ok;
          }
          assertThat(ok).as(in + " config " + c).isEqualTo(schedulable);
          nodes[c] += k[c];
        }
        for (int c = 1; c < 3; c++) {
          fewer[c] += k[c] < k[0] ? 1 : 0;
          more[c] += k[c] > k[0] ? 1 : 0;
        }
      }
      System.out.printf(
          "HornFlowTest search %s: %d instances, nodes cumulative %d, + Horn flow %d (%d fewer,"
              + " %d more), + flow with compulsory parts %d (%d fewer, %d more)%n",
          unit ? "unit uses" : "uses above one",
          trials,
          nodes[0],
          nodes[1],
          fewer[1],
          more[1],
          nodes[2],
          fewer[2],
          more[2]);
    }
  }
}
