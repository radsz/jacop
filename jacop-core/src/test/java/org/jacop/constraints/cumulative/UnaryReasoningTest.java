/*
 * UnaryReasoningTest.java
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

package org.jacop.constraints.cumulative;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Arrays;
import java.util.Random;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestMin;
import org.junit.jupiter.api.Test;

/**
 * Compares the unary resource rules of {@link UnaryReasoning} (time line for the overload check and
 * detectable precedences) with the Theta-tree algorithms of {@link UnaryReasoningReference} on
 * random tasks with holes in the start domains and variable durations.
 *
 * <p>The overload check, not-last and edge finding must prune exactly as the reference. Detectable
 * precedences on the time line may prune more in one call (a task behind a blocking task gets the
 * bound of its predecessors after the blocking task), but never more than the reference repeated to
 * its fixpoint. The whole constraint must reach the same fixpoint and explore the same search tree
 * as with the reference rules.
 */
class UnaryReasoningTest {

  /** Random instances per check; the {@code min} profile lowers it. */
  private static final int TRIALS = Integer.getInteger("unary.reasoning.trials", 2000);

  /** One random instance: start domains, duration bounds and a tightness of the horizon. */
  private record Instance(int[][] starts, int[][] durations) {

    int n() {
      return starts.length;
    }

    IntVar[][] post(Store store) {
      int n = n();
      IntVar[] s = new IntVar[n];
      IntVar[] d = new IntVar[n];
      IntVar[] r = new IntVar[n];
      for (int i = 0; i < n; i++) {
        s[i] = new IntVar(store, "s" + i);
        for (int v : starts[i]) {
          s[i].addDom(v, v);
        }
        d[i] = new IntVar(store, "d" + i, durations[i][0], durations[i][1]);
        r[i] = new IntVar(store, "r" + i, 1, 1);
      }
      return new IntVar[][] {s, d, r};
    }

    @Override
    public String toString() {
      return "starts="
          + Arrays.deepToString(starts)
          + " durations="
          + Arrays.deepToString(durations);
    }
  }

  private static Instance instance(Random random, int maxTasks) {
    return instance(random, maxTasks, false);
  }

  private static Instance instance(Random random, int maxTasks, boolean constantDurations) {
    int n = 1 + random.nextInt(maxTasks);
    int[][] durations = new int[n][];
    int total = 0;
    for (int i = 0; i < n; i++) {
      int lo = 1 + random.nextInt(random.nextBoolean() ? 3 : 12);
      int hi = !constantDurations && random.nextInt(3) == 0 ? lo + random.nextInt(4) : lo;
      durations[i] = new int[] {lo, hi};
      total += lo;
    }
    // a horizon from very tight (failures, blocking tasks) to loose
    int horizon = Math.max(1, (int) (total * (0.6 + random.nextDouble())));
    int[][] starts = new int[n][];
    for (int i = 0; i < n; i++) {
      int a = random.nextInt(horizon);
      int b = random.nextInt(horizon);
      int lo = Math.min(a, b);
      int hi = random.nextInt(3) == 0 ? lo + random.nextInt(4) : Math.max(a, b);
      int[] values = new int[hi - lo + 1];
      int k = 0;
      for (int v = lo; v <= hi; v++) {
        if (v == lo || v == hi || random.nextInt(5) != 0) {
          values[k++] = v;
        }
      }
      starts[i] = Arrays.copyOf(values, k);
    }
    return new Instance(starts, durations);
  }

  /** The rules of one view, applied to fresh stores built from the same instance. */
  private enum Rule {
    OVERLOAD,
    DETECTABLE,
    NOT_LAST,
    EDGE_FIND
  }

  /** The bounds of the start variables after a rule, or null if the rule failed. */
  private static int[][] apply(Instance inst, Rule rule, boolean reversed, boolean reference) {
    Store store = new Store();
    IntVar[][] v = inst.post(store);
    int n = inst.n();
    TaskView[] ts = new TaskView[n];
    for (int i = 0; i < n; i++) {
      ts[i] =
          reversed
              ? new TaskReversedView(v[0][i], v[1][i], v[2][i])
              : new TaskNormalView(v[0][i], v[1][i], v[2][i]);
      ts[i].index = i;
    }
    store.setLevel(1);
    try {
      if (reference) {
        UnaryReasoningReference u = new UnaryReasoningReference();
        u.load(ts, n);
        switch (rule) {
          case OVERLOAD -> u.overload(n);
          case DETECTABLE -> u.detectable(ts, n, store);
          case NOT_LAST -> u.notLast(ts, n, store);
          case EDGE_FIND -> u.edgeFind(ts, n, store);
        }
      } else {
        UnaryReasoning u = new UnaryReasoning();
        u.load(ts, n);
        switch (rule) {
          case OVERLOAD -> u.overload(n);
          case DETECTABLE -> u.detectable(ts, n, store);
          case NOT_LAST -> u.notLast(ts, n, store);
          case EDGE_FIND -> u.edgeFind(ts, n, store);
        }
      }
    } catch (FailException e) {
      return null;
    }
    return bounds(v[0]);
  }

  /** Bounds after the reference detectable precedences repeated until nothing changes. */
  private static int[][] referenceDetectableFixpoint(Instance inst, boolean reversed) {
    Store store = new Store();
    IntVar[][] v = inst.post(store);
    int n = inst.n();
    TaskView[] ts = new TaskView[n];
    for (int i = 0; i < n; i++) {
      ts[i] =
          reversed
              ? new TaskReversedView(v[0][i], v[1][i], v[2][i])
              : new TaskNormalView(v[0][i], v[1][i], v[2][i]);
      ts[i].index = i;
    }
    store.setLevel(1);
    UnaryReasoningReference u = new UnaryReasoningReference();
    try {
      int[][] before;
      do {
        before = bounds(v[0]);
        u.load(ts, n);
        u.detectable(ts, n, store);
      } while (!Arrays.deepEquals(before, bounds(v[0])));
    } catch (FailException e) {
      return null;
    }
    return bounds(v[0]);
  }

  private static int[][] bounds(IntVar[] vars) {
    int[][] b = new int[vars.length][];
    for (int i = 0; i < vars.length; i++) {
      b[i] = new int[] {vars[i].min(), vars[i].max()};
    }
    return b;
  }

  @Test
  void overloadNotLastAndEdgeFindingPruneAsTheThetaTree() {
    Random random = new Random(11);
    for (int trial = 0; trial < TRIALS; trial++) {
      Instance inst = instance(random, trial % 2 == 0 ? 8 : 40);
      for (boolean reversed : new boolean[] {false, true}) {
        for (Rule rule : new Rule[] {Rule.OVERLOAD, Rule.NOT_LAST, Rule.EDGE_FIND}) {
          assertThat(apply(inst, rule, reversed, false))
              .as("%s reversed=%s on %s", rule, reversed, inst)
              .isDeepEqualTo(apply(inst, rule, reversed, true));
        }
      }
    }
  }

  @Test
  void detectablePrecedencesLieBetweenOneCallAndTheFixpointOfTheThetaTree() {
    Random random = new Random(12);
    int failures = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      Instance inst = instance(random, trial % 2 == 0 ? 8 : 40);
      for (boolean reversed : new boolean[] {false, true}) {
        String as = "reversed=" + reversed + " on " + inst;
        int[][] timeLine = apply(inst, Rule.DETECTABLE, reversed, false);
        int[][] oneCall = apply(inst, Rule.DETECTABLE, reversed, true);
        int[][] fixpoint = referenceDetectableFixpoint(inst, reversed);
        if (fixpoint == null) {
          failures++;
          continue;
        }
        assertThat(timeLine)
            .as("time line fails, the reference fixpoint does not: " + as)
            .isNotNull();
        assertThat(oneCall).as(as).isNotNull();
        for (int i = 0; i < inst.n(); i++) {
          for (int k = 0; k < 2; k++) {
            int lo = k == 0 ? oneCall[i][k] : fixpoint[i][k];
            int hi = k == 0 ? fixpoint[i][k] : oneCall[i][k];
            assertThat(timeLine[i][k]).as("task %d bound %d: %s", i, k, as).isBetween(lo, hi);
          }
        }
      }
    }
    // the blocking task case and failures must both be exercised
    // failures must be exercised; the blocking task case is rare here, see the next test
    assertThat(failures).isPositive();
  }

  @Test
  void taskBehindBlockingTaskGetsTheBoundAfterIt() {
    // b in [5, 6] with duration 10 has a compulsory part [6, 15); q (ect 7) must follow b, and k
    // (start 5..8, duration 1) must precede b. The time line filters q after b with k on the time
    // line: k takes [5, 6), so b ends at 16 and q starts at 16. The Theta tree gives q only
    // ect({b}) = 15 in this call and 16 in the next.
    int[] k = {5, 6, 7, 8};
    int[] q = new int[27];
    for (int v = 0; v < q.length; v++) {
      q[v] = 4 + v;
    }
    int[] b = {5, 6};
    Instance inst = new Instance(new int[][] {k, q, b}, new int[][] {{1, 1}, {3, 3}, {10, 10}});
    assertThat(apply(inst, Rule.DETECTABLE, false, false)[1][0]).isEqualTo(16);
    assertThat(apply(inst, Rule.DETECTABLE, false, true)[1][0]).isEqualTo(15);
    assertThat(referenceDetectableFixpoint(inst, false)[1][0]).isEqualTo(16);
  }

  /** CumulativeUnary with the Theta-tree rules of the reference and the general profile. */
  private static final class ReferenceUnary extends CumulativeUnary {

    private final UnaryReasoningReference normal = new UnaryReasoningReference();
    private final UnaryReasoningReference reversed = new UnaryReasoningReference();

    ReferenceUnary(IntVar[] s, IntVar[] d, IntVar[] r, IntVar limit, boolean profile) {
      super(s, d, r, limit, profile, true);
    }

    // the general profile, as CumulativeUnary ran it before the unary time-table
    @Override
    void unaryProfile(Store store) {
      profileProp(store);
    }

    // the rules as CumulativeUnary ran them before the time line: a fresh load before each
    @Override
    void unaryRules(Store store, TaskView[] tn, TaskView[] tr, boolean overload) {
      int n = tn.length;
      if (overload) {
        normal.load(tn, n);
        normal.overload(n);
      }
      normal.load(tn, n);
      normal.detectable(tn, n, store);
      reversed.load(tr, n);
      reversed.detectable(tr, n, store);
      normal.load(tn, n);
      normal.notLast(tn, n, store);
      reversed.load(tr, n);
      reversed.notLast(tr, n, store);
      normal.load(tn, n);
      normal.edgeFind(tn, n, store);
      reversed.load(tr, n);
      reversed.edgeFind(tr, n, store);
    }
  }

  /** Bounds of all variables at the root fixpoint, or null on failure. */
  private static int[][] rootFixpoint(Instance inst, boolean profile, boolean reference) {
    Store store = new Store();
    IntVar[][] v = inst.post(store);
    IntVar limit = new IntVar(store, 1, 1);
    store.impose(
        reference
            ? new ReferenceUnary(v[0], v[1], v[2], limit, profile)
            : new CumulativeUnary(v[0], v[1], v[2], limit, profile, true));
    if (!store.consistency()) {
      return null;
    }
    IntVar[] all = new IntVar[2 * inst.n()];
    System.arraycopy(v[0], 0, all, 0, inst.n());
    System.arraycopy(v[1], 0, all, inst.n(), inst.n());
    return bounds(all);
  }

  @Test
  void constraintReachesTheSameFixpoint() {
    Random random = new Random(13);
    for (int trial = 0; trial < TRIALS; trial++) {
      Instance inst = instance(random, trial % 2 == 0 ? 10 : 40);
      for (boolean profile : new boolean[] {false, true}) {
        assertThat(rootFixpoint(inst, profile, false))
            .as("profile=%s on %s", profile, inst)
            .isDeepEqualTo(rootFixpoint(inst, profile, true));
      }
    }
  }

  @Test
  void rulesRunAgainAfterTheTimeTableChangesBounds() {
    // found by random testing: a rule that pruned nothing in one pass prunes after the time-table
    // changed bounds in a later pass, so the time-table must reset the skipped rules
    Instance inst =
        new Instance(
            new int[][] {
              {24, 25},
              {6, 7, 8, 9, 10, 11, 13, 15, 17, 18, 19, 21, 22, 23},
              {3, 4, 5, 7},
              {22},
              {15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31},
              {2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 17, 18, 20},
              {22, 23, 24, 25, 26, 29}
            },
            new int[][] {{1, 1}, {1, 4}, {7, 9}, {1, 1}, {6, 8}, {2, 5}, {7, 7}});
    assertThat(rootFixpoint(inst, true, false)).isDeepEqualTo(rootFixpoint(inst, true, true));
  }

  /** Solutions and nodes of a random-order search over all solutions, or the first if many. */
  private static long[] search(Instance inst, boolean profile, boolean reference, long seed) {
    return search(inst, profile, reference, seed, false);
  }

  private static long[] search(
      Instance inst, boolean profile, boolean reference, long seed, boolean leftToRight) {
    Store store = new Store();
    IntVar[][] v = inst.post(store);
    IntVar limit = new IntVar(store, 1, 1);
    store.impose(
        reference
            ? new ReferenceUnary(v[0], v[1], v[2], limit, profile)
            : new CumulativeUnary(v[0], v[1], v[2], limit, profile, true));
    IntVar[] vars = new IntVar[2 * inst.n()];
    System.arraycopy(v[0], 0, vars, 0, inst.n());
    System.arraycopy(v[1], 0, vars, inst.n(), inst.n());
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    // left to right: the earliest start first, as job shop searches do, so the tasks fixed first
    // end before the others
    SelectChoicePoint<IntVar> select =
        leftToRight
            ? new SimpleSelect<>(
                vars,
                new SmallestMin<>(),
                seed % 2 == 0 ? new IndomainMin<>() : new IndomainRandom<>((int) seed))
            : new SimpleSelect<>(vars, null, new IndomainRandom<>((int) seed));
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.setSolutionListener(search.getSolutionListener());
    search.setNodesOut(20_000);
    boolean found = search.labeling(store, select);
    return new long[] {
      found ? search.getSolutionListener().solutionsNo() : 0,
      search.getNodes(),
      search.getDecisions(),
      search.getWrongDecisions()
    };
  }

  @Test
  void leftToRightSearchExploresTheSameTree() {
    // the fixed tasks that end before the others are left out of the rules and the time-table
    Random random = new Random(15);
    for (int trial = 0; trial < TRIALS / 5; trial++) {
      Instance inst = instance(random, 14, trial % 3 != 0);
      long seed = random.nextLong();
      assertThat(search(inst, true, false, seed, true))
          .as("seed=%d on %s", seed, inst)
          .containsExactly(search(inst, true, true, seed, true));
    }
  }

  /**
   * An instance whose first tasks are fixed one after another, and the others start after them, or
   * sometimes earlier so that they overlap the fixed tasks.
   */
  private static Instance fixedPrefixInstance(Random random) {
    Instance rest = instance(random, 12, random.nextBoolean());
    int fixed = 1 + random.nextInt(6);
    int n = fixed + rest.n();
    int[][] starts = new int[n][];
    int[][] durations = new int[n][];
    int time = 0;
    for (int i = 0; i < fixed; i++) {
      int d = 1 + random.nextInt(5);
      time += random.nextInt(3) == 0 ? random.nextInt(3) : 0;
      starts[i] = new int[] {time};
      durations[i] = new int[] {d, d};
      // sometimes two fixed tasks overlap
      time += random.nextInt(8) == 0 ? d - 1 : d;
    }
    int shift = random.nextInt(4) == 0 ? time - 1 - random.nextInt(3) : time;
    for (int i = 0; i < rest.n(); i++) {
      int[] values = rest.starts()[i].clone();
      for (int k = 0; k < values.length; k++) {
        values[k] += shift;
      }
      starts[fixed + i] = values;
      durations[fixed + i] = rest.durations()[i];
    }
    return new Instance(starts, durations);
  }

  @Test
  void fixedTasksBeforeTheOthersChangeNothing() {
    Random random = new Random(16);
    int failures = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      Instance inst = fixedPrefixInstance(random);
      int[][] reference = rootFixpoint(inst, true, true);
      assertThat(rootFixpoint(inst, true, false)).as("%s", inst).isDeepEqualTo(reference);
      if (reference == null) {
        failures++;
      }
      if (trial % 10 == 0) {
        long seed = random.nextLong();
        assertThat(search(inst, true, false, seed, true))
            .as("seed=%d on %s", seed, inst)
            .containsExactly(search(inst, true, true, seed, true));
      }
    }
    assertThat(failures).isPositive();
  }

  @Test
  void searchExploresTheSameTree() {
    Random random = new Random(14);
    for (int trial = 0; trial < TRIALS / 10; trial++) {
      Instance inst = instance(random, 9);
      long seed = random.nextLong();
      for (boolean profile : new boolean[] {false, true}) {
        assertThat(search(inst, profile, false, seed))
            .as("profile=%s on %s", profile, inst)
            .containsExactly(search(inst, profile, true, seed));
      }
    }
  }

  @Test
  void timeLineHandlesLargeTimes() {
    // the time line adds all durations to the last earliest start time
    Store store = new Store();
    int big = IntDomain.MAX_INT - 10;
    IntVar[] s = {
      new IntVar(store, big - 30, big - 20), new IntVar(store, big - 30, big - 20),
    };
    IntVar[] d = {new IntVar(store, 6, 6), new IntVar(store, 6, 6)};
    IntVar[] r = {new IntVar(store, 1, 1), new IntVar(store, 1, 1)};
    store.impose(new CumulativeUnary(s, d, r, new IntVar(store, 1, 1), false, true));
    assertThat(store.consistency()).isTrue();
    s[0].domain.in(store.level, s[0], big - 30, big - 30);
    assertThat(store.consistency()).isTrue();
    assertThat(s[1].min()).isEqualTo(big - 24);
  }
}
