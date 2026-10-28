/*
 * UnaryTimetableTest.java
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
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Compares the unary time-table of {@link UnaryTimetable} with the sweep of {@link
 * CumulativePrimary} that {@link CumulativeUnary} ran before, on random tasks with constant
 * durations and resource uses and holes in the start domains: the same domains of the starts and
 * the limit after each call, the same failures, and the same search trees.
 */
class UnaryTimetableTest {

  /** Random instances per check; the {@code min} profile lowers it. */
  private static final int TRIALS = Integer.getInteger("unary.reasoning.trials", 2000);

  /**
   * One random instance: start domains, durations, resource uses and the limit bounds. Every two
   * tasks with a positive resource use exceed the largest limit together.
   */
  private record Instance(int[][] starts, int[] durations, int[] resources, int[] limit) {

    int n() {
      return starts.length;
    }

    IntVar[] post(Store store) {
      int n = n();
      IntVar[] v = new IntVar[3 * n + 1];
      for (int i = 0; i < n; i++) {
        v[i] = new IntVar(store, "s" + i);
        for (int x : starts[i]) {
          v[i].addDom(x, x);
        }
        v[n + i] = new IntVar(store, "d" + i, durations[i], durations[i]);
        v[2 * n + i] = new IntVar(store, "r" + i, resources[i], resources[i]);
      }
      v[3 * n] = new IntVar(store, "limit", limit[0], limit[1]);
      return v;
    }

    CumulativeUnary constraint(IntVar[] v, boolean reference) {
      int n = n();
      IntVar[] s = Arrays.copyOfRange(v, 0, n);
      IntVar[] d = Arrays.copyOfRange(v, n, 2 * n);
      IntVar[] r = Arrays.copyOfRange(v, 2 * n, 3 * n);
      return reference
          ? new SweepUnary(s, d, r, v[3 * n])
          : new CumulativeUnary(s, d, r, v[3 * n], true, true);
    }

    @Override
    public String toString() {
      return "starts="
          + Arrays.deepToString(starts)
          + " durations="
          + Arrays.toString(durations)
          + " resources="
          + Arrays.toString(resources)
          + " limit="
          + Arrays.toString(limit);
    }
  }

  /** CumulativeUnary with the general profile instead of the unary time-table. */
  private static final class SweepUnary extends CumulativeUnary {

    SweepUnary(IntVar[] s, IntVar[] d, IntVar[] r, IntVar limit) {
      super(s, d, r, limit, true, true);
    }

    @Override
    void unaryProfile(Store store) {
      profileProp(store);
    }
  }

  private static Instance instance(Random random, int maxTasks) {
    int n = 1 + random.nextInt(maxTasks);
    // resource uses 1 under limit 1, or 2 and 3 under a limit of at most 3 (sometimes below 3, so
    // a task with use 3 does not fit), with some tasks that do not use the resource
    boolean ones = random.nextBoolean();
    int[] limit =
        ones
            ? new int[] {random.nextInt(2), 1}
            : new int[] {random.nextInt(3), 2 + random.nextInt(2)};
    int[] durations = new int[n];
    int[] resources = new int[n];
    int total = 0;
    for (int i = 0; i < n; i++) {
      durations[i] =
          random.nextInt(10) == 0 ? 0 : 1 + random.nextInt(random.nextBoolean() ? 3 : 12);
      resources[i] = random.nextInt(10) == 0 ? 0 : ones ? 1 : 2 + random.nextInt(2);
      total += durations[i];
    }
    // a horizon from very tight (failures) to loose
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
    return new Instance(starts, durations, resources, limit);
  }

  /** The domains of the starts and the limit after one profile call, or null on failure. */
  private static String profileOnce(Instance inst, boolean reference) {
    Store store = new Store();
    IntVar[] v = inst.post(store);
    CumulativeUnary c = inst.constraint(v, reference);
    store.setLevel(1);
    try {
      c.unaryProfile(store);
    } catch (FailException e) {
      return null;
    }
    StringBuilder b = new StringBuilder();
    for (int i = 0; i < inst.n(); i++) {
      b.append(v[i].dom()).append(' ');
    }
    return b.append(v[3 * inst.n()].dom()).toString();
  }

  @Test
  void prunesAsTheSweepInEachCall() {
    Random random = new Random(21);
    int failures = 0;
    int pruned = 0;
    for (int trial = 0; trial < 5 * TRIALS; trial++) {
      Instance inst = instance(random, trial % 2 == 0 ? 8 : 40);
      String sweep = profileOnce(inst, true);
      assertThat(profileOnce(inst, false)).as("%s", inst).isEqualTo(sweep);
      if (sweep == null) {
        failures++;
      } else if (!sweep.equals(profileUnpruned(inst))) {
        pruned++;
      }
    }
    assertThat(failures).isPositive();
    assertThat(pruned).isPositive();
  }

  private static String profileUnpruned(Instance inst) {
    Store store = new Store();
    IntVar[] v = inst.post(store);
    StringBuilder b = new StringBuilder();
    for (int i = 0; i < inst.n(); i++) {
      b.append(v[i].dom()).append(' ');
    }
    return b.append(v[3 * inst.n()].dom()).toString();
  }

  @Test
  void ownPartEndsTheBlockOfTheOtherParts() {
    // the part of a [3, 5) touches the part of b [5, 7): for b only a counts, so b cannot start at
    // 4; for c (duration 2) they form one block [3, 7), so c cannot start at 2..6
    Instance inst =
        new Instance(
            new int[][] {{3}, {4, 5}, {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}},
            new int[] {2, 3, 2},
            new int[] {1, 1, 1},
            new int[] {1, 1});
    String sweep = profileOnce(inst, true);
    assertThat(profileOnce(inst, false)).isEqualTo(sweep);
    assertThat(sweep).isEqualTo("3 5 {0..1, 7..12} 1");
  }

  /** Solutions and nodes of a random-order search over all solutions, or the first if many. */
  private static long[] search(Instance inst, boolean reference, long seed) {
    Store store = new Store();
    IntVar[] v = inst.post(store);
    store.impose(inst.constraint(v, reference));
    IntVar[] vars = Arrays.copyOf(v, inst.n() + 1);
    vars[inst.n()] = v[3 * inst.n()];
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(vars, null, new IndomainRandom<>((int) seed));
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
  void searchExploresTheSameTree() {
    Random random = new Random(22);
    for (int trial = 0; trial < TRIALS / 5; trial++) {
      Instance inst = instance(random, 10);
      long seed = random.nextLong();
      assertThat(search(inst, false, seed))
          .as("%s", inst)
          .containsExactly(search(inst, true, seed));
    }
  }
}
