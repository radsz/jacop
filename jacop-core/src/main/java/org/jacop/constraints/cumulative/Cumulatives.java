/*
 * Cumulatives.java
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

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Cumulatives of Beldiceanu and Carlsson ("A new multi-resource cumulatives constraint with
 * negative heights", CP 2002): task i starts at {@code starts[i]}, lasts {@code durations[i]} and
 * uses {@code heights[i]} on machine {@code machines[i]}; machine k (numbered from {@code
 * firstMachine}) has the bound {@code bounds[k - firstMachine]}. At every time at which at least
 * one task runs on a machine, the sum of the heights of the tasks running there is at most its
 * bound (upper form) or at least its bound (lower form). Heights and bounds may be negative; a task
 * of duration 0 never runs. With {@code present}, task i takes part only when {@code present[i]} is
 * 1.
 *
 * <p>The propagation is a sweep over the profile of each machine. In the upper form (the lower form
 * negates heights and bounds) a task contributes its least height over its compulsory part once it
 * is on the machine and present for sure, and the least of 0 and its least height over the times at
 * which it can run there. For each task and each machine it can use, the times at which the task
 * would raise this least load above the largest bound are forbidden: they remove starts when the
 * machine is fixed, the machine when no start avoids them, and presence when no machine is left.
 * Conversely, where a compulsory part makes the bound apply and the other tasks alone exceed it, a
 * task with a negative height has to run there: it becomes present, takes the machine, and its
 * start, duration and height are bounded so that it covers those times (the rule that makes the
 * lower form require enough tasks under a demand). Bounds are pruned by the least loads under
 * compulsory parts, heights of fixed tasks by the slack of the bound under their compulsory parts,
 * and the duration of a fixed task by its first forbidden time. Under lazy clause generation each
 * pruning is explained by the least load at one time ({@link CumulativesExplanation}).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Cumulatives extends Constraint
    implements SatisfiedPresent, Copyable<Cumulatives>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final IntVar[] starts;
  final IntVar[] durations;
  final IntVar[] heights;
  final IntVar[] machines;
  final IntVar[] bounds;
  final boolean upper;
  final int firstMachine;
  final IntVar[] present;

  private final int n;
  private final int m;

  // profile events of one machine: key is time << 32 | event, with load and count deltas per event
  private final long[] keys;
  private final long[] loadDelta;
  private final int[] countDelta;

  // profile segments [time[j], time[j + 1]) of one machine, their least load and compulsory count
  private final int[] time;
  private final long[] load;
  private final int[] count;
  private int segments;

  // forbidden times [lo[f], hi[f]) of one task on one machine
  private final int[] forbiddenLo;
  private final int[] forbiddenHi;
  private int forbidden;

  // times [forcedLo, forcedHi] at which a task has to run on a machine, and its largest height
  // there
  private static final int NO_TIME = Integer.MIN_VALUE;
  private int forcedLo;
  private int forcedHi;
  private long forcedCap;

  /**
   * It creates a cumulatives constraint whose tasks are all present.
   *
   * @param starts the start times of the tasks.
   * @param durations the durations of the tasks, non-negative.
   * @param heights the heights of the tasks.
   * @param machines the machines of the tasks.
   * @param bounds the bounds of the machines.
   * @param upper true for upper bounds, false for lower bounds.
   * @param firstMachine the number of the machine of {@code bounds[0]}.
   */
  public Cumulatives(
      IntVar[] starts,
      IntVar[] durations,
      IntVar[] heights,
      IntVar[] machines,
      IntVar[] bounds,
      boolean upper,
      int firstMachine) {
    this(starts, durations, heights, machines, bounds, upper, firstMachine, null);
  }

  /**
   * It creates a cumulatives constraint with optional tasks.
   *
   * @param starts the start times of the tasks.
   * @param durations the durations of the tasks, non-negative.
   * @param heights the heights of the tasks.
   * @param machines the machines of the tasks.
   * @param bounds the bounds of the machines.
   * @param upper true for upper bounds, false for lower bounds.
   * @param firstMachine the number of the machine of {@code bounds[0]}.
   * @param present 0/1 variables, task i takes part iff present[i] = 1; null if all are present.
   */
  public Cumulatives(
      IntVar[] starts,
      IntVar[] durations,
      IntVar[] heights,
      IntVar[] machines,
      IntVar[] bounds,
      boolean upper,
      int firstMachine,
      IntVar[] present) {

    checkInputForNullness(
        new String[] {"starts", "durations", "heights", "machines", "bounds"},
        new Object[][] {starts, durations, heights, machines, bounds});
    n = starts.length;
    if (durations.length != n
        || heights.length != n
        || machines.length != n
        || (present != null && present.length != n)) {
      throw new IllegalArgumentException("Cumulatives needs the same number of entries per task.");
    }
    if (bounds.length == 0) {
      throw new IllegalArgumentException("Cumulatives needs at least one machine.");
    }
    for (IntVar d : durations) {
      if (d.min() < 0) {
        throw new IllegalArgumentException("Cumulatives needs non-negative durations.");
      }
    }
    if (present != null) {
      for (IntVar p : present) {
        if (p.min() < 0 || p.max() > 1) {
          throw new IllegalArgumentException("Cumulatives needs 0/1 presence variables.");
        }
      }
    }

    this.numberId = idNumber.incrementAndGet();
    this.starts = Arrays.copyOf(starts, n);
    this.durations = Arrays.copyOf(durations, n);
    this.heights = Arrays.copyOf(heights, n);
    this.machines = Arrays.copyOf(machines, n);
    this.bounds = Arrays.copyOf(bounds, bounds.length);
    this.upper = upper;
    this.firstMachine = firstMachine;
    this.present = present == null ? null : Arrays.copyOf(present, n);
    this.m = bounds.length;

    keys = new long[4 * n];
    loadDelta = new long[4 * n];
    countDelta = new int[4 * n];
    time = new int[4 * n + 1];
    load = new long[4 * n];
    count = new int[4 * n];
    forbiddenLo = new int[4 * n + 2];
    forbiddenHi = new int[4 * n + 2];

    this.queueIndex = 2;

    Stream<IntVar> scope =
        Stream.of(this.starts, this.durations, this.heights, this.machines, this.bounds)
            .flatMap(Arrays::stream);
    if (this.present != null) {
      scope = Stream.concat(scope, Arrays.stream(this.present));
    }
    setScope(scope.map(v -> v));
  }

  @Override
  public void impose(Store store) {
    super.impose(store);
    for (IntVar v : machines) {
      v.domain.in(store.level, v, firstMachine, firstMachine + m - 1);
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  private boolean surelyPresent(int i) {
    return present == null || present[i].min() == 1;
  }

  private boolean possiblyPresent(int i) {
    return present == null || present[i].max() == 1;
  }

  // the least height of task i in the upper form
  private int height(int i) {
    return upper ? heights[i].min() : -heights[i].max();
  }

  // the largest bound of machine k in the upper form
  private long bound(int k) {
    return upper ? bounds[k].max() : -(long) bounds[k].min();
  }

  // task i runs on machine k at least over [starts.max, starts.min + durations.min)
  private boolean compulsory(int i, int k) {
    return surelyPresent(i)
        && machines[i].singleton(firstMachine + k)
        && starts[i].max() < starts[i].min() + durations[i].min();
  }

  @Override
  public void consistency(Store store) {
    do {
      store.propagationHasOccurred = false;
      for (int k = 0; k < m; k++) {
        sweep(store, k);
      }
    } while (store.propagationHasOccurred);
  }

  private void sweep(Store store, int k) {
    int machine = firstMachine + k;
    profile(k);

    long b = bound(k);
    // the bound holds under every compulsory part
    long least = Long.MIN_VALUE;
    for (int j = 0; j < segments; j++) {
      if (count[j] > 0 && load[j] > least) {
        least = load[j];
      }
    }
    if (least != Long.MIN_VALUE) {
      if (least > b) {
        throw Store.failException;
      }
      if (upper) {
        if (least > bounds[k].min()) {
          bounds[k].domain.inMin(store.level, bounds[k], (int) least);
        }
      } else if (-least < bounds[k].max()) {
        bounds[k].domain.inMax(store.level, bounds[k], (int) -least);
      }
    }

    for (int i = 0; i < n; i++) {
      if (!possiblyPresent(i) || durations[i].max() == 0 || !machines[i].domain.contains(machine)) {
        continue;
      }
      if (compulsory(i, k)) {
        heightSlack(store, i, b);
      }
      int dmin = durations[i].min();
      if (dmin == 0 && height(i) >= 0) {
        continue;
      }
      forbiddenTimes(i, k, b);
      if (forcedLo != NO_TIME) {
        force(store, i, k);
      }
      boolean fixed = surelyPresent(i) && machines[i].singleton(machine);
      dmin = durations[i].min();
      if (dmin == 0) {
        continue;
      }
      if (fixed) {
        pruneStart(store, i, dmin);
        pruneDuration(store, i);
      } else if (forbidden > 0 && earliestStart(starts[i].dom(), dmin) == Integer.MAX_VALUE) {
        if (surelyPresent(i)) {
          machines[i].domain.inComplement(store.level, machines[i], machine);
        } else if (noMachineLeft(i, k)) {
          present[i].domain.in(store.level, present[i], 0, 0);
        }
      }
    }
  }

  // the least load profile of machine k
  private void profile(int k) {
    int e = 0;
    int machine = firstMachine + k;
    for (int i = 0; i < n; i++) {
      if (!possiblyPresent(i) || durations[i].max() == 0 || !machines[i].domain.contains(machine)) {
        continue;
      }
      int h = height(i);
      int neg = Math.min(0, h);
      int smin = starts[i].min();
      int smax = starts[i].max();
      if (neg < 0) {
        e = event(e, smin, neg, 0);
        e = event(e, smax + durations[i].max(), -neg, 0);
      }
      if (compulsory(i, k)) {
        e = event(e, smax, (long) h - neg, 1);
        e = event(e, smin + durations[i].min(), (long) neg - h, -1);
      }
    }
    Arrays.sort(keys, 0, e);
    segments = 0;
    long current = 0;
    int covering = 0;
    int a = 0;
    while (a < e) {
      int t = (int) (keys[a] >> 32);
      while (a < e && (int) (keys[a] >> 32) == t) {
        int ev = (int) keys[a];
        current += loadDelta[ev];
        covering += countDelta[ev];
        a++;
      }
      time[segments] = t;
      if (a < e) {
        load[segments] = current;
        count[segments] = covering;
        segments++;
      }
    }
    // time[segments] closes the last segment
  }

  private int event(int e, int t, long delta, int c) {
    keys[e] = ((long) t << 32) | e;
    loadDelta[e] = delta;
    countDelta[e] = c;
    return e + 1;
  }

  // the least load at segment j, 0 outside the profile
  private int segmentAt(int t) {
    if (segments == 0 || t < time[0] || t >= time[segments]) {
      return -1;
    }
    int lo = 0;
    int hi = segments - 1;
    while (lo < hi) {
      int mid = (lo + hi + 1) >>> 1;
      if (time[mid] <= t) {
        lo = mid;
      } else {
        hi = mid - 1;
      }
    }
    return lo;
  }

  // the times in [starts.min, starts.max + durations.max) at which task i cannot run on machine k
  private void forbiddenTimes(int i, int k, long b) {
    forbidden = 0;
    forcedLo = NO_TIME;
    forcedCap = Long.MAX_VALUE;
    int h = height(i);
    int neg = Math.min(0, h);
    boolean comp = compulsory(i, k);
    int smin = starts[i].min();
    int smax = starts[i].max();
    int cEnd = smin + durations[i].min();
    int end = smax + durations[i].max();
    int t = smin;
    int j = segmentAt(t);
    while (t < end) {
      long l;
      int next;
      if (j < 0) {
        l = 0;
        next = segments > 0 && t < time[0] ? time[0] : end;
      } else {
        l = load[j];
        next = time[j + 1];
      }
      next = Math.min(next, end);
      long own;
      boolean inside = comp && t >= smax && t < cEnd;
      if (inside) {
        own = h;
      } else {
        own = neg;
      }
      if (!inside && neg < 0 && j >= 0 && count[j] > 0 && l - own > b) {
        // a task runs there and the others exceed the bound, so this task runs there too
        if (forcedLo == NO_TIME) {
          forcedLo = t;
        }
        forcedHi = next - 1;
        forcedCap = Math.min(forcedCap, b - (l - own));
      }
      if (l - own + h > b) {
        if (forbidden > 0 && forbiddenHi[forbidden - 1] == t) {
          forbiddenHi[forbidden - 1] = next;
        } else {
          forbiddenLo[forbidden] = t;
          forbiddenHi[forbidden] = next;
          forbidden++;
        }
      }
      t = next;
      if (j >= 0) {
        j = j + 1 < segments ? j + 1 : -1;
      } else if (segments > 0 && t == time[0]) {
        j = 0;
      }
    }
  }

  // task i runs on machine k over [forcedLo, forcedHi] with a height of at most forcedCap
  private void force(Store store, int i, int k) {
    if (present != null && present[i].min() == 0) {
      present[i].domain.in(store.level, present[i], 1, 1);
    }
    machines[i].domain.in(store.level, machines[i], firstMachine + k, firstMachine + k);
    IntVar s = starts[i];
    IntVar d = durations[i];
    if (forcedLo < s.max()) {
      s.domain.inMax(store.level, s, forcedLo);
    }
    long latest = (long) forcedHi - d.max() + 1;
    if (latest > s.min()) {
      s.domain.inMin(store.level, s, (int) latest);
    }
    long shortest = (long) forcedHi - s.max() + 1;
    if (shortest > d.min()) {
      d.domain.inMin(store.level, d, (int) Math.min(IntDomain.MAX_INT, shortest));
    }
    if (upper) {
      if (forcedCap < heights[i].max()) {
        heights[i].domain.inMax(
            store.level, heights[i], (int) Math.max(IntDomain.MIN_INT, forcedCap));
      }
    } else if (-forcedCap > heights[i].min()) {
      heights[i].domain.inMin(
          store.level, heights[i], (int) Math.min(IntDomain.MAX_INT, -forcedCap));
    }
  }

  // a start s is excluded when [s, s + dmin) meets a forbidden time
  private void pruneStart(Store store, int i, int dmin) {
    for (int f = 0; f < forbidden; f++) {
      int lo = forbiddenLo[f] - dmin + 1;
      int hi = forbiddenHi[f] - 1;
      if (lo <= starts[i].max() && hi >= starts[i].min()) {
        starts[i].domain.inComplement(store.level, starts[i], lo, hi);
      }
    }
  }

  // a task with a fixed start ends by its first forbidden time
  private void pruneDuration(Store store, int i) {
    if (!starts[i].singleton() || durations[i].singleton()) {
      return;
    }
    int s = starts[i].value();
    for (int f = 0; f < forbidden; f++) {
      if (forbiddenHi[f] > s) {
        int limit = Math.max(forbiddenLo[f], s) - s;
        if (limit < durations[i].max()) {
          durations[i].domain.inMax(store.level, durations[i], limit);
        }
        return;
      }
    }
  }

  // the height of a task over its compulsory part keeps the least load within the bound
  private void heightSlack(Store store, int i, long b) {
    int h = height(i);
    int from = starts[i].max();
    int to = starts[i].min() + durations[i].min();
    long slack = Long.MAX_VALUE;
    for (int j = segmentAt(from); j >= 0 && j < segments && time[j] < to; j++) {
      slack = Math.min(slack, b - load[j] + h);
    }
    if (slack == Long.MAX_VALUE) {
      return;
    }
    if (upper) {
      if (slack < heights[i].max()) {
        heights[i].domain.inMax(store.level, heights[i], (int) Math.max(IntDomain.MIN_INT, slack));
      }
    } else if (-slack > heights[i].min()) {
      heights[i].domain.inMin(store.level, heights[i], (int) Math.min(IntDomain.MAX_INT, -slack));
    }
  }

  // the earliest start in dom that keeps [s, s + dmin) off the forbidden times, MAX_VALUE if none
  private int earliestStart(IntDomain dom, int dmin) {
    int v = dom.min();
    int max = dom.max();
    int f = 0;
    while (true) {
      while (f < forbidden && forbiddenHi[f] <= v) {
        f++;
      }
      if (f == forbidden || forbiddenLo[f] >= v + dmin) {
        return v;
      }
      int w = forbiddenHi[f];
      if (w > max) {
        return Integer.MAX_VALUE;
      }
      if (dom.contains(w)) {
        v = w;
      } else {
        int next = dom.nextValue(w);
        if (next <= w) {
          return Integer.MAX_VALUE;
        }
        v = next;
      }
    }
  }

  // an optional task has no machine left besides k, on which it cannot run
  private boolean noMachineLeft(int i, int k) {
    int dmin = durations[i].min();
    for (int other = 0; other < m; other++) {
      if (other == k || !machines[i].domain.contains(firstMachine + other)) {
        continue;
      }
      profile(other);
      forbiddenTimes(i, other, bound(other));
      boolean feasible =
          forbidden == 0 || earliestStart(starts[i].dom(), dmin) != Integer.MAX_VALUE;
      if (feasible) {
        profile(k);
        return false;
      }
    }
    profile(k);
    return true;
  }

  private CumulativesExplanation explanation;

  /**
   * Explains an atom by the least load of the other tasks at one time on one machine, re-derived
   * from the bounds just before it (see {@link CumulativesExplanation}).
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (explanation == null) {
      explanation = new CumulativesExplanation(this);
    }
    return explanation.explain(trail, entry, out);
  }

  /** Explains a failure: a time at which the least load under a compulsory part passes a bound. */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (explanation == null) {
      explanation = new CumulativesExplanation(this);
    }
    return explanation.explainFailure(trail, out);
  }

  @Override
  public boolean satisfied() {
    if (!grounded()) {
      return false;
    }
    for (int k = 0; k < m; k++) {
      int machine = firstMachine + k;
      long b = bounds[k].value();
      for (int i = 0; i < n; i++) {
        if (!runs(i, machine)) {
          continue;
        }
        // the load changes only at starts and ends, so checking there suffices
        if (violated(machine, b, starts[i].value())
            || violated(machine, b, starts[i].value() + durations[i].value())) {
          return false;
        }
      }
    }
    return true;
  }

  private boolean violated(int machine, long b, int t) {
    long sum = 0;
    boolean running = false;
    for (int j = 0; j < n; j++) {
      if (runs(j, machine)
          && starts[j].value() <= t
          && t < starts[j].value() + durations[j].value()) {
        sum += heights[j].value();
        running = true;
      }
    }
    return running && (upper ? sum > b : sum < b);
  }

  private boolean runs(int i, int machine) {
    return (present == null || present[i].value() == 1)
        && durations[i].value() > 0
        && machines[i].value() == machine;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : Cumulatives(").append(Arrays.toString(starts));
    result.append(", ").append(Arrays.toString(durations));
    result.append(", ").append(Arrays.toString(heights));
    result.append(", ").append(Arrays.toString(machines));
    result.append(", ").append(Arrays.toString(bounds));
    result.append(", ").append(upper ? "upper" : "lower").append(", ").append(firstMachine);
    if (present != null) {
      result.append(", ").append(Arrays.toString(present));
    }
    return result.append(")").toString();
  }

  @Override
  public Cumulatives copy(VarMap map) {
    return new Cumulatives(
        map.get(starts),
        map.get(durations),
        map.get(heights),
        map.get(machines),
        map.get(bounds),
        upper,
        firstMachine,
        present == null ? null : map.get(present));
  }
}
