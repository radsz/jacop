/*
 * WeightedCompletion.java
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

package org.jacop.constraints;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Total weighted completion time on a unary resource (Kovács and Beck, "A global constraint for
 * total weighted completion time for unary resources", Constraints 16, 2011). Tasks i with start
 * s[i] and duration d[i] do not overlap, and sum(i) w[i] * (s[i] + d[i]) is at most cost.
 *
 * <p>The lower bound on the cost is the preemptive mean busy time relaxation (Goemans): the tasks
 * that are not fixed are released at the minimum of their start and processed with preemption, at
 * every moment the released task with the largest w / d first, around the fixed tasks. In any
 * schedule a task completes half its duration after its mean busy time, so the optimum of the
 * relaxation plus sum(i) w[i] * d[i] / 2 bounds the cost. For each task i the bound is computed as
 * a function of the start t of i, with i fixed at t: it is piecewise quadratic (linear in the cases
 * of the paper), and the pieces are found by running the relaxation once per piece with t as a
 * parameter and recording, for every comparison of two event times, the shift of t up to which its
 * outcome holds. Start times whose bound exceeds the maximum of the cost are removed (holes
 * included), and the minimum of the cost becomes the largest over i of the smallest bound left.
 *
 * <p>The constraint enforces non overlap only with the fixed tasks and through the cost; post it as
 * a redundant constraint next to a unary resource (cumulative with capacity 1, disjunctive). The
 * cost is an upper bound, as in the paper, which filters only its minimum; post the sum as well
 * when it must be equal. With a constant tail q[i] after each task (sum(i) w[i] * (s[i] + d[i] +
 * q[i]) at most cost) the constant sum(i) w[i] * q[i] can be subtracted from the cost first.
 *
 * <p>On a resource of capacity m &gt; 1 (tasks with resource uses, identical machines with uses of
 * 1) the cost is bounded by the bound of Eastman, Even and Isaacs (W. L. Eastman, S. Even and I. M.
 * Isaacs, "Bounds for the optimal scheduling of n jobs on m processors", Management Science 11(2),
 * 1964) with release dates: the same relaxation on a single machine of speed m, which processes the
 * energy r[i] * d[i] of each task; without release dates it is LB1 / m + (m - 1) / (2m) * sum(i)
 * w[i] * d[i] with LB1 the single machine bound of Smith's rule. A. S. Schulz ("Scheduling to
 * minimize total weighted completion time: performance guarantees of LP-based heuristics and lower
 * bounds", IPCO 1996, LNCS 1084) gives it as LP inequalities. Fixed tasks count with their
 * completion and are left out of the relaxation, and a free task's latest start is bounded by the
 * bound of the other tasks plus its own completion.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class WeightedCompletion extends Constraint
    implements SatisfiedPresent, Copyable<WeightedCompletion>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final IntVar[] starts;
  final int[] durations;
  final int[] weights;
  final int[] resources;
  final int capacity;
  final IntVar cost;

  private final int n;

  // processing of each task in the relaxation: its duration on a unary resource (0 if it uses
  // none), its energy resources * durations on a resource of larger capacity
  private final int[] proc;

  // a resource of capacity above 1: the Eastman, Even and Isaacs bound instead of the unary sweep
  private final boolean parallel;

  // fixed tasks by start and by end, for the profile check of a parallel resource
  private final long[] endKey;
  private int fixedUsed;

  // the load of the fixed tasks of a parallel resource: from changeTime[k] on it is changeLoad[k]
  private final long[] changeTime;
  private final long[] changeLoad;
  private int changes;

  // per job of the fluid relaxation: energy left and the integral of t over its processing
  private final double[] fluidRem;
  private final double[] fluidMoment;

  // tasks of the relaxation (not fixed, positive duration) by increasing release, and their release
  private final int[] jobs;
  private final long[] release;
  private int jobCount;

  // fixed tasks with a positive duration, by increasing start
  private final int[] fixedTask;
  private int fixedCount;

  // the blocks of the simulation: fixed tasks and the task under study, as a + b * delta
  private final long[] blockStartA;
  private final long[] blockStartB;
  private final long[] blockEndA;
  private final long[] blockEndB;

  // per task: remaining processing a + b * delta and sum of e^2 - s^2 over its pieces
  // (coefficients)
  private final long[] remA;
  private final long[] remB;
  private final long[] square0;
  private final long[] square1;
  private final long[] square2;

  // heap of released tasks by decreasing w / d
  private final int[] heap;

  // sort keys: minimum start and task
  private final long[] key;

  // per task its position in jobs, and per job its weighted mean busy time without a fixed task
  private final int[] position;
  private final double[] busy;

  // the shift of the parameter up to which the comparisons of the current simulation hold
  private double limit;

  // the bound of the last simulation: q0 + q1 * delta + q2 * delta^2
  private double q0;
  private double q1;
  private double q2;

  private final IntervalDomain removed = new IntervalDomain();

  // the prefix rows of the parallel bound (Schulz's inequalities with each task's earliest
  // completion), on unless -Dorg.jacop.weightedCompletion.prefixRows=false
  static final boolean PREFIX_ROWS =
      !"false".equals(System.getProperty("org.jacop.weightedCompletion.prefixRows"));

  // the work (tasks times time points) of one bound above which the prefix rows are left out
  static final long PREFIX_WORK = Long.getLong("org.jacop.weightedCompletion.prefixWork", 40_000L);

  // the prefix rows also in the bound of the others that limits each start (one more pass per
  // task), off unless -Dorg.jacop.weightedCompletion.prefixOthers=true
  static final boolean PREFIX_OTHERS =
      "true".equals(System.getProperty("org.jacop.weightedCompletion.prefixOthers"));

  // weakened LCG reasons of the parallel bound, on unless
  // -Dorg.jacop.weightedCompletion.weakReasons=false
  static final boolean WEAK_REASONS =
      !"false".equals(System.getProperty("org.jacop.weightedCompletion.weakReasons"));

  // the halvings tried when weakening a reason
  static final int REASON_ROUNDS =
      Integer.getInteger("org.jacop.weightedCompletion.reasonRounds", 4);

  // parallel resource: the bounds the bound reads (fixed when equal), from the domains or the trail
  private final long[] lo;
  private final long[] hi;
  // the minima on the trail and the weakest minima of a reason
  private final long[] low;
  private final long[] root;
  // per task whether it is a job of the relaxation, and the bound of the others (NaN if not
  // computed)
  private final boolean[] isJob;
  private final double[] othersBound;
  private final double[] evaluated = new double[1];
  // the tasks of positive energy by decreasing w / e (Smith's order)
  private final int[] smith;
  // the pieces of the fluid schedule: task, interval and speed, and per task its pieces
  private int segments;
  private int[] segTask;
  private double[] segFrom;
  private double[] segTo;
  private long[] segSpeed;
  private int[] segOrder;
  private final int[] segFirst;
  private final int[] segFill;
  // the time points of the prefix rows and the curves A and B on them
  private double[] grid = new double[0];
  private double[] curveA = new double[0];
  private double[] curveB = new double[0];

  /**
   * It constructs a weighted completion time constraint on a unary resource.
   *
   * @param starts the start of each task.
   * @param durations the duration of each task, at least 0.
   * @param weights the weight of each task, at least 0.
   * @param cost the bound on sum(i) weights[i] * (starts[i] + durations[i]).
   */
  public WeightedCompletion(IntVar[] starts, int[] durations, int[] weights, IntVar cost) {
    this(starts, durations, ones(starts), weights, 1, cost);
  }

  /**
   * It constructs a weighted completion time constraint on a cumulative resource: task i uses
   * resources[i] units of a resource of the given capacity during its duration, and sum(i)
   * weights[i] * (starts[i] + durations[i]) is at most cost. With capacity 1 it is the unary
   * constraint (a task with resource 0 does not use the machine). With a larger capacity the cost
   * is bounded by the Eastman, Even and Isaacs bound with release dates, from a single machine of
   * speed capacity, and the starts by that bound with each task taken out at its own start.
   *
   * @param starts the start of each task.
   * @param durations the duration of each task, at least 0.
   * @param resources the resource use of each task, at least 0.
   * @param weights the weight of each task, at least 0.
   * @param capacity the capacity of the resource, at least 1.
   * @param cost the bound on sum(i) weights[i] * (starts[i] + durations[i]).
   */
  public WeightedCompletion(
      IntVar[] starts, int[] durations, int[] resources, int[] weights, int capacity, IntVar cost) {

    if (starts == null
        || durations == null
        || weights == null
        || resources == null
        || durations.length != starts.length
        || weights.length != starts.length
        || resources.length != starts.length) {
      throw new IllegalArgumentException(
          "WeightedCompletion needs one duration, one resource use and one weight per task.");
    }
    checkInputForNullness(new String[] {"starts", "cost"}, starts, new Object[] {cost});
    if (capacity < 1) {
      throw new IllegalArgumentException("WeightedCompletion needs a capacity of at least 1.");
    }
    for (int i = 0; i < starts.length; i++) {
      if (durations[i] < 0 || weights[i] < 0 || resources[i] < 0) {
        throw new IllegalArgumentException(
            "WeightedCompletion needs durations, resource uses and weights of at least 0.");
      }
      if (capacity > 1 && (long) durations[i] * resources[i] > IntDomain.MAX_INT) {
        throw new IllegalArgumentException(
            "WeightedCompletion needs durations * resource uses within the integer range.");
      }
    }
    if (capacity > 1 && starts.length >= 1 << 24) {
      throw new IllegalArgumentException("WeightedCompletion takes at most 2^24 - 1 tasks.");
    }

    this.numberId = idNumber.incrementAndGet();
    this.starts = Arrays.copyOf(starts, starts.length);
    this.durations = Arrays.copyOf(durations, durations.length);
    this.weights = Arrays.copyOf(weights, weights.length);
    this.resources = Arrays.copyOf(resources, resources.length);
    this.capacity = capacity;
    this.parallel = capacity > 1;
    this.cost = cost;
    this.n = starts.length;
    this.proc = new int[n];
    for (int i = 0; i < n; i++) {
      if (parallel) {
        proc[i] = durations[i] * resources[i];
      } else {
        proc[i] = resources[i] > 0 ? durations[i] : 0;
      }
    }
    this.endKey = new long[parallel ? n : 0];
    this.changeTime = new long[parallel ? 2 * n : 0];
    this.changeLoad = new long[parallel ? 2 * n : 0];
    this.fluidRem = new double[parallel ? n : 0];
    this.fluidMoment = new double[parallel ? n : 0];
    int pn = parallel ? n : 0;
    this.lo = new long[pn];
    this.hi = new long[pn];
    this.low = new long[pn];
    this.root = new long[pn];
    this.isJob = new boolean[pn];
    this.othersBound = new double[pn];
    this.segFirst = new int[pn + 1];
    this.segFill = new int[pn];
    int segs = parallel ? 4 * n + 4 : 0;
    this.segTask = new int[segs];
    this.segFrom = new double[segs];
    this.segTo = new double[segs];
    this.segSpeed = new long[segs];
    this.segOrder = new int[segs];
    this.smith =
        parallel
            ? IntStream.range(0, n)
                .filter(i -> proc[i] > 0)
                .boxed()
                .sorted(
                    (a, b) -> {
                      int c =
                          Long.compare((long) weights[b] * proc[a], (long) weights[a] * proc[b]);
                      return c != 0 ? c : Integer.compare(a, b);
                    })
                .mapToInt(Integer::intValue)
                .toArray()
            : new int[0];

    this.jobs = new int[n];
    this.release = new long[n];
    this.fixedTask = new int[n];
    this.blockStartA = new long[n + 1];
    this.blockStartB = new long[n + 1];
    this.blockEndA = new long[n + 1];
    this.blockEndB = new long[n + 1];
    this.remA = new long[n];
    this.remB = new long[n];
    this.square0 = new long[n];
    this.square1 = new long[n];
    this.square2 = new long[n];
    this.heap = new int[n];
    this.key = new long[n];
    this.position = new int[n];
    this.busy = new double[n];

    this.queueIndex = 3;

    setScope(Stream.concat(Arrays.stream(starts), Stream.of(cost)));
  }

  // the bounds of the starts change only by narrowing, so their sum tells whether one changed
  private long boundsSum() {
    long sum = 0;
    for (IntVar s : starts) {
      sum += (long) s.max() - s.min();
    }
    return sum;
  }

  private static int[] ones(IntVar[] starts) {
    int[] one = new int[starts == null ? 0 : starts.length];
    Arrays.fill(one, 1);
    return one;
  }

  @Override
  public void consistency(Store store) {

    for (int i = 0; i < n; i++) {
      if (durations[i] > 0 && resources[i] > capacity) {
        throw Store.failException;
      }
    }
    if (parallel) {
      // the bound reads the minima of the starts and which tasks are fixed; it runs again when a
      // start changed (one it pruned, or the cost when it is also a start)
      long before;
      do {
        before = boundsSum();
        consistencyParallel(store);
      } while (boundsSum() != before);
      return;
    }

    boolean again;
    do {
      // the relaxation reads only the bounds of the starts, so it runs again only when they change
      again = false;

      double constant = collect();
      // the bound with no task fixed at a parameter: tasks of the relaxation and the others
      limit = Double.POSITIVE_INFINITY;
      simulate(-1, 0);
      double bound = q0 + constant;
      double best = bound;
      double totalWeight = 0;
      for (int k = 0; k < jobCount; k++) {
        int j = jobs[k];
        position[j] = k;
        busy[k] = weights[j] / (2.0 * proc[j]) * square0[k];
        totalWeight += weights[j];
      }

      for (int i = 0; i < n; i++) {
        IntVar s = starts[i];
        if (s.singleton()) {
          continue;
        }
        int min = s.min();
        int max = s.max();
        if (proc[i] == 0) {
          // the bound grows by weights[i] for each unit of start
          if (weights[i] > 0) {
            double others = bound - (double) weights[i] * ((long) s.min() + durations[i]);
            long last =
                (long) Math.floor((cost.max() - others + slack(cost.max())) / weights[i])
                    - durations[i];
            if (last < s.max()) {
              s.domain.inMax(store.level, s, (int) Math.max(last, IntDomain.MIN_INT));
            }
          }
        } else if (fixedLimit(i, bound, totalWeight)) {
          // no start of i can raise the bound above the maximum of the cost
          removeOverlaps(store, i);
        } else {
          best = Math.max(best, sweep(store, i, constant));
        }
        again |= s.min() != min || s.max() != max;
      }

      double lower = Math.ceil(best - slack(best));
      if (lower > IntDomain.MAX_INT) {
        throw Store.failException;
      }
      if (lower > cost.min()) {
        cost.domain.inMin(store.level, cost, (int) lower);
      }

    } while (again);
  }

  /**
   * It tells if the bound with task i at its latest start stays within the maximum of the cost. The
   * bound with i at t is at most the bound without i plus w * (t + d) of i, plus a delay of d and
   * the fixed tasks after the earliest start of i for every other task: the schedule of the
   * relaxation with the pieces of i removed and the others from t on moved right is a schedule of
   * the relaxation with i at t.
   */
  private boolean fixedLimit(int i, double bound, double totalWeight) {
    int k = position[i];
    long est = starts[i].min();
    long delay = durations[i];
    for (int f = 0; f < fixedCount; f++) {
      int task = fixedTask[f];
      if ((long) starts[task].value() + durations[task] > est) {
        delay += durations[task];
      }
    }
    double highest =
        bound
            - busy[k]
            - weights[i] * durations[i] / 2.0
            + (double) weights[i] * ((long) starts[i].max() + durations[i])
            + (totalWeight - weights[i]) * delay;
    return highest + slack(highest) < cost.max();
  }

  // it removes the starts of i at which i overlaps a fixed task
  private void removeOverlaps(Store store, int i) {
    IntVar s = starts[i];
    removed.clear();
    for (int f = 0; f < fixedCount; f++) {
      int task = fixedTask[f];
      long fs = starts[task].value();
      long from = Math.max(fs - durations[i] + 1, s.min());
      long to = Math.min(fs + durations[task] - 1, s.max());
      remove(from, to);
    }
    if (!removed.isEmpty()) {
      s.domain.inComplement(store.level, s, removed);
    }
  }

  // tolerance of the floating point bound, far below the unit of the cost
  private static double slack(double value) {
    return 1e-9 * (1.0 + Math.abs(value));
  }

  /**
   * It sorts the tasks of the relaxation by release and the fixed tasks by start, and fails if two
   * fixed tasks overlap.
   *
   * @return the part of the bound that does not depend on the relaxation: sum of w * (s + d) of the
   *     fixed tasks, w * min(s) of the free tasks without duration and w * d / 2 of the others.
   */
  private double collect() {
    long twice = 0;
    jobCount = 0;
    fixedCount = 0;
    for (int i = 0; i < n; i++) {
      IntVar s = starts[i];
      if (s.singleton()) {
        twice += 2L * weights[i] * ((long) s.value() + durations[i]);
        if (proc[i] > 0) {
          fixedTask[fixedCount++] = i;
        }
      } else if (proc[i] == 0) {
        twice += 2L * weights[i] * ((long) s.min() + durations[i]);
      } else {
        twice += (long) weights[i] * durations[i];
        jobs[jobCount++] = i;
      }
    }
    sortBy(jobs, jobCount);
    sortBy(fixedTask, fixedCount);
    for (int k = 1; k < fixedCount; k++) {
      int a = fixedTask[k - 1];
      if ((long) starts[a].value() + durations[a] > starts[fixedTask[k]].value()) {
        throw Store.failException;
      }
    }
    for (int k = 0; k < jobCount; k++) {
      release[k] = starts[jobs[k]].min();
    }
    return twice / 2.0;
  }

  private void sortBy(int[] tasks, int count) {
    for (int k = 0; k < count; k++) {
      int t = tasks[k];
      key[k] = ((long) starts[t].min() << 32) | t;
    }
    Arrays.sort(key, 0, count);
    for (int k = 0; k < count; k++) {
      tasks[k] = (int) key[k];
    }
  }

  /**
   * It finds, for task i, the bound as a function of its start over its domain, removes the starts
   * whose bound exceeds the maximum of the cost and returns the smallest bound left.
   */
  private double sweep(Store store, int i, double constant) {
    IntVar s = starts[i];
    int p = durations[i];
    double max = cost.max();
    removed.clear();
    double least = Double.POSITIVE_INFINITY;

    long lo = s.min();
    long end = s.max();
    int f = 0;
    while (lo <= end) {
      // the next fixed task that ends after lo cuts the starts of i overlapping it
      while (f < fixedCount
          && (long) starts[fixedTask[f]].value() + durations[fixedTask[f]] <= lo) {
        f++;
      }
      long hi = end;
      long resume = end + 1;
      if (f < fixedCount) {
        long fs = starts[fixedTask[f]].value();
        long fe = fs + durations[fixedTask[f]];
        if (fs - p + 1 <= lo) {
          // lo overlaps the fixed task
          remove(lo, Math.min(fe - 1, end));
          lo = fe;
          continue;
        }
        hi = Math.min(end, fs - p);
        resume = fs - p + 1;
      }

      long t = lo;
      while (t <= hi) {
        limit = (double) hi - t;
        simulate(i, t);
        double c0 = q0 + constant + (double) weights[i] * (t + p) - (double) weights[i] * p / 2.0;
        double c1 = q1 + weights[i];
        double c2 = q2;
        long length = (long) Math.floor(limit);
        least = Math.min(least, prune(t, length, c0, c1, c2, max));
        t += Math.max(length, 1);
      }
      lo = resume;
    }

    if (!removed.isEmpty()) {
      s.domain.inComplement(store.level, s, removed);
    }
    return least;
  }

  private void remove(long from, long to) {
    if (from <= to) {
      removed.unionAdapt((int) from, (int) to);
    }
  }

  /**
   * It removes the starts t + delta, 0 &le; delta &le; length, with c0 + c1 * delta + c2 * delta^2
   * above max and returns the smallest bound of the others.
   */
  private double prune(long t, long length, double c0, double c1, double c2, double max) {
    double tol = slack(max);
    double limitValue = max + tol;
    // feasible deltas: one interval [a, b], or two [0, a] and [b, length] when concave
    long a;
    long b;
    boolean outside;
    if (Math.abs(c2) < 1e-12) {
      c2 = 0;
      outside = false;
      if (c1 > 0) {
        a = 0;
        b = (long) Math.floor((limitValue - c0) / c1);
      } else if (c1 < 0) {
        a = (long) Math.ceil((limitValue - c0) / c1);
        b = length;
      } else {
        a = 0;
        b = c0 <= limitValue ? length : -1;
      }
    } else {
      double disc = c1 * c1 - 4 * c2 * (c0 - limitValue);
      if (c2 > 0) {
        outside = false;
        if (disc < 0) {
          a = 0;
          b = -1;
        } else {
          double r = Math.sqrt(disc);
          a = (long) Math.ceil((-c1 - r) / (2 * c2));
          b = (long) Math.floor((-c1 + r) / (2 * c2));
        }
      } else {
        if (disc < 0) {
          outside = false;
          a = 0;
          b = length;
        } else {
          outside = true;
          double r = Math.sqrt(disc);
          // with c2 < 0 the larger root comes from -c1 - r
          a = (long) Math.floor((-c1 + r) / (2 * c2));
          b = (long) Math.ceil((-c1 - r) / (2 * c2));
        }
      }
    }

    double least = Double.POSITIVE_INFINITY;
    if (!outside) {
      a = Math.max(a, 0);
      b = Math.min(b, length);
      // the roots are rounded, so the ends are checked on the values themselves
      while (a > 0 && value(c0, c1, c2, a - 1) <= limitValue) {
        a--;
      }
      while (a <= b && value(c0, c1, c2, a) > limitValue) {
        a++;
      }
      while (b < length && value(c0, c1, c2, b + 1) <= limitValue) {
        b++;
      }
      while (b >= a && value(c0, c1, c2, b) > limitValue) {
        b--;
      }
      if (a > b) {
        remove(t, t + length);
        return least;
      }
      remove(t, t + a - 1);
      remove(t + b + 1, t + length);
      least = smallest(c0, c1, c2, a, b);
    } else {
      // concave: [0, a] and [b, length] are feasible
      a = Math.min(a, length);
      b = Math.max(b, 0);
      while (a >= 0 && value(c0, c1, c2, a) > limitValue) {
        a--;
      }
      while (a + 1 < b && value(c0, c1, c2, a + 1) <= limitValue) {
        a++;
      }
      while (b <= length && value(c0, c1, c2, b) > limitValue) {
        b++;
      }
      while (b - 1 > a && value(c0, c1, c2, b - 1) <= limitValue) {
        b--;
      }
      remove(t + a + 1, t + Math.min(b, length + 1) - 1);
      if (a >= 0) {
        least = Math.min(least, smallest(c0, c1, c2, 0, a));
      }
      if (b <= length) {
        least = Math.min(least, smallest(c0, c1, c2, b, length));
      }
    }
    return least;
  }

  private static double value(double c0, double c1, double c2, long delta) {
    double d = (double) delta;
    return c0 + c1 * d + c2 * d * d;
  }

  // the smallest value over the integers of [a, b]
  private static double smallest(double c0, double c1, double c2, long a, long b) {
    double m = Math.min(value(c0, c1, c2, a), value(c0, c1, c2, b));
    if (c2 > 0) {
      double vertex = -c1 / (2 * c2);
      if (vertex > a && vertex < b) {
        long v = (long) Math.floor(vertex);
        m = Math.min(m, Math.min(value(c0, c1, c2, v), value(c0, c1, c2, v + 1)));
      }
    }
    return m;
  }

  /**
   * It runs the preemptive relaxation with task i fixed at t + delta (none for i &lt; 0) and sets
   * q0 + q1 * delta + q2 * delta^2 to the weighted mean busy time of the tasks of the relaxation
   * other than i. Event times are a + b * delta; each comparison keeps the outcome it has just
   * above delta = 0 and lowers limit to the shift where the outcome would change.
   */
  private void simulate(int i, long t) {
    simulate(i, t, true);
  }

  /**
   * As {@link #simulate(int, long)}; without blocking, task i is only left out of the relaxation
   * and does not occupy the machine.
   */
  private void simulate(int i, long t, boolean blocking) {
    // blocks: fixed tasks and task i, in start order (they do not overlap)
    int blocks = 0;
    boolean placed = i < 0 || !blocking;
    for (int k = 0; k < fixedCount; k++) {
      int f = fixedTask[k];
      long fs = starts[f].value();
      if (!placed && t < fs) {
        blockStartA[blocks] = t;
        blockStartB[blocks] = 1;
        blockEndA[blocks] = t + durations[i];
        blockEndB[blocks++] = 1;
        placed = true;
      }
      blockStartA[blocks] = fs;
      blockStartB[blocks] = 0;
      blockEndA[blocks] = fs + durations[f];
      blockEndB[blocks++] = 0;
    }
    if (!placed) {
      blockStartA[blocks] = t;
      blockStartB[blocks] = 1;
      blockEndA[blocks] = t + durations[i];
      blockEndB[blocks++] = 1;
    }

    for (int k = 0; k < jobCount; k++) {
      int j = jobs[k];
      remA[k] = proc[j];
      remB[k] = 0;
      square0[k] = 0;
      square1[k] = 0;
      square2[k] = 0;
    }

    int size = 0;
    int next = 0;
    int block = 0;
    long curA = 0;
    long curB = 0;
    boolean started = false;
    while (true) {
      if (!started) {
        // skip i itself among the jobs
        while (next < jobCount && jobs[next] == i) {
          next++;
        }
        if (next == jobCount) {
          break;
        }
        curA = release[next];
        curB = 0;
        started = true;
      }
      // release the jobs available now
      while (next < jobCount && (jobs[next] == i || compare(release[next], 0, curA, curB) <= 0)) {
        if (jobs[next] != i) {
          size = push(size, next);
        }
        next++;
      }
      // the machine is busy with a block starting now (or before, after an idle jump)
      if (block < blocks && compare(blockStartA[block], blockStartB[block], curA, curB) <= 0) {
        if (compare(blockEndA[block], blockEndB[block], curA, curB) > 0) {
          curA = blockEndA[block];
          curB = blockEndB[block];
        }
        block++;
        continue;
      }
      if (size == 0) {
        if (next == jobCount) {
          break;
        }
        curA = release[next];
        curB = 0;
        continue;
      }
      int k = heap[0];
      long endA = curA + remA[k];
      long endB = curB + remB[k];
      // the next event: a release or a block start
      boolean hasEvent = false;
      long evA = 0;
      long evB = 0;
      if (next < jobCount) {
        evA = release[next];
        evB = 0;
        hasEvent = true;
      }
      if (block < blocks
          && (!hasEvent || compare(blockStartA[block], blockStartB[block], evA, evB) < 0)) {
        evA = blockStartA[block];
        evB = blockStartB[block];
        hasEvent = true;
      }
      if (!hasEvent || compare(endA, endB, evA, evB) <= 0) {
        piece(k, curA, curB, endA, endB);
        size = pop(size);
        curA = endA;
        curB = endB;
      } else {
        piece(k, curA, curB, evA, evB);
        remA[k] -= evA - curA;
        remB[k] -= evB - curB;
        curA = evA;
        curB = evB;
      }
    }

    q0 = 0;
    q1 = 0;
    q2 = 0;
    for (int k = 0; k < jobCount; k++) {
      int j = jobs[k];
      if (j == i || weights[j] == 0) {
        continue;
      }
      double factor = weights[j] / (2.0 * proc[j]);
      q0 += factor * square0[k];
      q1 += factor * square1[k];
      q2 += factor * square2[k];
    }
  }

  // a piece of job k from s to e: e^2 - s^2 as a polynomial in delta
  private void piece(int k, long sA, long sB, long eA, long eB) {
    square0[k] += eA * eA - sA * sA;
    square1[k] += 2 * (eA * eB - sA * sB);
    square2[k] += eB * eB - sB * sB;
  }

  /**
   * It compares x = xa + xb * delta with y = ya + yb * delta just above delta = 0 and lowers limit
   * to the delta where they meet if the outcome changes there.
   */
  private int compare(long xa, long xb, long ya, long yb) {
    long a = xa - ya;
    long b = xb - yb;
    if (a == 0) {
      return Long.signum(b);
    }
    if (b != 0 && Long.signum(a) != Long.signum(b)) {
      double meet = (double) a / -b;
      if (meet < limit) {
        limit = meet;
      }
    }
    return Long.signum(a);
  }

  // job k before job l: larger w / d first, then earlier release
  private boolean before(int k, int l) {
    int a = jobs[k];
    int b = jobs[l];
    long left = (long) weights[a] * proc[b];
    long right = (long) weights[b] * proc[a];
    return left > right || left == right && k < l;
  }

  private int push(int size, int k) {
    int c = size;
    while (c > 0) {
      int p = (c - 1) >>> 1;
      if (!before(k, heap[p])) {
        break;
      }
      heap[c] = heap[p];
      c = p;
    }
    heap[c] = k;
    return size + 1;
  }

  private int pop(int size) {
    int last = heap[size - 1];
    int m = size - 1;
    int c = 0;
    while (true) {
      int l = 2 * c + 1;
      if (l >= m) {
        break;
      }
      int r = l + 1;
      int better = r < m && before(heap[r], heap[l]) ? r : l;
      if (!before(heap[better], last)) {
        break;
      }
      heap[c] = heap[better];
      c = better;
    }
    heap[c] = last;
    return m;
  }

  /**
   * The bound of Eastman, Even and Isaacs (1964) for a resource of capacity m &gt; 1, with release
   * dates and fixed tasks: any schedule is a fluid schedule that processes the energy e = r * d of
   * each free task after its earliest start within the capacity the fixed tasks leave. The weighted
   * mean busy time over the fluid schedules is smallest for the greedy schedule that gives all of
   * it to the released task with the largest w / e ({@link #fluid(int)}), and a task completes d /
   * 2 after its mean busy time in a schedule without preemption, so sum(i) w * (M + d / 2) bounds
   * the cost. Without release dates and fixed tasks this is LB1 / m + (m - 1) / (2m) * sum(i) w * d
   * with LB1 the bound of Smith's rule (Eastman, Even and Isaacs; Schulz, IPCO 1996, for the LP
   * form). The rows of the prefixes of Smith's order are tightened with the earliest completion of
   * each task ({@link #prefixRows(int)}). A free task i at start t adds w * (t + d) to the bound of
   * the others, which removes the starts above the largest fitting t.
   */
  private void consistencyParallel(Store store) {
    for (int i = 0; i < n; i++) {
      lo[i] = starts[i].min();
      hi[i] = starts[i].max();
    }
    if (overloaded()) {
      throw Store.failException;
    }
    double max = cost.max();
    double[] result = evaluate(max, -1);
    double best = result[0];
    for (int i = 0; i < n; i++) {
      IntVar s = starts[i];
      if (s.singleton() || weights[i] == 0 || Double.isNaN(othersBound[i])) {
        continue;
      }
      long latest = latest(i, max);
      if (latest < s.max()) {
        s.domain.inMax(store.level, s, (int) Math.max(latest, IntDomain.MIN_INT));
      }
      best = Math.max(best, othersBound[i] + (double) weights[i] * (lo[i] + durations[i]));
    }

    double lower = Math.ceil(best - slack(best));
    if (lower > IntDomain.MAX_INT) {
      throw Store.failException;
    }
    if (lower > cost.min()) {
      cost.domain.inMin(store.level, cost, (int) lower);
    }
  }

  // the latest start of free task i that keeps the bound within max
  private long latest(int i, double max) {
    double others = othersBound[i];
    return (long) Math.floor((max - others + slack(max)) / weights[i]) - durations[i];
  }

  /**
   * It computes, from the bounds in lo and hi (the fixed tasks are those with lo == hi), the bound
   * of all tasks and, in othersBound, the bound of the tasks other than i for each free task i of
   * positive weight whose latest start the bound may limit (NaN for the others). Only task only (at
   * least 0) is computed when given.
   *
   * @return the bound in element 0
   */
  private double[] evaluate(double max, int only) {
    // before sortBy, which reuses the keys of the fixed tasks
    profile();
    long twice = 0;
    jobCount = 0;
    for (int i = 0; i < n; i++) {
      isJob[i] = false;
      if (lo[i] == hi[i]) {
        twice += 2L * weights[i] * (lo[i] + durations[i]);
      } else if (proc[i] == 0) {
        twice += 2L * weights[i] * (lo[i] + durations[i]);
      } else {
        twice += (long) weights[i] * durations[i];
        jobs[jobCount++] = i;
        isJob[i] = true;
      }
    }
    double constant = twice / 2.0;
    sortByLow(jobs, jobCount);
    double bound = constant + relaxation(-1);
    evaluated[0] = bound;
    for (int i = 0; i < n; i++) {
      othersBound[i] = Double.NaN;
      int w = weights[i];
      if (lo[i] == hi[i] || w == 0 || only >= 0 && i != only) {
        continue;
      }
      int d = durations[i];
      if (proc[i] == 0) {
        othersBound[i] = bound - (double) w * (lo[i] + d);
      } else {
        // the term of i in the bound is at least w * (min + d / 2)
        double highest = bound - w * (lo[i] + d / 2.0) + (double) w * (hi[i] + d);
        if (only < 0 && highest + slack(highest) <= max) {
          continue;
        }
        othersBound[i] = constant - w * d / 2.0 + relaxation(i);
      }
    }
    return evaluated;
  }

  // the relaxation of the free tasks other than skip: the fluid bound, with the prefix rows when
  // they are on and small enough
  private double relaxation(int skip) {
    double value = fluid(skip);
    if (!PREFIX_ROWS
        || skip >= 0 && !PREFIX_OTHERS
        || (long) jobCount * (2L * segments + 2L * jobCount) > PREFIX_WORK) {
      return value;
    }
    return Math.max(value, prefixRows(skip));
  }

  private void sortByLow(int[] tasks, int count) {
    for (int k = 0; k < count; k++) {
      int t = tasks[k];
      key[k] = (lo[t] << 32) | t;
    }
    Arrays.sort(key, 0, count);
    for (int k = 0; k < count; k++) {
      tasks[k] = (int) key[k];
    }
  }

  /**
   * It builds the free capacity left by the fixed tasks as change points: from changeTime[k] on the
   * fixed tasks use changeLoad[k] units. It reads the fixed tasks sorted in key and endKey by
   * {@link #overloaded()}.
   */
  private void profile() {
    changes = 0;
    int e = 0;
    long load = 0;
    for (int k = 0; k < fixedUsed; k++) {
      long time = key[k] >> 24;
      while (e < fixedUsed && endKey[e] >> 24 <= time) {
        long end = endKey[e] >> 24;
        load -= resources[(int) (endKey[e++] & 0xFFFFFF)];
        change(end, load);
      }
      load += resources[(int) (key[k] & 0xFFFFFF)];
      change(time, load);
    }
    while (e < fixedUsed) {
      long end = endKey[e] >> 24;
      load -= resources[(int) (endKey[e++] & 0xFFFFFF)];
      change(end, load);
    }
  }

  private void change(long time, long load) {
    if (changes > 0 && changeTime[changes - 1] == time) {
      changeLoad[changes - 1] = load;
    } else {
      changeTime[changes] = time;
      changeLoad[changes++] = load;
    }
  }

  /**
   * The fluid relaxation of a parallel resource: the free tasks other than i are released at the
   * minimum of their start and share the capacity the fixed tasks leave, all of it going at every
   * moment to the released task with the largest w / e (e = r * d its energy). This greedy schedule
   * minimises the weighted mean busy time over the fluid schedules, whatever the capacity profile
   * (exchange argument), and every schedule of the tasks is one. The pieces of the schedule are
   * kept for {@link #prefixRows(int)}.
   *
   * @return sum(j) w[j] * M[j] over the free tasks j other than i, M[j] the mean busy time.
   */
  private double fluid(int i) {
    for (int k = 0; k < jobCount; k++) {
      fluidRem[k] = proc[jobs[k]];
      fluidMoment[k] = 0;
    }
    segments = 0;
    int size = 0;
    int next = 0;
    int change = 0;
    long load = 0;
    double cur = Double.NEGATIVE_INFINITY;
    while (true) {
      while (next < jobCount && jobs[next] == i) {
        next++;
      }
      if (size == 0) {
        if (next == jobCount) {
          break;
        }
        cur = Math.max(cur, lo[jobs[next]]);
      }
      while (next < jobCount && (jobs[next] == i || lo[jobs[next]] <= cur)) {
        if (jobs[next] != i) {
          size = push(size, next);
        }
        next++;
      }
      while (change < changes && changeTime[change] <= cur) {
        load = changeLoad[change++];
      }
      double event = Double.POSITIVE_INFINITY;
      if (next < jobCount) {
        event = lo[jobs[next]];
      }
      if (change < changes) {
        event = Math.min(event, (double) changeTime[change]);
      }
      long speed = capacity - load;
      if (speed <= 0) {
        cur = event;
        continue;
      }
      int k = heap[0];
      double finish = cur + fluidRem[k] / speed;
      double end = Math.min(finish, event);
      // the energy speed * (end - cur) processed at the mean time (cur + end) / 2
      fluidMoment[k] += speed * (end - cur) * (cur + end) / 2;
      addSegment(jobs[k], cur, end, speed);
      if (finish <= event) {
        fluidRem[k] = 0;
        size = pop(size);
      } else {
        fluidRem[k] -= speed * (end - cur);
      }
      cur = end;
    }
    double total = 0;
    for (int k = 0; k < jobCount; k++) {
      int j = jobs[k];
      if (j != i && weights[j] > 0) {
        total += weights[j] * fluidMoment[k] / proc[j];
      }
    }
    return total;
  }

  private void addSegment(int task, double from, double to, long speed) {
    if (to <= from) {
      return;
    }
    if (segments == segTask.length) {
      int size = 2 * segments;
      segTask = Arrays.copyOf(segTask, size);
      segFrom = Arrays.copyOf(segFrom, size);
      segTo = Arrays.copyOf(segTo, size);
      segSpeed = Arrays.copyOf(segSpeed, size);
      segOrder = Arrays.copyOf(segOrder, size);
    }
    segTask[segments] = task;
    segFrom[segments] = from;
    segTo[segments] = to;
    segSpeed[segments++] = speed;
  }

  /**
   * The rows of the prefixes of Smith's order (largest w / e first) with each task's earliest
   * completion. With y[j] = e[j] * M[j], any schedule satisfies y(S) &gt;= F(S) for a set S of free
   * tasks, F(S) = t0 * e(S) + integral from t0 of (e(S) - U(t)) dt, where U(t) is any upper bound
   * on the energy of S processed by t and t0 the earliest release: the work processed by t is at
   * most both the work of the fluid schedule of S alone (the earliest one, A(t), which is the fluid
   * schedule of all the tasks restricted to S when S is a prefix) and sum(j in S) r[j] * min(d[j],
   * max(0, t - est[j])), each task's own earliest processing (B(t)), so U = min(A, B). With A alone
   * F(S) is the parallel inequality of Schulz (IPCO 1996) with release dates, with B alone it is
   * the sum of the earliest completions. Since the costs c = w / e decrease along the order, sum(j)
   * w[j] * M[j] = sum(k) (c[k] - c[k + 1]) * y(S_k) &gt;= sum(k) (c[k] - c[k + 1]) * F(S_k) (the
   * greedy dual of the rows, as in Queyranne's polytope), which is the fluid bound with A alone.
   *
   * @return sum(j) w[j] * M[j] bounded from below, over the free tasks other than skip
   */
  private double prefixRows(int skip) {
    // the times at which A or B may bend: the pieces of the fluid schedule, the earliest starts
    // and ends
    int points = 0;
    int need = 2 * segments + 2 * jobCount;
    if (grid.length < need) {
      grid = new double[need];
      curveA = new double[need];
      curveB = new double[need];
    }
    for (int g = 0; g < segments; g++) {
      grid[points++] = segFrom[g];
      grid[points++] = segTo[g];
    }
    for (int k = 0; k < jobCount; k++) {
      int j = jobs[k];
      if (j != skip) {
        grid[points++] = lo[j];
        grid[points++] = (double) lo[j] + durations[j];
      }
    }
    if (points == 0) {
      return 0;
    }
    Arrays.sort(grid, 0, points);
    int m = 1;
    for (int g = 1; g < points; g++) {
      if (grid[g] != grid[m - 1]) {
        grid[m++] = grid[g];
      }
    }
    Arrays.fill(curveA, 0, m, 0);
    Arrays.fill(curveB, 0, m, 0);
    // the pieces of each task, in time order
    Arrays.fill(segFirst, 0);
    for (int g = 0; g < segments; g++) {
      segFirst[segTask[g] + 1]++;
    }
    for (int t = 0; t < n; t++) {
      segFirst[t + 1] += segFirst[t];
    }
    System.arraycopy(segFirst, 0, segFill, 0, n);
    for (int g = 0; g < segments; g++) {
      segOrder[segFill[segTask[g]]++] = g;
    }
    double t0 = grid[0];
    double total = 0;
    double energy = 0;
    double previous = 0;
    for (int j : smith) {
      if (!isJob[j] || j == skip) {
        continue;
      }
      // A and B of the prefix with j
      int p = segFirst[j];
      int last = segFirst[j + 1];
      double done = 0;
      for (int g = 0; g < m; g++) {
        double t = grid[g];
        while (p < last && segTo[segOrder[p]] <= t) {
          int sg = segOrder[p++];
          done += segSpeed[sg] * (segTo[sg] - segFrom[sg]);
        }
        double part = 0;
        if (p < last && segFrom[segOrder[p]] < t) {
          part = segSpeed[segOrder[p]] * (t - segFrom[segOrder[p]]);
        }
        curveA[g] += done + part;
        double own = Math.min(durations[j], Math.max(0, t - lo[j]));
        curveB[g] += (double) resources[j] * own;
      }
      energy += proc[j];
      double rows = t0 * energy;
      for (int g = 0; g + 1 < m; g++) {
        rows +=
            area(grid[g], grid[g + 1], curveA[g], curveA[g + 1], curveB[g], curveB[g + 1], energy);
      }
      total += (double) weights[j] / proc[j] * (rows - previous);
      previous = rows;
    }
    return total;
  }

  // the integral over [x0, x1] of e - min(A, B), A and B linear
  private static double area(
      double x0, double x1, double a0, double a1, double b0, double b1, double e) {
    double f0 = a0 - b0;
    double f1 = a1 - b1;
    if (f0 <= 0 && f1 <= 0) {
      return (x1 - x0) * (e - (a0 + a1) / 2);
    }
    if (f0 >= 0 && f1 >= 0) {
      return (x1 - x0) * (e - (b0 + b1) / 2);
    }
    double lambda = f0 / (f0 - f1);
    double xm = x0 + lambda * (x1 - x0);
    double vm = a0 + lambda * (a1 - a0);
    double low0 = Math.min(a0, b0);
    double low1 = Math.min(a1, b1);
    return (xm - x0) * (e - (low0 + vm) / 2) + (x1 - xm) * (e - (vm + low1) / 2);
  }

  /**
   * It checks the profile of the fixed tasks of a parallel resource, from the bounds in lo and hi.
   *
   * @return true if the fixed tasks use more than the capacity at some time.
   */
  private boolean overloaded() {
    int count = 0;
    for (int i = 0; i < n; i++) {
      if (lo[i] == hi[i] && durations[i] > 0 && resources[i] > 0) {
        key[count] = (lo[i] << 24) | i;
        endKey[count++] = ((lo[i] + durations[i]) << 24) | i;
      }
    }
    Arrays.sort(key, 0, count);
    Arrays.sort(endKey, 0, count);
    fixedUsed = count;
    long load = 0;
    int e = 0;
    for (int k = 0; k < count; k++) {
      long time = key[k] >> 24;
      while (e < count && endKey[e] >> 24 <= time) {
        load -= resources[(int) (endKey[e++] & 0xFFFFFF)];
      }
      load += resources[(int) (key[k] & 0xFFFFFF)];
      if (load > capacity) {
        return true;
      }
    }
    return false;
  }

  /**
   * On a parallel resource the bound reads only the minima of the free starts, the values of the
   * fixed ones and, to prune starts, the maximum of the cost: every schedule within those bounds
   * costs at least the bound, so those atoms explain the minimum of the cost, the latest starts and
   * a failure, with the holes a pruned bound skipped. The minima of the free starts are weakened
   * towards their root values as far as the propagation still holds ({@link #weakReason}); the
   * unary case uses the replayed or generic reason.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (!parallel) {
      return false;
    }
    int kind = trail.kind(entry);
    if (!WEAK_REASONS || !weakReason(trail, entry, out)) {
      reason(trail, entry, out);
    }
    // the bound computed by inMax (a start) or inMin (the cost) may lie in a hole: the domain moved
    // past the holes next to it, which the bounds alone do not imply
    if (kind == AtomicTrail.GE || kind == AtomicTrail.LE) {
      trail.addSkippedHoles(
          entry, kind == AtomicTrail.GE ? Integer.MIN_VALUE : Integer.MAX_VALUE, out);
    }
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (!parallel) {
      return false;
    }
    if (!WEAK_REASONS || !weakReason(trail, trail.size(), out)) {
      reason(trail, trail.size(), out);
    }
    return true;
  }

  private void reason(AtomicTrail trail, int position, EntryList out) {
    for (IntVar s : starts) {
      trail.addLowerBound(s, position, out);
      if (trail.minBefore(s, position) == trail.maxBefore(s, position)) {
        trail.addUpperBound(s, position, out);
      }
    }
    trail.addUpperBound(cost, position, out);
  }

  /**
   * A smaller reason: the fixed tasks with both bounds, the cost's maximum when the propagation
   * reads it, and the minima of the free starts lowered towards their root minima by a common
   * fraction, the largest (of 1, 1/2, 1/4, ...) at which the propagation still follows. The bound
   * only grows with the minima, so the weaker atoms imply it. A start pruned by its latest start
   * does not need its own minimum. It gives up (false) when the entry is not one the bound
   * explains, and the full reason is used.
   */
  private boolean weakReason(AtomicTrail trail, int position, EntryList out) {
    // what to explain: 0 cost >= v, 1 start of task <= v, 2 a failure
    int what;
    int task = -1;
    long v = 0;
    if (position == trail.size()) {
      what = 2;
    } else {
      IntVar x = trail.variable(position);
      int kind = trail.kind(position);
      for (int i = 0; i < n; i++) {
        if (starts[i] == x) {
          if (task >= 0 || x == cost) {
            return false;
          }
          task = i;
        }
      }
      if (x == cost && kind == AtomicTrail.GE) {
        what = 0;
      } else if (task >= 0 && kind == AtomicTrail.LE) {
        what = 1;
      } else {
        return false;
      }
      v = trail.skippedBound(position);
    }
    double max = trail.maxBefore(cost, position);
    for (int i = 0; i < n; i++) {
      lo[i] = trail.minBefore(starts[i], position);
      hi[i] = trail.maxBefore(starts[i], position);
      low[i] = lo[i];
      root[i] = lo[i] == hi[i] ? lo[i] : Math.min(lo[i], trail.rootDomain(starts[i]).min());
    }
    if (what == 2 && overloaded()) {
      // the fixed tasks alone
      for (int i = 0; i < n; i++) {
        if (lo[i] == hi[i] && durations[i] > 0 && resources[i] > 0) {
          trail.addLowerBound(starts[i], position, out);
          trail.addUpperBound(starts[i], position, out);
        }
      }
      return true;
    }
    if (what == 1) {
      // the bound of the others does not read the minimum of the task itself
      root[task] = lo[task];
    }
    if (!holds(what, task, v, max, 0)) {
      return false;
    }
    double fraction = 0;
    double step = 1;
    for (int round = 0; round < REASON_ROUNDS; round++) {
      double tryFraction = fraction + step;
      if (tryFraction <= 1 && holds(what, task, v, max, tryFraction)) {
        fraction = tryFraction;
        if (fraction == 1) {
          break;
        }
      }
      step /= 2;
    }
    for (int i = 0; i < n; i++) {
      IntVar s = starts[i];
      if (low[i] == hi[i]) {
        trail.addLowerBound(s, position, out);
        trail.addUpperBound(s, position, out);
      } else if (i != task || what != 1) {
        long limit = low[i] - (long) Math.floor(fraction * (low[i] - root[i]));
        if (weights[i] > 0 || proc[i] > 0) {
          trail.addBoundReaching(s, position, true, limit, out);
        }
      }
    }
    if (what != 0) {
      trail.addUpperBound(cost, position, out);
    }
    return true;
  }

  // whether the propagation follows with the free minima lowered by fraction towards the root
  private boolean holds(int what, int task, long v, double max, double fraction) {
    for (int i = 0; i < n; i++) {
      lo[i] = low[i] == hi[i] ? low[i] : low[i] - (long) Math.floor(fraction * (low[i] - root[i]));
    }
    if (overloaded()) {
      return true;
    }
    double[] result = evaluate(max, what == 1 ? task : -1);
    double bound = result[0];
    if (what == 1) {
      return !Double.isNaN(othersBound[task]) && latest(task, max) <= v;
    }
    double best = bound;
    for (int i = 0; i < n; i++) {
      if (!Double.isNaN(othersBound[i])) {
        if (what == 2 && latest(i, max) < lo[i]) {
          return true;
        }
        best = Math.max(best, othersBound[i] + (double) weights[i] * (lo[i] + durations[i]));
      }
    }
    double lower = Math.ceil(best - slack(best));
    return what == 0 ? lower >= v : lower > max;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    long total = 0;
    for (int i = 0; i < n; i++) {
      if (!starts[i].singleton()) {
        return false;
      }
      total += (long) weights[i] * starts[i].value() + (long) weights[i] * durations[i];
    }
    if (parallel) {
      for (int i = 0; i < n; i++) {
        lo[i] = starts[i].value();
        hi[i] = lo[i];
      }
      return !overloaded() && total <= cost.min();
    }
    for (int i = 0; i < n; i++) {
      if (durations[i] > 0 && resources[i] > capacity) {
        return false;
      }
      for (int j = i + 1; j < n; j++) {
        if (proc[i] > 0
            && proc[j] > 0
            && starts[i].value() < (long) starts[j].value() + durations[j]
            && starts[j].value() < (long) starts[i].value() + durations[i]) {
          return false;
        }
      }
    }
    return total <= cost.min();
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : WeightedCompletion([");
    for (int i = 0; i < n; i++) {
      result.append(starts[i]);
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(Arrays.toString(durations));
    if (parallel || Arrays.stream(resources).anyMatch(r -> r != 1)) {
      result.append(", ").append(Arrays.toString(resources));
    }
    result.append(", ").append(Arrays.toString(weights));
    if (parallel) {
      result.append(", ").append(capacity);
    }
    result.append(", ").append(cost).append(")");

    return result.toString();
  }

  @Override
  public WeightedCompletion copy(VarMap map) {
    return new WeightedCompletion(
        map.get(starts), durations, resources, weights, capacity, map.get(cost));
  }
}
