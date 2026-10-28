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
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

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
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class WeightedCompletion extends Constraint
    implements SatisfiedPresent, Copyable<WeightedCompletion> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final IntVar[] starts;
  final int[] durations;
  final int[] weights;
  final IntVar cost;

  private final int n;

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

  /**
   * It constructs a weighted completion time constraint on a unary resource.
   *
   * @param starts the start of each task.
   * @param durations the duration of each task, at least 0.
   * @param weights the weight of each task, at least 0.
   * @param cost the bound on sum(i) weights[i] * (starts[i] + durations[i]).
   */
  public WeightedCompletion(IntVar[] starts, int[] durations, int[] weights, IntVar cost) {

    if (starts == null
        || durations == null
        || weights == null
        || durations.length != starts.length
        || weights.length != starts.length) {
      throw new IllegalArgumentException(
          "WeightedCompletion needs one duration and one weight per task.");
    }
    checkInputForNullness(new String[] {"starts", "cost"}, starts, new Object[] {cost});
    for (int i = 0; i < starts.length; i++) {
      if (durations[i] < 0 || weights[i] < 0) {
        throw new IllegalArgumentException(
            "WeightedCompletion needs durations and weights of at least 0.");
      }
    }

    this.numberId = idNumber.incrementAndGet();
    this.starts = Arrays.copyOf(starts, starts.length);
    this.durations = Arrays.copyOf(durations, durations.length);
    this.weights = Arrays.copyOf(weights, weights.length);
    this.cost = cost;
    this.n = starts.length;

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

  @Override
  public void consistency(Store store) {

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
        busy[k] = weights[j] / (2.0 * durations[j]) * square0[k];
        totalWeight += weights[j];
      }

      for (int i = 0; i < n; i++) {
        IntVar s = starts[i];
        if (s.singleton()) {
          continue;
        }
        int min = s.min();
        int max = s.max();
        if (durations[i] == 0) {
          // the bound grows by weights[i] for each unit of start
          if (weights[i] > 0) {
            double others = bound - (double) weights[i] * s.min();
            long last = (long) Math.floor((cost.max() - others + slack(cost.max())) / weights[i]);
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
        if (durations[i] > 0) {
          fixedTask[fixedCount++] = i;
        }
      } else if (durations[i] == 0) {
        twice += 2L * weights[i] * s.min();
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
    // blocks: fixed tasks and task i, in start order (they do not overlap)
    int blocks = 0;
    boolean placed = i < 0;
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
      remA[k] = durations[j];
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
      double factor = weights[j] / (2.0 * durations[j]);
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
    long left = (long) weights[a] * durations[b];
    long right = (long) weights[b] * durations[a];
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
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (durations[i] > 0
            && durations[j] > 0
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
    result.append(", ").append(Arrays.toString(weights));
    result.append(", ").append(cost).append(")");

    return result.toString();
  }

  @Override
  public WeightedCompletion copy(VarMap map) {
    return new WeightedCompletion(map.get(starts), durations, weights, map.get(cost));
  }
}
