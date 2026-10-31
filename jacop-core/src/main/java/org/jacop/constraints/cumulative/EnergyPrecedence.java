/*
 * EnergyPrecedence.java
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
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
 * Energy precedence reasoning on a cumulative resource whose tasks are ordered by precedences,
 * following Laborie, "Algorithms for propagating resource constraints in AI planning and
 * scheduling: existing approaches and new results", Artificial Intelligence 143 (2003).
 *
 * <p>The precedences {@code to >= from + lag} may involve variables that are not task starts, for
 * example a makespan or the tasks of other resources; they are only used to find which tasks come
 * before or after which time points, and the model has to post them itself. A task i precedes a
 * time point v when the longest path of precedences from the start of i to v is at least the
 * duration of i, so that i ends by v. If a set of tasks precedes v, all their energy has to be
 * spent between the earliest start of the set and v:
 *
 * <pre>
 *   v &gt;= min start(set) + ceil(energy(set) / limit)
 * </pre>
 *
 * The rule is applied with the best set, made of the predecessors of v that start at or after some
 * time t, in O(n) per time point after one sort. Symmetrically, the latest value of a time point
 * that every task of a set has to follow is bounded by the latest end of the set minus its energy
 * divided by the limit. Edge finding and time-tabling do not see this when the time windows of the
 * tasks are wide, since they do not know the precedences.
 *
 * <p>The constraint only adds pruning to a model with the cumulative and the precedences. It bounds
 * the starts of its tasks and the points that end or begin the precedences (such as a makespan),
 * and only these are in its scope. It holds when the tasks never use more than the limit and the
 * precedences it uses between these points hold, which it checks once they are fixed, so it is a
 * correct constraint on its own. To keep its cost low it runs at the lowest priority, makes one
 * pass per call rather than a fixpoint, and after 64 calls in a row without pruning skips the
 * following calls, 1, 2, 4, ... up to 64 of them, until it prunes again.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class EnergyPrecedence extends Constraint
    implements SatisfiedPresent, Copyable<EnergyPrecedence>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The largest number of (time point, task) pairs the precedence closure may hold. */
  public static final long MAX_CLOSURE = 4_000_000L;

  private static final int NONE = Integer.MIN_VALUE;

  // a pass that prunes nothing IDLE_LIMIT times in a row is skipped for 1, 2, 4, ... up to MAX_SKIP
  // calls after each further pass without pruning
  private static final int IDLE_LIMIT = 64;
  private static final int MAX_SKIP = 64;

  private int skipCalls;
  private int idleCalls;
  private int skipPeriod;

  final IntVar[] starts;
  final IntVar[] durations;
  final IntVar[] heights;
  final IntVar limit;
  final int[] lag;

  private final int n;

  // time points: the distinct variables of starts, from and to
  private final IntVar[] points;
  private final int[] pointOfTask;

  // longest path of precedences from the start of task i to point v, NONE when there is none
  private final int[][] after;
  // longest path from point u to the start of task k, NONE when there is none
  private final int[][] before;
  // the points that some task can precede, and the points that some task can follow
  private final int[] forwardTargets;
  private final int[] backwardTargets;
  // false when the precedences are contradictory (a cycle of positive length)
  private final boolean feasible;
  // the precedences the rule uses, between points in the scope: points[p[1]] >= points[p[0]] + p[2]
  private final int[][] pairs;

  // tasks with energy sorted by decreasing earliest start and by increasing latest end
  private final long[] keys;
  private final int[] byStart;
  private final int[] byEnd;
  private int active;
  // the bounds the sort used: a pass may tighten them, and the sets must stay those of the sort
  private final long[] est;
  private final long[] lct;

  /**
   * It creates energy precedence reasoning on a cumulative resource.
   *
   * @param starts the start times of the tasks.
   * @param durations the durations of the tasks.
   * @param heights the resource use of the tasks.
   * @param limit the capacity of the resource.
   * @param from the first variable of each precedence.
   * @param to the second variable of each precedence.
   * @param lag the distances, {@code to[k] >= from[k] + lag[k]}.
   */
  public EnergyPrecedence(
      IntVar[] starts,
      IntVar[] durations,
      IntVar[] heights,
      IntVar limit,
      IntVar[] from,
      IntVar[] to,
      int[] lag) {

    checkInputForNullness(
        new String[] {"starts", "durations", "heights", "from", "to"},
        new Object[][] {starts, durations, heights, from, to});
    checkInputForNullness("limit", new Object[] {limit});
    if (durations.length != starts.length || heights.length != starts.length) {
      throw new IllegalArgumentException(
          "EnergyPrecedence needs one duration and one height per task.");
    }
    if (lag == null || from.length != to.length || lag.length != from.length) {
      throw new IllegalArgumentException(
          "EnergyPrecedence needs two variables and one lag per precedence.");
    }
    for (int i = 0; i < starts.length; i++) {
      if (durations[i].min() < 0 || heights[i].min() < 0) {
        throw new IllegalArgumentException(
            "EnergyPrecedence needs durations and heights of at least 0.");
      }
    }

    this.numberId = idNumber.incrementAndGet();
    this.starts = Arrays.copyOf(starts, starts.length);
    this.durations = Arrays.copyOf(durations, durations.length);
    this.heights = Arrays.copyOf(heights, heights.length);
    this.limit = limit;
    this.lag = Arrays.copyOf(lag, lag.length);
    this.n = starts.length;

    Map<IntVar, Integer> index = new IdentityHashMap<>();
    List<IntVar> pointList = new ArrayList<>();
    for (IntVar[] vs : new IntVar[][] {starts, from, to}) {
      for (IntVar v : vs) {
        index.computeIfAbsent(
            v,
            k -> {
              pointList.add(k);
              return pointList.size() - 1;
            });
      }
    }
    this.points = pointList.toArray(new IntVar[0]);
    int m = points.length;
    this.pointOfTask = new int[n];
    for (int i = 0; i < n; i++) {
      pointOfTask[i] = index.get(starts[i]);
    }

    int arcs = from.length;
    int[] arcFrom = new int[arcs];
    int[] arcTo = new int[arcs];
    for (int k = 0; k < arcs; k++) {
      arcFrom[k] = index.get(from[k]);
      arcTo[k] = index.get(to[k]);
    }

    this.after = new int[n][];
    this.before = new int[m][];
    boolean ok = true;
    if ((long) n * m <= MAX_CLOSURE && (long) n * m * Math.max(1, arcs) <= 50 * MAX_CLOSURE) {
      int[][] out = adjacency(m, arcFrom, arcTo);
      int[][] in = adjacency(m, arcTo, arcFrom);
      int[] dist = new int[m];
      for (int i = 0; i < n && ok; i++) {
        ok = longestPaths(pointOfTask[i], out, arcFrom, arcTo, true, dist);
        after[i] = Arrays.copyOf(dist, m);
      }
      int[][] distTo = new int[n][];
      for (int i = 0; i < n && ok; i++) {
        ok = longestPaths(pointOfTask[i], in, arcFrom, arcTo, false, dist);
        distTo[i] = Arrays.copyOf(dist, m);
      }
      for (int u = 0; u < m && ok; u++) {
        before[u] = new int[n];
        for (int i = 0; i < n; i++) {
          before[u][i] = distTo[i][u];
        }
      }
    }
    this.feasible = ok;

    // the points with arcs into them and out of them
    boolean[] hasIn = new boolean[m];
    boolean[] hasOut = new boolean[m];
    boolean[] taskPoint = new boolean[m];
    for (int k = 0; k < arcs; k++) {
      hasOut[arcFrom[k]] = true;
      hasIn[arcTo[k]] = true;
    }
    for (int i = 0; i < n; i++) {
      taskPoint[pointOfTask[i]] = true;
    }
    // the rule bounds the starts of the tasks and the points that end or begin the precedences,
    // such
    // as a makespan; other points, starts of tasks of other resources for example, are left to the
    // precedences, so that the constraint does not wake up on them
    List<Integer> fw = new ArrayList<>();
    List<Integer> bw = new ArrayList<>();
    List<int[]> implied = new ArrayList<>();
    if (ok && n > 0 && after[0] != null) {
      for (int v = 0; v < m; v++) {
        List<int[]> into = new ArrayList<>();
        List<int[]> outOf = new ArrayList<>();
        for (int i = 0; i < n; i++) {
          if (pointOfTask[i] != v && after[i][v] != NONE && after[i][v] >= durations[i].min()) {
            into.add(new int[] {pointOfTask[i], v, after[i][v]});
          }
          if (pointOfTask[i] != v && before[v][i] != NONE && before[v][i] >= 0) {
            outOf.add(new int[] {v, pointOfTask[i], before[v][i]});
          }
        }
        // a single task gives no more than the precedence itself
        if (into.size() >= 2 && (taskPoint[v] || !hasOut[v])) {
          fw.add(v);
          implied.addAll(into);
        }
        if (outOf.size() >= 2 && (taskPoint[v] || !hasIn[v])) {
          bw.add(v);
          implied.addAll(outOf);
        }
      }
    }
    this.forwardTargets = fw.stream().mapToInt(Integer::intValue).toArray();
    this.backwardTargets = bw.stream().mapToInt(Integer::intValue).toArray();
    this.pairs = implied.toArray(new int[0][]);

    this.keys = new long[n];
    this.byStart = new int[n];
    this.byEnd = new int[n];
    this.est = new long[n];
    this.lct = new long[n];

    // the cheaper propagators of the model run first
    this.queueIndex = 4;

    setScope(
        Stream.concat(
            Stream.of(starts, durations, heights, new IntVar[] {limit}).flatMap(Arrays::stream),
            Stream.concat(
                    Arrays.stream(forwardTargets).boxed(), Arrays.stream(backwardTargets).boxed())
                .map(v -> points[v])));
  }

  /**
   * It tells if the precedences give the rule something to work on: some time point has at least
   * two tasks before it or after it.
   *
   * @return true if the constraint can prune.
   */
  public boolean propagates() {
    return !feasible || forwardTargets.length > 0 || backwardTargets.length > 0;
  }

  private static int[][] adjacency(int m, int[] tail, int[] head) {
    int[] count = new int[m];
    for (int t : tail) {
      count[t]++;
    }
    int[][] adj = new int[m][];
    for (int u = 0; u < m; u++) {
      adj[u] = new int[count[u]];
    }
    Arrays.fill(count, 0);
    for (int k = 0; k < tail.length; k++) {
      adj[tail[k]][count[tail[k]]++] = k;
    }
    return adj;
  }

  // longest paths from (or, backwards, to) the source by the queue-based Bellman-Ford; false on a
  // cycle of positive length, found as a longest path with as many arcs as points
  private boolean longestPaths(
      int source, int[][] adj, int[] arcFrom, int[] arcTo, boolean forward, int[] dist) {
    int m = dist.length;
    Arrays.fill(dist, NONE);
    dist[source] = 0;
    int[] arcsOnPath = new int[m];
    boolean[] queued = new boolean[m];
    ArrayDeque<Integer> queue = new ArrayDeque<>();
    queue.add(source);
    queued[source] = true;
    while (!queue.isEmpty()) {
      int u = queue.poll();
      queued[u] = false;
      for (int k : adj[u]) {
        int w = forward ? arcTo[k] : arcFrom[k];
        long d = (long) dist[u] + lag[k];
        if (d > dist[w] && d < IntDomain.MAX_INT) {
          dist[w] = (int) d;
          arcsOnPath[w] = arcsOnPath[u] + 1;
          if (arcsOnPath[w] >= m) {
            return false;
          }
          if (!queued[w]) {
            queue.add(w);
            queued[w] = true;
          }
        }
      }
    }
    return true;
  }

  @Override
  public void consistency(Store store) {

    if (!feasible) {
      throw Store.failException;
    }
    long capacity = limit.max();
    if (capacity <= 0 || (forwardTargets.length == 0 && backwardTargets.length == 0)) {
      if (grounded()) {
        check();
      }
      return;
    }

    // one pass, not to a fixpoint: the rule is redundant, and most of its pruning comes in the
    // first pass
    if (skipCalls > 0) {
      skipCalls--;
    } else {
      store.propagationHasOccurred = false;
      sortTasks();
      for (int v : forwardTargets) {
        forward(store, v, capacity);
      }
      for (int u : backwardTargets) {
        backward(store, u, capacity);
      }
      if (store.propagationHasOccurred) {
        idleCalls = 0;
        skipPeriod = 0;
      } else if (++idleCalls >= IDLE_LIMIT) {
        skipPeriod = Math.min(Math.max(1, 2 * skipPeriod), MAX_SKIP);
        skipCalls = skipPeriod;
      }
    }

    if (grounded()) {
      check();
    }
  }

  private static long energy(IntVar d, IntVar r) {
    return (long) d.min() * r.min();
  }

  private void sortTasks() {
    active = 0;
    for (int i = 0; i < n; i++) {
      if (durations[i].min() > 0 && heights[i].min() > 0) {
        est[i] = starts[i].min();
        lct[i] = (long) starts[i].max() + durations[i].max();
        keys[active++] = (est[i] << 32) | i;
      }
    }
    Arrays.sort(keys, 0, active);
    for (int k = 0; k < active; k++) {
      byStart[active - 1 - k] = (int) keys[k];
    }
    for (int k = 0; k < active; k++) {
      int i = byStart[k];
      keys[k] = (lct[i] << 32) | i;
    }
    Arrays.sort(keys, 0, active);
    for (int k = 0; k < active; k++) {
      byEnd[k] = (int) keys[k];
    }
  }

  // v >= t + ceil(energy of the predecessors of v starting at or after t / capacity) + the
  // smallest lag from the end of one of them to v
  private void forward(Store store, int v, long capacity) {
    IntVar x = points[v];
    long bound = Long.MIN_VALUE;
    long sum = 0;
    long gap = Long.MAX_VALUE;
    for (int k = 0; k < active; k++) {
      int i = byStart[k];
      int d = after[i][v];
      if (d == NONE || pointOfTask[i] == v || d < durations[i].max()) {
        continue;
      }
      sum += energy(durations[i], heights[i]);
      gap = Math.min(gap, (long) d - durations[i].max());
      long b = est[i] + (sum + capacity - 1) / capacity + gap;
      if (b > bound) {
        bound = b;
      }
    }
    if (bound > x.min()) {
      if (bound > IntDomain.MAX_INT) {
        throw Store.failException;
      }
      x.domain.inMin(store.level, x, (int) bound);
    }
  }

  // u <= t - ceil(energy of the tasks following u that end by t / capacity) - the lag to them
  private void backward(Store store, int u, long capacity) {
    IntVar x = points[u];
    long bound = Long.MAX_VALUE;
    long sum = 0;
    int gap = Integer.MAX_VALUE;
    for (int k = 0; k < active; k++) {
      int i = byEnd[k];
      int d = before[u][i];
      if (d == NONE || pointOfTask[i] == u || d < 0) {
        continue;
      }
      sum += energy(durations[i], heights[i]);
      gap = Math.min(gap, d);
      long b = lct[i] - (sum + capacity - 1) / capacity - gap;
      if (b < bound) {
        bound = b;
      }
    }
    if (bound < x.max()) {
      if (bound < IntDomain.MIN_INT) {
        throw Store.failException;
      }
      x.domain.inMax(store.level, x, (int) bound);
    }
  }

  /**
   * Explains a bound of a time point by a set of tasks that precede it (or follow it): their
   * earliest starts (latest ends), the smallest durations and heights that make their energy, the
   * largest durations that keep them before the point, and the largest limit. The set is the best
   * one with the bounds just before the entry, among those of the tasks starting at or after some
   * time, the sets the rule tries.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (getClass() != EnergyPrecedence.class || !feasible || trail.kind(entry) == AtomicTrail.NE) {
      return false;
    }
    IntVar x = trail.variable(entry);
    boolean lower = trail.kind(entry) == AtomicTrail.GE;
    long a = trail.value(entry);
    int mark = out.size();
    for (int v : lower ? forwardTargets : backwardTargets) {
      if (points[v] == x) {
        long reached = rule(trail, entry, v, lower, a, out);
        if (reached != Long.MIN_VALUE) {
          out.sortUnique(mark);
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  /** Explains a failure: a time point whose rule bound passes its other bound. */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (getClass() != EnergyPrecedence.class || !feasible) {
      return false;
    }
    int now = trail.size();
    int mark = out.size();
    for (boolean lower : new boolean[] {true, false}) {
      for (int v : lower ? forwardTargets : backwardTargets) {
        IntVar x = points[v];
        long other = lower ? trail.maxBefore(x, now) + 1L : trail.minBefore(x, now) - 1L;
        long reached = rule(trail, now, v, lower, other, out);
        if (reached != Long.MIN_VALUE
            && addBound(trail, x, !lower, lower ? reached - 1 : reached + 1, now, out)) {
          out.sortUnique(mark);
          return true;
        }
        out.truncate(mark);
      }
    }
    return explainPrecedence(trail, now, out) || explainOverload(trail, now, out);
  }

  // a precedence the bounds violate: to <= max to < min from + lag
  private boolean explainPrecedence(AtomicTrail trail, int now, EntryList out) {
    for (int[] p : pairs) {
      IntVar from = points[p[0]];
      IntVar to = points[p[1]];
      long fromMin = trail.minBefore(from, now);
      long toMax = trail.maxBefore(to, now);
      if (toMax < fromMin + p[2]) {
        int mark = out.size();
        if (addBound(trail, from, true, fromMin, now, out)
            && addBound(trail, to, false, toMax, now, out)) {
          out.sortUnique(mark);
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  // the compulsory parts [latest start, earliest end) of the tasks overload the limit at a time
  private boolean explainOverload(AtomicTrail trail, int now, EntryList out) {
    long capacity = trail.maxBefore(limit, now);
    for (int k = 0; k < n; k++) {
      long time = trail.maxBefore(starts[k], now);
      long load = 0;
      for (int i = 0; i < n; i++) {
        if (covers(trail, i, time, now)) {
          load += trail.minBefore(heights[i], now);
        }
      }
      if (load <= capacity) {
        continue;
      }
      int mark = out.size();
      boolean ok = addBound(trail, limit, false, capacity, now, out);
      for (int i = 0; ok && i < n; i++) {
        if (covers(trail, i, time, now)) {
          long dMin = trail.minBefore(durations[i], now);
          ok =
              addBound(trail, starts[i], false, time, now, out)
                  && addBound(trail, starts[i], true, time - dMin + 1, now, out)
                  && addBound(trail, durations[i], true, dMin, now, out)
                  && addBound(trail, heights[i], true, trail.minBefore(heights[i], now), now, out);
        }
      }
      if (ok) {
        out.sortUnique(mark);
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  // whether the compulsory part of task i, with a positive height, covers the time
  private boolean covers(AtomicTrail trail, int i, long time, int now) {
    return trail.minBefore(heights[i], now) > 0
        && trail.maxBefore(starts[i], now) <= time
        && (long) trail.minBefore(starts[i], now) + trail.minBefore(durations[i], now) > time;
  }

  /**
   * Adds the reason of the rule bounding point v to at least a (lower) or at most a, with the
   * bounds just before the position; returns the bound the set reaches, or Long.MIN_VALUE when no
   * set reaches a.
   */
  private long rule(AtomicTrail trail, int position, int v, boolean lower, long a, EntryList out) {
    long capacity = trail.maxBefore(limit, position);
    if (capacity <= 0) {
      return Long.MIN_VALUE;
    }
    int[] tasks = new int[n];
    long[] time = new long[n];
    int count = 0;
    for (int i = 0; i < n; i++) {
      if (pointOfTask[i] == v
          || trail.minBefore(durations[i], position) <= 0
          || trail.minBefore(heights[i], position) <= 0) {
        continue;
      }
      long dMax = trail.maxBefore(durations[i], position);
      int d = lower ? after[i][v] : before[v][i];
      if (d == NONE || (lower ? d < dMax : d < 0)) {
        continue;
      }
      tasks[count] = i;
      // the earliest start, or the latest end negated, so both sides take the largest first
      time[count++] =
          lower
              ? trail.minBefore(starts[i], position)
              : -(trail.maxBefore(starts[i], position) + dMax);
    }
    Integer[] order = new Integer[count];
    for (int k = 0; k < count; k++) {
      order[k] = k;
    }
    Arrays.sort(order, (p, q) -> Long.compare(time[q], time[p]));
    long sum = 0;
    long gap = Long.MAX_VALUE;
    for (int k = 0; k < count; k++) {
      int i = tasks[order[k]];
      long dMax = trail.maxBefore(durations[i], position);
      sum += (long) trail.minBefore(durations[i], position) * trail.minBefore(heights[i], position);
      gap = Math.min(gap, lower ? after[i][v] - dMax : before[v][i]);
      long t = lower ? time[order[k]] : -time[order[k]];
      long b =
          lower
              ? t + (sum + capacity - 1) / capacity + gap
              : t - (sum + capacity - 1) / capacity - gap;
      if (lower ? b >= a : b <= a) {
        for (int j = 0; j <= k; j++) {
          if (!addTask(trail, tasks[order[j]], lower, t, position, out)) {
            return Long.MIN_VALUE;
          }
        }
        if (!addBound(trail, limit, false, capacity, position, out)) {
          return Long.MIN_VALUE;
        }
        return b;
      }
    }
    return Long.MIN_VALUE;
  }

  // the atoms of task i in a set of the rule from time t: its start (or end) within t, its energy
  // and its largest duration
  private boolean addTask(
      AtomicTrail trail, int i, boolean lower, long t, int position, EntryList out) {
    long dMin = trail.minBefore(durations[i], position);
    long dMax = trail.maxBefore(durations[i], position);
    long hMin = trail.minBefore(heights[i], position);
    return addBound(trail, starts[i], lower, lower ? t : t - dMax, position, out)
        && addBound(trail, durations[i], true, dMin, position, out)
        && addBound(trail, durations[i], false, dMax, position, out)
        && addBound(trail, heights[i], true, hMin, position, out);
  }

  // the weakest atom giving x >= value (lower) or x <= value before the position
  private static boolean addBound(
      AtomicTrail trail, IntVar x, boolean lower, long value, int position, EntryList out) {
    int e =
        lower
            ? trail.earliestLowerBound(x, value, position)
            : trail.earliestUpperBound(x, value, position);
    if (e == Integer.MAX_VALUE) {
      return false;
    }
    if (e >= 0) {
      out.add(e);
    }
    return true;
  }

  private void check() {
    if (!holds()) {
      throw Store.failException;
    }
  }

  // the precedences and the capacity hold for the fixed values
  private boolean holds() {
    for (int[] p : pairs) {
      if ((long) points[p[1]].value() < (long) points[p[0]].value() + p[2]) {
        return false;
      }
    }
    long[] events = new long[2 * n];
    int e = 0;
    for (int i = 0; i < n; i++) {
      if (durations[i].value() > 0 && heights[i].value() > 0) {
        // ends sort before starts at the same time
        events[e++] = ((long) starts[i].value() << 32) | (1L << 31) | i;
        events[e++] = ((long) (starts[i].value() + durations[i].value()) << 32) | i;
      }
    }
    Arrays.sort(events, 0, e);
    long load = 0;
    for (int k = 0; k < e; k++) {
      int i = (int) (events[k] & 0x7fffffffL);
      if ((events[k] & (1L << 31)) != 0) {
        load += heights[i].value();
        if (load > limit.value()) {
          return false;
        }
      } else {
        load -= heights[i].value();
      }
    }
    return true;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    return grounded() && holds();
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : EnergyPrecedence(").append(Arrays.toString(starts));
    result.append(", ").append(Arrays.toString(durations));
    result.append(", ").append(Arrays.toString(heights));
    result.append(", ").append(limit);
    result.append(", [");
    for (int k = 0; k < pairs.length; k++) {
      result.append(k > 0 ? ", " : "").append(points[pairs[k][0]].id()).append(" + ");
      result.append(pairs[k][2]).append(" <= ").append(points[pairs[k][1]].id());
    }
    return result.append("])").toString();
  }

  @Override
  public EnergyPrecedence copy(VarMap map) {
    // only the points the rule bounds are in the scope, so the copy keeps the precedences it uses
    IntVar[] f = new IntVar[pairs.length];
    IntVar[] t = new IntVar[pairs.length];
    int[] l = new int[pairs.length];
    for (int k = 0; k < pairs.length; k++) {
      f[k] = map.get(points[pairs[k][0]]);
      t[k] = map.get(points[pairs[k][1]]);
      l[k] = pairs[k][2];
    }
    return new EnergyPrecedence(
        map.get(starts), map.get(durations), map.get(heights), map.get(limit), f, t, l);
  }
}
