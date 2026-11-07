/*
 * HornFlow.java
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
 * A feasibility check of a cumulative resource by the preemptive relaxation and a maximum flow,
 * after Horn, "Some simple scheduling algorithms", Naval Research Logistics Quarterly 21(1) (1974)
 * 177-185, and Federgruen and Groenevelt, "Preemptive scheduling of uniform machines by ordinary
 * network flow techniques", Management Science 32(3) (1986) 341-349. Shioura, Strusevich and
 * Shakhlevich, "Generalizing Horn's conditions for preemptive scheduling on identical parallel
 * machines via network flow techniques", Networks 83(3) (2024) 527-546, derive the feasibility
 * conditions from the structure of the minimum cuts of the same network, which the explanation
 * below uses.
 *
 * <p>With unit resource uses and capacity m, the tasks are the jobs of P|r_j, d_j, pmtn|: job j
 * needs p_j units of time in [est_j, lct_j) and runs on at most one of the m machines at a time.
 * Horn's network has an arc of capacity p_j from the source to every job, an arc of capacity |I|
 * from a job to every elementary interval I of its window (the time between two consecutive release
 * dates or deadlines), and an arc of capacity m |I| from every interval to the sink. A preemptive
 * schedule exists if and only if the maximum flow is the sum of the p_j, and a schedule of the
 * cumulative is a preemptive one, so a smaller flow means the cumulative has no solution.
 *
 * <p>The constraint uses the same network for any resource use r_j and capacity C: task j needs r_j
 * p_j units of energy at a rate of at most r_j, so its arcs to the intervals have capacity r_j |I|
 * and the intervals have C |I|, where p_j and r_j are the smallest duration and resource use and C
 * is the largest capacity. With the compulsory part [lst_j, ect_j) of a task it is strengthened by
 * the time-table: the task runs at its full rate there, which the interval capacities lose up
 * front, and it needs r_j (p_j - |[lst_j, ect_j)|) more elsewhere in its window. The check is then
 * at least as strong as the time-table check and the energy overload check of the tasks.
 *
 * <p>When the flow is short, the minimum cut gives a set U of intervals, a union of time ranges,
 * whose demand passes its capacity: every task j has to spend at least r_j max(|[lst_j, ect_j)
 * &cap; U|, p_j - |[est_j, lct_j) \ U|) units of energy in U, and together more than C |U|. This
 * inequality is the failure's explanation for lazy clause generation, with the bounds of the tasks
 * that contribute, weakened as far as the excess allows.
 *
 * <p>The constraint only adds a failure check to a model with the cumulative constraint; it prunes
 * no values. It holds when the tasks never use more than the capacity, which the check decides once
 * all tasks are fixed, so it is a correct constraint on its own. It runs at the lowest priority and
 * costs one maximum flow on at most n tasks and 4n intervals per call.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class HornFlow extends Constraint
    implements SatisfiedPresent, Copyable<HornFlow>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  // larger energies are not checked, so that no sum of them overflows
  private static final long MAX_ENERGY = 1L << 58;

  final IntVar[] starts;
  final IntVar[] durations;
  final IntVar[] resources;
  final IntVar limit;

  private final int n;

  private boolean compulsoryParts = true;

  // the tasks of the current check: earliest and latest start, smallest duration and use
  private final long[] est;
  private final long[] lst;
  private final long[] dur;
  private final long[] use;
  private final int[] task;
  private int m;
  private long capacity;

  // elementary intervals [time[k], time[k + 1]) for k < intervals
  private long[] time;
  private int intervals;
  // capacity left by the compulsory parts in each interval, and the flow into the sink
  private long[] intervalCap;
  private long[] intervalFlow;
  // energy each task still needs, and the flow from the source
  private final long[] demand;
  private final long[] taskFlow;
  // window [first, last) and compulsory part [cpFirst, cpLast) of each task, as interval indices
  private final int[] first;
  private final int[] last;
  private final int[] cpFirst;
  private final int[] cpLast;
  // flow from task j to interval k at arcOffset[j] + k - first[j]
  private final int[] arcOffset;
  private long[] arcFlow;
  // the tasks with an arc into interval k: coverTask[coverStart[k] .. coverStart[k + 1])
  private int[] coverStart;
  private int[] coverTask;

  // Dinic's levels and current arcs
  private final int[] taskLevel;
  private int[] intervalLevel;
  private final int[] taskCurrent;
  private int[] intervalCurrent;
  private int[] queue;
  private int sinkLevel;

  // the intervals of the minimum cut after a failed check
  private boolean[] inCut;

  /**
   * It creates the flow check of a cumulative resource.
   *
   * @param starts the start times of the tasks.
   * @param durations the durations of the tasks.
   * @param resources the resource use of the tasks.
   * @param limit the capacity of the resource.
   */
  public HornFlow(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit) {

    checkInputForNullness(
        new String[] {"starts", "durations", "resources"},
        new Object[][] {starts, durations, resources});
    checkInputForNullness("limit", new Object[] {limit});
    if (durations.length != starts.length || resources.length != starts.length) {
      throw new IllegalArgumentException("HornFlow needs one duration and one resource per task.");
    }
    for (int i = 0; i < starts.length; i++) {
      if (durations[i].min() < 0 || resources[i].min() < 0) {
        throw new IllegalArgumentException("HornFlow needs durations and resources of at least 0.");
      }
    }

    this.numberId = idNumber.incrementAndGet();
    this.starts = Arrays.copyOf(starts, starts.length);
    this.durations = Arrays.copyOf(durations, durations.length);
    this.resources = Arrays.copyOf(resources, resources.length);
    this.limit = limit;
    this.n = starts.length;

    est = new long[n];
    lst = new long[n];
    dur = new long[n];
    use = new long[n];
    task = new int[n];
    demand = new long[n];
    taskFlow = new long[n];
    first = new int[n];
    last = new int[n];
    cpFirst = new int[n];
    cpLast = new int[n];
    arcOffset = new int[n + 1];
    taskLevel = new int[n];
    taskCurrent = new int[n];
    int k = 4 * n + 1;
    time = new long[k];
    intervalCap = new long[k];
    intervalFlow = new long[k];
    intervalLevel = new int[k];
    intervalCurrent = new int[k];
    coverStart = new int[k + 1];
    inCut = new boolean[k];
    queue = new int[n + k];
    arcFlow = new long[0];
    coverTask = new int[0];

    // the cheaper propagators of the model run first
    this.queueIndex = 4;

    setScope(Stream.of(starts, durations, resources, new IntVar[] {limit}).flatMap(Arrays::stream));
  }

  /**
   * It sets whether the compulsory parts of the tasks are taken out of the interval capacities (the
   * default), which adds the time-table check to the flow. Without them the check is Horn's
   * preemptive relaxation alone.
   *
   * @param compulsory true to use the compulsory parts.
   */
  public void useCompulsoryParts(boolean compulsory) {
    this.compulsoryParts = compulsory;
  }

  @Override
  public void consistency(Store store) {
    if (load(null, 0) ? !feasible() : grounded() && !holds()) {
      throw Store.failException;
    }
  }

  // loads the tasks with positive energy, from the domains (trail null) or from the trail just
  // before a position; false when the numbers are too large to check
  private boolean load(AtomicTrail trail, int position) {
    capacity = trail == null ? limit.max() : trail.maxBefore(limit, position);
    if (capacity < 0) {
      return false;
    }
    m = 0;
    for (int i = 0; i < n; i++) {
      long p = trail == null ? durations[i].min() : trail.minBefore(durations[i], position);
      long r = trail == null ? resources[i].min() : trail.minBefore(resources[i], position);
      if (p <= 0 || r <= 0) {
        continue;
      }
      long e = trail == null ? starts[i].min() : trail.minBefore(starts[i], position);
      long l = trail == null ? starts[i].max() : trail.maxBefore(starts[i], position);
      if (p * r > MAX_ENERGY / (n + 1) || r * (l + p - e) > MAX_ENERGY / (n + 1)) {
        return false;
      }
      est[m] = e;
      lst[m] = l;
      dur[m] = p;
      use[m] = r;
      task[m] = i;
      m++;
    }
    if (m == 0) {
      return false;
    }
    long horizonMin = Long.MAX_VALUE;
    long horizonMax = Long.MIN_VALUE;
    for (int j = 0; j < m; j++) {
      horizonMin = Math.min(horizonMin, est[j]);
      horizonMax = Math.max(horizonMax, lst[j] + dur[j]);
    }
    return capacity * (horizonMax - horizonMin) <= MAX_ENERGY;
  }

  // the elementary intervals, the network and its maximum flow; false when the flow is short, with
  // the intervals of the minimum cut in inCut
  private boolean feasible() {
    buildIntervals();
    Arrays.fill(inCut, 0, intervals, false);
    // the compulsory parts alone may overload an interval
    for (int k = 0; k < intervals; k++) {
      if (intervalCap[k] < 0) {
        inCut[k] = true;
        return false;
      }
    }
    buildArcs();
    long total = 0;
    for (int j = 0; j < m; j++) {
      total += demand[j];
    }
    if (total == 0) {
      return true;
    }
    long flow = greedy();
    while (flow < total && levels()) {
      for (int j = 0; j < m && flow < total; j++) {
        if (taskLevel[j] == 1) {
          long d = pushTask(j, demand[j] - taskFlow[j]);
          taskFlow[j] += d;
          flow += d;
        }
      }
    }
    if (flow >= total) {
      return true;
    }
    // the last search for levels did not reach the sink: the intervals it reached are the cut
    for (int k = 0; k < intervals; k++) {
      inCut[k] = intervalLevel[k] >= 0;
    }
    return false;
  }

  private void buildIntervals() {
    int t = 0;
    for (int j = 0; j < m; j++) {
      time[t++] = est[j];
      time[t++] = lst[j] + dur[j];
      if (compulsoryParts && lst[j] < est[j] + dur[j]) {
        time[t++] = lst[j];
        time[t++] = est[j] + dur[j];
      }
    }
    Arrays.sort(time, 0, t);
    int unique = 0;
    for (int k = 0; k < t; k++) {
      if (unique == 0 || time[unique - 1] != time[k]) {
        time[unique++] = time[k];
      }
    }
    intervals = unique - 1;
    for (int k = 0; k < intervals; k++) {
      intervalCap[k] = capacity * (time[k + 1] - time[k]);
      intervalFlow[k] = 0;
    }
    for (int j = 0; j < m; j++) {
      first[j] = index(est[j]);
      last[j] = index(lst[j] + dur[j]);
      long cp = lst[j] < est[j] + dur[j] ? est[j] + dur[j] - lst[j] : 0;
      if (compulsoryParts && cp > 0) {
        cpFirst[j] = index(lst[j]);
        cpLast[j] = index(est[j] + dur[j]);
        for (int k = cpFirst[j]; k < cpLast[j]; k++) {
          intervalCap[k] -= use[j] * (time[k + 1] - time[k]);
        }
      } else {
        cp = 0;
        cpFirst[j] = last[j];
        cpLast[j] = last[j];
      }
      demand[j] = use[j] * (dur[j] - cp);
      taskFlow[j] = 0;
    }
  }

  private int index(long t) {
    return Arrays.binarySearch(time, 0, intervals + 1, t);
  }

  private void buildArcs() {
    arcOffset[0] = 0;
    for (int j = 0; j < m; j++) {
      arcOffset[j + 1] = arcOffset[j] + last[j] - first[j];
    }
    int arcs = arcOffset[m];
    if (arcFlow.length < arcs) {
      arcFlow = new long[Math.max(arcs, 2 * arcFlow.length)];
      coverTask = new int[arcFlow.length];
    }
    Arrays.fill(arcFlow, 0, arcs, 0);
    Arrays.fill(coverStart, 0, intervals + 1, 0);
    for (int j = 0; j < m; j++) {
      if (demand[j] == 0) {
        continue;
      }
      for (int k = first[j]; k < last[j]; k++) {
        if (k < cpFirst[j] || k >= cpLast[j]) {
          coverStart[k + 1]++;
        }
      }
    }
    for (int k = 0; k < intervals; k++) {
      coverStart[k + 1] += coverStart[k];
    }
    System.arraycopy(coverStart, 0, intervalCurrent, 0, intervals);
    for (int j = 0; j < m; j++) {
      if (demand[j] == 0) {
        continue;
      }
      for (int k = first[j]; k < last[j]; k++) {
        if (k < cpFirst[j] || k >= cpLast[j]) {
          coverTask[intervalCurrent[k]++] = j;
        }
      }
    }
  }

  private long arcCap(int j, int k) {
    return use[j] * (time[k + 1] - time[k]);
  }

  // a starting flow: tasks by earliest deadline, each one into its intervals from the left
  private long greedy() {
    long[] keys = new long[m];
    for (int j = 0; j < m; j++) {
      keys[j] = ((long) last[j] << 32) | j;
    }
    Arrays.sort(keys);
    long flow = 0;
    for (long key : keys) {
      int j = (int) key;
      for (int k = first[j]; k < last[j] && taskFlow[j] < demand[j]; k++) {
        if (k >= cpFirst[j] && k < cpLast[j]) {
          continue;
        }
        long d =
            Math.min(
                demand[j] - taskFlow[j], Math.min(arcCap(j, k), intervalCap[k] - intervalFlow[k]));
        if (d > 0) {
          arcFlow[arcOffset[j] + k - first[j]] += d;
          intervalFlow[k] += d;
          taskFlow[j] += d;
          flow += d;
        }
      }
    }
    return flow;
  }

  // levels of the residual network from the source; true when the sink is reached. Queue entries
  // below m are tasks, the others intervals.
  private boolean levels() {
    Arrays.fill(taskLevel, 0, m, -1);
    Arrays.fill(intervalLevel, 0, intervals, -1);
    int head = 0;
    int tail = 0;
    for (int j = 0; j < m; j++) {
      if (taskFlow[j] < demand[j]) {
        taskLevel[j] = 1;
        queue[tail++] = j;
      }
    }
    sinkLevel = -1;
    while (head < tail) {
      int u = queue[head++];
      if (u < m) {
        int level = taskLevel[u];
        if (sinkLevel >= 0 && level + 1 >= sinkLevel) {
          continue;
        }
        for (int k = first[u]; k < last[u]; k++) {
          if (k == cpFirst[u]) {
            k = cpLast[u] - 1;
            continue;
          }
          if (intervalLevel[k] < 0 && arcFlow[arcOffset[u] + k - first[u]] < arcCap(u, k)) {
            intervalLevel[k] = level + 1;
            queue[tail++] = m + k;
          }
        }
      } else {
        int k = u - m;
        int level = intervalLevel[k];
        if (intervalFlow[k] < intervalCap[k] && sinkLevel < 0) {
          sinkLevel = level + 1;
        }
        if (sinkLevel >= 0 && level + 1 >= sinkLevel) {
          continue;
        }
        for (int c = coverStart[k]; c < coverStart[k + 1]; c++) {
          int j = coverTask[c];
          if (taskLevel[j] < 0 && arcFlow[arcOffset[j] + k - first[j]] > 0) {
            taskLevel[j] = level + 1;
            queue[tail++] = j;
          }
        }
      }
    }
    if (sinkLevel < 0) {
      return false;
    }
    System.arraycopy(first, 0, taskCurrent, 0, m);
    System.arraycopy(coverStart, 0, intervalCurrent, 0, intervals);
    return true;
  }

  // sends at most f from task j towards the sink along the levels; returns the amount sent. An arc
  // is passed over once it is saturated or nothing more gets through it in this phase.
  private long pushTask(int j, long f) {
    long sent = 0;
    while (taskCurrent[j] < last[j]) {
      int k = taskCurrent[j];
      if (k == cpFirst[j]) {
        taskCurrent[j] = cpLast[j];
        continue;
      }
      int a = arcOffset[j] + k - first[j];
      long room = arcCap(j, k) - arcFlow[a];
      if (room > 0 && intervalLevel[k] == taskLevel[j] + 1) {
        long d = pushInterval(k, Math.min(f - sent, room));
        arcFlow[a] += d;
        sent += d;
        if (sent == f) {
          return sent;
        }
      }
      taskCurrent[j]++;
    }
    return sent;
  }

  private long pushInterval(int k, long f) {
    if (intervalLevel[k] + 1 == sinkLevel) {
      long d = Math.min(f, intervalCap[k] - intervalFlow[k]);
      if (d > 0) {
        intervalFlow[k] += d;
        return d;
      }
      return 0;
    }
    long sent = 0;
    while (intervalCurrent[k] < coverStart[k + 1]) {
      int j = coverTask[intervalCurrent[k]];
      int a = arcOffset[j] + k - first[j];
      if (arcFlow[a] > 0 && taskLevel[j] == intervalLevel[k] + 1) {
        long d = pushTask(j, Math.min(f - sent, arcFlow[a]));
        arcFlow[a] -= d;
        sent += d;
        if (sent == f) {
          return sent;
        }
      }
      intervalCurrent[k]++;
    }
    return sent;
  }

  // |[a, b) & U| for the intervals of the cut, given its prefix lengths
  private long cutLength(long a, long b, long[] prefix) {
    if (a >= b) {
      return 0;
    }
    return cutBefore(b, prefix) - cutBefore(a, prefix);
  }

  private long cutBefore(long t, long[] prefix) {
    if (t <= time[0]) {
      return 0;
    }
    if (t >= time[intervals]) {
      return prefix[intervals];
    }
    int k = Arrays.binarySearch(time, 0, intervals + 1, t);
    if (k >= 0) {
      return prefix[k];
    }
    k = -k - 2;
    return prefix[k] + (inCut[k] ? t - time[k] : 0);
  }

  // the energy a task with starts in [e, l], duration p and use r must spend in the cut
  private long need(long e, long l, long p, long r, long[] prefix) {
    long outside = l + p - e - cutLength(e, l + p, prefix);
    long need = p - outside;
    if (compulsoryParts && l < e + p) {
      need = Math.max(need, cutLength(l, e + p, prefix));
    }
    return need > 0 ? r * need : 0;
  }

  /** The constraint prunes no values, so it explains only failures. */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return false;
  }

  /**
   * Explains a failure by the minimum cut: a union U of intervals and the tasks that must spend
   * more energy in it than the capacity gives. A task's bounds are weakened while the energy stays
   * above the capacity, and tasks are left out while it does.
   */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (getClass() != HornFlow.class) {
      return false;
    }
    int now = trail.size();
    if (!load(trail, now) || feasible()) {
      return false;
    }
    long[] prefix = new long[intervals + 1];
    for (int k = 0; k < intervals; k++) {
      prefix[k + 1] = prefix[k] + (inCut[k] ? time[k + 1] - time[k] : 0);
    }
    long cut = prefix[intervals];
    long[] needs = new long[m];
    long total = 0;
    for (int j = 0; j < m; j++) {
      needs[j] = need(est[j], lst[j], dur[j], use[j], prefix);
      total += needs[j];
    }
    long slack = total - capacity * cut - 1;
    if (slack < 0) {
      return false;
    }
    // the tasks that need the least are left out first
    Integer[] order = new Integer[m];
    for (int j = 0; j < m; j++) {
      order[j] = j;
    }
    Arrays.sort(order, (a, b) -> Long.compare(needs[a], needs[b]));
    int mark = out.size();
    for (int j : order) {
      if (needs[j] == 0) {
        continue;
      }
      if (needs[j] <= slack) {
        slack -= needs[j];
        continue;
      }
      slack = citeTask(trail, now, j, needs[j], slack, prefix, out);
      if (slack < 0) {
        out.truncate(mark);
        return false;
      }
    }
    long lifted = cut > 0 ? capacity + slack / cut : capacity;
    trail.addBoundReaching(limit, now, false, Math.min(lifted, IntDomain.MAX_INT), out);
    out.sortUnique(mark);
    return true;
  }

  // cites the bounds of task j, weakening its start bounds while its need drops by at most slack;
  // returns the slack left
  private long citeTask(
      AtomicTrail trail, int now, int j, long need, long slack, long[] prefix, EntryList out) {
    int i = task[j];
    long p = dur[j];
    long r = use[j];
    trail.addBoundReaching(durations[i], now, true, p, out);
    trail.addBoundReaching(resources[i], now, true, r, out);
    IntVar s = starts[i];
    IntDomain root = trail.rootDomain(s);
    long target = need - slack;
    // the earliest start: the smallest e with need(e, lst) >= target
    long lo = root.min();
    long hi = est[j];
    while (lo < hi) {
      long mid = lo + (hi - lo) / 2;
      if (need(mid, lst[j], p, r, prefix) >= target) {
        hi = mid;
      } else {
        lo = mid + 1;
      }
    }
    long e = trail.addBoundReaching(s, now, true, lo, out);
    // the latest start: the largest l with need(e, l) >= target
    lo = lst[j];
    hi = root.max();
    while (lo < hi) {
      long mid = lo + (hi - lo + 1) / 2;
      if (need(e, mid, p, r, prefix) >= target) {
        lo = mid;
      } else {
        hi = mid - 1;
      }
    }
    long l = trail.addBoundReaching(s, now, false, lo, out);
    return slack - (need - need(e, l, p, r, prefix));
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    return grounded() && holds();
  }

  // the fixed tasks never use more than the fixed capacity
  private boolean holds() {
    long[] events = new long[2 * n];
    int e = 0;
    for (int i = 0; i < n; i++) {
      if (durations[i].value() > 0 && resources[i].value() > 0) {
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
        load += resources[i].value();
        if (load > limit.value()) {
          return false;
        }
      } else {
        load -= resources[i].value();
      }
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : HornFlow(").append(Arrays.toString(starts));
    result.append(", ").append(Arrays.toString(durations));
    result.append(", ").append(Arrays.toString(resources));
    return result.append(", ").append(limit).append(")").toString();
  }

  @Override
  public HornFlow copy(VarMap map) {
    HornFlow copy =
        new HornFlow(map.get(starts), map.get(durations), map.get(resources), map.get(limit));
    copy.useCompulsoryParts(compulsoryParts);
    return copy;
  }
}
