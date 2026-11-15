/*
 * ProjectSchedule.java
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Random;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.core.IntVar;
import org.jacop.lcg.LinearForm;

/**
 * A primal heuristic for resource-constrained project scheduling with a makespan objective: the
 * tasks of the cumulative resources of a model (fixed durations, demands and capacities), the
 * precedences between their starts (rows {@code s[a] + lag <= s[b]}) and the rows {@code cost >=
 * s[a] + lag} that make the cost a makespan. Other constraints are not part of it; the caller
 * checks each schedule in the store.
 *
 * <p>Schedules are built from activity lists by the serial schedule generation scheme (Kelley 1963;
 * Kolisch, "Serial and parallel resource-constrained project scheduling methods revisited", EJOR
 * 90, 1996) and improved by forward-backward improvement, the double justification of Li and Willis
 * ("An iterative scheduling technique for resource-constrained project scheduling", EJOR 56, 1992)
 * and Valls, Ballestín and Quintanilla ("Justification and RCPSP: A technique that pays", EJOR 165,
 * 2005). The activity lists evolve in the genetic algorithm of Hartmann ("A competitive genetic
 * algorithm for resource-constrained project scheduling", Naval Research Logistics 45, 1998):
 * two-point crossover, which keeps lists precedence feasible, and swaps of neighbours; each child
 * is replaced by the list of its justified schedule.
 */
public final class ProjectSchedule {

  /** Receives the better schedules. */
  public interface Listener {
    /**
     * A schedule better than all before it.
     *
     * @param start the start of each task, in the order of {@link #starts()}
     * @param makespan its makespan
     * @return false to stop the search
     */
    boolean improved(int[] start, int makespan);

    /**
     * Whether the search must stop now.
     *
     * @return true to stop
     */
    boolean stop();

    /**
     * The best cost known elsewhere; schedules must beat it to be reported.
     *
     * @return the bound
     */
    default long bound() {
      return Long.MAX_VALUE;
    }
  }

  // the most tasks and the most cells of the resource profiles
  private static final int MAX_TASKS = 5_000;
  private static final long MAX_CELLS = 20_000_000L;
  // the longest horizon: the profiles are scanned time unit by time unit
  private static final long MAX_HORIZON = 100_000L;

  private final IntVar[] startVar;
  private final int n;
  private final int[] dur;
  private final int[] release;
  private final int[] latest;
  // resources: capacity and, per resource, the tasks on it and their demands
  private final int[] cap;
  private final int[][] resTasks;
  private final int[][] resDemand;
  // per task: the resources it uses and its demand on each
  private final int[][] taskRes;
  private final int[][] taskDem;
  // precedences: successors and predecessors with lags
  private final int[][] succ;
  private final int[][] succLag;
  private final int[][] pred;
  private final int[][] predLag;
  // cost >= s + sinkLag[t]; Integer.MIN_VALUE when no such row
  private final int[] sinkLag;
  private final int horizon;
  private final long lowerBound;
  // direct precedence between two tasks, for the swap mutation
  private final long[][] before;

  private final Random random;
  private int[][] use;

  // statistics
  private long schedules;
  private long improvements;
  private long restarts;

  private ProjectSchedule(
      IntVar[] startVar,
      int[] dur,
      int[] cap,
      List<int[]> resTaskList,
      List<int[]> resDemList,
      List<int[]> arcs,
      int[] sinkLag,
      int horizon,
      long lowerBound,
      long seed) {
    this.startVar = startVar;
    this.n = startVar.length;
    this.dur = dur;
    this.cap = cap;
    this.resTasks = resTaskList.toArray(new int[0][]);
    this.resDemand = resDemList.toArray(new int[0][]);
    this.sinkLag = sinkLag;
    this.horizon = horizon;
    this.lowerBound = lowerBound;
    this.random = new Random(seed);
    release = new int[n];
    latest = new int[n];
    for (int t = 0; t < n; t++) {
      release[t] = startVar[t].min();
      latest[t] = startVar[t].max();
    }
    int[] rc = new int[n];
    for (int[] tasks : resTasks) {
      for (int t : tasks) {
        rc[t]++;
      }
    }
    taskRes = new int[n][];
    taskDem = new int[n][];
    for (int t = 0; t < n; t++) {
      taskRes[t] = new int[rc[t]];
      taskDem[t] = new int[rc[t]];
      rc[t] = 0;
    }
    for (int r = 0; r < resTasks.length; r++) {
      for (int k = 0; k < resTasks[r].length; k++) {
        int t = resTasks[r][k];
        taskRes[t][rc[t]] = r;
        taskDem[t][rc[t]] = resDemand[r][k];
        rc[t]++;
      }
    }
    int[] sc = new int[n];
    int[] pc = new int[n];
    for (int[] a : arcs) {
      sc[a[0]]++;
      pc[a[1]]++;
    }
    succ = new int[n][];
    succLag = new int[n][];
    pred = new int[n][];
    predLag = new int[n][];
    for (int t = 0; t < n; t++) {
      succ[t] = new int[sc[t]];
      succLag[t] = new int[sc[t]];
      pred[t] = new int[pc[t]];
      predLag[t] = new int[pc[t]];
      sc[t] = 0;
      pc[t] = 0;
    }
    before = new long[n][(n + 63) >>> 6];
    for (int[] a : arcs) {
      succ[a[0]][sc[a[0]]] = a[1];
      succLag[a[0]][sc[a[0]]++] = a[2];
      pred[a[1]][pc[a[1]]] = a[0];
      predLag[a[1]][pc[a[1]]++] = a[2];
      before[a[0]][a[1] >>> 6] |= 1L << a[1];
    }
    use = new int[cap.length][horizon + 1];
  }

  /**
   * Finds the project scheduling structure around a cost variable: the cost must be bounded below
   * by rows {@code cost >= s + lag} of task starts, the tasks are the starts of the cumulative
   * constraints reached from them through their constraints, with fixed durations, demands and
   * capacities, and the precedences are the two-variable rows between task starts.
   *
   * @param cost the cost variable, minimised
   * @param seed the seed of the random choices
   * @return the structure, or null when the model is not of this kind
   */
  public static ProjectSchedule detect(IntVar cost, long seed) {
    Map<IntVar, Integer> taskOf = new IdentityHashMap<>();
    List<IntVar> tasks = new ArrayList<>();
    List<Integer> durations = new ArrayList<>();
    Map<IntVar, Integer> sink = new IdentityHashMap<>();
    for (Constraint c : cost.dom().constraints()) {
      int[] lag = new int[1];
      IntVar s = sinkRow(c, cost, lag);
      if (s != null) {
        sink.merge(s, lag[0], Math::max);
      }
    }
    if (sink.isEmpty()) {
      return null;
    }
    // breadth-first over the task starts and their constraints
    ArrayDeque<IntVar> queue = new ArrayDeque<>();
    Map<Constraint, Boolean> seen = new IdentityHashMap<>();
    List<CumulativeBasic> resources = new ArrayList<>();
    for (IntVar s : sink.keySet()) {
      addTask(s, -1, taskOf, tasks, durations, queue);
    }
    List<IntVar[]> arcVars = new ArrayList<>();
    List<Integer> arcLags = new ArrayList<>();
    while (!queue.isEmpty()) {
      IntVar x = queue.poll();
      for (Constraint c : x.dom().constraints()) {
        if (seen.put(c, Boolean.TRUE) != null) {
          continue;
        }
        if (c instanceof CumulativeBasic cb) {
          if (c.getClass().getSimpleName().contains("Optional")) {
            return null;
          }
          IntVar[][] t = cb.tasks();
          if (!cb.limit().singleton()) {
            return null;
          }
          for (int k = 0; k < t[0].length; k++) {
            if (!t[1][k].singleton() || !t[2][k].singleton()) {
              return null;
            }
            if (t[1][k].value() > 0 && t[2][k].value() > 0) {
              if (t[2][k].value() > cb.limit().value()) {
                return null;
              }
              if (!addTask(t[0][k], t[1][k].value(), taskOf, tasks, durations, queue)) {
                return null;
              }
            }
          }
          resources.add(cb);
          continue;
        }
        int[] lag = new int[1];
        IntVar[] arc = precedenceRow(c, lag);
        if (arc != null && arc[0] != cost && arc[1] != cost) {
          arcVars.add(arc);
          arcLags.add(lag[0]);
          addTask(arc[0], -1, taskOf, tasks, durations, queue);
          addTask(arc[1], -1, taskOf, tasks, durations, queue);
        }
      }
      if (tasks.size() > MAX_TASKS) {
        return null;
      }
    }
    if (resources.isEmpty() || tasks.size() < 3) {
      return null;
    }
    int n = tasks.size();
    int[] dur = new int[n];
    for (int t = 0; t < n; t++) {
      dur[t] = Math.max(0, durations.get(t));
    }
    // resources, with the tasks of positive duration and demand
    int[] cap = new int[resources.size()];
    List<int[]> resTaskList = new ArrayList<>();
    List<int[]> resDemList = new ArrayList<>();
    for (int r = 0; r < cap.length; r++) {
      CumulativeBasic cb = resources.get(r);
      IntVar[][] t = cb.tasks();
      cap[r] = cb.limit().value();
      int[] ts = new int[t[0].length];
      int[] ds = new int[t[0].length];
      int m = 0;
      boolean[] in = new boolean[n];
      for (int k = 0; k < t[0].length; k++) {
        if (t[1][k].value() > 0 && t[2][k].value() > 0) {
          int task = taskOf.get(t[0][k]);
          if (in[task]) {
            return null;
          }
          in[task] = true;
          ts[m] = task;
          ds[m++] = t[2][k].value();
        }
      }
      resTaskList.add(Arrays.copyOf(ts, m));
      resDemList.add(Arrays.copyOf(ds, m));
    }
    if (!cumulative(resDemList, cap)) {
      // machines only: the disjunctive scheduling of local search is the heuristic for them
      return null;
    }
    List<int[]> arcs = new ArrayList<>();
    for (int k = 0; k < arcVars.size(); k++) {
      arcs.add(
          new int[] {taskOf.get(arcVars.get(k)[0]), taskOf.get(arcVars.get(k)[1]), arcLags.get(k)});
    }
    int[] sinkLag = new int[n];
    Arrays.fill(sinkLag, Integer.MIN_VALUE);
    for (Map.Entry<IntVar, Integer> e : sink.entrySet()) {
      sinkLag[taskOf.get(e.getKey())] = e.getValue();
    }
    // the horizon: the latest end of a task
    long h = 0;
    long serial = 0;
    for (int t = 0; t < n; t++) {
      serial += dur[t];
      h = Math.max(h, (long) tasks.get(t).min());
    }
    for (int[] a : arcs) {
      serial += Math.max(0, a[2]);
    }
    h += serial;
    long latestEnd = 0;
    for (int t = 0; t < n; t++) {
      latestEnd = Math.max(latestEnd, (long) tasks.get(t).max() + dur[t]);
    }
    h = Math.min(h, latestEnd);
    if (h <= 0 || h > MAX_HORIZON || h * cap.length > MAX_CELLS) {
      return null;
    }
    if (tasks.stream().anyMatch(x -> x.min() < 0)) {
      return null;
    }
    ProjectSchedule ps =
        new ProjectSchedule(
            tasks.toArray(new IntVar[0]),
            dur,
            cap,
            resTaskList,
            resDemList,
            arcs,
            sinkLag,
            (int) h,
            cost.min(),
            seed);
    return ps.topological(ps.identityKeys(), false) == null ? null : ps;
  }

  // whether some resource lets two of its tasks run together: not every resource is a machine
  private static boolean cumulative(List<int[]> demands, int[] cap) {
    for (int r = 0; r < cap.length; r++) {
      int smallest = Integer.MAX_VALUE;
      int second = Integer.MAX_VALUE;
      for (int d : demands.get(r)) {
        if (d < smallest) {
          second = smallest;
          smallest = d;
        } else if (d < second) {
          second = d;
        }
      }
      if (second != Integer.MAX_VALUE && (long) smallest + second <= cap[r]) {
        return true;
      }
    }
    return false;
  }

  private static boolean addTask(
      IntVar x,
      int d,
      Map<IntVar, Integer> taskOf,
      List<IntVar> tasks,
      List<Integer> durations,
      ArrayDeque<IntVar> queue) {
    Integer t = taskOf.get(x);
    if (t == null) {
      taskOf.put(x, tasks.size());
      tasks.add(x);
      durations.add(d);
      queue.add(x);
      return true;
    }
    int old = durations.get(t);
    if (d >= 0) {
      if (old >= 0 && old != d) {
        // one start with two durations
        return false;
      }
      durations.set(t, d);
    }
    return true;
  }

  // a row cost >= s + lag (a cost - a s >= b, a > 0): s, with lag[0] = ceil(b / a)
  private static IntVar sinkRow(Constraint c, IntVar cost, int[] lag) {
    LinearForm f = LinearForms.of(c);
    if (f == null || f.vars().length != 2 || f.relation() == LinearForm.NE) {
      return null;
    }
    int k = f.vars()[0] == cost ? 0 : f.vars()[1] == cost ? 1 : -1;
    if (k < 0 || f.vars()[1 - k] == cost) {
      return null;
    }
    long a = f.weights()[k];
    long b = f.weights()[1 - k];
    if (a != -b) {
      return null;
    }
    long rhs = f.c();
    // normalise to a cost - a s >= rhs with a > 0
    if (f.relation() == LinearForm.LE) {
      a = -a;
      rhs = -rhs;
    } else if (f.relation() == LinearForm.EQ && a < 0) {
      a = -a;
      rhs = -rhs;
    }
    if (a <= 0) {
      return null;
    }
    long l = Math.ceilDiv(rhs, a);
    if (l < Integer.MIN_VALUE / 4 || l > Integer.MAX_VALUE / 4) {
      return null;
    }
    lag[0] = (int) l;
    return f.vars()[1 - k];
  }

  // a row s[a] + lag <= s[b] between two variables: {a, b}, with lag[0]
  private static IntVar[] precedenceRow(Constraint c, int[] lag) {
    LinearForm f = LinearForms.of(c);
    if (f == null
        || f.vars().length != 2
        || (f.relation() != LinearForm.LE && f.relation() != LinearForm.GE)) {
      return null;
    }
    long a0 = f.weights()[0];
    long a1 = f.weights()[1];
    long r = f.c();
    if (f.relation() == LinearForm.GE) {
      a0 = -a0;
      a1 = -a1;
      r = -r;
    }
    if (a0 != -a1 || a0 == 0 || f.vars()[0] == f.vars()[1]) {
      return null;
    }
    // a x - a y <= r: y >= x - floor(r / a) for a > 0
    long a = Math.abs(a0);
    long l = -Math.floorDiv(r, a);
    if (l < Integer.MIN_VALUE / 4 || l > Integer.MAX_VALUE / 4) {
      return null;
    }
    lag[0] = (int) l;
    return a0 > 0
        ? new IntVar[] {f.vars()[0], f.vars()[1]}
        : new IntVar[] {f.vars()[1], f.vars()[0]};
  }

  /**
   * The start variables of the tasks.
   *
   * @return the starts, in the order of the schedules reported
   */
  public IntVar[] starts() {
    return startVar;
  }

  /**
   * The number of tasks.
   *
   * @return the tasks
   */
  public int tasks() {
    return n;
  }

  /**
   * The number of cumulative resources.
   *
   * @return the resources
   */
  public int resources() {
    return cap.length;
  }

  /**
   * The schedules built so far.
   *
   * @return the schedules
   */
  public long schedules() {
    return schedules;
  }

  /**
   * The better schedules found so far.
   *
   * @return the improvements
   */
  public long improvements() {
    return improvements;
  }

  // ------------------------------------------------------------ lists

  private double[] identityKeys() {
    double[] k = new double[n];
    for (int t = 0; t < n; t++) {
      k[t] = t;
    }
    return k;
  }

  /**
   * A precedence-feasible order of the tasks, ready tasks taken by the smallest key (the largest
   * when backward, over the reversed graph); null when the precedences have a cycle.
   */
  private int[] topological(double[] key, boolean backward) {
    int[][] in = backward ? succ : pred;
    int[][] out = backward ? pred : succ;
    int[] deg = new int[n];
    PriorityQueue<Integer> ready =
        new PriorityQueue<>(
            (a, b) -> {
              int c = backward ? Double.compare(key[b], key[a]) : Double.compare(key[a], key[b]);
              return c != 0 ? c : Integer.compare(a, b);
            });
    for (int t = 0; t < n; t++) {
      deg[t] = in[t].length;
      if (deg[t] == 0) {
        ready.add(t);
      }
    }
    int[] order = new int[n];
    int m = 0;
    while (!ready.isEmpty()) {
      int t = ready.poll();
      order[m++] = t;
      for (int s : out[t]) {
        if (--deg[s] == 0) {
          ready.add(s);
        }
      }
    }
    return m == n ? order : null;
  }

  // ------------------------------------------------------------ schedule generation

  // the earliest time >= from at which task t fits on its resources, or -1 beyond its latest start
  private int earliestFit(int t, int from) {
    int d = dur[t];
    int s = from;
    int[] rs = taskRes[t];
    int[] ds = taskDem[t];
    outer:
    while (true) {
      if (s > latest[t] || s + d > horizon) {
        return -1;
      }
      for (int u = s + d - 1; u >= s; u--) {
        for (int k = 0; k < rs.length; k++) {
          if (use[rs[k]][u] + ds[k] > cap[rs[k]]) {
            s = u + 1;
            continue outer;
          }
        }
      }
      return s;
    }
  }

  // the latest time <= from at which task t fits on its resources, or -1 before its release
  private int latestFit(int t, int from) {
    int d = dur[t];
    int s = Math.min(from, horizon - d);
    int[] rs = taskRes[t];
    int[] ds = taskDem[t];
    outer:
    while (true) {
      if (s < release[t]) {
        return -1;
      }
      for (int u = s; u < s + d; u++) {
        for (int k = 0; k < rs.length; k++) {
          if (use[rs[k]][u] + ds[k] > cap[rs[k]]) {
            s = u - d;
            continue outer;
          }
        }
      }
      return s;
    }
  }

  private void place(int t, int s, int sign) {
    int[] rs = taskRes[t];
    int[] ds = taskDem[t];
    for (int k = 0; k < rs.length; k++) {
      int[] row = use[rs[k]];
      int dd = sign * ds[k];
      for (int u = s; u < s + dur[t]; u++) {
        row[u] += dd;
      }
    }
  }

  /**
   * The serial schedule generation scheme: the tasks in list order, each at its earliest precedence
   * and resource feasible start.
   *
   * @return the makespan, or Long.MAX_VALUE when a task cannot start before its latest start
   */
  private long forward(int[] list, int[] start) {
    schedules++;
    long makespan = Long.MIN_VALUE;
    int placed = 0;
    for (; placed < list.length; placed++) {
      int t = list[placed];
      int es = release[t];
      for (int k = 0; k < pred[t].length; k++) {
        es = Math.max(es, start[pred[t][k]] + predLag[t][k]);
      }
      int s = earliestFit(t, es);
      if (s < 0) {
        break;
      }
      start[t] = s;
      place(t, s, 1);
      if (sinkLag[t] != Integer.MIN_VALUE) {
        makespan = Math.max(makespan, (long) s + sinkLag[t]);
      }
    }
    for (int k = 0; k < placed; k++) {
      place(list[k], start[list[k]], -1);
    }
    return placed < list.length ? Long.MAX_VALUE : makespan;
  }

  /**
   * The backward pass of the justification: the tasks by decreasing end, each at its latest start
   * that keeps the successors, the makespan and the resources.
   *
   * @return false when a task would start before its release
   */
  private boolean backward(int[] start, long makespan, int[] late) {
    double[] key = new double[n];
    for (int t = 0; t < n; t++) {
      key[t] = start[t] + dur[t] + random.nextDouble() * 1e-3;
    }
    int[] order = topological(key, true);
    int placed = 0;
    boolean ok = true;
    for (; placed < n; placed++) {
      int t = order[placed];
      long ls = latest[t];
      if (sinkLag[t] != Integer.MIN_VALUE) {
        ls = Math.min(ls, makespan - sinkLag[t]);
      }
      for (int k = 0; k < succ[t].length; k++) {
        ls = Math.min(ls, (long) late[succ[t][k]] - succLag[t][k]);
      }
      int s = ls < 0 ? -1 : latestFit(t, (int) Math.min(ls, Integer.MAX_VALUE / 2));
      if (s < 0) {
        ok = false;
        break;
      }
      late[t] = s;
      place(t, s, 1);
    }
    for (int k = 0; k < placed; k++) {
      place(order[k], late[order[k]], -1);
    }
    return ok;
  }

  // the list of a schedule: tasks by start, kept precedence feasible
  private int[] listOf(int[] start) {
    double[] key = new double[n];
    for (int t = 0; t < n; t++) {
      key[t] = start[t] + random.nextDouble() * 1e-3;
    }
    return topological(key, false);
  }

  /**
   * Decodes a list and improves the schedule by forward-backward passes while they shorten it.
   * Replaces the list by the list of the final schedule.
   *
   * @return the makespan, Long.MAX_VALUE when infeasible
   */
  private long decode(int[] list, int[] start) {
    long best = forward(list, start);
    if (best == Long.MAX_VALUE) {
      return best;
    }
    int[] late = new int[n];
    int[] next = new int[n];
    for (int pass = 0; pass < 4; pass++) {
      if (!backward(start, best, late)) {
        break;
      }
      int[] l = listOf(late);
      long m = forward(l, next);
      if (m > best) {
        break;
      }
      boolean better = m < best;
      best = m;
      System.arraycopy(next, 0, start, 0, n);
      if (!better) {
        break;
      }
    }
    int[] l = listOf(start);
    System.arraycopy(l, 0, list, 0, n);
    return best;
  }

  // ------------------------------------------------------------ priority rules

  // latest finish times of the precedence graph from the horizon, by reverse topological order
  private long[] latestFinish() {
    int[] order = topological(identityKeys(), false);
    long[] lf = new long[n];
    long[] es = new long[n];
    long m = 0;
    for (int t : order) {
      long e = release[t];
      for (int k = 0; k < pred[t].length; k++) {
        e = Math.max(e, es[pred[t][k]] + predLag[t][k]);
      }
      es[t] = e;
      if (sinkLag[t] != Integer.MIN_VALUE) {
        m = Math.max(m, e + sinkLag[t]);
      }
    }
    for (int i = n - 1; i >= 0; i--) {
      int t = order[i];
      long l = sinkLag[t] != Integer.MIN_VALUE ? m - sinkLag[t] : m;
      for (int k = 0; k < succ[t].length; k++) {
        l = Math.min(l, lf[succ[t][k]] - succLag[t][k]);
      }
      lf[t] = l;
    }
    // lf holds latest starts; finish = start + duration
    for (int t = 0; t < n; t++) {
      lf[t] += dur[t];
    }
    return lf;
  }

  private int[] successorsCount() {
    int[] order = topological(identityKeys(), false);
    long[][] reach = new long[n][(n + 63) >>> 6];
    int[] count = new int[n];
    for (int i = n - 1; i >= 0; i--) {
      int t = order[i];
      for (int s : succ[t]) {
        reach[t][s >>> 6] |= 1L << s;
        long[] rs = reach[s];
        long[] rt = reach[t];
        for (int w = 0; w < rt.length; w++) {
          rt[w] |= rs[w];
        }
      }
      for (long w : reach[t]) {
        count[t] += Long.bitCount(w);
      }
    }
    return count;
  }

  // ------------------------------------------------------------ genetic algorithm

  // the population: lists and makespans, the better half first
  private int pop;
  private int[][] lists;
  private long[] fit;
  private long best = Long.MAX_VALUE;
  private int[] bestStart;
  private long lastImprovement;
  private long lastRestart;
  private long[] lf;
  private int[] work;
  private int[] child;
  private int[] child2;
  private boolean[] taken;
  // the listener of the current search, null while improving a solution of another search
  private Listener listener;
  private boolean over;

  /**
   * Searches for short schedules until the listener stops it, no better schedule was found in
   * {@code patience} schedules, or the makespan reaches the lower bound of the cost.
   *
   * @param listener receives the better schedules
   * @param patience the schedules without improvement after which the search ends
   */
  public void run(Listener listener, long patience) {
    this.listener = listener;
    try {
      if (!initialise()) {
        return;
      }
      while (!over && !listener.stop() && schedules - lastImprovement <= patience) {
        generation();
      }
    } finally {
      this.listener = null;
    }
  }

  /**
   * Goes on with the genetic algorithm from a solution found by another search, for a number of
   * schedules: the list of that solution joins the population.
   *
   * @param incumbent the start of each task in that solution, in the order of {@link #starts()}
   * @param budget the schedules to build
   * @return a schedule with a shorter makespan than the incumbent's, or null
   */
  public int[] improve(int[] incumbent, long budget) {
    long m = Long.MIN_VALUE;
    for (int t = 0; t < n; t++) {
      if (incumbent[t] < release[t] || incumbent[t] > latest[t]) {
        return null;
      }
      if (sinkLag[t] != Integer.MIN_VALUE) {
        m = Math.max(m, (long) incumbent[t] + sinkLag[t]);
      }
    }
    over = false;
    if (lists == null && !initialise()) {
      return null;
    }
    if (m < best) {
      // the other search is ahead: its list replaces the worst one
      int[] l = listOf(incumbent);
      long f = decode(l, work);
      lists[2 * pop - 1] = l;
      fit[2 * pop - 1] = f;
      consider(f, work);
      if (f >= m) {
        best = m;
        bestStart = incumbent.clone();
        lastImprovement = schedules;
      }
      sort(lists, fit);
    }
    long end = schedules + budget;
    while (!over && schedules < end) {
      generation();
    }
    return best < m ? bestStart.clone() : null;
  }

  /**
   * The first population: priority rules (latest finish, most total successors, latest start), then
   * biased random sampling around latest finish.
   *
   * @return false when the search is over
   */
  private boolean initialise() {
    if (lists != null) {
      return !over;
    }
    pop = n <= 60 ? 30 : 40;
    lists = new int[2 * pop][];
    fit = new long[2 * pop];
    work = new int[n];
    child = new int[n];
    child2 = new int[n];
    taken = new boolean[n];
    lf = latestFinish();
    int[] mts = successorsCount();
    for (int i = 0; i < 2 * pop; i++) {
      double[] key = new double[n];
      for (int t = 0; t < n; t++) {
        key[t] =
            switch (i) {
              case 0 -> lf[t];
              case 1 -> -mts[t];
              case 2 -> lf[t] - dur[t];
              default -> lf[t] * (1 + 0.5 * random.nextDouble()) + random.nextDouble();
            };
      }
      lists[i] = topological(key, false);
      fit[i] = decode(lists[i], work);
      consider(fit[i], work);
      if (over || (listener != null && listener.stop())) {
        // the population is complete enough to go on later
        for (int j = i + 1; j < 2 * pop; j++) {
          lists[j] = lists[i].clone();
          fit[j] = fit[i];
        }
        sort(lists, fit);
        return false;
      }
    }
    sort(lists, fit);
    lastRestart = schedules;
    return true;
  }

  // a decoded schedule: the best one so far is kept and reported
  private void consider(long f, int[] start) {
    if (f >= best) {
      return;
    }
    best = f;
    bestStart = start.clone();
    lastImprovement = schedules;
    if (listener != null && f < listener.bound() && !report(listener, start, f)) {
      over = true;
    }
    if (f <= lowerBound) {
      over = true;
    }
  }

  /**
   * One generation: the children of random pairs replace the worse half; a population that found
   * nothing better for a while starts again around the best list, half of it by shifts of that list
   * and half by biased random sampling.
   */
  private void generation() {
    long restartAfter = Math.max(5_000, 100L * n);
    if (schedules - Math.max(lastImprovement, lastRestart) > restartAfter) {
      restarts++;
      lastRestart = schedules;
      for (int i = 1; i < 2 * pop && !over; i++) {
        int[] l;
        if (i % 2 == 0) {
          double[] key = new double[n];
          for (int t = 0; t < n; t++) {
            key[t] = lf[t] * (1 + 0.5 * random.nextDouble()) + random.nextDouble();
          }
          l = topological(key, false);
        } else {
          l = lists[0].clone();
          int shifts = 1 + random.nextInt(Math.max(1, n / 8));
          for (int k = 0; k < shifts; k++) {
            shift(l);
          }
        }
        fit[i] = decode(l, work);
        lists[i] = l;
        consider(fit[i], work);
      }
      sort(lists, fit);
      return;
    }
    for (int c = pop; c < 2 * pop && !over; c += 2) {
      int a = random.nextInt(pop);
      int b = random.nextInt(pop);
      while (b == a) {
        b = random.nextInt(pop);
      }
      int q1 = random.nextInt(n);
      int q2 = q1 + random.nextInt(n - q1 + 1);
      crossover(lists[a], lists[b], q1, q2, child, taken);
      crossover(lists[b], lists[a], q1, q2, child2, taken);
      for (int which = 0; which < 2 && c + which < 2 * pop; which++) {
        int[] l = (which == 0 ? child : child2).clone();
        mutate(l);
        if (random.nextInt(4) == 0) {
          shift(l);
        }
        long f = decode(l, work);
        lists[c + which] = l;
        fit[c + which] = f;
        consider(f, work);
      }
    }
    sort(lists, fit);
  }

  /**
   * Moves a random task of a list to a random position between its last predecessor and its first
   * successor in the list, which keeps the list precedence feasible.
   */
  private void shift(int[] list) {
    int i = random.nextInt(n);
    int t = list[i];
    int lo = i;
    while (lo > 0 && (before[list[lo - 1]][t >>> 6] & (1L << t)) == 0) {
      lo--;
    }
    int hi = i;
    while (hi + 1 < n && (before[t][list[hi + 1] >>> 6] & (1L << list[hi + 1])) == 0) {
      hi++;
    }
    int j = lo + random.nextInt(hi - lo + 1);
    if (j < i) {
      System.arraycopy(list, j, list, j + 1, i - j);
    } else if (j > i) {
      System.arraycopy(list, i + 1, list, i, j - i);
    }
    list[j] = t;
  }

  private boolean report(Listener listener, int[] start, long makespan) {
    improvements++;
    return listener.improved(start.clone(), (int) makespan);
  }

  // Hartmann's two-point crossover: positions before q1 from the first parent, then up to q2 the
  // first parent's ... in the second's order, then the rest in the first's order
  private void crossover(int[] mother, int[] father, int q1, int q2, int[] child, boolean[] taken) {
    Arrays.fill(taken, false);
    int m = 0;
    for (int i = 0; i < q1; i++) {
      child[m++] = mother[i];
      taken[mother[i]] = true;
    }
    for (int i = 0; i < n && m < q2; i++) {
      if (!taken[father[i]]) {
        child[m++] = father[i];
        taken[father[i]] = true;
      }
    }
    for (int i = 0; i < n && m < n; i++) {
      if (!taken[mother[i]]) {
        child[m++] = mother[i];
        taken[mother[i]] = true;
      }
    }
  }

  // swaps of neighbours that are not in a direct precedence
  private void mutate(int[] list) {
    double p = 0.05;
    for (int i = 0; i + 1 < n; i++) {
      if (random.nextDouble() < p) {
        int a = list[i];
        int b = list[i + 1];
        if ((before[a][b >>> 6] & (1L << b)) == 0) {
          list[i] = b;
          list[i + 1] = a;
        }
      }
    }
  }

  private static void sort(int[][] lists, long[] fit) {
    Integer[] idx = new Integer[lists.length];
    for (int i = 0; i < idx.length; i++) {
      idx[i] = i;
    }
    Arrays.sort(idx, (a, b) -> Long.compare(fit[a], fit[b]));
    int[][] l = new int[lists.length][];
    long[] f = new long[lists.length];
    for (int i = 0; i < idx.length; i++) {
      l[i] = lists[idx[i]];
      f[i] = fit[idx[i]];
    }
    System.arraycopy(l, 0, lists, 0, l.length);
    System.arraycopy(f, 0, fit, 0, f.length);
  }

  /**
   * The restarts of the population so far.
   *
   * @return the restarts
   */
  public long restarts() {
    return restarts;
  }

  @Override
  public String toString() {
    return "ProjectSchedule(tasks "
        + n
        + ", resources "
        + cap.length
        + ", schedules "
        + schedules
        + ", improvements "
        + improvements
        + ")";
  }
}
