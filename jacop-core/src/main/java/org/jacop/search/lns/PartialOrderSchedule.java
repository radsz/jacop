/*
 * PartialOrderSchedule.java
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

package org.jacop.search.lns;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.IntUnaryOperator;

/**
 * The partial-order schedule (POS) of a solution over cumulative resources: a set of precedences
 * between its tasks, chained over the units of each resource, under which every schedule that keeps
 * the precedences (and the model's own temporal constraints) uses no resource above its limit. A
 * neighbourhood removes some tasks from the POS and keeps the precedences between the others, so
 * that the others keep their order but not their times: they may move both ways, which leaves room
 * for the removed tasks (Godard, Laborie and Nuijten 2005).
 *
 * <p>The POS is built by chaining (Policella, Cesta, Oddi and Smith 2004): the tasks of a resource,
 * in the order of their starts in the solution, take the units they use from the chains whose last
 * task ends before they start, those that end latest first, and become the last task of those
 * chains. Each chain it takes from gives a precedence from that chain's last task.
 *
 * <p>The precedences between the tasks a neighbourhood keeps are given to the search as a window
 * {@code [est, lst]} of each kept start: the earliest and latest start along the precedences, the
 * removed tasks bridged (a chain through a removed task still orders the tasks before and after
 * it), within the current domain and with every task ending by the end of the solution's schedule.
 * The windows need no new variables or literals, which suits lazy clause generation, but they are
 * weaker than the precedences: two kept tasks whose windows overlap may swap.
 *
 * <p>References:
 *
 * <ul>
 *   <li>D. Godard, P. Laborie, W. Nuijten. Randomized Large Neighborhood Search for Cumulative
 *       Scheduling. ICAPS 2005, 81-89.
 *   <li>N. Policella, A. Cesta, A. Oddi, S. F. Smith. Generating Robust Schedules through Temporal
 *       Flexibility. ICAPS 2004, 209-218.
 * </ul>
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class PartialOrderSchedule {

  // the resources: starts, durations and uses of their tasks and the limit, as references (a node,
  // or -1 - value for a constant)
  private final List<int[]> starts = new ArrayList<>();
  private final List<int[]> durations = new ArrayList<>();
  private final List<int[]> uses = new ArrayList<>();
  private final List<Integer> limits = new ArrayList<>();

  // the tasks: the distinct start nodes, and the task of each start node
  private final List<Integer> taskNodes = new ArrayList<>();
  private final Map<Integer, Integer> taskOfNode = new HashMap<>();
  // the variable nodes of each task's durations and uses, over its resources
  private final List<List<Integer>> taskParts = new ArrayList<>();

  // built from a solution: starts and durations of the tasks, the precedences and their lags, the
  // tasks in the order of their starts and the end of the schedule
  private int[] start = new int[0];
  private int[] duration = new int[0];
  private int[][] succ = new int[0][];
  private int[][] succLag = new int[0][];
  private int[][] pred = new int[0][];
  private int[][] predLag = new int[0][];
  private int[] order = new int[0];
  private long end;
  private int edges;
  private boolean built;

  /**
   * Adds a resource; a constant start is a task of its own.
   *
   * @param s the references of the starts
   * @param d the references of the durations
   * @param r the references of the uses
   * @param limit the reference of the limit
   */
  void addResource(int[] s, int[] d, int[] r, int limit) {
    int[] own = new int[s.length];
    for (int i = 0; i < s.length; i++) {
      Integer t = s[i] >= 0 ? taskOfNode.get(s[i]) : null;
      if (t == null) {
        t = taskNodes.size();
        taskNodes.add(s[i]);
        taskParts.add(new ArrayList<>());
        if (s[i] >= 0) {
          taskOfNode.put(s[i], t);
        }
      }
      own[i] = t;
      if (d[i] >= 0) {
        taskParts.get(t).add(d[i]);
      }
      if (r[i] >= 0) {
        taskParts.get(t).add(r[i]);
      }
    }
    starts.add(own);
    durations.add(d);
    uses.add(r);
    limits.add(limit);
    built = false;
  }

  /** Returns whether there are resources with at least two tasks. */
  boolean usable() {
    return taskNodes.size() > 1;
  }

  /** The number of tasks. */
  int tasks() {
    return taskNodes.size();
  }

  /** The start node of a task, or -1 - value for a constant start. */
  int startNode(int t) {
    return taskNodes.get(t);
  }

  /** The variable nodes of a task's durations and uses. */
  List<Integer> parts(int t) {
    return taskParts.get(t);
  }

  /** Forgets the POS, so that the next use builds it from the new solution. */
  void invalidate() {
    built = false;
  }

  /** Returns the number of precedences of the last POS built. */
  int precedences() {
    return edges;
  }

  /** The tasks in the order of their starts in the solution. */
  int[] order() {
    return order;
  }

  /** The tasks right before and after a task in the POS. */
  int[] neighbours(int t) {
    int[] n = Arrays.copyOf(pred[t], pred[t].length + succ[t].length);
    System.arraycopy(succ[t], 0, n, pred[t].length, succ[t].length);
    return n;
  }

  /**
   * Builds the POS of a solution, unless it was built since the last {@link #invalidate()}.
   *
   * @param value the value of a reference in the solution
   */
  void build(IntUnaryOperator value) {
    if (built) {
      return;
    }
    built = true;
    int n = taskNodes.size();
    start = new int[n];
    duration = new int[n];
    long last = Long.MIN_VALUE;
    for (int t = 0; t < n; t++) {
      start[t] = value.applyAsInt(taskNodes.get(t));
    }
    Map<Long, Integer> lag = new HashMap<>();
    for (int k = 0; k < starts.size(); k++) {
      int[] own = starts.get(k);
      int[] d = new int[own.length];
      int[] r = new int[own.length];
      for (int i = 0; i < own.length; i++) {
        d[i] = value.applyAsInt(durations.get(k)[i]);
        r[i] = value.applyAsInt(uses.get(k)[i]);
        duration[own[i]] = Math.max(duration[own[i]], d[i]);
        last = Math.max(last, (long) start[own[i]] + d[i]);
      }
      chain(own, startsOf(own), d, r, value.applyAsInt(limits.get(k)), lag);
    }
    end = last;
    List<List<int[]>> out = new ArrayList<>();
    List<List<int[]>> in = new ArrayList<>();
    for (int t = 0; t < n; t++) {
      out.add(new ArrayList<>());
      in.add(new ArrayList<>());
    }
    for (Map.Entry<Long, Integer> e : lag.entrySet()) {
      int a = (int) (e.getKey() >>> 32);
      int b = (int) (e.getKey() & 0xffffffffL);
      out.get(a).add(new int[] {b, e.getValue()});
      in.get(b).add(new int[] {a, e.getValue()});
    }
    succ = new int[n][];
    succLag = new int[n][];
    pred = new int[n][];
    predLag = new int[n][];
    for (int t = 0; t < n; t++) {
      // sorted, so that the order of a hash map does not decide anything
      out.get(t).sort((x, y) -> Integer.compare(x[0], y[0]));
      in.get(t).sort((x, y) -> Integer.compare(x[0], y[0]));
      succ[t] = out.get(t).stream().mapToInt(x -> x[0]).toArray();
      succLag[t] = out.get(t).stream().mapToInt(x -> x[1]).toArray();
      pred[t] = in.get(t).stream().mapToInt(x -> x[0]).toArray();
      predLag[t] = in.get(t).stream().mapToInt(x -> x[1]).toArray();
    }
    edges = lag.size();
    Integer[] o = new Integer[n];
    for (int t = 0; t < n; t++) {
      o[t] = t;
    }
    // every precedence has a positive lag, so the order of the starts is a topological order
    Arrays.sort(o, (a, b) -> start[a] != start[b] ? Integer.compare(start[a], start[b]) : a - b);
    order = Arrays.stream(o).mapToInt(Integer::intValue).toArray();
  }

  /**
   * Chains the tasks of one resource: each task, in the order of the starts, takes its units from
   * the chains whose last task ends by its start, the latest first. Tasks of no duration or use
   * take nothing. A resource whose tasks cannot be chained (a solution above the limit) gives no
   * precedences.
   */
  private static void chain(
      int[] own, int[] s, int[] d, int[] r, int limit, Map<Long, Integer> lag) {
    int m = own.length;
    Integer[] o = new Integer[m];
    int count = 0;
    for (int i = 0; i < m; i++) {
      if (d[i] > 0 && r[i] > 0) {
        o[count++] = i;
      }
    }
    if (count < 2) {
      return;
    }
    Integer[] tasks = Arrays.copyOf(o, count);
    Arrays.sort(
        tasks,
        (a, b) ->
            s[a] != s[b] ? Integer.compare(s[a], s[b]) : Integer.compare(s[a] + d[a], s[b] + d[b]));
    // the chains, grouped by their last task: last task (index into own, -1 for none), its end,
    // units
    List<long[]> groups = new ArrayList<>();
    groups.add(new long[] {-1, Long.MIN_VALUE, limit});
    Map<Long, Integer> mine = new HashMap<>();
    for (int i : tasks) {
      long st = s[i];
      long need = r[i];
      // the chains free by the start, the latest end first; ties to the earlier group
      List<long[]> free = new ArrayList<>();
      for (long[] g : groups) {
        if (g[1] <= st) {
          free.add(g);
        }
      }
      free.sort((x, y) -> Long.compare(y[1], x[1]));
      for (long[] g : free) {
        if (need == 0) {
          break;
        }
        long take = Math.min(need, g[2]);
        need -= take;
        g[2] -= take;
        if (g[0] >= 0) {
          int a = own[(int) g[0]];
          int b = own[i];
          if (a != b) {
            mine.merge(((long) a << 32) | b, d[(int) g[0]], Math::max);
          }
        }
      }
      if (need > 0) {
        // the solution uses more than the limit, or the limit is not what the solution had
        return;
      }
      groups.removeIf(g -> g[2] == 0);
      groups.add(new long[] {i, st + d[i], r[i]});
    }
    for (Map.Entry<Long, Integer> e : mine.entrySet()) {
      lag.merge(e.getKey(), e.getValue(), Math::max);
    }
  }

  /** The starts in the solution of the tasks of a resource. */
  private int[] startsOf(int[] own) {
    int[] s = new int[own.length];
    for (int i = 0; i < own.length; i++) {
      s[i] = start[own[i]];
    }
    return s;
  }

  /**
   * The windows of the kept tasks: the earliest and latest starts along the precedences of the POS
   * between kept tasks, through the removed ones, within the bounds given, ending by the end of the
   * solution's schedule. A window always holds the task's start in the solution when the bounds do.
   *
   * @param removed the tasks the neighbourhood removes
   * @param min the smallest start of each task now
   * @param max the largest start of each task now
   * @param low the earliest starts, set for the kept tasks
   * @param high the latest starts, set for the kept tasks
   */
  void windows(boolean[] removed, int[] min, int[] max, long[] low, long[] high) {
    int n = start.length;
    long[] carry = new long[n];
    for (int t : order) {
      long e = Long.MIN_VALUE;
      for (int k = 0; k < pred[t].length; k++) {
        int p = pred[t][k];
        long v = removed[p] ? carry[p] : low[p] + predLag[t][k];
        e = Math.max(e, v);
      }
      if (removed[t]) {
        carry[t] = e;
      } else {
        low[t] = Math.min(Math.max(e, min[t]), start[t]);
      }
    }
    for (int j = n - 1; j >= 0; j--) {
      int t = order[j];
      long l = Long.MAX_VALUE;
      for (int k = 0; k < succ[t].length; k++) {
        int q = succ[t][k];
        long v = removed[q] ? carry[q] : high[q];
        if (v != Long.MAX_VALUE) {
          l = Math.min(l, v - succLag[t][k]);
        }
      }
      if (removed[t]) {
        // the latest start of the kept tasks after it, for the tasks before it
        long c = Long.MAX_VALUE;
        for (int q : succ[t]) {
          c = Math.min(c, removed[q] ? carry[q] : high[q]);
        }
        carry[t] = c;
      } else {
        l = Math.min(l, end - duration[t]);
        high[t] = Math.max(Math.min(l, max[t]), start[t]);
      }
    }
  }
}
