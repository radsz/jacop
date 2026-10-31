/*
 * DisjunctiveCliques.java
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

package org.jacop.presolve;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.core.IntVar;

/**
 * Finds sets of tasks that can never run at the same time, so that a unary resource can be posted
 * on each of them as a redundant constraint (Sidorov, Marijnissen and Demirović, "Unite and Lead:
 * Finding Disjunctive Cliques for Scheduling Problems", CP 2025).
 *
 * <p>A task is a start variable and a duration that is always positive. Two tasks are disjoint when
 *
 * <ul>
 *   <li>their resource uses on one cumulative resource exceed its capacity ({@link #conflict}),
 *   <li>a disjunction orders them one way or the other ({@link #disjunction}), or
 *   <li>the difference constraints between start times order them ({@link #precedence}); the
 *       longest paths of these constraints are used, so a chain of precedences counts.
 * </ul>
 *
 * <p>The disjoint pairs are the edges of a conflict graph, and every clique of it is a unary
 * resource. The cliques are chosen greedily to cover the edges that the precedences do not already
 * order and that no unary resource of the model ({@link #unary}) contains: each clique starts from
 * such an edge and grows by the task adjacent to the most remaining candidates. Cliques of fewer
 * than three tasks are dropped, since a pair is already handled by the constraint it came from.
 *
 * <p>The paper finds cliques during search in a solver with clause learning; here the detection is
 * static and runs once before search, as the follow-up paper (Sidorov, "On Inferring Cumulative
 * Constraints", CP 2026) does for its disjunctive constraints.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class DisjunctiveCliques {

  /** The default largest number of tasks; with more tasks no clique is searched. */
  public static final int DEFAULT_MAX_TASKS = 5000;

  /** The default largest number of cliques returned. */
  public static final int DEFAULT_MAX_CLIQUES = 500;

  // arcs relaxed by the longest paths of the precedences; sources left over add no order
  private static final long CLOSURE_BUDGET = 20_000_000L;

  // word operations of the clique search; the cliques found before it runs out are kept
  private static final long CLIQUE_BUDGET = 50_000_000L;

  private static final long NO_PATH = Long.MIN_VALUE;

  private final int maxTasks;
  private final int maxCliques;

  // tasks: start, duration variable (null for a constant) and duration bounds
  private final List<IntVar> starts = new ArrayList<>();
  private final List<IntVar> durationVars = new ArrayList<>();
  private final List<int[]> durationBounds = new ArrayList<>();
  private final Map<IntVar, List<Integer>> tasksOfStart = new IdentityHashMap<>();

  // pairs of tasks, two entries each
  private int[] conflicts = new int[64];
  private int conflictEntries;
  private final List<int[]> unaries = new ArrayList<>();

  // a disjunction: b >= a + lagAB or a >= b + lagBA
  private record Disjunction(IntVar a, int lagAB, IntVar b, int lagBA) {}

  private final List<Disjunction> disjunctions = new ArrayList<>();

  // the difference graph on start times: to >= from + lag
  private final Map<IntVar, Integer> vertexOf = new IdentityHashMap<>();
  private final List<List<long[]>> out = new ArrayList<>();
  private int precedences;

  private long work;

  /** It creates a detector with the default limits. */
  public DisjunctiveCliques() {
    this(DEFAULT_MAX_TASKS, DEFAULT_MAX_CLIQUES);
  }

  /**
   * It creates a detector.
   *
   * @param maxTasks the largest number of tasks; with more tasks no clique is searched.
   * @param maxCliques the largest number of cliques returned.
   */
  public DisjunctiveCliques(int maxTasks, int maxCliques) {
    this.maxTasks = maxTasks;
    this.maxCliques = maxCliques;
  }

  /**
   * It returns the task with the given start and duration, adding it if it is new. Two calls with
   * the same start variable and the same duration (the same variable, or equal constants) return
   * the same task.
   *
   * @param start the start variable.
   * @param duration the duration variable.
   * @return the index of the task, or -1 if the duration can be zero or less.
   */
  public int task(IntVar start, IntVar duration) {
    if (duration.singleton()) {
      return task(start, duration.value());
    }
    return task(start, duration, duration.min(), duration.max());
  }

  /**
   * It returns the task with the given start and constant duration, adding it if it is new.
   *
   * @param start the start variable.
   * @param duration the duration.
   * @return the index of the task, or -1 if the duration is zero or less.
   */
  public int task(IntVar start, int duration) {
    return task(start, null, duration, duration);
  }

  private int task(IntVar start, IntVar duration, int min, int max) {
    if (min <= 0) {
      return -1;
    }
    List<Integer> same = tasksOfStart.computeIfAbsent(start, k -> new ArrayList<>());
    for (int t : same) {
      IntVar d = durationVars.get(t);
      if (duration != null ? d == duration : d == null && durationBounds.get(t)[0] == min) {
        return t;
      }
    }
    int t = starts.size();
    starts.add(start);
    durationVars.add(duration);
    durationBounds.add(new int[] {min, max});
    same.add(t);
    return t;
  }

  /**
   * It records that two tasks can never overlap, for example because their resource uses exceed a
   * capacity.
   *
   * @param i a task.
   * @param j another task.
   */
  public void conflict(int i, int j) {
    if (i >= 0 && j >= 0 && i != j) {
      if (conflictEntries == conflicts.length) {
        conflicts = Arrays.copyOf(conflicts, 2 * conflicts.length);
      }
      conflicts[conflictEntries++] = i;
      conflicts[conflictEntries++] = j;
    }
  }

  /**
   * It records tasks that are already on a unary resource of the model, so their pairs need no new
   * clique.
   *
   * @param tasks the tasks.
   */
  public void unary(int... tasks) {
    unaries.add(tasks.clone());
  }

  /**
   * It records the difference constraint {@code to >= from + lag}.
   *
   * @param from a start variable.
   * @param to another start variable.
   * @param lag the smallest difference, possibly negative.
   */
  public void precedence(IntVar from, IntVar to, int lag) {
    if (from == to) {
      return;
    }
    out.get(vertex(from)).add(new long[] {vertex(to), lag});
    precedences++;
  }

  private int vertex(IntVar v) {
    Integer k = vertexOf.get(v);
    if (k == null) {
      k = out.size();
      vertexOf.put(v, k);
      out.add(new ArrayList<>());
    }
    return k;
  }

  /**
   * It records the disjunction {@code b >= a + lagAB \/ a >= b + lagBA}. The tasks on a and b whose
   * durations are at most lagAB and lagBA are disjoint.
   *
   * @param a a start variable.
   * @param lagAB the smallest distance from a to b in the first case.
   * @param b another start variable.
   * @param lagBA the smallest distance from b to a in the second case.
   */
  public void disjunction(IntVar a, int lagAB, IntVar b, int lagBA) {
    if (a != b) {
      disjunctions.add(new Disjunction(a, lagAB, b, lagBA));
    }
  }

  /**
   * It returns the number of tasks.
   *
   * @return the number of tasks.
   */
  public int size() {
    return starts.size();
  }

  /**
   * It returns the start variable of a task.
   *
   * @param t the task.
   * @return its start variable.
   */
  public IntVar start(int t) {
    return starts.get(t);
  }

  /**
   * It returns the duration variable of a task.
   *
   * @param t the task.
   * @return its duration variable, or null if the duration is a constant.
   */
  public IntVar durationVar(int t) {
    return durationVars.get(t);
  }

  /**
   * It returns the smallest duration of a task, its duration if it is a constant.
   *
   * @param t the task.
   * @return the smallest duration.
   */
  public int minDuration(int t) {
    return durationBounds.get(t)[0];
  }

  private int maxDuration(int t) {
    return durationBounds.get(t)[1];
  }

  /**
   * It returns the transition times between the tasks of a clique that its disjunctions imply. Two
   * tasks of a clique never overlap, so when task a comes first every disjunction between their
   * starts gives {@code s_b >= s_a + lag}, which is {@code s_a + d_a + (lag - d_a)}; the transition
   * from a to b is the largest such lag minus the largest duration of a, or zero.
   *
   * @param clique the tasks.
   * @return the transition from each task of the clique to each other, by their positions.
   */
  public int[][] transitions(int[] clique) {
    int m = clique.length;
    Map<IntVar, List<Integer>> position = new IdentityHashMap<>();
    for (int k = 0; k < m; k++) {
      position.computeIfAbsent(starts.get(clique[k]), v -> new ArrayList<>()).add(k);
    }
    int[][] tt = new int[m][m];
    for (Disjunction d : disjunctions) {
      List<Integer> pa = position.get(d.a);
      List<Integer> pb = position.get(d.b);
      if (pa == null || pb == null) {
        continue;
      }
      for (int x : pa) {
        for (int y : pb) {
          tt[x][y] = Math.max(tt[x][y], d.lagAB - maxDuration(clique[x]));
          tt[y][x] = Math.max(tt[y][x], d.lagBA - maxDuration(clique[y]));
        }
      }
    }
    return tt;
  }

  /**
   * It finds the cliques.
   *
   * @return the cliques, each of at least three tasks given by their indices in increasing order.
   */
  public List<int[]> cliques() {
    int n = starts.size();
    List<int[]> result = new ArrayList<>();
    if (n < 3 || n > maxTasks) {
      return result;
    }
    Graph g = new Graph(n);
    for (int k = 0; k < conflictEntries; k += 2) {
      g.edge(conflicts[k], conflicts[k + 1], false);
    }
    for (Disjunction d : disjunctions) {
      List<Integer> ta = tasksOfStart.get(d.a);
      List<Integer> tb = tasksOfStart.get(d.b);
      if (ta == null || tb == null) {
        continue;
      }
      for (int i : ta) {
        for (int j : tb) {
          if (maxDuration(i) <= d.lagAB && maxDuration(j) <= d.lagBA) {
            g.edge(i, j, false);
          }
        }
      }
    }
    if (precedences > 0) {
      orderByPrecedences(g);
    }
    for (int[] u : unaries) {
      for (int i : u) {
        for (int j : u) {
          if (i >= 0 && j >= 0 && i != j) {
            g.cover(i, j);
          }
        }
      }
    }
    work = 0;
    g.uncovered();
    while (result.size() < maxCliques && work < CLIQUE_BUDGET) {
      int[] clique = g.nextClique();
      if (clique == null) {
        break;
      }
      if (clique.length >= 3) {
        result.add(clique);
      }
    }
    return result;
  }

  // adds the edges of the tasks ordered by the longest paths of the difference constraints
  private void orderByPrecedences(Graph g) {
    // the vertices of the start variables of tasks and their tasks
    List<Integer> hosts = new ArrayList<>();
    List<List<Integer>> hostTasks = new ArrayList<>();
    for (Map.Entry<IntVar, List<Integer>> e : tasksOfStart.entrySet()) {
      Integer x = vertexOf.get(e.getKey());
      if (x != null) {
        hosts.add(x);
        hostTasks.add(e.getValue());
      }
    }
    int v = out.size();
    long[] dist = new long[v];
    int[] relaxed = new int[v];
    boolean[] queued = new boolean[v];
    // a circular queue; a vertex is in it at most once
    int[] queue = new int[v + 1];
    work = 0;
    for (int h = 0; h < hosts.size() && work < CLOSURE_BUDGET; h++) {
      int source = hosts.get(h);
      if (out.get(source).isEmpty()) {
        continue;
      }
      Arrays.fill(dist, NO_PATH);
      Arrays.fill(relaxed, 0);
      Arrays.fill(queued, false);
      dist[source] = 0;
      if (!longestPaths(source, dist, relaxed, queued, queue)) {
        // a positive cycle: the model has no solution, which the propagators find
        continue;
      }
      for (int k = 0; k < hosts.size(); k++) {
        long d = dist[hosts.get(k)];
        if (k == h || d == NO_PATH) {
          continue;
        }
        for (int i : hostTasks.get(h)) {
          if (d >= maxDuration(i)) {
            for (int j : hostTasks.get(k)) {
              g.edge(i, j, true);
            }
          }
        }
      }
    }
  }

  // the longest paths from the source by label correction; false on a positive cycle
  private boolean longestPaths(
      int source, long[] dist, int[] relaxed, boolean[] queued, int[] queue) {
    int v = out.size();
    int head = 0;
    int tail = 0;
    queue[tail++] = source;
    queued[source] = true;
    while (head != tail) {
      int x = queue[head];
      head = head == v ? 0 : head + 1;
      queued[x] = false;
      for (long[] arc : out.get(x)) {
        work++;
        int y = (int) arc[0];
        long d = dist[x] + arc[1];
        if (d > dist[y]) {
          if (y == source || ++relaxed[y] > v) {
            return false;
          }
          dist[y] = d;
          if (!queued[y]) {
            queued[y] = true;
            queue[tail] = y;
            tail = tail == v ? 0 : tail + 1;
          }
        }
      }
    }
    return true;
  }

  // the conflict graph as bit sets
  private final class Graph {
    final int n;
    final int words;
    final long[][] adj;
    // edges ordered by precedences
    final long[][] ordered;
    // edges that a clique must still cover
    final long[][] open;
    final int[] openDegree;

    Graph(int n) {
      this.n = n;
      this.words = (n + 63) >>> 6;
      adj = new long[n][words];
      ordered = new long[n][words];
      open = new long[n][words];
      openDegree = new int[n];
    }

    void edge(int i, int j, boolean order) {
      if (i == j) {
        return;
      }
      set(adj[i], j);
      set(adj[j], i);
      if (order) {
        set(ordered[i], j);
        set(ordered[j], i);
      }
    }

    // a pair on a unary resource of the model; open marks it as covered until uncovered() runs
    void cover(int i, int j) {
      set(open[i], j);
    }

    // turns the covered marks into the set of edges still to cover
    void uncovered() {
      for (int i = 0; i < n; i++) {
        int degree = 0;
        for (int w = 0; w < words; w++) {
          open[i][w] = adj[i][w] & ~ordered[i][w] & ~open[i][w];
          degree += Long.bitCount(open[i][w]);
        }
        openDegree[i] = degree;
      }
      work += (long) n * words;
    }

    // the next clique grown from an edge still to cover, or null if every edge is covered
    int[] nextClique() {
      int u = -1;
      for (int i = 0; i < n; i++) {
        if (openDegree[i] > 0 && (u < 0 || openDegree[i] > openDegree[u])) {
          u = i;
        }
      }
      if (u < 0) {
        return null;
      }
      int v = -1;
      for (int j = nextSet(open[u], 0); j >= 0; j = nextSet(open[u], j + 1)) {
        if (v < 0 || openDegree[j] > openDegree[v]) {
          v = j;
        }
      }
      long[] members = new long[words];
      set(members, u);
      set(members, v);
      long[] candidates = new long[words];
      for (int w = 0; w < words; w++) {
        candidates[w] = adj[u][w] & adj[v][w];
      }
      int size = 2;
      while (true) {
        int best = -1;
        int bestGrowth = -1;
        int bestOpen = -1;
        for (int c = nextSet(candidates, 0); c >= 0; c = nextSet(candidates, c + 1)) {
          int growth = 0;
          int toCover = 0;
          for (int w = 0; w < words; w++) {
            growth += Long.bitCount(adj[c][w] & candidates[w]);
            toCover += Long.bitCount(open[c][w] & members[w]);
          }
          work += words;
          if (growth > bestGrowth
              || growth == bestGrowth
                  && (toCover > bestOpen
                      || toCover == bestOpen && maxDuration(c) > maxDuration(best))) {
            best = c;
            bestGrowth = growth;
            bestOpen = toCover;
          }
        }
        if (best < 0) {
          break;
        }
        set(members, best);
        size++;
        for (int w = 0; w < words; w++) {
          candidates[w] &= adj[best][w];
        }
      }
      int[] clique = new int[size];
      int k = 0;
      for (int i = nextSet(members, 0); i >= 0; i = nextSet(members, i + 1)) {
        clique[k++] = i;
        for (int w = 0; w < words; w++) {
          long covered = open[i][w] & members[w];
          openDegree[i] -= Long.bitCount(covered);
          open[i][w] &= ~members[w];
        }
      }
      work += (long) size * words;
      return clique;
    }
  }

  private static void set(long[] bits, int i) {
    bits[i >>> 6] |= 1L << (i & 63);
  }

  private static int nextSet(long[] bits, int from) {
    int w = from >>> 6;
    if (w >= bits.length) {
      return -1;
    }
    long word = bits[w] & (-1L << (from & 63));
    while (true) {
      if (word != 0) {
        return (w << 6) + Long.numberOfTrailingZeros(word);
      }
      if (++w == bits.length) {
        return -1;
      }
      word = bits[w];
    }
  }
}
