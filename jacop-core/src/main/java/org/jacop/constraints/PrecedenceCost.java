/*
 * PrecedenceCost.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Convex costs of start times under precedences: s[j] &gt;= s[i] + d for every precedence (i, j, d)
 * of an acyclic precedence graph, and sum(i) f[i](s[i]) &lt;= cost, where each f[i] is a convex
 * piecewise-linear function given as a sum of earliness and tardiness terms e * max(0, b - s[i]) +
 * t * max(0, s[i] - b) with e, t &gt;= 0 (any convex piecewise-linear function with integer
 * breakpoints and slopes is such a sum).
 *
 * <p>The constraint computes the exact minimum of sum(i) f[i](s[i]) over all start times within the
 * current bounds that respect the precedences, and makes it the minimum of the cost. This problem
 * is the dual of a convex-cost network flow (Ahuja, Hochbaum and Orlin 2003): the start times are
 * the potentials of a graph with one node per task and a root, a precedence is an arc that may
 * carry any flow at a profit of d per unit, and the cost of task i is a set of arcs between i and
 * the root whose costs are the breakpoints of f[i] (the conjugate of f[i]). The constraint solves
 * the flow by successive shortest paths with node potentials, starting from the previous optimal
 * schedule; the potentials at the end are an optimal schedule. The bound used is the value of the
 * flow (the dual), which is a lower bound for any flow, so the pruning stays sound even if the flow
 * were not optimal.
 *
 * <p>Reduced-cost filtering: moving s[i] later than its optimal value by delta costs at least c *
 * (delta - l) more, where l is the length of a shortest path from i to the root in the residual
 * graph (reduced costs) and c its bottleneck capacity, since that much flow can be sent around the
 * cycle the new bound s[i] &gt;= v closes. Start times whose increase exceeds the maximum of the
 * cost minus the bound are removed, and the same holds for earlier start times with paths from the
 * root. The precedences are propagated on bounds as well.
 *
 * <p>Under lazy clause generation the reason of the bound is the flow certificate: f[i] depends on
 * the lower bound of s[i] only when the flow y[i] from i to the root is below the right derivative
 * of f[i] at that bound (and on the upper bound when y[i] is above the left derivative there), so
 * the reason holds only those bounds, weakened as far as the slack of the bound allows (each by the
 * difference of the derivative and the flow per unit). The reason of a removed start time is the
 * reason of the bound of the problem with that start time added. Precedence propagation is
 * explained by the one bound it follows from.
 *
 * <p>References: R. K. Ahuja, D. S. Hochbaum and J. B. Orlin, Solving the Convex Cost Integer Dual
 * Network Flow Problem, Management Science 49(7), 950-964, 2003; P. Chr&eacute;tienne and F. Sourd,
 * PERT scheduling with convex cost functions, Theoretical Computer Science 292(1), 145-164, 2003;
 * J.-N. Monette, Y. Deville and P. Van Hentenryck, Just-In-Time Scheduling with Constraint
 * Programming, ICAPS 2009 (AAAI).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class PrecedenceCost extends Constraint
    implements SatisfiedPresent, Explainable, Copyable<PrecedenceCost> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final long INF = Long.MAX_VALUE / 4;

  final IntVar[] starts;
  final IntVar cost;

  // the precedences (from, to, lag): s[to] >= s[from] + lag, and the cost terms (task, b, e, t)
  final int[][] precedences;
  final int[][] terms;

  private final int n;
  private final int m;
  private final int[] from;
  private final int[] to;
  private final long[] lag;

  // the precedences by topological position of their tail (forward pass) and of their head
  private final int[] forward;
  private final int[] backward;

  // per task: arcs into and out of it
  private final int[][] in;
  private final int[][] out;

  // f[i](s) = constant[i] + slope[i] * s + sum(k) weight[i][k] * max(0, s - point[i][k])
  private final long[] constant;
  private final long[] slope;
  private final long[][] point;
  private final long[][] weight;

  private final Map<IntVar, Integer> index = new IdentityHashMap<>();

  // the flow graph: tasks 0..n-1 and the root n; arc a and a ^ 1 are the two directions
  private final int root;
  private final int[] arcTo;
  private final int[] arcNext;
  private final long[] arcCap;
  private final long[] arcCost;
  private final int[] first;
  private int arcCount;
  private final int[] segmentStart;
  private final int[] segmentEnd;

  private final long[] pot;
  private final long[] excess;
  private final long[] dist;
  private final long[] bottleneck;
  private final int[] parent;
  // the task next to the root on the path of a shortest path tree
  private final int[] firstNode;
  private final int[] heap;
  private final int[] heapPos;
  private final boolean[] done;
  private int heapSize;

  // the box of a solve, its precedence closure, and the schedule it starts from and ends with
  private final long[] lo;
  private final long[] hi;
  private final long[] closedLo;
  private final long[] closedHi;
  private final long[] warm;
  private final long[] schedule;
  // the flow from each task to the root at the end of a solve
  private final long[] flowOut;
  private final long[] pointBuffer;

  // the box of the last solve of propagation and its bound; an explanation solves again and
  // invalidates the flow
  private final long[] solvedLo;
  private final long[] solvedHi;
  private long solvedBound;
  private boolean graphValid;

  // the certificates of the last propagation: of the bound of the cost, and per task 2 * i (its
  // lower bound) and 2 * i + 1 (its upper bound), so an explanation needs no solve
  private Certificate costReason;
  private final Certificate[] startReason;

  /**
   * The bounds a dual flow depends on (lower bound of task j as 2 * j, upper as 2 * j + 1, with
   * their values and the rate mu at which weakening them lowers the bound), the maximum of the cost
   * it used (or Long.MIN_VALUE), the bound it proves (the pruned bound of a start, or the minimum
   * of the cost) and how far it exceeds what was needed.
   */
  private static final class Certificate {
    int[] literal;
    long[] value;
    long[] mu;
    int count;
    long costMax;
    long limit;
    long room;
  }

  /**
   * It constructs an earliness and tardiness constraint: each task i costs earliness[i] per unit
   * that s[i] is below due[i] and tardiness[i] per unit above it.
   *
   * @param starts the start times.
   * @param precedences triples {i, j, d}: s[j] &gt;= s[i] + d, over an acyclic graph.
   * @param due the due date of each task.
   * @param earliness the earliness cost of each task per unit, at least 0.
   * @param tardiness the tardiness cost of each task per unit, at least 0.
   * @param cost the bound on the total cost.
   */
  public PrecedenceCost(
      IntVar[] starts,
      int[][] precedences,
      int[] due,
      int[] earliness,
      int[] tardiness,
      IntVar cost) {
    this(starts, precedences, termsOf(starts, due, earliness, tardiness), cost);
  }

  /**
   * It constructs a precedence constraint with convex costs: the cost of task i is the sum of the
   * terms {i, b, e, t}, each e * max(0, b - s[i]) + t * max(0, s[i] - b).
   *
   * @param starts the start times.
   * @param precedences triples {i, j, d}: s[j] &gt;= s[i] + d, over an acyclic graph.
   * @param terms quadruples {i, b, e, t} with e, t &gt;= 0; a task may have several or none.
   * @param cost the bound on the total cost.
   */
  public PrecedenceCost(IntVar[] starts, int[][] precedences, int[][] terms, IntVar cost) {
    checkInputForNullness(new String[] {"starts", "cost"}, starts, new Object[] {cost});
    if (precedences == null || terms == null) {
      throw new IllegalArgumentException("PrecedenceCost needs precedences and terms.");
    }
    this.n = starts.length;
    this.m = precedences.length;
    this.numberId = idNumber.incrementAndGet();
    this.starts = Arrays.copyOf(starts, n);
    this.cost = cost;
    for (int i = 0; i < n; i++) {
      if (index.put(starts[i], i) != null || starts[i] == cost) {
        throw new IllegalArgumentException(
            "PrecedenceCost needs distinct start variables, other than the cost.");
      }
    }
    this.precedences = new int[m][];
    this.from = new int[m];
    this.to = new int[m];
    this.lag = new long[m];
    for (int p = 0; p < m; p++) {
      int[] r = precedences[p];
      if (r == null || r.length != 3 || r[0] < 0 || r[0] >= n || r[1] < 0 || r[1] >= n) {
        throw new IllegalArgumentException(
            "PrecedenceCost needs precedences {i, j, d} over the start variables.");
      }
      this.precedences[p] = r.clone();
      from[p] = r[0];
      to[p] = r[1];
      lag[p] = r[2];
    }
    this.terms = new int[terms.length][];
    List<TreeMap<Long, Long>> hinges = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      hinges.add(new TreeMap<>());
    }
    this.constant = new long[n];
    this.slope = new long[n];
    for (int k = 0; k < terms.length; k++) {
      int[] r = terms[k];
      if (r == null || r.length != 4 || r[0] < 0 || r[0] >= n || r[2] < 0 || r[3] < 0) {
        throw new IllegalArgumentException(
            "PrecedenceCost needs terms {i, b, e, t} with e, t >= 0 over the start variables.");
      }
      this.terms[k] = r.clone();
      int i = r[0];
      long b = r[1];
      long e = r[2];
      long t = r[3];
      // e * max(0, b - s) = e * (b - s) + e * max(0, s - b)
      constant[i] += e * b;
      slope[i] -= e;
      if (e + t > 0) {
        hinges.get(i).merge(b, e + t, Long::sum);
      }
    }
    this.point = new long[n][];
    this.weight = new long[n][];
    int segments = 0;
    for (int i = 0; i < n; i++) {
      TreeMap<Long, Long> h = hinges.get(i);
      point[i] = new long[h.size()];
      weight[i] = new long[h.size()];
      int k = 0;
      for (Map.Entry<Long, Long> e : h.entrySet()) {
        point[i][k] = e.getKey();
        weight[i][k] = e.getValue();
        k++;
      }
      // a point per breakpoint and per bound, each with up to two arcs
      segments += 2 * (h.size() + 2);
    }

    int[] position = topologicalOrder();
    Integer[] f = new Integer[m];
    Integer[] b = new Integer[m];
    for (int p = 0; p < m; p++) {
      f[p] = p;
      b[p] = p;
    }
    Arrays.sort(f, (p, q) -> Integer.compare(position[from[p]], position[from[q]]));
    Arrays.sort(b, (p, q) -> Integer.compare(position[to[q]], position[to[p]]));
    this.forward = Arrays.stream(f).mapToInt(Integer::intValue).toArray();
    this.backward = Arrays.stream(b).mapToInt(Integer::intValue).toArray();
    int[] inCount = new int[n];
    int[] outCount = new int[n];
    for (int p = 0; p < m; p++) {
      inCount[to[p]]++;
      outCount[from[p]]++;
    }
    this.in = new int[n][];
    this.out = new int[n][];
    for (int i = 0; i < n; i++) {
      in[i] = new int[inCount[i]];
      out[i] = new int[outCount[i]];
    }
    for (int p = 0; p < m; p++) {
      in[to[p]][--inCount[to[p]]] = p;
      out[from[p]][--outCount[from[p]]] = p;
    }

    this.root = n;
    int arcs = 2 * m + 2 * segments;
    this.arcTo = new int[arcs];
    this.arcNext = new int[arcs];
    this.arcCap = new long[arcs];
    this.arcCost = new long[arcs];
    this.first = new int[n + 1];
    this.segmentStart = new int[n];
    this.segmentEnd = new int[n];
    this.pot = new long[n + 1];
    this.excess = new long[n + 1];
    this.dist = new long[n + 1];
    this.bottleneck = new long[n + 1];
    this.parent = new int[n + 1];
    this.firstNode = new int[n + 1];
    this.heap = new int[n + 1];
    this.heapPos = new int[n + 1];
    this.done = new boolean[n + 1];
    this.lo = new long[n];
    this.hi = new long[n];
    this.closedLo = new long[n];
    this.closedHi = new long[n];
    this.warm = new long[n];
    this.schedule = new long[n];
    this.flowOut = new long[n];
    int most = 0;
    for (int i = 0; i < n; i++) {
      most = Math.max(most, point[i].length);
    }
    this.pointBuffer = new long[most + 2];
    this.solvedLo = new long[n];
    this.solvedHi = new long[n];
    this.startReason = new Certificate[2 * n];
    for (int i = 0; i < n; i++) {
      warm[i] = starts[i].min();
    }

    this.queueIndex = 3;
    setScope(Stream.concat(Arrays.stream(starts), Stream.of(cost)));
  }

  private static int[][] termsOf(IntVar[] starts, int[] due, int[] earliness, int[] tardiness) {
    if (starts == null
        || due == null
        || earliness == null
        || tardiness == null
        || due.length != starts.length
        || earliness.length != starts.length
        || tardiness.length != starts.length) {
      throw new IllegalArgumentException(
          "PrecedenceCost needs one due date, earliness and tardiness cost per task.");
    }
    int[][] t = new int[starts.length][];
    for (int i = 0; i < starts.length; i++) {
      t[i] = new int[] {i, due[i], earliness[i], tardiness[i]};
    }
    return t;
  }

  // topological position of each task, or an exception when the precedences have a cycle
  private int[] topologicalOrder() {
    int[] indegree = new int[n];
    List<List<Integer>> succ = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      succ.add(new ArrayList<>());
    }
    for (int p = 0; p < m; p++) {
      indegree[to[p]]++;
      succ.get(from[p]).add(to[p]);
    }
    int[] queue = new int[n];
    int head = 0;
    int tail = 0;
    for (int i = 0; i < n; i++) {
      if (indegree[i] == 0) {
        queue[tail++] = i;
      }
    }
    int[] position = new int[n];
    while (head < tail) {
      int i = queue[head];
      position[i] = head++;
      for (int j : succ.get(i)) {
        if (--indegree[j] == 0) {
          queue[tail++] = j;
        }
      }
    }
    if (tail < n) {
      throw new IllegalArgumentException("PrecedenceCost needs an acyclic precedence graph.");
    }
    return position;
  }

  // ---------------------------------------------------------------- the cost functions

  /**
   * It returns the cost of a task at a start time.
   *
   * @param i the task.
   * @param s the start time.
   * @return f[i](s).
   */
  public long taskCost(int i, long s) {
    long v = constant[i] + slope[i] * s;
    for (int k = 0; k < point[i].length; k++) {
      if (s > point[i][k]) {
        v += weight[i][k] * (s - point[i][k]);
      }
    }
    return v;
  }

  // the slope of f[i] just right of s
  private long rightSlope(int i, long s) {
    long v = slope[i];
    for (int k = 0; k < point[i].length && point[i][k] <= s; k++) {
      v += weight[i][k];
    }
    return v;
  }

  // the slope of f[i] just left of s
  private long leftSlope(int i, long s) {
    long v = slope[i];
    for (int k = 0; k < point[i].length && point[i][k] < s; k++) {
      v += weight[i][k];
    }
    return v;
  }

  // ---------------------------------------------------------------- the flow

  private void addArc(int u, int v, long cap, long c) {
    int a = arcCount;
    arcTo[a] = v;
    arcCap[a] = cap;
    arcCost[a] = c;
    arcNext[a] = first[u];
    first[u] = a;
    arcTo[a + 1] = u;
    arcCap[a + 1] = 0;
    arcCost[a + 1] = -c;
    arcNext[a + 1] = first[v];
    first[v] = a + 1;
    arcCount += 2;
  }

  private void build() {
    Arrays.fill(first, -1);
    arcCount = 0;
    for (int p = 0; p < m; p++) {
      addArc(from[p], to[p], INF, -lag[p]);
    }
    for (int i = 0; i < n; i++) {
      segmentStart[i] = arcCount;
      addSegments(i);
      segmentEnd[i] = arcCount;
    }
  }

  // the conjugate of f[i] over [lo, hi]: at each point P (a bound, or a breakpoint inside) its
  // slope
  // is P for the flows y from i to the root between the slopes of f[i] left and right of P
  private void addSegments(int i) {
    long l = lo[i];
    long h = hi[i];
    int count = 0;
    pointBuffer[count++] = l;
    for (long b : point[i]) {
      if (b > l && b < h) {
        pointBuffer[count++] = b;
      }
    }
    if (h > l) {
      pointBuffer[count++] = h;
    }
    for (int k = 0; k < count; k++) {
      long p = pointBuffer[k];
      long left = k == 0 ? -INF : leftSlope(i, p);
      long right = k == count - 1 ? INF : rightSlope(i, p);
      long s = Math.max(0, left);
      if (right > s) {
        addArc(i, root, right >= INF ? INF : right - s, p);
      }
      s = Math.max(0, -right);
      if (-left > s) {
        addArc(root, i, left <= -INF ? INF : -left - s, -p);
      }
    }
  }

  /**
   * Closes the box lo, hi under the precedences into closedLo, closedHi.
   *
   * @return false when the box has no schedule
   */
  private boolean close() {
    System.arraycopy(lo, 0, closedLo, 0, n);
    System.arraycopy(hi, 0, closedHi, 0, n);
    for (int p : forward) {
      closedLo[to[p]] = Math.max(closedLo[to[p]], closedLo[from[p]] + lag[p]);
    }
    for (int p : backward) {
      closedHi[from[p]] = Math.min(closedHi[from[p]], closedHi[to[p]] - lag[p]);
    }
    for (int i = 0; i < n; i++) {
      if (closedLo[i] > closedHi[i]) {
        return false;
      }
    }
    return true;
  }

  /**
   * Minimises sum(i) f[i](s[i]) over the box lo, hi and the precedences, whose closure must have a
   * schedule (see close). The schedule is in {@code schedule}, the flows to the root in {@code
   * flowOut}.
   *
   * @return the value of the dual flow, the minimum
   */
  private long solve() {
    graphValid = false;
    build();
    // a schedule of the box: the warm start moved into the closed box and repaired forward
    for (int i = 0; i < n; i++) {
      schedule[i] = Math.min(Math.max(warm[i], closedLo[i]), closedHi[i]);
    }
    for (int p : forward) {
      schedule[to[p]] = Math.max(schedule[to[p]], schedule[from[p]] + lag[p]);
    }
    for (int i = 0; i < n; i++) {
      pot[i] = schedule[i];
      excess[i] = 0;
    }
    pot[root] = 0;
    excess[root] = 0;
    // saturate the arcs of negative reduced cost (finite ones only)
    long open = 0;
    for (int a = 0; a < arcCount; a += 2) {
      int u = arcTo[a + 1];
      int v = arcTo[a];
      if (arcCost[a] - pot[u] + pot[v] < 0) {
        long c = arcCap[a];
        if (c >= INF) {
          throw new IllegalStateException("PrecedenceCost: the start schedule is infeasible");
        }
        arcCap[a] = 0;
        arcCap[a + 1] += c;
        excess[v] += c;
        excess[u] -= c;
      }
    }
    for (int v = 0; v <= n; v++) {
      if (excess[v] > 0) {
        open += excess[v];
      }
    }
    while (open > 0) {
      int t = shortestToDeficit();
      long amount = -excess[t];
      int v = t;
      while (parent[v] >= 0) {
        int a = parent[v];
        amount = Math.min(amount, arcCap[a]);
        v = arcTo[a ^ 1];
      }
      amount = Math.min(amount, excess[v]);
      v = t;
      while (parent[v] >= 0) {
        int a = parent[v];
        arcCap[a] -= amount;
        arcCap[a ^ 1] += amount;
        v = arcTo[a ^ 1];
      }
      excess[v] -= amount;
      excess[t] += amount;
      open -= amount;
      long dt = dist[t];
      for (int u = 0; u <= n; u++) {
        pot[u] -= Math.min(dist[u], dt);
      }
      if (open > 0) {
        open -= admissibleFlow();
      }
    }
    long dual = 0;
    for (int p = 0; p < m; p++) {
      dual += lag[p] * arcCap[2 * p + 1];
    }
    for (int i = 0; i < n; i++) {
      schedule[i] = pot[i] - pot[root];
      long y = 0;
      for (int a = segmentStart[i]; a < segmentEnd[i]; a += 2) {
        y += arcTo[a] == root ? arcCap[a + 1] : -arcCap[a + 1];
      }
      flowOut[i] = y;
      dual -= conjugate(i, y);
    }
    return dual;
  }

  // sup over s in [lo, hi] of y * s - f[i](s), attained at a bound or at a breakpoint inside
  private long conjugate(int i, long y) {
    long best = Math.max(y * lo[i] - taskCost(i, lo[i]), y * hi[i] - taskCost(i, hi[i]));
    for (long b : point[i]) {
      if (b > lo[i] && b < hi[i]) {
        best = Math.max(best, y * b - taskCost(i, b));
      }
    }
    return best;
  }

  /**
   * Sends flow from the nodes with excess to nodes with a deficit along arcs of reduced cost 0,
   * which keeps the reduced costs of the residual arcs at least 0, so one shortest path search
   * serves for many augmentations.
   *
   * @return the flow sent
   */
  private long admissibleFlow() {
    long sent = 0;
    for (int s = 0; s <= n; s++) {
      while (excess[s] > 0) {
        long f = admissiblePath(s);
        if (f == 0) {
          break;
        }
        sent += f;
      }
    }
    return sent;
  }

  // one path of arcs of reduced cost 0 from s to a node with a deficit, augmented; 0 for none
  private long admissiblePath(int s) {
    for (int v = 0; v <= n; v++) {
      done[v] = false;
    }
    int depth = 0;
    heap[0] = s;
    done[s] = true;
    parent[s] = first[s];
    while (depth >= 0) {
      int u = heap[depth];
      if (excess[u] < 0 && depth > 0) {
        long amount = Math.min(excess[s], -excess[u]);
        for (int k = 1; k <= depth; k++) {
          amount = Math.min(amount, arcCap[heapPos[heap[k]]]);
        }
        for (int k = 1; k <= depth; k++) {
          int a = heapPos[heap[k]];
          arcCap[a] -= amount;
          arcCap[a ^ 1] += amount;
        }
        excess[s] -= amount;
        excess[u] += amount;
        return amount;
      }
      int a = parent[u];
      while (a >= 0 && (arcCap[a] <= 0 || done[arcTo[a]] || reduced(a) != 0)) {
        a = arcNext[a];
      }
      if (a < 0) {
        depth--;
        continue;
      }
      parent[u] = arcNext[a];
      int v = arcTo[a];
      done[v] = true;
      parent[v] = first[v];
      // the arc into the node at this depth
      heapPos[v] = a;
      heap[++depth] = v;
    }
    return 0;
  }

  private long reduced(int a) {
    return arcCost[a] - pot[arcTo[a ^ 1]] + pot[arcTo[a]];
  }

  // Dijkstra from the nodes with excess to the nearest node with a deficit, in reduced costs
  private int shortestToDeficit() {
    heapSize = 0;
    for (int v = 0; v <= n; v++) {
      done[v] = false;
      heapPos[v] = -1;
      parent[v] = -1;
      if (excess[v] > 0) {
        dist[v] = 0;
        push(v);
      } else {
        dist[v] = INF;
      }
    }
    while (heapSize > 0) {
      int u = pop();
      done[u] = true;
      if (excess[u] < 0) {
        return u;
      }
      for (int a = first[u]; a >= 0; a = arcNext[a]) {
        if (arcCap[a] <= 0) {
          continue;
        }
        int v = arcTo[a];
        if (done[v]) {
          continue;
        }
        long d = dist[u] + reduced(a);
        if (d < dist[v]) {
          dist[v] = d;
          parent[v] = a;
          push(v);
        }
      }
    }
    throw new IllegalStateException("PrecedenceCost: no path to a deficit");
  }

  // shortest residual paths from the root (outward) or to the root (inward), with bottlenecks
  private void shortestFromRoot(boolean outward) {
    heapSize = 0;
    for (int v = 0; v <= n; v++) {
      done[v] = false;
      heapPos[v] = -1;
      dist[v] = INF;
    }
    dist[root] = 0;
    bottleneck[root] = INF;
    firstNode[root] = -1;
    push(root);
    while (heapSize > 0) {
      int u = pop();
      done[u] = true;
      for (int b = first[u]; b >= 0; b = arcNext[b]) {
        // outward: arc u -> v; inward: arc v -> u, the reverse of b
        int a = outward ? b : b ^ 1;
        if (arcCap[a] <= 0) {
          continue;
        }
        int v = arcTo[b];
        if (done[v]) {
          continue;
        }
        long d = dist[u] + reduced(a);
        if (d < dist[v]) {
          dist[v] = d;
          bottleneck[v] = Math.min(bottleneck[u], arcCap[a]);
          firstNode[v] = u == root ? v : firstNode[u];
          push(v);
        }
      }
    }
  }

  private void push(int s) {
    int i = heapPos[s];
    if (i < 0) {
      i = heapSize++;
    }
    while (i > 0) {
      int p = (i - 1) >> 1;
      if (dist[heap[p]] <= dist[s]) {
        break;
      }
      heap[i] = heap[p];
      heapPos[heap[i]] = i;
      i = p;
    }
    heap[i] = s;
    heapPos[s] = i;
  }

  private int pop() {
    int top = heap[0];
    heapPos[top] = -1;
    int last = heap[--heapSize];
    if (heapSize > 0) {
      int i = 0;
      while (true) {
        int l = 2 * i + 1;
        if (l >= heapSize) {
          break;
        }
        int r = l + 1;
        int c = r < heapSize && dist[heap[r]] < dist[heap[l]] ? r : l;
        if (dist[heap[c]] >= dist[last]) {
          break;
        }
        heap[i] = heap[c];
        heapPos[heap[i]] = i;
        i = c;
      }
      heap[i] = last;
      heapPos[last] = i;
    }
    return top;
  }

  // ---------------------------------------------------------------- propagation

  /**
   * It returns the minimum of the total cost over the current bounds of the start times and the
   * precedences, or Long.MAX_VALUE when no schedule respects them.
   *
   * @return the minimum.
   */
  public long minimumCost() {
    for (int i = 0; i < n; i++) {
      lo[i] = starts[i].min();
      hi[i] = starts[i].max();
    }
    if (!close()) {
      return Long.MAX_VALUE;
    }
    return solve();
  }

  @Override
  public void consistency(Store store) {
    boolean changed;
    do {
      changed = false;
      propagatePrecedences(store);
      for (int i = 0; i < n; i++) {
        lo[i] = starts[i].min();
        hi[i] = starts[i].max();
      }
      long bound;
      if (graphValid && insideSolvedBox()) {
        // the optimum of a larger box is in this one, so it is still optimal and the flow of that
        // solve still certifies the bound and the reduced costs; that solve may be of a node that
        // failed on it, or its filtering undone by backtracking, so both are done again
        bound = solvedBound;
      } else {
        if (!close()) {
          throw Store.failException;
        }
        bound = solve();
        System.arraycopy(schedule, 0, warm, 0, n);
        System.arraycopy(lo, 0, solvedLo, 0, n);
        System.arraycopy(hi, 0, solvedHi, 0, n);
        solvedBound = bound;
        graphValid = true;
      }
      if (bound > cost.max()) {
        throw Store.failException;
      }
      if (bound > cost.min()) {
        costReason = certificate(-1, 0, Long.MIN_VALUE, bound, 0);
        cost.domain.inMin(store.level, cost, (int) bound);
      }
      changed = filter(store, bound);
    } while (changed);
  }

  // whether the box is inside the box of the last solve of propagation and holds its optimum
  private boolean insideSolvedBox() {
    for (int i = 0; i < n; i++) {
      if (lo[i] < solvedLo[i] || hi[i] > solvedHi[i] || warm[i] < lo[i] || warm[i] > hi[i]) {
        return false;
      }
    }
    return true;
  }

  // reduced-cost filtering of the starts with the flow of the last solve; true when it pruned
  private boolean filter(Store store, long bound) {
    long max = cost.max();
    long slack = max - bound;
    boolean changed = false;
    shortestFromRoot(false);
    for (int i = 0; i < n; i++) {
      long c = bottleneck[i];
      long limit = warm[i] + dist[i] + (c >= INF ? 0 : slack / c);
      if (limit < starts[i].max()) {
        // s[i] >= limit + 1 sends c more units around root -> i -> ... -> root
        startReason[2 * i + 1] =
            c >= INF
                ? null
                : certificate(
                    firstNode[i], c, max, limit, bound + c * (limit + 1 - warm[i] - dist[i]));
        starts[i].domain.inMax(store.level, starts[i], (int) limit);
        changed = true;
      }
    }
    shortestFromRoot(true);
    for (int i = 0; i < n; i++) {
      long c = bottleneck[i];
      long limit = warm[i] - dist[i] - (c >= INF ? 0 : slack / c);
      if (limit > starts[i].min()) {
        startReason[2 * i] =
            c >= INF
                ? null
                : certificate(
                    firstNode[i], -c, max, limit, bound + c * (warm[i] - limit + 1 - dist[i]));
        starts[i].domain.inMin(store.level, starts[i], (int) limit);
        changed = true;
      }
    }
    return changed;
  }

  /**
   * The bounds of the last solve of propagation that the flow with dy more units from task k to the
   * root depends on, for a proved value of value against a maximum of the cost of max (none when
   * Long.MIN_VALUE).
   */
  private Certificate certificate(int k, long dy, long max, long limit, long value) {
    Certificate c = new Certificate();
    c.literal = new int[4];
    c.value = new long[4];
    c.mu = new long[4];
    c.costMax = max;
    c.limit = limit;
    c.room = max == Long.MIN_VALUE ? value - limit : value - max - 1;
    for (int j = 0; j < n; j++) {
      long y = flowOut[j] + (j == k ? dy : 0);
      long mu = rightSlope(j, solvedLo[j]) - y;
      if (mu > 0) {
        add(c, 2 * j, solvedLo[j], mu);
      }
      mu = y - leftSlope(j, solvedHi[j]);
      if (mu > 0) {
        add(c, 2 * j + 1, solvedHi[j], mu);
      }
    }
    return c;
  }

  private static void add(Certificate c, int literal, long value, long mu) {
    if (c.count == c.literal.length) {
      int size = 2 * c.count;
      c.literal = Arrays.copyOf(c.literal, size);
      c.value = Arrays.copyOf(c.value, size);
      c.mu = Arrays.copyOf(c.mu, size);
    }
    c.literal[c.count] = literal;
    c.value[c.count] = value;
    c.mu[c.count] = mu;
    c.count++;
  }

  // adds the bounds of a certificate before a position, weakened within its room; false when one
  // of them did not hold then
  private boolean addCertificate(AtomicTrail trail, int position, Certificate c, EntryList reason) {
    if (c.costMax != Long.MIN_VALUE && trail.maxBefore(cost, position) > c.costMax) {
      return false;
    }
    for (int k = 0; k < c.count; k++) {
      IntVar x = starts[c.literal[k] >> 1];
      if ((c.literal[k] & 1) == 0
          ? trail.minBefore(x, position) < c.value[k]
          : trail.maxBefore(x, position) > c.value[k]) {
        return false;
      }
    }
    long room = c.room;
    if (c.costMax != Long.MIN_VALUE) {
      long now = trail.maxBefore(cost, position);
      long used = trail.addBoundWithin(cost, position, false, c.costMax - now + room, reason);
      room -= Math.max(0, used - (c.costMax - now));
    }
    for (int k = 0; k < c.count; k++) {
      IntVar x = starts[c.literal[k] >> 1];
      boolean lower = (c.literal[k] & 1) == 0;
      long tighter =
          lower
              ? trail.minBefore(x, position) - c.value[k]
              : c.value[k] - trail.maxBefore(x, position);
      long mu = c.mu[k];
      long used = trail.addBoundWithin(x, position, lower, tighter + room / mu, reason);
      room -= mu * Math.max(0, used - tighter);
    }
    return true;
  }

  private void propagatePrecedences(Store store) {
    for (int p : forward) {
      long v = starts[from[p]].min() + lag[p];
      IntVar y = starts[to[p]];
      if (v > y.min()) {
        if (v > y.max()) {
          throw Store.failException;
        }
        y.domain.inMin(store.level, y, (int) v);
      }
    }
    for (int p : backward) {
      long v = starts[to[p]].max() - lag[p];
      IntVar x = starts[from[p]];
      if (v < x.max()) {
        if (v < x.min()) {
          throw Store.failException;
        }
        x.domain.inMax(store.level, x, (int) v);
      }
    }
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
      total += taskCost(i, starts[i].value());
    }
    for (int p = 0; p < m; p++) {
      if (starts[to[p]].value() < starts[from[p]].value() + lag[p]) {
        return false;
      }
    }
    return total <= cost.min();
  }

  // ---------------------------------------------------------------- explanations

  // reads the bounds of the starts just before a trail position
  private void boundsBefore(AtomicTrail trail, int position) {
    for (int i = 0; i < n; i++) {
      lo[i] = trail.minBefore(starts[i], position);
      hi[i] = trail.maxBefore(starts[i], position);
    }
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList reason) {
    int kind = trail.kind(entry);
    if (kind != AtomicTrail.GE && kind != AtomicTrail.LE) {
      return false;
    }
    boolean ge = kind == AtomicTrail.GE;
    IntVar x = trail.variable(entry);
    int value = trail.skippedBound(entry);
    if (x == cost) {
      if (!ge) {
        return false;
      }
      Certificate c = costReason;
      if (c != null && c.limit >= value) {
        EntryList scratch = new EntryList();
        Certificate shifted = shift(c, value);
        if (addCertificate(trail, entry, shifted, scratch)) {
          trail.addSkippedHoles(entry, value, reason);
          for (int k = 0; k < scratch.size(); k++) {
            reason.add(scratch.get(k));
          }
          return true;
        }
      }
      boundsBefore(trail, entry);
      if (!close()) {
        return false;
      }
      long bound = solve();
      if (bound < value) {
        return false;
      }
      trail.addSkippedHoles(entry, value, reason);
      addCertificate(trail, entry, bound - value, -1, reason);
      return true;
    }
    Integer task = index.get(x);
    if (task == null) {
      return false;
    }
    int i = task;
    // one precedence
    if (ge) {
      for (int p : in[i]) {
        if (trail.minBefore(starts[from[p]], entry) + lag[p] >= value) {
          trail.addSkippedHoles(entry, value, reason);
          trail.addBoundReaching(starts[from[p]], entry, true, value - lag[p], reason);
          return true;
        }
      }
    } else {
      for (int p : out[i]) {
        if (trail.maxBefore(starts[to[p]], entry) - lag[p] <= value) {
          trail.addSkippedHoles(entry, value, reason);
          trail.addBoundReaching(starts[to[p]], entry, false, value + lag[p], reason);
          return true;
        }
      }
    }
    // the cost: the certificate of the propagation, if it proves the atom with bounds that held
    Certificate c = startReason[ge ? 2 * i : 2 * i + 1];
    if (c != null && (ge ? c.limit >= value : c.limit <= value)) {
      EntryList scratch = new EntryList();
      if (addCertificate(trail, entry, c, scratch)) {
        trail.addSkippedHoles(entry, value, reason);
        for (int k = 0; k < scratch.size(); k++) {
          reason.add(scratch.get(k));
        }
        return true;
      }
    }
    // the problem with the negation of the atom costs more than the maximum of the cost
    boundsBefore(trail, entry);
    if (ge) {
      hi[i] = (long) value - 1;
    } else {
      lo[i] = (long) value + 1;
    }
    if (lo[i] > hi[i] || !close()) {
      return false;
    }
    long bound = solve();
    long max = trail.maxBefore(cost, entry);
    if (bound <= max) {
      return false;
    }
    trail.addSkippedHoles(entry, value, reason);
    long room = bound - max - 1;
    room -= trail.addBoundWithin(cost, entry, false, room, reason);
    addCertificate(trail, entry, room, ge ? 2 * i + 1 : 2 * i, reason);
    return true;
  }

  // the certificate of the bound of the cost for a weaker bound: more room
  private static Certificate shift(Certificate c, long value) {
    Certificate d = new Certificate();
    d.literal = c.literal;
    d.value = c.value;
    d.mu = c.mu;
    d.count = c.count;
    d.costMax = c.costMax;
    d.limit = value;
    d.room = c.room + c.limit - value;
    return d;
  }

  // the bounds the dual flow of the last solve depends on, weakened within the room; skip is 2 * i
  // for the lower bound of task i (2 * i + 1 for its upper bound), which is the negated atom
  private void addCertificate(
      AtomicTrail trail, int position, long room, int skip, EntryList reason) {
    for (int k = 0; k < n; k++) {
      long y = flowOut[k];
      long mu = rightSlope(k, lo[k]) - y;
      if (mu > 0 && skip != 2 * k) {
        room -= mu * trail.addBoundWithin(starts[k], position, true, room / mu, reason);
      }
      mu = y - leftSlope(k, hi[k]);
      if (mu > 0 && skip != 2 * k + 1) {
        room -= mu * trail.addBoundWithin(starts[k], position, false, room / mu, reason);
      }
    }
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList reason) {
    int now = trail.size();
    for (int p = 0; p < m; p++) {
      long l = trail.minBefore(starts[from[p]], now) + lag[p];
      long h = trail.maxBefore(starts[to[p]], now);
      if (l > h) {
        long room = l - h - 1;
        room -= trail.addBoundWithin(starts[from[p]], now, true, room, reason);
        trail.addBoundWithin(starts[to[p]], now, false, room, reason);
        return true;
      }
    }
    boundsBefore(trail, now);
    if (!close()) {
      return false;
    }
    long bound = solve();
    long max = trail.maxBefore(cost, now);
    if (bound <= max) {
      return false;
    }
    long room = bound - max - 1;
    room -= trail.addBoundWithin(cost, now, false, room, reason);
    addCertificate(trail, now, room, -1, reason);
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : PrecedenceCost([");
    for (int i = 0; i < n; i++) {
      result.append(starts[i]);
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(Arrays.deepToString(precedences));
    result.append(", ").append(Arrays.deepToString(terms));
    result.append(", ").append(cost).append(")");
    return result.toString();
  }

  @Override
  public PrecedenceCost copy(VarMap map) {
    return new PrecedenceCost(map.get(starts), precedences, terms, map.get(cost));
  }
}
