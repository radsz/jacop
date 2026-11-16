/*
 * ArcTimes.java
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
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * ArcTimes: the arc-time precedences of a tour written with successors, {@code x[v] = w + offset ->
 * t[w] >= t[v] + lag[v][w]}, as a vehicle route with time windows has them (the arrival time at the
 * successor is at least the arrival time here plus the service and the travel time of the arc). It
 * removes every successor w of v with {@code min t[v] + lag[v][w] > max t[w]}, which the
 * decomposition into an element of the times and an element of the travel times does not see, as it
 * reads the least travel time over all successors. The removal is explained by the two bounds
 * {@code t[v] >= max t[w] - lag[v][w] + 1} and {@code t[w] <= max t[w]}. It does not propagate the
 * times: the constraints of the model do that once the successor is fixed.
 *
 * <p>Reference: M. Desrochers, J. Desrosiers and M. Solomon, A new optimization algorithm for the
 * vehicle routing problem with time windows, Operations Research 40(2), 1992 (the time window
 * reduction of the arcs, here at every node of the search).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ArcTimes extends Constraint
    implements SatisfiedPresent, Copyable<ArcTimes>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** No precedence for the arc. */
  public static final long NO_LAG = Long.MIN_VALUE;

  private final IntVar[] x;
  private final int offset;
  private final IntVar[] t;
  private final long[][] lag;
  private final int n;

  // the nodes v whose successor w may have a precedence to w, for each w
  private final int[][] predecessors;

  // the nodes of each successor variable and of each time variable (a time may be shared)
  private final Map<IntVar, Integer> nodeOf = new IdentityHashMap<>();
  private final Map<IntVar, int[]> nodesOfTime = new IdentityHashMap<>();

  // nodes whose successors are to be checked again
  private final boolean[] dirty;
  private final int[] queue;
  private int queued;

  // nodes whose arcs in are to be checked again
  private final boolean[] headDirty;
  private final int[] heads;
  private int headCount;
  private boolean all = true;

  // the node whose successors all came too late in the last failure, or -1
  private int failed = -1;

  /**
   * It constructs the constraint.
   *
   * @param x the successor of each node v, the value w + offset for node w.
   * @param offset the value of node 0 in x.
   * @param t the time of each node.
   * @param lag lag[v][w] is the least t[w] - t[v] when x[v] = w + offset, NO_LAG where there is
   *     none; lag[v] may be null for a node without precedences.
   */
  public ArcTimes(IntVar[] x, int offset, IntVar[] t, long[][] lag) {
    checkInputForNullness("x", x);
    checkInputForNullness("t", t);
    if (x.length != t.length || lag == null || lag.length != x.length) {
      throw new IllegalArgumentException("ArcTimes needs a successor, a time and lags per node");
    }
    this.numberId = idNumber.incrementAndGet();
    this.n = x.length;
    this.x = Arrays.copyOf(x, n);
    this.offset = offset;
    this.t = Arrays.copyOf(t, n);
    this.lag = new long[n][];
    List<List<Integer>> preds = new ArrayList<>();
    for (int w = 0; w < n; w++) {
      preds.add(new ArrayList<>());
    }
    for (int v = 0; v < n; v++) {
      if (lag[v] != null) {
        if (lag[v].length != n) {
          throw new IllegalArgumentException("ArcTimes needs a lag for each pair of nodes");
        }
        this.lag[v] = lag[v].clone();
        for (int w = 0; w < n; w++) {
          if (lag[v][w] != NO_LAG && w != v) {
            preds.get(w).add(v);
          }
        }
      }
      if (nodeOf.put(this.x[v], v) != null) {
        throw new IllegalArgumentException(
            "ArcTimes needs a different successor variable per node");
      }
    }
    predecessors = new int[n][];
    for (int w = 0; w < n; w++) {
      predecessors[w] = preds.get(w).stream().mapToInt(Integer::intValue).toArray();
    }
    for (int v = 0; v < n; v++) {
      int[] old = nodesOfTime.get(this.t[v]);
      int[] now = old == null ? new int[] {v} : Arrays.copyOf(old, old.length + 1);
      now[now.length - 1] = v;
      nodesOfTime.put(this.t[v], now);
    }
    dirty = new boolean[n];
    queue = new int[n];
    headDirty = new boolean[n];
    heads = new int[n];
    this.queueIndex = 1;
    List<Var> scope = new ArrayList<>(Arrays.asList(this.x));
    for (IntVar tv : nodesOfTime.keySet()) {
      if (!nodeOf.containsKey(tv)) {
        scope.add(tv);
      }
    }
    setScope(scope.stream());
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void queueVariable(int level, Var v) {
    int[] nodes = nodesOfTime.get(v);
    if (nodes == null) {
      return;
    }
    for (int u : nodes) {
      // a later start at u: its successors; an earlier end at u: the arcs into it
      mark(u);
      if (!headDirty[u]) {
        headDirty[u] = true;
        heads[headCount++] = u;
      }
    }
  }

  private void mark(int v) {
    if (!dirty[v] && lag[v] != null) {
      dirty[v] = true;
      queue[queued++] = v;
    }
  }

  @Override
  public void consistency(Store store) {
    failed = -1;
    try {
      if (all) {
        all = false;
        for (int v = 0; v < n; v++) {
          check(store, v);
        }
      } else {
        for (int i = 0; i < queued; i++) {
          check(store, queue[i]);
        }
        for (int i = 0; i < headCount; i++) {
          into(store, heads[i]);
        }
      }
    } finally {
      for (int i = 0; i < queued; i++) {
        dirty[queue[i]] = false;
      }
      queued = 0;
      for (int i = 0; i < headCount; i++) {
        headDirty[heads[i]] = false;
      }
      headCount = 0;
    }
  }

  // removes w from the successors of the nodes that cannot reach it in time
  private void into(Store store, int w) {
    int end = t[w].max();
    int value = w + offset;
    for (int v : predecessors[w]) {
      if (!dirty[v] && x[v].domain.contains(value) && t[v].min() + lag[v][w] > end) {
        if (x[v].getSize() == 1) {
          failed = v;
        }
        x[v].domain.inComplement(store.level, x[v], value);
      }
    }
  }

  // removes the successors of v that its earliest time cannot reach in time
  private void check(Store store, int v) {
    long[] l = lag[v];
    if (l == null) {
      return;
    }
    long start = t[v].min();
    List<Integer> late = null;
    for (ValueEnumeration e = x[v].domain.valueEnumeration(); e.hasMoreElements(); ) {
      int value = e.nextElement();
      int w = value - offset;
      if (w >= 0 && w < n && l[w] != NO_LAG && start + l[w] > t[w].max()) {
        if (late == null) {
          late = new ArrayList<>();
        }
        late.add(value);
      }
    }
    if (late != null) {
      if (late.size() == x[v].getSize()) {
        failed = v;
      }
      for (int value : late) {
        x[v].domain.inComplement(store.level, x[v], value);
      }
    }
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    Integer node = nodeOf.get(trail.variable(entry));
    if (node == null || lag[node] == null) {
      return false;
    }
    int from = trail.removedMin(entry);
    int to = trail.removedMax(entry);
    return late(trail, entry, node, from, to, out);
  }

  /**
   * Explains a failure by the node whose successors all reach their nodes too late: the bounds that
   * make each of them late, and the removals of the others.
   */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int v = failed;
    if (v < 0 || lag[v] == null) {
      return false;
    }
    IntDomain root = trail.rootDomain(x[v]);
    return late(trail, trail.size(), v, root.min(), root.max(), out);
  }

  // the reason why the values from..to of x[v] are out just before the position: each value was
  // removed before, or reaches its node too late by the bounds of the times
  private boolean late(AtomicTrail trail, int position, int v, int from, int to, EntryList out) {
    long[] l = lag[v];
    IntVar xv = x[v];
    long start = trail.minBefore(t[v], position);
    long need = Long.MIN_VALUE;
    int mark = out.size();
    for (long u = from; u <= to; u++) {
      if (trail.excludedBefore(xv, (int) u, position, out)) {
        continue;
      }
      int w = (int) (u - offset);
      if (w < 0 || w >= n || l[w] == NO_LAG) {
        out.truncate(mark);
        return false;
      }
      long end = trail.maxBefore(t[w], position);
      if (start + l[w] <= end) {
        out.truncate(mark);
        return false;
      }
      trail.addBoundReaching(t[w], position, false, end, out);
      need = Math.max(need, end - l[w] + 1);
    }
    if (need != Long.MIN_VALUE) {
      trail.addBoundReaching(t[v], position, true, need, out);
    }
    return true;
  }

  @Override
  public boolean satisfied() {
    for (int v = 0; v < n; v++) {
      if (!x[v].singleton()) {
        return false;
      }
      int w = x[v].value() - offset;
      if (lag[v] != null && w >= 0 && w < n && lag[v][w] != NO_LAG) {
        if (!t[v].singleton() || !t[w].singleton() || t[w].value() < t[v].value() + lag[v][w]) {
          return false;
        }
      }
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : ArcTimes([");
    appendArrayToString(result, x);
    result.append("], ").append(offset).append(", [");
    appendArrayToString(result, t);
    result.append("], [");
    for (int v = 0; v < n; v++) {
      result.append(v == 0 ? "" : ", ");
      if (lag[v] == null) {
        result.append("-");
      } else {
        result.append('[');
        for (int w = 0; w < n; w++) {
          result.append(w == 0 ? "" : ", ").append(lag[v][w] == NO_LAG ? "_" : lag[v][w]);
        }
        result.append(']');
      }
    }
    result.append("])");
    return result.toString();
  }

  @Override
  public ArcTimes copy(VarMap map) {
    IntVar[] cx = new IntVar[n];
    IntVar[] ct = new IntVar[n];
    for (int v = 0; v < n; v++) {
      cx[v] = map.get(x[v]);
      ct[v] = map.get(t[v]);
    }
    return new ArcTimes(cx, offset, ct, lag);
  }
}
