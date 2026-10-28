/*
 * Reservoir.java
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
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Reservoir: event i changes the level of a reservoir by {@code changes[i]} at time {@code
 * times[i]}, and the level, {@code initial} plus the changes of all events at or before a time,
 * stays within {@code [min, max]} at all times. Positive changes are productions and negative ones
 * consumptions.
 *
 * <p>The propagation is the balance constraint of Laborie, "Algorithms for propagating resource
 * constraints in AI planning and scheduling: existing approaches and new results", Artificial
 * Intelligence 143 (2003). For each event x the other events are before x for sure, after x for
 * sure or unranked, using the bounds of the times and the precedences given to the constraint
 * ({@code to[k] >= from[k] + lag[k]}, over the times and any other variables). The constraint also
 * enforces the precedences between its events that these imply, and only those: the other variables
 * are not in its scope. The level just after x is at most the level of the events surely before it
 * plus the unranked productions, and at least that level plus the unranked consumptions. From these
 * bounds:
 *
 * <ul>
 *   <li>the constraint fails when the level after x cannot reach {@code min} or must exceed {@code
 *       max};
 *   <li>when the events before x leave the level below {@code min}, enough unranked productions
 *       have to come before x, so x is not before the earliest time at which they can have
 *       happened;
 *   <li>an unranked production without which (and without the productions that must follow it) the
 *       level after x cannot reach {@code min} comes before x; an unranked consumption that would
 *       take the level below {@code min} comes after x;
 *   <li>symmetrically for consumptions and {@code max}.
 * </ul>
 *
 * A pass costs O(n² log n). Precedences make the reasoning much stronger, since the bounds of the
 * times alone rank few events while the time windows are wide.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Reservoir extends Constraint implements SatisfiedPresent, Copyable<Reservoir> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The largest number of events for which the precedences are closed transitively. */
  public static final int MAX_CLOSURE_EVENTS = 2000;

  private static final int NONE = Integer.MIN_VALUE;

  final IntVar[] times;
  final int[] changes;
  final int initial;
  final int min;
  final int max;
  final IntVar[] from;
  final IntVar[] to;
  final int[] lag;

  private final int n;

  // longest path of precedences from the time of event y to the time of event x, null without
  private final int[][] dist;

  // false when the precedences are contradictory (a cycle of positive length)
  private final boolean feasible;

  // implied precedences between events: times[p[1]] >= times[p[0]] + p[2]
  private final int[][] pairs;

  // bounds of the times at the start of a pass
  private final int[] tmin;
  private final int[] tmax;

  // unranked productions and consumptions of the current event, and sort keys
  private final int[] unranked;
  private final long[] keys;

  /**
   * It creates a reservoir that starts at level 0 and has no precedences.
   *
   * @param times the times of the events.
   * @param changes the changes of the level at the events.
   * @param min the least level.
   * @param max the largest level.
   */
  public Reservoir(IntVar[] times, int[] changes, int min, int max) {
    this(times, changes, 0, min, max, new IntVar[0], new IntVar[0], new int[0]);
  }

  /**
   * It creates a reservoir with precedences between the times of its events.
   *
   * @param times the times of the events.
   * @param changes the changes of the level at the events.
   * @param initial the level before all events.
   * @param min the least level.
   * @param max the largest level.
   * @param from the first variable of each precedence.
   * @param to the second variable of each precedence.
   * @param lag the distances, {@code to[k] >= from[k] + lag[k]}.
   */
  public Reservoir(
      IntVar[] times,
      int[] changes,
      int initial,
      int min,
      int max,
      IntVar[] from,
      IntVar[] to,
      int[] lag) {

    checkInputForNullness(new String[] {"times", "from", "to"}, new Object[][] {times, from, to});
    if (changes == null || changes.length != times.length) {
      throw new IllegalArgumentException("Reservoir needs one change per event.");
    }
    if (lag == null || from.length != to.length || lag.length != from.length) {
      throw new IllegalArgumentException(
          "Reservoir needs two variables and one lag per precedence.");
    }
    if (min > max) {
      throw new IllegalArgumentException("Reservoir needs min <= max.");
    }

    this.numberId = idNumber.incrementAndGet();
    this.times = Arrays.copyOf(times, times.length);
    this.changes = Arrays.copyOf(changes, changes.length);
    this.initial = initial;
    this.min = min;
    this.max = max;
    this.from = Arrays.copyOf(from, from.length);
    this.to = Arrays.copyOf(to, to.length);
    this.lag = Arrays.copyOf(lag, lag.length);
    this.n = times.length;

    int[][] d = null;
    boolean ok = true;
    if (from.length > 0 && n <= MAX_CLOSURE_EVENTS) {
      Map<IntVar, Integer> index = new IdentityHashMap<>();
      List<IntVar> points = new ArrayList<>();
      for (IntVar[] vs : new IntVar[][] {times, from, to}) {
        for (IntVar v : vs) {
          index.computeIfAbsent(
              v,
              k -> {
                points.add(k);
                return points.size() - 1;
              });
        }
      }
      int m = points.size();
      int[][] out = new int[m][];
      int[] count = new int[m];
      for (IntVar v : from) {
        count[index.get(v)]++;
      }
      for (int u = 0; u < m; u++) {
        out[u] = new int[count[u]];
      }
      Arrays.fill(count, 0);
      int[] head = new int[from.length];
      for (int k = 0; k < from.length; k++) {
        int u = index.get(from[k]);
        head[k] = index.get(to[k]);
        out[u][count[u]++] = k;
      }
      d = new int[n][n];
      int[] path = new int[m];
      for (int y = 0; y < n && ok; y++) {
        ok = longestPaths(index.get(times[y]), out, head, path);
        for (int x = 0; x < n; x++) {
          d[y][x] = path[index.get(times[x])];
        }
      }
    }
    this.dist = ok ? d : null;
    this.feasible = ok;
    // the precedences between events that the given ones imply, kept as pairs y, x, distance
    List<int[]> implied = new ArrayList<>();
    if (dist != null) {
      for (int y = 0; y < n; y++) {
        for (int x = 0; x < n; x++) {
          if (x != y && dist[y][x] != NONE && times[x] != times[y]) {
            implied.add(new int[] {y, x, dist[y][x]});
          }
        }
      }
    }
    this.pairs = implied.toArray(new int[0][]);

    this.unranked = new int[n];
    this.tmin = new int[n];
    this.tmax = new int[n];
    this.keys = new long[n];

    this.queueIndex = 2;

    setScope(times);
  }

  // longest paths from the source by the queue-based Bellman-Ford; false on a cycle of positive
  // length, found as a longest path with as many arcs as points
  private boolean longestPaths(int source, int[][] out, int[] head, int[] path) {
    int m = path.length;
    Arrays.fill(path, NONE);
    path[source] = 0;
    int[] arcsOnPath = new int[m];
    boolean[] queued = new boolean[m];
    ArrayDeque<Integer> queue = new ArrayDeque<>();
    queue.add(source);
    queued[source] = true;
    while (!queue.isEmpty()) {
      int u = queue.poll();
      queued[u] = false;
      for (int k : out[u]) {
        int w = head[k];
        long d = (long) path[u] + lag[k];
        if (d > path[w] && d < IntDomain.MAX_INT) {
          path[w] = (int) d;
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

  // the time of y is at or before the time of x in every solution
  private boolean before(int y, int x) {
    return tmax[y] <= tmin[x] || (dist != null && dist[y][x] != NONE && dist[y][x] >= 0);
  }

  // the time of y is after the time of x in every solution
  private boolean after(int y, int x) {
    return tmin[y] > tmax[x] || (dist != null && dist[x][y] != NONE && dist[x][y] >= 1);
  }

  @Override
  public void consistency(Store store) {

    if (!feasible || initial < min || initial > max) {
      throw Store.failException;
    }

    do {
      store.propagationHasOccurred = false;
      // the precedences between events are part of the constraint, so they hold in its solutions
      for (int[] p : pairs) {
        precede(store, p[0], p[1], p[2]);
      }
      for (int x = 0; x < n; x++) {
        tmin[x] = times[x].min();
        tmax[x] = times[x].max();
      }
      for (int x = 0; x < n; x++) {
        if (changes[x] != 0) {
          event(store, x);
        }
      }
    } while (store.propagationHasOccurred);
  }

  // the level just after event x
  private void event(Store store, int x) {
    long base = (long) initial + changes[x];
    long up = 0;
    long down = 0;
    int k = 0;
    for (int y = 0; y < n; y++) {
      if (y == x || changes[y] == 0) {
        continue;
      }
      if (before(y, x)) {
        base += changes[y];
      } else if (!after(y, x)) {
        unranked[k++] = y;
        if (changes[y] > 0) {
          up += changes[y];
        } else {
          down += changes[y];
        }
      }
    }
    long upper = base + up;
    long lower = base + down;
    if (upper < min || lower > max) {
      throw Store.failException;
    }
    if (base < min) {
      // productions worth min - base come before x
      earliest(store, x, k, true, min - base);
      for (int a = 0; a < k; a++) {
        int y = unranked[a];
        if (changes[y] > 0) {
          if (upper - following(y, k, true) < min) {
            precede(store, y, x, 0);
          }
        } else if (upper + changes[y] < min) {
          precede(store, x, y, 1);
        }
      }
    }
    if (base > max) {
      // consumptions worth base - max come before x
      earliest(store, x, k, false, base - max);
      for (int a = 0; a < k; a++) {
        int y = unranked[a];
        if (changes[y] < 0) {
          if (lower - following(y, k, false) > max) {
            precede(store, y, x, 0);
          }
        } else if (lower + changes[y] > max) {
          precede(store, x, y, 1);
        }
      }
    }
  }

  // x is not before the earliest time at which unranked changes of the sign worth need can all
  // have happened
  private void earliest(Store store, int x, int k, boolean productions, long need) {
    int c = 0;
    for (int a = 0; a < k; a++) {
      int y = unranked[a];
      if (changes[y] > 0 == productions) {
        keys[c++] = ((long) times[y].min() << 32) | y;
      }
    }
    Arrays.sort(keys, 0, c);
    long sum = 0;
    for (int a = 0; a < c; a++) {
      int y = (int) keys[a];
      sum += Math.abs(changes[y]);
      if (sum >= need) {
        int t = (int) (keys[a] >> 32);
        if (t > times[x].min()) {
          times[x].domain.inMin(store.level, times[x], t);
        }
        return;
      }
    }
  }

  // the unranked changes of the sign of y's change at events that are not before y
  private long following(int y, int k, boolean productions) {
    long sum = 0;
    for (int a = 0; a < k; a++) {
      int z = unranked[a];
      if (changes[z] > 0 == productions && (z == y || before(y, z))) {
        sum += changes[z];
      }
    }
    return sum;
  }

  // time of a + gap <= time of b
  private void precede(Store store, int a, int b, int gap) {
    if ((long) times[a].max() + gap > times[b].max()) {
      times[a].domain.inMax(
          store.level, times[a], (int) Math.max(IntDomain.MIN_INT, (long) times[b].max() - gap));
    }
    if ((long) times[b].min() < (long) times[a].min() + gap) {
      times[b].domain.inMin(
          store.level, times[b], (int) Math.min(IntDomain.MAX_INT, (long) times[a].min() + gap));
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    if (!grounded()) {
      return false;
    }
    for (int[] p : pairs) {
      if ((long) times[p[1]].value() < (long) times[p[0]].value() + p[2]) {
        return false;
      }
    }
    if (initial < min || initial > max) {
      return false;
    }
    for (int x = 0; x < n; x++) {
      long level = initial;
      for (int y = 0; y < n; y++) {
        if (times[y].value() <= times[x].value()) {
          level += changes[y];
        }
      }
      if (level < min || level > max) {
        return false;
      }
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : Reservoir(").append(Arrays.toString(times));
    result.append(", ").append(Arrays.toString(changes));
    result.append(", ").append(initial).append(", ").append(min).append(", ").append(max);
    result.append(", [");
    for (int k = 0; k < pairs.length; k++) {
      result.append(k > 0 ? ", " : "").append(times[pairs[k][0]].id()).append(" + ");
      result.append(pairs[k][2]).append(" <= ").append(times[pairs[k][1]].id());
    }
    return result.append("])").toString();
  }

  @Override
  public Reservoir copy(VarMap map) {
    // only the times are in the scope, so the copy keeps the precedences between events
    IntVar[] t = map.get(times);
    IntVar[] f = new IntVar[pairs.length];
    IntVar[] g = new IntVar[pairs.length];
    int[] l = new int[pairs.length];
    for (int k = 0; k < pairs.length; k++) {
      f[k] = t[pairs[k][0]];
      g[k] = t[pairs[k][1]];
      l[k] = pairs[k][2];
    }
    return new Reservoir(t, changes, initial, min, max, f, g, l);
  }
}
