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
import java.util.stream.Stream;
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
 * ({@code to[k] >= from[k] + lag[k]}, over the times and any other variables, which the constraint
 * also enforces). The level just after x is at most the level of the events surely before it plus
 * the unranked productions, and at least that level plus the unranked consumptions. From these
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

    this.unranked = new int[n];
    this.keys = new long[n];

    this.queueIndex = 2;

    setScope(Stream.of(times, from, to).flatMap(Arrays::stream));
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
    return times[y].max() <= times[x].min()
        || (dist != null && dist[y][x] != NONE && dist[y][x] >= 0);
  }

  // the time of y is after the time of x in every solution
  private boolean after(int y, int x) {
    return times[y].min() > times[x].max()
        || (dist != null && dist[x][y] != NONE && dist[x][y] >= 1);
  }

  @Override
  public void consistency(Store store) {

    if (!feasible || initial < min || initial > max) {
      throw Store.failException;
    }

    do {
      store.propagationHasOccurred = false;
      // the precedences are part of the constraint, so they hold in its solutions
      for (int k = 0; k < from.length; k++) {
        if ((long) from[k].max() + lag[k] > to[k].max()) {
          from[k].domain.inMax(store.level, from[k], to[k].max() - lag[k]);
        }
        if ((long) to[k].min() < (long) from[k].min() + lag[k]) {
          to[k].domain.inMin(store.level, to[k], from[k].min() + lag[k]);
        }
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
    if (times[a].max() > times[b].max() - gap) {
      times[a].domain.inMax(store.level, times[a], times[b].max() - gap);
    }
    if (times[b].min() < times[a].min() + gap) {
      times[b].domain.inMin(store.level, times[b], times[a].min() + gap);
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
    for (int k = 0; k < from.length; k++) {
      if ((long) to[k].value() < (long) from[k].value() + lag[k]) {
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
    for (int k = 0; k < from.length; k++) {
      result.append(k > 0 ? ", " : "").append(from[k].id()).append(" + ").append(lag[k]);
      result.append(" <= ").append(to[k].id());
    }
    return result.append("])").toString();
  }

  @Override
  public Reservoir copy(VarMap map) {
    return new Reservoir(
        map.get(times), changes, initial, min, max, map.get(from), map.get(to), lag);
  }
}
