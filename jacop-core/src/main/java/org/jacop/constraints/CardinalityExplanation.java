/*
 * CardinalityExplanation.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of cardinality constraints (global cardinality, count of values) by cuts of their
 * flow network: each variable sends one unit to a value of its domain, value j passes between
 * low[j] and up[j] units to the sink, and the uncounted values, when the variables may take them,
 * pass any number (or the bounds of a counter of them). The constraint has a solution exactly when
 * this network has a feasible circulation.
 *
 * <p>An atom is explained by the network of the domains just before it, with the negation of the
 * atom in place of the domain of its variable: when that network has no feasible circulation, a set
 * X of nodes violates Hoffman's condition, the lower bounds of the arcs entering X exceed the
 * capacities of the arcs leaving it. The reason is what keeps those bounds and capacities: the
 * atoms that removed the values of the arcs that leave X missing, the upper bounds of the counters
 * of values in X with the sink outside, and the lower bounds of the counters of values outside X
 * with the sink inside (Downing, Feydy and Stuckey, "Explaining Flow-Based Propagation", CPAIOR
 * 2012). A failure is explained the same way by the network now. The explanation checks its own
 * reason, so it refuses (and leaves the generic reason) when the network is feasible, which a
 * propagator that prunes more than the network implies can cause, and when it is too large.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class CardinalityExplanation {

  /** The most arcs from variables to values considered. */
  private static final int ARC_LIMIT = 1 << 20;

  /** The most root values walked to find an uncounted value beyond a bound. */
  private static final int SCAN_LIMIT = 1 << 12;

  private static final int INFINITE = Integer.MAX_VALUE / 4;

  private final AtomicTrail trail;
  private final int position;
  private final IntVar[] list;
  // the counted values in increasing order, with their counters or fixed bounds
  private final int[] values;
  private final IntVar[] counters;
  private final int[] fixedLow;
  private final int[] fixedUp;
  // whether the variables may take uncounted values, and the counter of those (may be null)
  private final boolean open;
  private final IntVar rest;

  // the negated atom: its variable (null for a failure), kind and value
  private IntVar negated;
  private int negatedKind;
  private int negatedValue;

  // per variable of the list: bounds in the network, bounds before the position, holes (values and
  // entries), and whether it may take an uncounted value
  private int[] lo;
  private int[] hi;
  private int[] minBefore;
  private int[] maxBefore;
  private int[][] holeValue;
  private int[][] holeEntry;
  private boolean[] uncounted;
  // per value (m for the uncounted ones) the bounds of the arc to the sink
  private int[] low;
  private int[] up;
  // per counter the holes its bounds were moved past
  private EntryList[] lowHoles;
  private EntryList[] upHoles;
  // per counter its bounds before they were moved past the holes, which its bound atoms give
  private int[] lowBound;
  private int[] upBound;

  // the network: node 0 the source, 1 the sink, 2 and 3 the source and sink of the lower bound
  // reduction, then the variables, the values and the uncounted values
  private int nodes;
  private int[] first;
  private int[] next;
  private int[] head;
  private int[] cap;
  private int arcs;
  private int[] level;
  private int[] cursor;

  private CardinalityExplanation(
      AtomicTrail trail,
      int position,
      IntVar[] list,
      int[] values,
      IntVar[] counters,
      int[] fixedLow,
      int[] fixedUp,
      boolean open,
      IntVar rest) {
    this.trail = trail;
    this.position = position;
    this.list = list;
    this.values = values;
    this.counters = counters;
    this.fixedLow = fixedLow;
    this.fixedUp = fixedUp;
    this.open = open;
    this.rest = rest;
  }

  /**
   * The constraint whose flow network explains: variables, counted values and their bounds.
   *
   * @param list the counted variables
   * @param values the counted values, in increasing order, without repetitions
   * @param counters the counter of each value, or null when the bounds are fixed
   * @param fixedLow the fixed lower bound of each value, when counters is null
   * @param fixedUp the fixed upper bound of each value, when counters is null
   * @param open whether the variables may take values that are not counted
   * @param rest the number of variables taking an uncounted value, or null when it is free
   */
  static final class Network {
    private final IntVar[] list;
    private final int[] values;
    private final IntVar[] counters;
    private final int[] fixedLow;
    private final int[] fixedUp;
    private final boolean open;
    private final IntVar rest;

    Network(
        IntVar[] list,
        int[] values,
        IntVar[] counters,
        int[] fixedLow,
        int[] fixedUp,
        boolean open,
        IntVar rest) {
      this.list = list;
      this.values = values;
      this.counters = counters;
      this.fixedLow = fixedLow;
      this.fixedUp = fixedUp;
      this.open = open;
      this.rest = rest;
    }

    /**
     * Adds to {@code out} the reason of an entry of one of the variables or counters.
     *
     * @param trail the trail
     * @param entry the entry
     * @param out where the reason entries are added
     * @return false when the entry is not of the network's variables, the network with the negation
     *     of the entry is feasible, or it is too large
     */
    boolean explain(AtomicTrail trail, int entry, EntryList out) {
      CardinalityExplanation e = explanation(trail, entry);
      IntVar y = trail.variable(entry);
      if (!e.occurs(y)) {
        return false;
      }
      e.negated = y;
      e.negatedKind = trail.kind(entry);
      e.negatedValue = trail.value(entry);
      return e.run(out);
    }

    /**
     * Adds to {@code out} the reason of a failure.
     *
     * @param trail the trail
     * @param out where the reason entries are added
     * @return false when the network is feasible, or too large
     */
    boolean explainFailure(AtomicTrail trail, EntryList out) {
      return explanation(trail, trail.size()).run(out);
    }

    private CardinalityExplanation explanation(AtomicTrail trail, int position) {
      return new CardinalityExplanation(
          trail, position, list, values, counters, fixedLow, fixedUp, open, rest);
    }
  }

  private boolean occurs(IntVar y) {
    if (y == rest) {
      return true;
    }
    for (IntVar x : list) {
      if (x == y) {
        return true;
      }
    }
    if (counters != null) {
      for (IntVar c : counters) {
        if (c == y) {
          return true;
        }
      }
    }
    return false;
  }

  // whether the negated atom allows value v of the negated variable
  private boolean allowed(IntVar z, long v) {
    if (z != negated) {
      return true;
    }
    return switch (negatedKind) {
      case AtomicTrail.GE -> v < negatedValue;
      case AtomicTrail.LE -> v > negatedValue;
      default -> v == negatedValue;
    };
  }

  private boolean run(EntryList out) {
    int mark = out.size();
    if (!readDomains() || !readBounds() || !build()) {
      return false;
    }
    int demand = 0;
    for (int f = first[2]; f >= 0; f = next[f]) {
      demand += cap[f];
    }
    if (maxFlow() == demand) {
      return false;
    }
    boolean[] inCut = reachable();
    if (!addReason(inCut, out)) {
      out.truncate(mark);
      return false;
    }
    out.sortUnique(mark);
    return true;
  }

  private boolean readDomains() {
    int n = list.length;
    lo = new int[n];
    hi = new int[n];
    minBefore = new int[n];
    maxBefore = new int[n];
    holeValue = new int[n][];
    holeEntry = new int[n][];
    uncounted = new boolean[n];
    EntryList atoms = new EntryList();
    for (int i = 0; i < n; i++) {
      IntVar z = list[i];
      minBefore[i] = trail.minBefore(z, position);
      maxBefore[i] = trail.maxBefore(z, position);
      lo[i] = minBefore[i];
      hi[i] = maxBefore[i];
      if (z == negated) {
        switch (negatedKind) {
          case AtomicTrail.GE -> hi[i] = Math.min(hi[i], negatedValue - 1);
          case AtomicTrail.LE -> lo[i] = Math.max(lo[i], negatedValue + 1);
          default -> {
            lo[i] = Math.max(lo[i], negatedValue);
            hi[i] = Math.min(hi[i], negatedValue);
          }
        }
      }
      atoms.clear();
      trail.atomsBefore(z, position, atoms);
      int holes = 0;
      int[] hv = new int[atoms.size()];
      int[] he = new int[atoms.size()];
      for (int k = 0; k < atoms.size(); k++) {
        int f = atoms.get(k);
        if (trail.kind(f) == AtomicTrail.NE) {
          hv[holes] = trail.value(f);
          he[holes++] = f;
        }
      }
      sortHoles(hv, he, holes);
      holeValue[i] = Arrays.copyOf(hv, holes);
      holeEntry[i] = Arrays.copyOf(he, holes);
      if (open) {
        uncounted[i] = hasUncounted(i);
      }
    }
    return true;
  }

  private static void sortHoles(int[] hv, int[] he, int holes) {
    for (int a = 1; a < holes; a++) {
      int v = hv[a];
      int e = he[a];
      int b = a - 1;
      while (b >= 0 && hv[b] > v) {
        hv[b + 1] = hv[b];
        he[b + 1] = he[b];
        b--;
      }
      hv[b + 1] = v;
      he[b + 1] = e;
    }
  }

  // whether variable i may take value v in the network
  private boolean contains(int i, int v) {
    return v >= lo[i]
        && v <= hi[i]
        && trail.rootDomain(list[i]).contains(v)
        && Arrays.binarySearch(holeValue[i], v) < 0;
  }

  // whether variable i may take an uncounted value in the network
  private boolean hasUncounted(int i) {
    if (lo[i] > hi[i]) {
      return false;
    }
    IntDomain root = trail.rootDomain(list[i]);
    long size = root.intersect(lo[i], hi[i]).getSize();
    for (int h : holeValue[i]) {
      if (h >= lo[i] && h <= hi[i] && root.contains(h)) {
        size--;
      }
    }
    int counted = 0;
    int from = lowerIndex(lo[i]);
    for (int j = from; j < values.length && values[j] <= hi[i]; j++) {
      if (contains(i, values[j])) {
        counted++;
      }
    }
    return size > counted;
  }

  // the position of the first value at least v
  private int lowerIndex(int v) {
    int j = Arrays.binarySearch(values, v);
    return j >= 0 ? j : -j - 1;
  }

  private boolean readBounds() {
    int m = values.length;
    int n = list.length;
    low = new int[m + 1];
    up = new int[m + 1];
    lowHoles = new EntryList[m + 1];
    upHoles = new EntryList[m + 1];
    lowBound = new int[m + 1];
    upBound = new int[m + 1];
    for (int j = 0; j < m; j++) {
      if (counters == null) {
        low[j] = fixedLow[j];
        up[j] = fixedUp[j];
      } else if (!counterBounds(counters[j], j)) {
        return false;
      }
    }
    if (rest == null) {
      low[m] = 0;
      up[m] = n;
    } else if (!counterBounds(rest, m)) {
      return false;
    }
    if (counters == null) {
      for (int j = 0; j < m; j++) {
        low[j] = Math.max(low[j], 0);
        up[j] = Math.min(up[j], n);
        if (low[j] > up[j]) {
          return false;
        }
      }
    }
    return true;
  }

  // the bounds of a counter between 0 and n, moved past the holes it had; the holes passed are
  // kept to be cited with the bound
  private boolean counterBounds(IntVar c, int j) {
    long a = Math.max(trail.minBefore(c, position), 0L);
    long b = Math.min(trail.maxBefore(c, position), (long) list.length);
    if (c == negated) {
      switch (negatedKind) {
        case AtomicTrail.GE -> b = Math.min(b, negatedValue - 1L);
        case AtomicTrail.LE -> a = Math.max(a, negatedValue + 1L);
        default -> {
          a = Math.max(a, negatedValue);
          b = Math.min(b, negatedValue);
        }
      }
    }
    EntryList atoms = new EntryList();
    trail.atomsBefore(c, position, atoms);
    int holes = 0;
    int[] hv = new int[atoms.size()];
    int[] he = new int[atoms.size()];
    for (int k = 0; k < atoms.size(); k++) {
      int f = atoms.get(k);
      if (trail.kind(f) == AtomicTrail.NE) {
        hv[holes] = trail.value(f);
        he[holes++] = f;
      }
    }
    sortHoles(hv, he, holes);
    int[] holeValues = Arrays.copyOf(hv, holes);
    IntDomain root = trail.rootDomain(c);
    if (a > b) {
      return false;
    }
    lowBound[j] = (int) a;
    upBound[j] = (int) b;
    lowHoles[j] = new EntryList();
    upHoles[j] = new EntryList();
    while (a <= b && !inDomain(root, holeValues, he, (int) a, lowHoles[j])) {
      a++;
    }
    while (a <= b && !inDomain(root, holeValues, he, (int) b, upHoles[j])) {
      b--;
    }
    if (a > b) {
      return false;
    }
    low[j] = (int) a;
    up[j] = (int) b;
    return true;
  }

  // whether v is in a domain of the given root and holes; if it is a hole, its entry is added
  private static boolean inDomain(
      IntDomain root, int[] holes, int[] entries, int v, EntryList out) {
    if (!root.contains(v)) {
      return false;
    }
    int k = Arrays.binarySearch(holes, v);
    if (k >= 0) {
      out.add(entries[k]);
      return false;
    }
    return true;
  }

  private int variableNode(int i) {
    return 4 + i;
  }

  private int valueNode(int j) {
    return 4 + list.length + j;
  }

  private boolean build() {
    int n = list.length;
    int m = values.length;
    nodes = 4 + n + m + (open ? 1 : 0);
    first = new int[nodes];
    Arrays.fill(first, -1);
    int capacity = 64;
    next = new int[capacity];
    head = new int[capacity];
    cap = new int[capacity];
    arcs = 0;
    long[] excess = new long[nodes];
    // source to each variable: one unit exactly
    excess[0] -= n;
    for (int i = 0; i < n; i++) {
      excess[variableNode(i)] += 1;
      int from = lowerIndex(lo[i]);
      for (int j = from; j < m && values[j] <= hi[i]; j++) {
        if (contains(i, values[j])) {
          if (arcs >= 2 * ARC_LIMIT) {
            return false;
          }
          addArc(variableNode(i), valueNode(j), 1);
        }
      }
      if (open && uncounted[i]) {
        addArc(variableNode(i), valueNode(m), 1);
      }
    }
    for (int j = 0; j < m + (open ? 1 : 0); j++) {
      addArc(valueNode(j), 1, up[j] - low[j]);
      excess[1] += low[j];
      excess[valueNode(j)] -= low[j];
    }
    addArc(1, 0, INFINITE);
    for (int u = 0; u < nodes; u++) {
      if (u == 2 || u == 3) {
        continue;
      }
      if (excess[u] > 0) {
        addArc(2, u, (int) excess[u]);
      } else if (excess[u] < 0) {
        addArc(u, 3, (int) -excess[u]);
      }
    }
    return true;
  }

  private void addArc(int u, int v, int c) {
    if (arcs + 2 > head.length) {
      int size = 2 * head.length;
      next = Arrays.copyOf(next, size);
      head = Arrays.copyOf(head, size);
      cap = Arrays.copyOf(cap, size);
    }
    int forward = arcs;
    int backward = arcs + 1;
    head[forward] = v;
    cap[forward] = c;
    next[forward] = first[u];
    first[u] = forward;
    head[backward] = u;
    cap[backward] = 0;
    next[backward] = first[v];
    first[v] = backward;
    arcs += 2;
  }

  // Dinic's maximum flow from node 2 to node 3
  private int maxFlow() {
    level = new int[nodes];
    cursor = new int[nodes];
    int[] queue = new int[nodes];
    int flow = 0;
    while (true) {
      Arrays.fill(level, -1);
      level[2] = 0;
      int qh = 0;
      int qt = 0;
      queue[qt++] = 2;
      while (qh < qt) {
        int u = queue[qh++];
        for (int f = first[u]; f >= 0; f = next[f]) {
          if (cap[f] > 0 && level[head[f]] < 0) {
            level[head[f]] = level[u] + 1;
            queue[qt++] = head[f];
          }
        }
      }
      if (level[3] < 0) {
        return flow;
      }
      System.arraycopy(first, 0, cursor, 0, nodes);
      int pushed;
      while ((pushed = push(2, INFINITE)) > 0) {
        flow += pushed;
      }
    }
  }

  // an augmenting path along the levels, iteratively: the arcs taken so far
  private int push(int source, int limit) {
    List<Integer> path = new ArrayList<>();
    int u = source;
    while (true) {
      if (u == 3) {
        int amount = limit;
        for (int f : path) {
          amount = Math.min(amount, cap[f]);
        }
        for (int f : path) {
          cap[f] -= amount;
          cap[f ^ 1] += amount;
        }
        return amount;
      }
      int f = cursor[u];
      while (f >= 0 && (cap[f] <= 0 || level[head[f]] != level[u] + 1)) {
        f = next[f];
      }
      cursor[u] = f;
      if (f >= 0) {
        path.add(f);
        u = head[f];
      } else {
        if (path.isEmpty()) {
          return 0;
        }
        // dead end: no arc leads on from u in this phase
        level[u] = -1;
        int back = path.remove(path.size() - 1);
        u = head[back ^ 1];
        cursor[u] = next[cursor[u]];
      }
    }
  }

  // the nodes reachable from node 2 in the residual network
  private boolean[] reachable() {
    boolean[] seen = new boolean[nodes];
    int[] queue = new int[nodes];
    int qh = 0;
    int qt = 0;
    queue[qt++] = 2;
    seen[2] = true;
    while (qh < qt) {
      int u = queue[qh++];
      for (int f = first[u]; f >= 0; f = next[f]) {
        if (cap[f] > 0 && !seen[head[f]]) {
          seen[head[f]] = true;
          queue[qt++] = head[f];
        }
      }
    }
    return seen;
  }

  /**
   * Adds the atoms that keep the arcs of the violated set X: missing arcs leaving it, upper bounds
   * of counters leaving it and lower bounds of counters entering it. Checks that the set violates
   * Hoffman's condition with the bounds cited.
   */
  private boolean addReason(boolean[] inCut, EntryList out) {
    int n = list.length;
    int m = values.length;
    long leaving = 0;
    long entering = 0;
    if (inCut[1] && !inCut[0]) {
      return false;
    }
    for (int i = 0; i < n; i++) {
      int x = variableNode(i);
      if (!inCut[x]) {
        if (inCut[0]) {
          leaving++;
        }
        continue;
      }
      if (!inCut[0]) {
        entering++;
      }
      Exclusions ex = new Exclusions(i);
      for (int j = 0; j < m; j++) {
        if (inCut[valueNode(j)]) {
          continue;
        }
        if (contains(i, values[j])) {
          leaving++;
        } else {
          ex.exclude(values[j]);
        }
      }
      if (open && !inCut[valueNode(m)]) {
        if (uncounted[i]) {
          leaving++;
        } else if (!ex.excludeUncounted()) {
          return false;
        }
      }
      if (!ex.addTo(out)) {
        return false;
      }
    }
    for (int j = 0; j < m + (open ? 1 : 0); j++) {
      IntVar c = rest;
      if (j < m) {
        c = counters == null ? null : counters[j];
      }
      if (inCut[valueNode(j)] && !inCut[1]) {
        leaving += up[j];
        if (c != null && !(c == negated && negatedBoundsUp())) {
          addBound(c, false, upBound[j], out);
        }
        addAll(upHoles[j], out);
      } else if (!inCut[valueNode(j)] && inCut[1] && low[j] > 0) {
        entering += low[j];
        if (c != null && !(c == negated && negatedBoundsLow())) {
          addBound(c, true, lowBound[j], out);
        }
        addAll(lowHoles[j], out);
      }
    }
    return entering > leaving;
  }

  // whether the negated atom gives the counter's upper bound used: an entry c >= a leaves c <= a -
  // 1,
  // below the maximum before it, and c != a leaves c = a
  private boolean negatedBoundsUp() {
    return negatedKind != AtomicTrail.LE;
  }

  private boolean negatedBoundsLow() {
    return negatedKind != AtomicTrail.GE;
  }

  private static void addAll(EntryList from, EntryList out) {
    if (from != null) {
      for (int k = 0; k < from.size(); k++) {
        out.add(from.get(k));
      }
    }
  }

  // the weakest bound atom of c that gives c >= bound (lower) or c <= bound
  private void addBound(IntVar c, boolean lower, long bound, EntryList out) {
    int e =
        lower
            ? trail.earliestLowerBound(c, bound, position)
            : trail.earliestUpperBound(c, bound, position);
    if (e >= 0 && e != Integer.MAX_VALUE) {
      out.add(e);
    }
  }

  /** The values one variable must be kept away from, gathered before the atoms are added. */
  private final class Exclusions {
    private final int i;
    private final IntVar z;
    private final IntDomain root;
    // the lowest value the lower bound must exceed, the highest one the upper bound must stay below
    private long below = Long.MIN_VALUE;
    private long above = Long.MAX_VALUE;
    private final EntryList holes = new EntryList();
    // a value to exclude that the domain before the position still had
    private boolean missing;

    Exclusions(int i) {
      this.i = i;
      this.z = list[i];
      this.root = trail.rootDomain(z);
    }

    void exclude(int v) {
      if (!allowed(z, v) || !root.contains(v)) {
        return;
      }
      if (v < minBefore[i]) {
        below = Math.max(below, v);
      } else if (v > maxBefore[i]) {
        above = Math.min(above, v);
      } else {
        int k = Arrays.binarySearch(holeValue[i], v);
        if (k >= 0) {
          holes.add(holeEntry[i][k]);
        } else {
          missing = true;
        }
      }
    }

    // every uncounted value; false when one beyond a bound is too far to find
    boolean excludeUncounted() {
      boolean lowerSide = z != negated || negatedKind == AtomicTrail.GE;
      boolean upperSide = z != negated || negatedKind == AtomicTrail.LE;
      if (lowerSide && root.min() < minBefore[i]) {
        int v = minBefore[i];
        int steps = 0;
        while (true) {
          int u = root.previousValue(v);
          if (u >= v || ++steps > SCAN_LIMIT) {
            if (u < v) {
              return false;
            }
            break;
          }
          v = u;
          if (Arrays.binarySearch(values, v) < 0) {
            exclude(v);
            break;
          }
        }
      }
      if (upperSide && root.max() > maxBefore[i]) {
        int v = maxBefore[i];
        int steps = 0;
        while (true) {
          int u = root.nextValue(v);
          if (u <= v || ++steps > SCAN_LIMIT) {
            if (u > v) {
              return false;
            }
            break;
          }
          v = u;
          if (Arrays.binarySearch(values, v) < 0) {
            exclude(v);
            break;
          }
        }
      }
      for (int h : holeValue[i]) {
        if (Arrays.binarySearch(values, h) < 0) {
          exclude(h);
        }
      }
      return true;
    }

    boolean addTo(EntryList out) {
      if (missing) {
        return false;
      }
      if (below != Long.MIN_VALUE) {
        addBound(z, true, below + 1, out);
      }
      if (above != Long.MAX_VALUE) {
        addBound(z, false, above - 1, out);
      }
      for (int k = 0; k < holes.size(); k++) {
        out.add(holes.get(k));
      }
      return true;
    }
  }
}
