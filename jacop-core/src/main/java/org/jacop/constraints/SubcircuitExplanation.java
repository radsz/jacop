/*
 * SubcircuitExplanation.java
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

import java.util.Arrays;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of {@link Subcircuit} and {@link Circuit} by cuts of their successor graph, in the
 * manner of Francis and Stuckey, "Explaining circuit propagation" (Constraints, 2014). Node i has
 * an arc to j when x[i] may be offset + j, and may stay out of the circuit when x[i] may be offset
 * + i. A node that must be in the circuit is required; in a Circuit every node is.
 *
 * <p>Every reason is a set of nodes S closed under arcs (or under reverse arcs): the atoms that
 * removed the arcs leaving S (or entering it), with the atoms that make some nodes required. A
 * cycle through a node of S then stays in S. So:
 *
 * <ul>
 *   <li>arc v to t is on no cycle when there is no path from t to v;
 *   <li>v stays out when it is on no cycle, or when a required node and v do not reach each other;
 *   <li>v is required, and arc v to t is impossible, when every path between two required nodes
 *       passes through v, or misses the arc (the dominator pruning);
 *   <li>a value fixed for one node is removed from the others (all different);
 *   <li>in a Circuit, the arc that would close a chain of fixed arcs early is removed, with those
 *       arcs as the reason.
 * </ul>
 *
 * <p>The graph is that of the domains just before the explained entry. A propagation found on a
 * larger graph earlier in the same call holds on it too, as removing arcs only removes paths. What
 * this class cannot explain is left to the Hall sets of {@link AlldiffExplanation}, and then to the
 * generic reason.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class SubcircuitExplanation {

  /** The most nodes explained; larger graphs use the generic reason. */
  private static final int NODE_LIMIT = 4096;

  /** The most removed values of one atom explained one by one. */
  private static final int REMOVED_LIMIT = 256;

  /** The most nodes tried as the root of a dominator reason, after the recorded ones. */
  private static final int ROOT_TRIES = 4;

  private final AtomicTrail trail;
  private final int position;
  private final IntVar[] list;
  private final int n;
  private final int[] recentRoots;
  // the value pointing to node 0; and whether every node is in the circuit (Circuit)
  private final int offset;
  private final boolean circuit;

  // the domains just before the position: bounds, holes inside them, arcs and self loops
  private final int[] lo;
  private final int[] hi;
  private final int[][] holes;
  private int[] arcStart;
  private int[] arcTo;
  private int[] predStart;
  private int[] predFrom;
  private final boolean[] selfLoop;
  // the node fixed to each node's value, or -1; and two nodes fixed to the same value
  private final int[] fixedBy;
  private int clashA = -1;
  private int clashB = -1;

  // closures
  private final int[] mark;
  private int stamp;
  private final int[] queue;
  private int closureSize;
  private final boolean[] allowed;
  private final EntryList scratch = new EntryList();
  private final EntryList best = new EntryList();
  private boolean bestEmpty = true;
  private EntryList nodeOutCache;
  private int nodeOutNode = -1;

  private SubcircuitExplanation(
      AtomicTrail trail, int position, IntVar[] list, int offset, boolean circuit, int[] roots) {
    this.trail = trail;
    this.position = position;
    this.list = list;
    this.offset = offset;
    this.circuit = circuit;
    this.recentRoots = roots;
    n = list.length;
    lo = new int[n];
    hi = new int[n];
    holes = new int[n][];
    selfLoop = new boolean[n];
    fixedBy = new int[n];
    mark = new int[n];
    queue = new int[n];
    allowed = new boolean[n];
  }

  /**
   * Adds to {@code out} the reason of an entry of one of the variables.
   *
   * @param trail the trail
   * @param entry the entry
   * @param list the variables
   * @param offset the value that points to list[0]
   * @param circuit whether every node is in the circuit (Circuit rather than Subcircuit)
   * @param roots nodes recently used as roots of the dominator pruning, -1 for none
   * @param out where the reason entries are added
   * @return false when some removed value has no reason here
   */
  static boolean explain(
      AtomicTrail trail,
      int entry,
      IntVar[] list,
      int offset,
      boolean circuit,
      int[] roots,
      EntryList out) {
    if (list.length > NODE_LIMIT) {
      return false;
    }
    IntVar y = trail.variable(entry);
    int v = indexOf(list, y);
    if (v < 0) {
      return false;
    }
    IntDomain root = trail.rootDomain(y);
    int first = trail.removedMin(entry);
    int last = trail.removedMax(entry);
    int mark = out.size();
    int min = trail.minBefore(y, entry);
    if (first < min) {
      trail.addLowerBound(y, entry, out);
      first = min;
    }
    int max = trail.maxBefore(y, entry);
    if (last > max) {
      trail.addUpperBound(y, entry, out);
      last = max;
    }
    // values that point to no node are no arcs: the constraint removes them by itself
    first = Math.max(first, offset);
    last = (int) Math.min(last, offset + (long) list.length - 1);
    if (first > last) {
      return true;
    }
    if (last - first >= REMOVED_LIMIT) {
      out.truncate(mark);
      return false;
    }
    SubcircuitExplanation e = new SubcircuitExplanation(trail, entry, list, offset, circuit, roots);
    e.build();
    for (int w = first; w <= last; w++) {
      int t = w - offset;
      // a node of a circuit never points to itself
      if (circuit && t == v || !root.contains(w) || trail.excludedBefore(y, w, entry, out)) {
        continue;
      }
      boolean explained = t == v ? e.required(v, out) : e.arcRemoved(v, t, out);
      if (!explained) {
        out.truncate(mark);
        return false;
      }
    }
    out.sortUnique(mark);
    return true;
  }

  /**
   * Adds to {@code out} the reason of a failure.
   *
   * @param trail the trail
   * @param list the variables
   * @param offset the value that points to list[0]
   * @param circuit whether every node is in the circuit (Circuit rather than Subcircuit)
   * @param roots nodes recently used as roots of the dominator pruning, -1 for none
   * @param out where the reason entries are added
   * @return false when no reason is found here
   */
  static boolean explainFailure(
      AtomicTrail trail, IntVar[] list, int offset, boolean circuit, int[] roots, EntryList out) {
    if (list.length > NODE_LIMIT) {
      return false;
    }
    SubcircuitExplanation e =
        new SubcircuitExplanation(trail, trail.size(), list, offset, circuit, roots);
    e.build();
    return e.failure(out);
  }

  private static int indexOf(IntVar[] list, IntVar y) {
    for (int i = 0; i < list.length; i++) {
      if (list[i] == y) {
        return i;
      }
    }
    return -1;
  }

  private void build() {
    EntryList atoms = new EntryList();
    int[] holeMark = new int[n];
    long top = offset + (long) n - 1;
    arcStart = new int[n + 1];
    arcTo = new int[Math.max(16, 4 * n)];
    int count = 0;
    Arrays.fill(fixedBy, -1);
    for (int s = 0; s < n; s++) {
      IntVar x = list[s];
      lo[s] = trail.minBefore(x, position);
      hi[s] = trail.maxBefore(x, position);
      atoms.clear();
      trail.atomsBefore(x, position, atoms);
      int[] hole = new int[atoms.size()];
      int h = 0;
      for (int k = 0; k < atoms.size(); k++) {
        int f = atoms.get(k);
        if (trail.kind(f) == AtomicTrail.NE) {
          hole[h++] = f;
          long t = (long) trail.value(f) - offset;
          if (t >= 0 && t < n) {
            holeMark[(int) t] = s + 1;
          }
        }
      }
      holes[s] = Arrays.copyOf(hole, h);
      IntDomain root = trail.rootDomain(x);
      arcStart[s] = count;
      selfLoop[s] = false;
      for (int w = Math.max(lo[s], offset), end = (int) Math.min(hi[s], top); w <= end; w++) {
        int t = w - offset;
        if (holeMark[t] == s + 1 || !root.contains(w)) {
          continue;
        }
        if (t == s) {
          selfLoop[s] = !circuit;
        } else {
          if (count == arcTo.length) {
            arcTo = Arrays.copyOf(arcTo, 2 * count);
          }
          arcTo[count++] = t;
        }
      }
      if (lo[s] == hi[s] && lo[s] >= offset && lo[s] <= top) {
        int t = lo[s] - offset;
        if (fixedBy[t] >= 0) {
          clashA = fixedBy[t];
          clashB = s;
        } else {
          fixedBy[t] = s;
        }
      }
    }
    arcStart[n] = count;
  }

  private void buildPredecessors() {
    if (predStart != null) {
      return;
    }
    predStart = new int[n + 1];
    predFrom = new int[arcStart[n]];
    for (int a = 0; a < arcStart[n]; a++) {
      predStart[arcTo[a] + 1]++;
    }
    for (int t = 0; t < n; t++) {
      predStart[t + 1] += predStart[t];
    }
    int[] fill = Arrays.copyOf(predStart, n);
    for (int s = 0; s < n; s++) {
      for (int a = arcStart[s]; a < arcStart[s + 1]; a++) {
        predFrom[fill[arcTo[a]]++] = s;
      }
    }
  }

  // ---- closures ----

  private boolean inClosure(int s) {
    return mark[s] == stamp;
  }

  // the nodes reachable from seed by arcs without entering stop (-1 for none)
  private void forward(int seed, int stop) {
    stamp++;
    mark[seed] = stamp;
    queue[0] = seed;
    int tail = 1;
    for (int head = 0; head < tail; head++) {
      int s = queue[head];
      for (int a = arcStart[s]; a < arcStart[s + 1]; a++) {
        int t = arcTo[a];
        if (t != stop && mark[t] != stamp) {
          mark[t] = stamp;
          queue[tail++] = t;
        }
      }
    }
    closureSize = tail;
  }

  // the nodes that reach seed by arcs without passing through stop (-1 for none)
  private void backward(int seed, int stop) {
    buildPredecessors();
    stamp++;
    mark[seed] = stamp;
    queue[0] = seed;
    int tail = 1;
    for (int head = 0; head < tail; head++) {
      int t = queue[head];
      for (int a = predStart[t]; a < predStart[t + 1]; a++) {
        int s = predFrom[a];
        if (s != stop && mark[s] != stamp) {
          mark[s] = stamp;
          queue[tail++] = s;
        }
      }
    }
    closureSize = tail;
  }

  // whether some node of the closure other than v has an arc to v
  private boolean arcInto(int v) {
    for (int k = 0; k < closureSize; k++) {
      int s = queue[k];
      if (s != v) {
        for (int a = arcStart[s]; a < arcStart[s + 1]; a++) {
          if (arcTo[a] == v) {
            return true;
          }
        }
      }
    }
    return false;
  }

  // the first required node outside the closure other than skip, or -1
  private int requiredOutside(int skip) {
    for (int u = 0; u < n; u++) {
      if (!selfLoop[u] && u != skip && !inClosure(u)) {
        return u;
      }
    }
    return -1;
  }

  /**
   * Adds the atoms that removed the arcs leaving the forward closure: arcs to nodes outside it
   * other than stop, and arcs to forbid.
   */
  private void forwardCut(int stop, int forbid, EntryList out) {
    for (int t = 0; t < n; t++) {
      allowed[t] = (inClosure(t) && t != forbid) || t == stop;
    }
    for (int k = 0; k < closureSize; k++) {
      addRemovedArcs(queue[k], out);
    }
  }

  /** Adds the atoms that removed the arcs entering the backward closure from nodes but stop. */
  private void backwardCut(int stop, EntryList out) {
    for (int t = 0; t < n; t++) {
      allowed[t] = !inClosure(t);
    }
    for (int s = 0; s < n; s++) {
      if (s != stop && !inClosure(s)) {
        addRemovedArcs(s, out);
      }
    }
  }

  // the atoms that removed the arcs of s to nodes not allowed
  private void addRemovedArcs(int s, EntryList out) {
    IntVar x = list[s];
    for (int f : holes[s]) {
      long t = (long) trail.value(f) - offset;
      if (t >= 0 && t < n && t != s && !allowed[(int) t]) {
        out.add(f);
      }
    }
    IntDomain root = trail.rootDomain(x);
    long top = offset + (long) n - 1;
    for (long w = Math.min(lo[s] - 1L, top); w >= offset; w--) {
      int t = (int) (w - offset);
      if (t != s && !allowed[t] && root.contains((int) w)) {
        trail.addBoundReaching(x, position, true, w + 1L, out);
        break;
      }
    }
    for (long w = Math.max(hi[s] + 1L, offset); w <= top; w++) {
      int t = (int) (w - offset);
      if (t != s && !allowed[t] && root.contains((int) w)) {
        trail.addBoundReaching(x, position, false, w - 1L, out);
        break;
      }
    }
  }

  // the atom that removed u's self loop
  private void addRequired(int u, EntryList out) {
    if (circuit) {
      // the constraint itself keeps the node in the circuit
      return;
    }
    IntVar x = list[u];
    int w = u + offset;
    if (w < lo[u]) {
      trail.addBoundReaching(x, position, true, w + 1L, out);
    } else if (w > hi[u]) {
      trail.addBoundReaching(x, position, false, w - 1L, out);
    } else {
      for (int f : holes[u]) {
        if (trail.value(f) == w) {
          out.add(f);
          return;
        }
      }
    }
  }

  // the atoms that fix node p
  private void addFixed(int p, EntryList out) {
    trail.addBoundReaching(list[p], position, true, lo[p], out);
    trail.addBoundReaching(list[p], position, false, hi[p], out);
  }

  // keeps the smaller of the scratch reason and the best one so far
  private void offer() {
    scratch.sortUnique(0);
    if (bestEmpty || scratch.size() < best.size()) {
      best.clear();
      for (int k = 0; k < scratch.size(); k++) {
        best.add(scratch.get(k));
      }
      bestEmpty = false;
    }
    scratch.clear();
  }

  private void startBest() {
    best.clear();
    scratch.clear();
    bestEmpty = true;
  }

  private boolean takeBest(EntryList out) {
    if (bestEmpty) {
      return false;
    }
    for (int k = 0; k < best.size(); k++) {
      out.add(best.get(k));
    }
    return true;
  }

  // ---- reasons ----

  // no path from a to b, as a cut of the forward closure of a or the backward closure of b
  private void offerNoPath(int a, int b) {
    forward(a, -1);
    if (!inClosure(b)) {
      forwardCut(-1, -1, scratch);
      offer();
    }
    backward(b, -1);
    if (!inClosure(a)) {
      backwardCut(-1, scratch);
      offer();
    }
  }

  // v cannot be in the circuit
  private void offerNodeOut(int v) {
    forward(v, -1);
    if (!arcInto(v)) {
      forwardCut(-1, v, scratch);
      offer();
    }
    int u = requiredOutside(v);
    if (u >= 0) {
      forwardCut(-1, -1, scratch);
      addRequired(u, scratch);
      offer();
    }
    backward(v, -1);
    u = requiredOutside(v);
    if (u >= 0) {
      backwardCut(-1, scratch);
      addRequired(u, scratch);
      offer();
    }
  }

  // the reason why v cannot be in the circuit, computed once per explanation
  private EntryList nodeOut(int v) {
    if (nodeOutNode != v) {
      nodeOutNode = v;
      startBest();
      offerNodeOut(v);
      nodeOutCache = null;
      if (!bestEmpty) {
        nodeOutCache = new EntryList();
        takeBest(nodeOutCache);
      }
    }
    return nodeOutCache;
  }

  // the roots tried for dominator reasons: the recorded ones, then a few required nodes
  private int[] candidateRoots(int a, int b) {
    int[] roots = new int[recentRoots.length + ROOT_TRIES];
    int k = 0;
    for (int r : recentRoots) {
      if (r >= 0 && r < n && r != a && r != b && !selfLoop[r] && !contains(roots, k, r)) {
        roots[k++] = r;
      }
    }
    int limit = k + ROOT_TRIES;
    for (int r = 0; r < n && k < limit; r++) {
      if (!selfLoop[r] && r != a && r != b && !contains(roots, k, r)) {
        roots[k++] = r;
      }
    }
    return Arrays.copyOf(roots, k);
  }

  private static boolean contains(int[] a, int size, int value) {
    for (int k = 0; k < size; k++) {
      if (a[k] == value) {
        return true;
      }
    }
    return false;
  }

  // the node a node is fixed to point to, or -1
  private int fixedSuccessor(int s) {
    return lo[s] == hi[s] && lo[s] >= offset && lo[s] - (long) offset < n ? lo[s] - offset : -1;
  }

  // the number of nodes on the fixed arcs from t to v, or -1 when they do not lead to v
  private int chainLength(int t, int v) {
    int c = t;
    int count = 1;
    while (c >= 0 && c != v && count <= n) {
      c = fixedSuccessor(c);
      count++;
    }
    return c == v ? count : -1;
  }

  // arc v -> t is removed
  private boolean arcRemoved(int v, int t, EntryList out) {
    int p = fixedBy[t];
    if (p >= 0 && p != v) {
      addFixed(p, out);
      return true;
    }
    if (circuit) {
      // the fixed arcs from t lead to v, and arc v -> t would close a cycle without every node
      int length = chainLength(t, v);
      if (length > 0 && length < n) {
        for (int k = t; k != v; k = fixedSuccessor(k)) {
          addFixed(k, out);
        }
        return true;
      }
    }
    startBest();
    offerNoPath(t, v);
    EntryList outV = nodeOut(v);
    if (outV != null) {
      for (int k = 0; k < outV.size(); k++) {
        scratch.add(outV.get(k));
      }
      offer();
    }
    if (bestEmpty) {
      // t cannot be in the circuit
      offerNodeOut(t);
    }
    if (bestEmpty) {
      // a required root reaches v only through t, or t reaches the root only through v
      for (int r : candidateRoots(v, t)) {
        forward(r, t);
        if (!inClosure(v)) {
          forwardCut(t, -1, scratch);
          addRequired(r, scratch);
          offer();
        }
        backward(r, v);
        if (!inClosure(t)) {
          backwardCut(v, scratch);
          addRequired(r, scratch);
          offer();
        }
        if (!bestEmpty) {
          break;
        }
      }
    }
    return takeBest(out);
  }

  // v's self loop is removed: v is required
  private boolean required(int v, EntryList out) {
    int p = fixedBy[v];
    if (p >= 0 && p != v) {
      addFixed(p, out);
      return true;
    }
    startBest();
    // two required nodes whose paths all pass through v
    for (int r : candidateRoots(v, v)) {
      forward(r, v);
      int u = requiredOutside(v);
      if (u >= 0) {
        forwardCut(v, -1, scratch);
        addRequired(r, scratch);
        addRequired(u, scratch);
        offer();
      }
      backward(r, v);
      u = requiredOutside(v);
      if (u >= 0) {
        backwardCut(v, scratch);
        addRequired(r, scratch);
        addRequired(u, scratch);
        offer();
      }
      if (!bestEmpty) {
        break;
      }
    }
    return takeBest(out);
  }

  // a cycle of fixed arcs without every node
  private boolean shortCycle(EntryList out) {
    stamp++;
    for (int s = 0; s < n; s++) {
      if (mark[s] == stamp) {
        continue;
      }
      int c = s;
      int count = 0;
      while (c >= 0 && mark[c] != stamp) {
        mark[c] = stamp;
        queue[count++] = c;
        c = fixedSuccessor(c);
      }
      if (c < 0) {
        continue;
      }
      // c was reached before: a cycle when it is on this walk
      int at = -1;
      for (int k = 0; k < count && at < 0; k++) {
        if (queue[k] == c) {
          at = k;
        }
      }
      if (at >= 0 && count - at < n) {
        for (int k = at; k < count; k++) {
          addFixed(queue[k], out);
        }
        return true;
      }
    }
    return false;
  }

  private boolean failure(EntryList out) {
    int from = out.size();
    if (clashA >= 0) {
      addFixed(clashA, out);
      addFixed(clashB, out);
      out.sortUnique(from);
      return true;
    }
    if (circuit && shortCycle(out)) {
      out.sortUnique(from);
      return true;
    }
    startBest();
    int first = -1;
    for (int u = 0; u < n && first < 0; u++) {
      if (!selfLoop[u]) {
        first = u;
      }
    }
    if (first >= 0) {
      // two required nodes that do not reach each other
      forward(first, -1);
      int u = requiredOutside(first);
      if (u >= 0) {
        forwardCut(-1, -1, scratch);
        addRequired(first, scratch);
        addRequired(u, scratch);
        offer();
      }
      backward(first, -1);
      u = requiredOutside(first);
      if (u >= 0) {
        backwardCut(-1, scratch);
        addRequired(first, scratch);
        addRequired(u, scratch);
        offer();
      }
      // otherwise the required nodes share a cycle unless the only one is on none
      forward(first, -1);
      if (bestEmpty && !arcInto(first)) {
        forwardCut(-1, first, scratch);
        addRequired(first, scratch);
        offer();
      }
    }
    if (takeBest(out)) {
      out.sortUnique(from);
      return true;
    }
    return AlldiffExplanation.explainFailure(trail, list, new IntervalDomain(), out);
  }
}
