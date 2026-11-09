/*
 * TreeExplanation.java
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

package org.jacop.constraints.graph;

import java.util.Arrays;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations for lazy clause generation of the bounds of spanning tree constraints ({@link
 * SpanningTreeBound}, {@link ColouredSpanningTreeBound}). The minimum spanning tree T over the
 * domains just before an atom (forced edges first, then the free ones by increasing weight, as the
 * constraints build it) is rebuilt, and its weight is a lower bound for every spanning tree that
 * avoids a set R0 of excluded edges and contains a set R1 of forced ones, as long as T stays
 * optimal there by the cycle condition: every allowed edge outside T weighs at least each edge of
 * its tree path that is not in R1. R1 holds the forced tree edges that a cheaper edge outside the
 * tree could replace, and R0 the excluded edges cheaper than an edge of their path outside R1. The
 * reason of the bound is then the atoms of R0 and R1; the edge filtering adds the forced edges of
 * the path, the excluded edges that could replace a tree edge, and the upper bound of the cost
 * (Tarjan, Sensitivity analysis of minimum spanning trees, Inf. Process. Lett. 14, 1982).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class TreeExplanation {

  private final int n;
  private final IntVar[] es;
  private final int[] tail;
  private final int[] head;
  private final int m;
  private final IntVar cost;

  // domains just before the position of the last rebuild
  private final boolean[] forced;
  private final boolean[] allowed;
  private final boolean[] inTree;
  private final boolean[] needed;
  private final int[] parent;
  private final Integer[] order;
  private final int[] up;
  private final int[] upEdge;
  private final int[] depth;
  private final int[] adjStart;
  private final int[] adjEdge;
  private final int[] queue;

  /** The weight of the rebuilt tree. */
  long weight;

  TreeExplanation(int n, IntVar[] es, int[] tail, int[] head, IntVar cost) {
    this.n = n;
    this.cost = cost;
    this.es = es;
    this.tail = tail;
    this.head = head;
    this.m = es.length;
    forced = new boolean[m];
    allowed = new boolean[m];
    inTree = new boolean[m];
    needed = new boolean[m];
    parent = new int[n];
    order = new Integer[m];
    up = new int[n];
    upEdge = new int[n];
    depth = new int[n];
    adjStart = new int[n + 1];
    adjEdge = new int[2 * Math.max(n - 1, 0)];
    queue = new int[n];
  }

  /**
   * The edge of a variable.
   *
   * @param x the variable.
   * @return its edge, or -1.
   */
  int edgeOf(IntVar x) {
    for (int e = 0; e < m; e++) {
      if (es[e] == x) {
        return e;
      }
    }
    return -1;
  }

  /**
   * It explains a bound of the cost or of an edge variable with the tree for weights w, whose
   * weight minus offset, divided by scale and rounded up, bounds the cost from below.
   *
   * @param trail the trail.
   * @param entry the entry of the atom.
   * @param w the weight of each edge, scaled.
   * @param offset what the bound subtracts from a scaled tree weight.
   * @param scale the scale of the weights.
   * @param out where the entries are added.
   * @return false when the tree does not imply the atom; nothing is added then.
   */
  boolean explain(AtomicTrail trail, int entry, long[] w, long offset, long scale, EntryList out) {
    int kind = trail.kind(entry);
    IntVar x = trail.variable(entry);
    int edge = x == cost ? -1 : edgeOf(x);
    if (kind == AtomicTrail.NE
        || x == cost && kind != AtomicTrail.GE
        || x != cost && edge < 0
        || !rebuild(trail, entry, w)) {
      return false;
    }
    if (x == cost) {
      int value = trail.skippedBound(entry);
      if (Math.ceilDiv(weight - offset, scale) < value) {
        return false;
      }
      addBoundReason(trail, entry, out);
      trail.addSkippedHoles(entry, value, out);
      return true;
    }
    int mark = out.size();
    long limit = trail.maxBefore(cost, entry) * scale + offset;
    long with;
    if (kind == AtomicTrail.LE) {
      with = inTree[edge] ? weight : withEdge(trail, entry, edge, w, out);
    } else {
      with = inTree[edge] ? withoutEdge(trail, entry, edge, w, limit, out) : weight;
    }
    if (with != Long.MAX_VALUE && with <= limit) {
      out.truncate(mark);
      return false;
    }
    addBoundReason(trail, entry, out);
    if (with != Long.MAX_VALUE) {
      trail.addBoundReaching(cost, entry, false, Math.ceilDiv(with - offset, scale) - 1, out);
    }
    return true;
  }

  /**
   * It explains a failure by the bound of the tree for weights w over the cost's maximum.
   *
   * @param trail the trail.
   * @param w the weight of each edge, scaled.
   * @param offset what the bound subtracts from a scaled tree weight.
   * @param scale the scale of the weights.
   * @param out where the entries are added.
   * @return false when the bound does not exceed the maximum; nothing is added then.
   */
  boolean explainFailure(AtomicTrail trail, long[] w, long offset, long scale, EntryList out) {
    int now = trail.size();
    if (!rebuild(trail, now, w)) {
      return false;
    }
    long bound = Math.ceilDiv(weight - offset, scale);
    if (bound <= trail.maxBefore(cost, now)) {
      return false;
    }
    addBoundReason(trail, now, out);
    trail.addBoundReaching(cost, now, false, bound - 1, out);
    return true;
  }

  /**
   * It rebuilds the minimum spanning tree for weights w over the domains just before a trail
   * position and marks the forced and excluded edges its bound needs.
   *
   * @param trail the trail.
   * @param position the trail position.
   * @param w the weight of each edge.
   * @return false when the forced edges have a cycle or the allowed ones do not span the nodes.
   */
  boolean rebuild(AtomicTrail trail, int position, long[] w) {
    for (int v = 0; v < n; v++) {
      parent[v] = v;
    }
    int on = 0;
    int size = 0;
    for (int e = 0; e < m; e++) {
      forced[e] = trail.minBefore(es[e], position) == 1;
      allowed[e] = trail.maxBefore(es[e], position) == 1;
      inTree[e] = false;
      needed[e] = false;
      if (forced[e]) {
        if (!TreeReducedCosts.union(parent, tail[e], head[e])) {
          return false;
        }
        inTree[e] = true;
        size++;
      } else if (allowed[e]) {
        order[on++] = e;
      }
    }
    Arrays.sort(order, 0, on, (a, b) -> Long.compare(w[a], w[b]));
    long total = 0;
    for (int e = 0; e < m; e++) {
      if (inTree[e]) {
        total += w[e];
      }
    }
    for (int i = 0; i < on; i++) {
      int e = order[i];
      if (TreeReducedCosts.union(parent, tail[e], head[e])) {
        inTree[e] = true;
        total += w[e];
        size++;
      }
    }
    if (size != n - 1 || !root()) {
      return false;
    }
    weight = total;
    markNeeded(w);
    return true;
  }

  // R1: forced tree edges on the path of a cheaper edge outside the tree; R0: excluded edges
  // cheaper than an edge of their path outside R1
  private void markNeeded(long[] w) {
    for (int g = 0; g < m; g++) {
      if (!allowed[g] || inTree[g] || tail[g] == head[g]) {
        continue;
      }
      int u = tail[g];
      int v = head[g];
      while (u != v) {
        if (depth[u] < depth[v]) {
          int t = u;
          u = v;
          v = t;
        }
        int f = upEdge[u];
        if (forced[f] && w[g] < w[f]) {
          needed[f] = true;
        }
        u = up[u];
      }
    }
    for (int g = 0; g < m; g++) {
      if (allowed[g] || inTree[g] || tail[g] == head[g]) {
        continue;
      }
      needed[g] = w[g] < heaviestOnPath(g, w, false);
    }
  }

  // the heaviest edge on the tree path of g that is free or not needed (strict: free only), or
  // Long.MIN_VALUE when there is none
  private long heaviestOnPath(int g, long[] w, boolean freeOnly) {
    long heaviest = Long.MIN_VALUE;
    int u = tail[g];
    int v = head[g];
    while (u != v) {
      if (depth[u] < depth[v]) {
        int t = u;
        u = v;
        v = t;
      }
      int f = upEdge[u];
      boolean counts = freeOnly ? !forced[f] : !forced[f] || !needed[f];
      if (counts && w[f] > heaviest) {
        heaviest = w[f];
      }
      u = up[u];
    }
    return heaviest;
  }

  /**
   * It adds the atoms of the forced and excluded edges the bound of the rebuilt tree needs.
   *
   * @param trail the trail.
   * @param position the trail position.
   * @param out where the entries are added.
   */
  void addBoundReason(AtomicTrail trail, int position, EntryList out) {
    for (int e = 0; e < m; e++) {
      if (needed[e]) {
        addEdge(trail, position, e, out);
      }
    }
  }

  private void addEdge(AtomicTrail trail, int position, int e, EntryList out) {
    int entry = trail.boundEntry(es[e], position, forced[e]);
    if (entry >= 0) {
      out.add(entry);
    }
  }

  /**
   * The least weight of a spanning tree that contains edge e, which is outside the rebuilt tree,
   * with the forced edges of its path; it adds their atoms to the reason.
   *
   * @param trail the trail.
   * @param position the trail position.
   * @param e the edge.
   * @param w the weight of each edge.
   * @param out where the entries are added.
   * @return the weight, or Long.MAX_VALUE when every edge of the path is forced.
   */
  long withEdge(AtomicTrail trail, int position, int e, long[] w, EntryList out) {
    long heaviest = heaviestOnPath(e, w, true);
    int u = tail[e];
    int v = head[e];
    while (u != v) {
      if (depth[u] < depth[v]) {
        int t = u;
        u = v;
        v = t;
      }
      int f = upEdge[u];
      if (forced[f] && !needed[f]) {
        addEdge(trail, position, f, out);
      }
      u = up[u];
    }
    return heaviest == Long.MIN_VALUE ? Long.MAX_VALUE : weight - heaviest + w[e];
  }

  /**
   * The least weight of a spanning tree without edge e, a free edge of the rebuilt tree, where e is
   * replaced by an allowed edge outside the tree or by an excluded edge that is not cited; the
   * excluded edges that would give a tree of weight at most limit are added to the reason.
   *
   * @param trail the trail.
   * @param position the trail position.
   * @param e the edge.
   * @param w the weight of each edge.
   * @param limit the weight that every tree without e must exceed.
   * @param out where the entries are added.
   * @return the weight, or Long.MAX_VALUE when no edge outside the tree replaces e.
   */
  long withoutEdge(AtomicTrail trail, int position, int e, long[] w, long limit, EntryList out) {
    long result = Long.MAX_VALUE;
    for (int g = 0; g < m; g++) {
      if (inTree[g] || needed[g] || tail[g] == head[g] || !covers(g, e)) {
        continue;
      }
      long without = weight - w[e] + w[g];
      if (!allowed[g] && without <= limit) {
        addEdge(trail, position, g, out);
      } else if (without < result) {
        result = without;
      }
    }
    return result;
  }

  // whether tree edge e lies on the tree path of edge g
  private boolean covers(int g, int e) {
    int u = tail[g];
    int v = head[g];
    while (u != v) {
      if (depth[u] < depth[v]) {
        int t = u;
        u = v;
        v = t;
      }
      if (upEdge[u] == e) {
        return true;
      }
      u = up[u];
    }
    return false;
  }

  /**
   * It adds the atoms of forced edges that make a cycle, or of more than cap forced edges of one
   * colour, just before a trail position.
   *
   * @param trail the trail.
   * @param position the trail position.
   * @param colours the colour of each edge, -1 for none, or null.
   * @param caps the limit of each colour, or null.
   * @param out where the entries are added.
   * @return false when the forced edges have neither.
   */
  boolean addForcedConflict(
      AtomicTrail trail, int position, int[] colours, int[] caps, EntryList out) {
    for (int v = 0; v < n; v++) {
      parent[v] = v;
    }
    int[] count = caps == null ? null : new int[caps.length];
    for (int e = 0; e < m; e++) {
      if (trail.minBefore(es[e], position) != 1) {
        continue;
      }
      forced[e] = true;
      if (count != null && colours[e] >= 0 && ++count[colours[e]] > caps[colours[e]]) {
        for (int f = 0; f <= e; f++) {
          if (colours[f] == colours[e] && trail.minBefore(es[f], position) == 1) {
            addEdge(trail, position, f, out);
          }
        }
        return true;
      }
      if (!TreeReducedCosts.union(parent, tail[e], head[e])) {
        addCycle(trail, position, e, out);
        return true;
      }
    }
    return false;
  }

  // the forced edges before e that join its two nodes, with e: a path by breadth-first search
  private void addCycle(AtomicTrail trail, int position, int e, EntryList out) {
    Arrays.fill(up, -1);
    Arrays.fill(upEdge, -1);
    int qh = 0;
    int qt = 0;
    queue[qt++] = tail[e];
    up[tail[e]] = tail[e];
    while (qh < qt && up[head[e]] < 0) {
      int v = queue[qh++];
      for (int f = 0; f < e; f++) {
        if (trail.minBefore(es[f], position) != 1) {
          continue;
        }
        int w = tail[f] == v ? head[f] : head[f] == v ? tail[f] : -1;
        if (w >= 0 && up[w] < 0) {
          up[w] = v;
          upEdge[w] = f;
          queue[qt++] = w;
        }
      }
    }
    addEdge(trail, position, e, out);
    for (int v = head[e]; v != tail[e] && upEdge[v] >= 0; v = up[v]) {
      addEdge(trail, position, upEdge[v], out);
    }
  }

  // roots the rebuilt tree at node 0; false when it is not connected
  private boolean root() {
    Arrays.fill(adjStart, 0);
    for (int e = 0; e < m; e++) {
      if (inTree[e]) {
        adjStart[tail[e] + 1]++;
        adjStart[head[e] + 1]++;
      }
    }
    for (int v = 0; v < n; v++) {
      adjStart[v + 1] += adjStart[v];
    }
    int[] fill = Arrays.copyOf(adjStart, n);
    for (int e = 0; e < m; e++) {
      if (inTree[e]) {
        adjEdge[fill[tail[e]]++] = e;
        adjEdge[fill[head[e]]++] = e;
      }
    }
    Arrays.fill(up, -1);
    up[0] = 0;
    depth[0] = 0;
    int qh = 0;
    int qt = 0;
    queue[qt++] = 0;
    while (qh < qt) {
      int v = queue[qh++];
      for (int i = adjStart[v]; i < adjStart[v + 1]; i++) {
        int f = adjEdge[i];
        int w = tail[f] == v ? head[f] : tail[f];
        if (up[w] < 0) {
          up[w] = v;
          upEdge[w] = f;
          depth[w] = depth[v] + 1;
          queue[qt++] = w;
        }
      }
    }
    return qt == n;
  }
}
