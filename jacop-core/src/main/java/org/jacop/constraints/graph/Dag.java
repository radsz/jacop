/*
 * Dag.java
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
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Dag states that the selected edges of a directed graph form a directed acyclic graph, and that
 * each selected edge has both its nodes selected. The graph has the nodes {@code base .. base +
 * ns.length - 1} and the edges {@code from[e] -> to[e]}; node {@code base + i} is selected when
 * {@code ns[i]} is 1 and edge e when {@code es[e]} is 1. This is MiniZinc's {@code dag}, whose
 * decomposition (longest-path distances) is replaced by a native propagator.
 *
 * <p>The graph variable view is that of Dooms, Deville and Dupont, "CP(Graph): Introducing a graph
 * computation domain in constraint programming" (CP 2005), where acyclicity of a graph variable is
 * one of the basic constraints. Propagation, recomputed at each call:
 *
 * <ul>
 *   <li>a selected edge selects its two nodes, a node left out removes its edges, and a self-loop
 *       is removed;
 *   <li>the constraint fails when the selected edges have a cycle;
 *   <li>an edge u to v is removed when the selected edges have a path from v to u, as it would
 *       close a cycle (the transitive-closure rule of a DAG graph variable).
 * </ul>
 *
 * <p>The last rule is domain consistent for acyclicity alone: any edge it keeps can be added to the
 * selected edges without a cycle. For lazy clause generation it explains itself: a removed edge by
 * the selected edges of a path closing the cycle, or by the left-out node; a selected node by a
 * selected edge at it; a failure by the selected edges of a cycle.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class Dag extends Constraint implements SatisfiedPresent, Copyable<Dag>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private final int[] from;
  private final int[] to;
  private final IntVar[] ns;
  private final IntVar[] es;
  private final int base;
  private final int n;
  private final int m;

  // the graph with nodes from 0
  private final int[] tail;
  private final int[] head;
  private final int[] outStart;
  private final int[] outEdge;
  private final int[] inStart;
  private final int[] inEdge;

  // scratch for the searches
  private final int[] mark;
  private int stamp;
  private final int[] stack;
  private final int[] via;
  private final int[] indegree;
  private final boolean[] onPath;

  // what made the last failure: an edge selected at a node left out, or a cycle
  private int failEdge = -1;
  private int failNode = -1;

  /**
   * It constructs a dag constraint.
   *
   * @param from the tail of each edge, a node number from base.
   * @param to the head of each edge, a node number from base.
   * @param ns the Boolean of each node; ns[i] is node base + i.
   * @param es the Boolean of each edge.
   * @param base the number of the first node.
   */
  public Dag(int[] from, int[] to, IntVar[] ns, IntVar[] es, int base) {
    checkInputForNullness("ns", ns);
    checkInputForNullness("es", es);
    checkInputForNullness("from", from);
    checkInputForNullness("to", to);
    checkGraph(from, to, ns, es, base);
    this.n = ns.length;
    this.m = es.length;
    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 1;
    this.from = Arrays.copyOf(from, m);
    this.to = Arrays.copyOf(to, m);
    this.ns = Arrays.copyOf(ns, n);
    this.es = Arrays.copyOf(es, m);
    this.base = base;

    tail = new int[m];
    head = new int[m];
    outStart = new int[n + 1];
    for (int e = 0; e < m; e++) {
      tail[e] = from[e] - base;
      head[e] = to[e] - base;
      outStart[tail[e] + 1]++;
    }
    for (int v = 0; v < n; v++) {
      outStart[v + 1] += outStart[v];
    }
    outEdge = new int[m];
    int[] fill = Arrays.copyOf(outStart, n);
    for (int e = 0; e < m; e++) {
      outEdge[fill[tail[e]]++] = e;
    }
    inStart = new int[n + 1];
    for (int e = 0; e < m; e++) {
      inStart[head[e] + 1]++;
    }
    for (int v = 0; v < n; v++) {
      inStart[v + 1] += inStart[v];
    }
    inEdge = new int[m];
    fill = Arrays.copyOf(inStart, n);
    for (int e = 0; e < m; e++) {
      inEdge[fill[head[e]]++] = e;
    }
    mark = new int[n];
    stack = new int[n];
    via = new int[n];
    indegree = new int[n];
    onPath = new boolean[n];
    setScope(this.ns, this.es);
  }

  /**
   * It constructs a dag constraint on nodes numbered from 0.
   *
   * @param from the tail of each edge.
   * @param to the head of each edge.
   * @param ns the Boolean of each node.
   * @param es the Boolean of each edge.
   */
  public Dag(int[] from, int[] to, IntVar[] ns, IntVar[] es) {
    this(from, to, ns, es, 0);
  }

  // the edges and the Booleans of a graph with nodes base .. base + ns.length - 1
  private static void checkGraph(int[] from, int[] to, IntVar[] ns, IntVar[] es, int base) {
    if (from.length != es.length || to.length != es.length) {
      throw new IllegalArgumentException(
          "Dag needs a tail and a head for each of its " + es.length + " edges");
    }
    int last = base + ns.length - 1;
    for (int e = 0; e < es.length; e++) {
      int lo = Math.min(from[e], to[e]);
      int hi = Math.max(from[e], to[e]);
      if (lo < base || hi > last) {
        throw new IllegalArgumentException(
            "Dag: edge " + e + " has a node outside " + base + ".." + last);
      }
    }
    IntVar[][] groups = {ns, es};
    for (IntVar[] group : groups) {
      for (IntVar v : group) {
        if (v.min() < 0 || v.max() > 1) {
          throw new IllegalArgumentException("Dag needs 0/1 variables, got " + v);
        }
      }
    }
  }

  private static boolean ground(IntVar[] vars) {
    return Arrays.stream(vars).allMatch(IntVar::singleton);
  }

  /**
   * The node Booleans.
   *
   * @return the node Booleans, not a copy
   */
  public IntVar[] nodes() {
    return ns;
  }

  /**
   * The edge Booleans.
   *
   * @return the edge Booleans, not a copy
   */
  public IntVar[] edges() {
    return es;
  }

  @Override
  public void consistency(Store store) {
    boolean changed;
    do {
      changed = linkNodes(store);
      if (hasSelectedCycle()) {
        failEdge = -1;
        failNode = -1;
        throw Store.failException;
      }
      changed |= removeClosingEdges(store);
    } while (changed);
  }

  // selected edges select their nodes, left-out nodes remove their edges, self-loops go
  private boolean linkNodes(Store store) {
    boolean changed = false;
    for (int e = 0; e < m; e++) {
      IntVar x = es[e];
      if (x.max() == 0) {
        continue;
      }
      int t = tail[e];
      int h = head[e];
      if (t == h || ns[t].max() == 0 || ns[h].max() == 0) {
        if (x.min() == 1) {
          failEdge = e;
          failNode = t == h ? -1 : ns[t].max() == 0 ? t : h;
          throw Store.failException;
        }
        x.domain.in(store.level, x, 0, 0);
        changed = true;
      } else if (x.min() == 1) {
        if (ns[t].min() == 0) {
          ns[t].domain.in(store.level, ns[t], 1, 1);
          changed = true;
        }
        if (ns[h].min() == 0) {
          ns[h].domain.in(store.level, ns[h], 1, 1);
          changed = true;
        }
      }
    }
    return changed;
  }

  // Kahn's algorithm over the selected edges
  private boolean hasSelectedCycle() {
    Arrays.fill(indegree, 0);
    for (int e = 0; e < m; e++) {
      if (es[e].min() == 1) {
        indegree[head[e]]++;
      }
    }
    int sp = 0;
    for (int v = 0; v < n; v++) {
      if (indegree[v] == 0) {
        stack[sp++] = v;
      }
    }
    int done = 0;
    while (sp > 0) {
      int v = stack[--sp];
      done++;
      for (int k = outStart[v]; k < outStart[v + 1]; k++) {
        int e = outEdge[k];
        if (es[e].min() == 1 && --indegree[head[e]] == 0) {
          stack[sp++] = head[e];
        }
      }
    }
    return done < n;
  }

  // an open edge u -> v goes when the selected edges lead from v to u
  private boolean removeClosingEdges(Store store) {
    boolean changed = false;
    boolean[] searched = new boolean[n];
    for (int e = 0; e < m; e++) {
      if (es[e].singleton()) {
        continue;
      }
      int v = head[e];
      if (!searched[v]) {
        searched[v] = true;
        reachSelected(v);
        for (int i = inStart[v]; i < inStart[v + 1]; i++) {
          int k = inEdge[i];
          if (!es[k].singleton() && mark[tail[k]] == stamp) {
            es[k].domain.in(store.level, es[k], 0, 0);
            changed = true;
          }
        }
      }
    }
    return changed;
  }

  // marks with the new stamp the nodes the selected edges reach from s
  private void reachSelected(int s) {
    stamp++;
    mark[s] = stamp;
    int sp = 0;
    stack[sp++] = s;
    while (sp > 0) {
      int v = stack[--sp];
      for (int k = outStart[v]; k < outStart[v + 1]; k++) {
        int e = outEdge[k];
        int w = head[e];
        if (es[e].min() == 1 && mark[w] != stamp) {
          mark[w] = stamp;
          stack[sp++] = w;
        }
      }
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {
    if (!ground(ns) || !ground(es)) {
      return false;
    }
    for (int e = 0; e < m; e++) {
      if (es[e].value() == 1
          && (tail[e] == head[e] || ns[tail[e]].value() == 0 || ns[head[e]].value() == 0)) {
        return false;
      }
    }
    return !hasSelectedCycle();
  }

  // --- explanations for lazy clause generation

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar x = trail.variable(entry);
    int kind = trail.kind(entry);
    int mark0 = out.size();
    if (kind == AtomicTrail.LE) {
      // an edge set to 0; a variable may stand for several edges, any of them explains it
      for (int e = 0; e < m; e++) {
        if (es[e] == x && edgeRemoved(trail, entry, e, out)) {
          return true;
        }
        out.truncate(mark0);
      }
      return false;
    }
    if (kind == AtomicTrail.GE) {
      // a node set to 1 by a selected edge at it
      for (int v = 0; v < n; v++) {
        if (ns[v] != x) {
          continue;
        }
        for (int e = 0; e < m; e++) {
          if ((tail[e] == v || head[e] == v) && es[e] != x && trail.minBefore(es[e], entry) == 1) {
            trail.addLowerBound(es[e], entry, out);
            return true;
          }
        }
      }
    }
    return false;
  }

  private boolean edgeRemoved(AtomicTrail trail, int entry, int e, EntryList out) {
    int t = tail[e];
    int h = head[e];
    if (t == h) {
      return true;
    }
    if (ns[t] != es[e] && trail.maxBefore(ns[t], entry) == 0) {
      trail.addUpperBound(ns[t], entry, out);
      return true;
    }
    if (ns[h] != es[e] && trail.maxBefore(ns[h], entry) == 0) {
      trail.addUpperBound(ns[h], entry, out);
      return true;
    }
    return selectedPath(trail, entry, h, t, es[e], out);
  }

  // adds the selected edges (before the position) of a path from s to t, avoiding the edges of x
  private boolean selectedPath(
      AtomicTrail trail, int position, int s, int t, IntVar x, EntryList out) {
    stamp++;
    mark[s] = stamp;
    via[s] = -1;
    int sp = 0;
    stack[sp++] = s;
    while (sp > 0) {
      int v = stack[--sp];
      if (v == t) {
        for (int w = t; via[w] >= 0; w = tail[via[w]]) {
          trail.addLowerBound(es[via[w]], position, out);
        }
        return true;
      }
      for (int k = outStart[v]; k < outStart[v + 1]; k++) {
        int e = outEdge[k];
        int w = head[e];
        if (mark[w] != stamp && es[e] != x && trail.minBefore(es[e], position) == 1) {
          mark[w] = stamp;
          via[w] = e;
          stack[sp++] = w;
        }
      }
    }
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int now = trail.size();
    int e = failEdge;
    int v = failNode;
    failEdge = -1;
    failNode = -1;
    if (e >= 0) {
      if (trail.minBefore(es[e], now) != 1) {
        return false;
      }
      trail.addLowerBound(es[e], now, out);
      if (v >= 0) {
        if (trail.maxBefore(ns[v], now) != 0) {
          return false;
        }
        trail.addUpperBound(ns[v], now, out);
      }
      return true;
    }
    return selectedCycle(trail, now, out);
  }

  // adds the edges of a cycle of edges selected before the position
  private boolean selectedCycle(AtomicTrail trail, int position, EntryList out) {
    // iterative depth-first search; mark: stamp = on the current path or finished in this round
    stamp++;
    Arrays.fill(onPath, false);
    int[] next = new int[n];
    for (int r = 0; r < n; r++) {
      if (mark[r] == stamp) {
        continue;
      }
      int sp = 0;
      stack[sp++] = r;
      mark[r] = stamp;
      onPath[r] = true;
      via[r] = -1;
      next[r] = outStart[r];
      while (sp > 0) {
        int v = stack[sp - 1];
        if (next[v] < outStart[v + 1]) {
          int e = outEdge[next[v]++];
          if (trail.minBefore(es[e], position) != 1) {
            continue;
          }
          int w = head[e];
          if (onPath[w]) {
            trail.addLowerBound(es[e], position, out);
            for (int u = v; u != w; u = tail[via[u]]) {
              trail.addLowerBound(es[via[u]], position, out);
            }
            return true;
          }
          if (mark[w] != stamp) {
            mark[w] = stamp;
            onPath[w] = true;
            via[w] = e;
            next[w] = outStart[w];
            stack[sp++] = w;
          }
        } else {
          onPath[v] = false;
          sp--;
        }
      }
    }
    return false;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : Dag(");
    result.append(Arrays.toString(from)).append(", ").append(Arrays.toString(to)).append(", ");
    appendArrayToString(result, ns);
    result.append(", ");
    appendArrayToString(result, es);
    result.append(", ").append(base).append(")");
    return result.toString();
  }

  @Override
  public Dag copy(VarMap map) {
    return new Dag(from, to, map.get(ns), map.get(es), base);
  }
}
