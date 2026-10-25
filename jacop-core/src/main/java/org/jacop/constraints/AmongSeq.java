/*
 * AmongSeq.java
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
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * AmongSeq is a domain consistent propagator of the Sequence (sliding among) constraint: every
 * subsequence of q consecutive variables from the list takes between min and max values from the
 * set.
 *
 * <p>It uses the cumulative-sums encoding of Brand et al. (CP 2007). With S_0 = 0 and S_{i+1} - S_i
 * = 1 when list[i] takes a value from the set and 0 otherwise, the constraint holds if and only if
 * S_{i+q} - S_i is in min..max for every window. These are difference constraints, so the
 * constraint is a simple temporal network over S_0..S_n. Each call
 *
 * <ol>
 *   <li>finds one solution S of the network by label correcting from the solution of the previous
 *       call, or fails on a negative cycle;
 *   <li>computes the strongly connected components of the tight edges, the edges u -&gt; v of
 *       weight w with S_v - S_u = w.
 * </ol>
 *
 * <p>The value of list[i] in S always has a support. The other value has one if and only if the
 * shortest path from i to i + 1 (or back) is longer than the tight path, that is, if and only if i
 * and i + 1 are in different components. The cost of a call is linear in the list length plus the
 * label-correcting steps, and does not depend on q, while the automaton of the Regular
 * decomposition grows as 2^q.
 *
 * <p>The propagator is domain consistent when the list has no repeated variables. A repeated
 * variable is allowed: the pruning stays correct and an assignment is accepted only if it satisfies
 * the constraint.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class AmongSeq extends Constraint implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final IntVar[] list;
  final IntervalDomain set;
  final int q;
  final int min;
  final int max;

  private final int n;

  /** It is true when the set is one interval setMin..setMax. */
  private final boolean setIsInterval;

  private final int setMin;
  private final int setMax;
  private final boolean setIsEmpty;
  private final boolean hasDuplicates;

  /** Lower and upper bound of S_{i+1} - S_i, that is whether list[i] must or can be in the set. */
  private final int[] lb;

  private final int[] ub;

  /**
   * A solution of the network found by the last call. It is not restored on backtracking: a
   * solution of a deeper node satisfies the weaker constraints of its ancestors, so any values are
   * a valid start for label correcting.
   */
  private final int[] pot;

  private final int[] savedPot;
  private boolean potFound;
  private final int[] queue;
  private final boolean[] inQueue;
  private final boolean[] scan;
  private final int[] parent;
  private final int[] depth;
  private final int[] threadNext;
  private final int[] threadPrev;

  private final int[] index;
  private final int[] low;
  private final int[] component;
  private final int[] sccStack;
  private final boolean[] onStack;
  private final int[] callStack;
  private final int[] nextEdge;

  /**
   * It creates a domain consistent Sequence constraint.
   *
   * @param list variables which assignment is constrained.
   * @param set set of values which occurrence is counted within each subsequence.
   * @param q the length of the subsequence.
   * @param min the minimal number of values from set within a subsequence.
   * @param max the maximal number of values from set within a subsequence.
   */
  public AmongSeq(IntVar[] list, IntervalDomain set, int q, int min, int max) {

    checkInputForNullness("list", list);
    checkInputForNullness("set", new Object[] {set});
    if (q < 1) {
      throw new IllegalArgumentException(
          "Constraint AmongSeq needs a subsequence length q >= 1, not " + q + ".");
    }

    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 1;

    this.list = Arrays.copyOf(list, list.length);
    this.set = set.copy();
    this.q = q;
    this.min = min;
    this.max = max;
    this.n = list.length;

    this.setIsEmpty = set.isEmpty();
    this.setIsInterval = !setIsEmpty && set.getSize() == set.max() - set.min() + 1;
    this.setMin = setIsEmpty ? 0 : set.min();
    this.setMax = setIsEmpty ? 0 : set.max();

    Set<IntVar> distinct = new HashSet<>(Arrays.asList(list));
    this.hasDuplicates = distinct.size() < n;

    lb = new int[n];
    ub = new int[n];
    pot = new int[n + 1];
    savedPot = new int[n + 1];
    queue = new int[n + 1];
    inQueue = new boolean[n + 1];
    scan = new boolean[n + 1];
    parent = new int[n + 1];
    depth = new int[n + 2];
    threadNext = new int[n + 2];
    threadPrev = new int[n + 2];
    index = new int[n + 1];
    low = new int[n + 1];
    component = new int[n + 1];
    sccStack = new int[n + 1];
    onStack = new boolean[n + 1];
    callStack = new int[n + 1];
    nextEdge = new int[n + 1];

    setScope(list);
  }

  @Override
  public void consistency(Store store) {

    boolean changed;
    do {
      readBounds();
      findSolution();
      changed = prune(store);
    } while (hasDuplicates && changed);

    if (entailed()) {
      removeConstraint();
    }
  }

  private void readBounds() {
    for (int i = 0; i < n; i++) {
      IntDomain d = list[i].dom();
      if (setIsEmpty) {
        lb[i] = 0;
        ub[i] = 0;
      } else if (setIsInterval) {
        int dmin = d.min();
        int dmax = d.max();
        lb[i] = dmin >= setMin && dmax <= setMax ? 1 : 0;
        ub[i] = lb[i] == 1 || d.isIntersecting(setMin, setMax) ? 1 : 0;
      } else {
        lb[i] = set.contains(d) ? 1 : 0;
        ub[i] = lb[i] == 1 || d.isIntersecting(set) ? 1 : 0;
      }
    }
  }

  // The edges of the network: u -> v with weight w stands for S_v - S_u <= w. Every node u has
  // at most four outgoing edges, numbered 0..3: to u + 1, to u - 1, to u + q and to u - q.

  private int target(int u, int e) {
    switch (e) {
      case 0:
        return u < n ? u + 1 : -1;
      case 1:
        return u > 0 ? u - 1 : -1;
      case 2:
        return u + q <= n ? u + q : -1;
      default:
        return u - q >= 0 ? u - q : -1;
    }
  }

  private int weight(int u, int e) {
    switch (e) {
      case 0:
        return ub[u];
      case 1:
        return -lb[u - 1];
      case 2:
        return max;
      default:
        return -min;
    }
  }

  /**
   * Label correcting (FIFO Bellman-Ford) from the previous solution, with Tarjan's subtree
   * disassembly: the shortest path tree is kept as a preorder thread, and when the label of v goes
   * down, the subtree of v is detached. A negative cycle is found as soon as u, whose edge lowers
   * v, is in the subtree of v, so an infeasible network fails without running all the rounds.
   */
  private void findSolution() {

    int nodes = n + 1;
    int root = nodes;
    System.arraycopy(pot, 0, savedPot, 0, nodes);

    // every node starts as a child of a virtual root, with an edge of weight pot[u]
    depth[root] = 0;
    threadNext[root] = 0;
    threadPrev[root] = n;
    for (int u = 0; u < nodes; u++) {
      parent[u] = root;
      depth[u] = 1;
      threadNext[u] = u < n ? u + 1 : root;
      threadPrev[u] = u > 0 ? u - 1 : root;
    }

    // The previous solution satisfies the window edges, whose weights never change, and the
    // edges between neighbours with the weights it was found for. Weights only decrease along a
    // branch, so only the sources of now violated neighbour edges need to be queued.
    int head = 0;
    int size = 0;
    for (int u = 0; u < nodes; u++) {
      boolean violated =
          !potFound
              || u < n && pot[u + 1] - pot[u] > ub[u]
              || u > 0 && pot[u - 1] - pot[u] > -lb[u - 1];
      scan[u] = violated;
      inQueue[u] = violated;
      if (violated) {
        queue[size++] = u;
      }
    }

    while (size > 0) {
      int u = queue[head];
      head = head + 1 == nodes ? 0 : head + 1;
      size--;
      inQueue[u] = false;
      if (!scan[u]) {
        continue;
      }
      scan[u] = false;
      int pu = pot[u];
      for (int e = 0; e < 4; e++) {
        int v = target(u, e);
        if (v >= 0 && pu + weight(u, e) < pot[v]) {
          pot[v] = pu + weight(u, e);
          relink(u, v);
          scan[v] = true;
          if (!inQueue[v]) {
            inQueue[v] = true;
            int tail = head + size;
            queue[tail >= nodes ? tail - nodes : tail] = v;
            size++;
          }
        }
      }
    }

    potFound = true;
    int offset = pot[0];
    if (offset != 0) {
      for (int u = 0; u < nodes; u++) {
        pot[u] -= offset;
      }
    }
  }

  /** It makes v a child of u in the shortest path tree, detaching the old subtree of v. */
  private void relink(int u, int v) {
    if (parent[v] >= 0) {
      int dv = depth[v];
      int x = threadNext[v];
      while (depth[x] > dv) {
        if (x == u) {
          // u reaches v through the tree and the edge u -> v closes a negative cycle
          System.arraycopy(savedPot, 0, pot, 0, n + 1);
          throw Store.failException;
        }
        // detached nodes have no children: they get them only once relabelled and scanned again
        scan[x] = false;
        parent[x] = -1;
        x = threadNext[x];
      }
      int before = threadPrev[v];
      threadNext[before] = x;
      threadPrev[x] = before;
    }
    int after = threadNext[u];
    threadNext[u] = v;
    threadPrev[v] = u;
    threadNext[v] = after;
    threadPrev[after] = v;
    parent[v] = u;
    depth[v] = depth[u] + 1;
  }

  private boolean tight(int u, int e) {
    int v = target(u, e);
    return v >= 0 && pot[v] - pot[u] == weight(u, e);
  }

  /** Tarjan's algorithm on the tight edges, without recursion. */
  private void components() {

    int nodes = n + 1;
    Arrays.fill(index, -1);
    int counter = 0;
    int stackSize = 0;
    int componentCount = 0;

    for (int root = 0; root < nodes; root++) {
      if (index[root] >= 0) {
        continue;
      }
      callStack[0] = root;
      nextEdge[root] = 0;
      index[root] = low[root] = counter++;
      sccStack[stackSize++] = root;
      onStack[root] = true;
      int top = 0;

      while (top >= 0) {
        int u = callStack[top];
        if (nextEdge[u] < 4) {
          int e = nextEdge[u]++;
          if (!tight(u, e)) {
            continue;
          }
          int v = target(u, e);
          if (index[v] < 0) {
            index[v] = low[v] = counter++;
            nextEdge[v] = 0;
            sccStack[stackSize++] = v;
            onStack[v] = true;
            callStack[++top] = v;
          } else if (onStack[v] && index[v] < low[u]) {
            low[u] = index[v];
          }
        } else {
          if (low[u] == index[u]) {
            int w;
            do {
              w = sccStack[--stackSize];
              onStack[w] = false;
              component[w] = componentCount;
            } while (w != u);
            componentCount++;
          }
          top--;
          if (top >= 0) {
            int caller = callStack[top];
            if (low[u] < low[caller]) {
              low[caller] = low[u];
            }
          }
        }
      }
    }
  }

  private boolean prune(Store store) {

    components();

    boolean changed = false;
    for (int i = 0; i < n; i++) {
      if (lb[i] == ub[i] || component[i] != component[i + 1]) {
        continue;
      }
      IntVar x = list[i];
      int size = x.getSize();
      if (pot[i + 1] - pot[i] == 1) {
        x.domain.in(store.level, x, set);
      } else {
        x.domain.in(store.level, x, x.dom().subtract(set));
      }
      changed |= x.getSize() != size;
    }
    return changed;
  }

  /** It checks whether every window holds whatever values the variables take. */
  private boolean entailed() {
    if (q > n) {
      return true;
    }
    int sure = 0;
    int possible = 0;
    for (int i = 0; i < n; i++) {
      sure += lb[i];
      possible += ub[i];
      if (i >= q) {
        sure -= lb[i - q];
        possible -= ub[i - q];
      }
      if (i >= q - 1 && (sure < min || possible > max)) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean satisfied() {
    readBounds();
    return entailed();
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : AmongSeq([");
    for (int i = 0; i < n; i++) {
      result.append(list[i]);
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(set).append(", ").append(q);
    result.append(", ").append(min).append(", ").append(max).append(")");
    return result.toString();
  }
}
