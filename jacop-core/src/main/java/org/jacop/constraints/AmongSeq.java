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
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

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
 *   <li>updates, for the variables that changed, whether they must or can take a value from the
 *       set, and the counts of the windows that contain them; a window with more than max sure or
 *       fewer than min possible values fails at once;
 *   <li>finds one solution S of the network by label correcting from the solution of the previous
 *       call, starting from the edges of the changed variables, or fails on a negative cycle;
 *   <li>computes the strongly connected components of the tight edges, the edges u -&gt; v of
 *       weight w with S_v - S_u = w. These components are the classes of the cycles of weight 0,
 *       which do not depend on S, so only the components reached from the changed variables are
 *       visited; the fixed variables before the first free one, and after the last, are visited as
 *       one node each.
 * </ol>
 *
 * <p>The value of list[i] in S always has a support. The other value has one if and only if the
 * shortest path from i to i + 1 (or back) is longer than the tight path, that is, if and only if i
 * and i + 1 are in different components. The memberships and the window counts are trailed, so a
 * call costs the label-correcting steps plus the components it visits, and does not depend on q,
 * while the automaton of the Regular decomposition grows as 2^q.
 *
 * <p>The propagator is domain consistent when the list has no repeated variables. A repeated
 * variable is allowed: the pruning stays correct and an assignment is accepted only if it satisfies
 * the constraint.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class AmongSeq extends Constraint
    implements UsesQueueVariable, Stateful, SatisfiedPresent, Copyable<AmongSeq> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final IntVar[] list;
  final IntervalDomain set;
  final int q;
  final int min;
  final int max;

  private final int n;

  /** The number of windows, n - q + 1, or 0 when q is larger than n. */
  private final int windows;

  /** It is true when the set is one interval setMin..setMax. */
  private final boolean setIsInterval;

  private final int setMin;
  private final int setMax;
  private final boolean setIsEmpty;
  private final boolean hasDuplicates;

  /** The positions of each variable in the list. */
  private final Map<IntVar, int[]> positions;

  /** The same positions by store index minus firstIndex, when the indices are close together. */
  private final int[][] positionsByIndex;

  private final int firstIndex;

  /** Lower and upper bound of S_{i+1} - S_i, that is whether list[i] must or can be in the set. */
  private final int[] lb;

  private final int[] ub;

  /** The number of variables of window w that must (sure) or can (possible) be in the set. */
  private final int[] sure;

  private final int[] possible;

  // The trail of lb and ub: the level, the position and the old values of each change.
  private final int[] trailLevel;
  private final int[] trailPosition;
  private final int[] trailLb;
  private final int[] trailUb;
  private int trailSize;

  /** The store level at which lb, ub and the window counts were computed from scratch. */
  private int initialLevel = -1;

  // positions whose variables changed since the last call
  private final int[] changed;
  private final boolean[] isChanged;
  private int changedSize;

  /**
   * A solution of the network found by the last call. It is not restored on backtracking: a
   * solution of a deeper node satisfies the weaker constraints of its ancestors, so any values are
   * a valid start for label correcting.
   */
  private final int[] pot;

  private boolean potFound;

  // the labels changed by the current call, to restore the last solution on a failure
  private final int[] undoNode;
  private final int[] undoPot;
  private int undoSize;

  /**
   * Each call numbers its shortest path tree; a node whose stamp is older is not in the tree. Such
   * a node has no children, and its label is still an upper bound.
   */
  private int epoch;

  private final int[] treeStamp;
  private final int[] potStamp;

  private final int[] queue;
  private int queueHead;
  private int queueSize;
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
  private final int[] edgeEnd;
  private int edgeCount;
  private final int[] visit;
  private int visitStamp;

  // the positions whose weights changed since the last call, or all when allComponents is set
  private final int[] roots;
  private int rootCount;
  private boolean allComponents;

  /**
   * The tight edges of each node as a mask: bit 0 to u + 1, bit 1 to u - 1, bit 2 to u + q and bit
   * 3 to u - q. Only the nodes in dirtyNodes are out of date.
   */
  private final int[] tight;

  private final boolean[] dirty;
  private final int[] dirtyNodes;
  private int dirtySize;
  private final int[] edges;

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
    this.windows = q > n ? 0 : n - q + 1;

    this.setIsEmpty = set.isEmpty();
    this.setIsInterval = !setIsEmpty && set.getSize() == set.max() - set.min() + 1;
    this.setMin = setIsEmpty ? 0 : set.min();
    this.setMax = setIsEmpty ? 0 : set.max();

    Map<IntVar, int[]> map = new HashMap<>();
    for (int i = 0; i < n; i++) {
      int[] old = map.get(list[i]);
      int[] now = old == null ? new int[1] : Arrays.copyOf(old, old.length + 1);
      now[now.length - 1] = i;
      map.put(list[i], now);
    }
    this.positions = map;
    int lowest = Integer.MAX_VALUE;
    int highest = Integer.MIN_VALUE;
    for (IntVar v : list) {
      lowest = Math.min(lowest, v.index());
      highest = Math.max(highest, v.index());
    }
    this.firstIndex = lowest;
    if (n > 0 && lowest >= 0 && (long) highest - lowest < 8L * n + 64) {
      positionsByIndex = new int[highest - lowest + 1][];
      for (Map.Entry<IntVar, int[]> e : map.entrySet()) {
        positionsByIndex[e.getKey().index() - firstIndex] = e.getValue();
      }
    } else {
      positionsByIndex = null;
    }
    this.hasDuplicates = map.size() < n;

    lb = new int[n];
    ub = new int[n];
    sure = new int[windows];
    possible = new int[windows];
    // along a branch lb only goes up and ub only goes down, once each
    trailLevel = new int[2 * n];
    trailPosition = new int[2 * n];
    trailLb = new int[2 * n];
    trailUb = new int[2 * n];
    changed = new int[n];
    isChanged = new boolean[n];
    pot = new int[n + 1];
    undoNode = new int[n + 1];
    undoPot = new int[n + 1];
    treeStamp = new int[n + 2];
    potStamp = new int[n + 1];
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
    edgeEnd = new int[n + 1];
    visit = new int[n + 1];
    roots = new int[n];
    tight = new int[n + 1];
    dirty = new boolean[n + 1];
    dirtyNodes = new int[n + 1];
    // four edges for each node, and for each block of fixed variables the edges of q + 1 nodes
    edges = new int[4 * (n + 1) + 8 * (Math.min(q, n) + 1)];

    setScope(list);
  }

  @Override
  public void queueVariable(int level, Var v) {
    int[] at =
        positionsByIndex != null ? positionsByIndex[v.index() - firstIndex] : positions.get(v);
    for (int i : at) {
      if (!isChanged[i]) {
        isChanged[i] = true;
        changed[changedSize++] = i;
      }
    }
  }

  @Override
  public void removeLevel(int level) {
    while (trailSize > 0 && trailLevel[trailSize - 1] >= level) {
      trailSize--;
      setBounds(trailPosition[trailSize], trailLb[trailSize], trailUb[trailSize]);
    }
    if (level <= initialLevel) {
      initialLevel = -1;
    }
    clearChanged();
    rootCount = 0;
  }

  private void clearChanged() {
    for (int k = 0; k < changedSize; k++) {
      isChanged[changed[k]] = false;
    }
    changedSize = 0;
  }

  @Override
  public void consistency(Store store) {

    if (windows == 0 || min <= 0 && max >= q) {
      // every window holds whatever values the variables take
      removeConstraint();
      return;
    }
    rootCount = 0;
    if (initialLevel < 0) {
      initialize(store);
    } else {
      updateChanged(store);
    }

    boolean pruned;
    do {
      findSolution();
      clearChanged();
      pruned = prune(store);
      if (hasDuplicates && pruned) {
        updateChanged(store);
      }
    } while (hasDuplicates && pruned);
  }

  private void initialize(Store store) {
    trailSize = 0;
    Arrays.fill(sure, 0);
    Arrays.fill(possible, 0);
    Arrays.fill(lb, 0);
    Arrays.fill(ub, 0);
    initialLevel = store.level;
    potFound = false;
    allComponents = true;
    clearChanged();
    // the counts are partial until every position is read, so the windows are checked after
    for (int i = 0; i < n; i++) {
      int newLb = mustBeIn(list[i].dom()) ? 1 : 0;
      int newUb = newLb == 1 || canBeIn(list[i].dom()) ? 1 : 0;
      setBounds(i, newLb, newUb);
    }
    if (violatedWindow()) {
      throw Store.failException;
    }
  }

  private boolean violatedWindow() {
    for (int w = 0; w < windows; w++) {
      if (sure[w] > max || possible[w] < min) {
        return true;
      }
    }
    return false;
  }

  /** It reads the changed variables and fails when a window that contains one is violated. */
  private void updateChanged(Store store) {
    boolean fail = false;
    for (int k = 0; k < changedSize; k++) {
      int i = changed[k];
      IntDomain d = list[i].dom();
      int newLb = lb[i] == 1 || mustBeIn(d) ? 1 : 0;
      int newUb = ub[i] == 1 && (newLb == 1 || canBeIn(d)) ? 1 : 0;
      if (newLb != lb[i] || newUb != ub[i]) {
        fail |= trailAndSet(store.level, i, newLb, newUb);
        roots[rootCount++] = i;
      }
    }
    if (fail) {
      clearChanged();
      throw Store.failException;
    }
  }

  private boolean trailAndSet(int level, int i, int newLb, int newUb) {
    trailLevel[trailSize] = level;
    trailPosition[trailSize] = i;
    trailLb[trailSize] = lb[i];
    trailUb[trailSize] = ub[i];
    trailSize++;
    return setBounds(i, newLb, newUb);
  }

  /**
   * It sets lb and ub of position i and the counts of its windows.
   *
   * @return true when a window of position i has more than max sure or fewer than min possible.
   */
  private boolean setBounds(int i, int newLb, int newUb) {
    int dLb = newLb - lb[i];
    int dUb = newUb - ub[i];
    lb[i] = newLb;
    ub[i] = newUb;
    markDirty(i);
    markDirty(i + 1);
    boolean violated = false;
    int first = Math.max(0, i - q + 1);
    int last = Math.min(i, windows - 1);
    if (dLb != 0) {
      for (int w = first; w <= last; w++) {
        violated |= (sure[w] += dLb) > max;
      }
    }
    if (dUb != 0) {
      for (int w = first; w <= last; w++) {
        violated |= (possible[w] += dUb) < min;
      }
    }
    return violated;
  }

  private boolean mustBeIn(IntDomain d) {
    if (setIsEmpty) {
      return false;
    }
    if (setIsInterval) {
      return d.min() >= setMin && d.max() <= setMax;
    }
    return set.contains(d);
  }

  private boolean canBeIn(IntDomain d) {
    if (setIsEmpty) {
      return false;
    }
    if (setIsInterval) {
      int dmin = d.min();
      int dmax = d.max();
      // a bound inside the set intersects it, and a domain beside the set does not
      return dmax >= setMin
          && dmin <= setMax
          && (dmin >= setMin || dmax <= setMax || d.isIntersecting(setMin, setMax));
    }
    return d.isIntersecting(set);
  }

  // The edges of the network: u -> v with weight w stands for S_v - S_u <= w. Every node u has
  // at most four outgoing edges: to u + 1 with weight ub[u], to u - 1 with weight -lb[u - 1],
  // to u + q with weight max and to u - q with weight -min.

  /**
   * Label correcting (FIFO Bellman-Ford) from the previous solution, with Tarjan's subtree
   * disassembly: the shortest path tree is kept as a preorder thread, and when the label of v goes
   * down, the subtree of v is detached. A negative cycle is found as soon as u, whose edge lowers
   * v, is in the subtree of v, so an infeasible network fails without running all the rounds.
   */
  private void findSolution() {

    int nodes = n + 1;
    queueHead = 0;
    queueSize = 0;
    if (!potFound) {
      for (int u = 0; u < nodes; u++) {
        enqueue(u);
      }
    } else {
      // The previous solution satisfies the window edges, whose weights never change, and the
      // edges between neighbours with the weights it was found for. Weights only decrease along
      // a branch, so only the edges of the changed positions can be violated.
      for (int k = 0; k < changedSize; k++) {
        int i = changed[k];
        if (pot[i + 1] - pot[i] > ub[i] && !inQueue[i]) {
          enqueue(i);
        }
        if (pot[i] - pot[i + 1] > -lb[i] && !inQueue[i + 1]) {
          enqueue(i + 1);
        }
      }
    }
    if (queueSize == 0) {
      return;
    }

    if (++epoch == Integer.MAX_VALUE) {
      Arrays.fill(treeStamp, 0);
      Arrays.fill(potStamp, 0);
      epoch = 1;
    }
    undoSize = 0;
    int root = nodes;
    treeStamp[root] = epoch;
    depth[root] = 0;
    threadNext[root] = root;
    threadPrev[root] = root;

    try {
      while (queueSize > 0) {
        int u = queue[queueHead];
        queueHead = queueHead + 1 == nodes ? 0 : queueHead + 1;
        queueSize--;
        inQueue[u] = false;
        if (!scan[u]) {
          continue;
        }
        scan[u] = false;
        if (treeStamp[u] != epoch) {
          // a queued node that was not relabelled yet is a child of the root
          treeStamp[u] = epoch;
          insertAfter(root, u);
        }
        int pu = pot[u];
        if (u < n) {
          relax(u, u + 1, pu + ub[u]);
        }
        if (u > 0) {
          relax(u, u - 1, pu - lb[u - 1]);
        }
        if (u + q < nodes) {
          relax(u, u + q, pu + max);
        }
        if (u >= q) {
          relax(u, u - q, pu - min);
        }
      }
    } catch (RuntimeException e) {
      // a negative cycle: keep the last solution and leave the queue empty
      for (int k = undoSize - 1; k >= 0; k--) {
        pot[undoNode[k]] = undoPot[k];
      }
      while (queueSize > 0) {
        int u = queue[queueHead];
        queueHead = queueHead + 1 == nodes ? 0 : queueHead + 1;
        queueSize--;
        inQueue[u] = false;
        scan[u] = false;
      }
      throw e;
    }

    potFound = true;
    if (pot[0] < -(1 << 29)) {
      int offset = pot[0];
      for (int u = 0; u < nodes; u++) {
        pot[u] -= offset;
      }
    }
  }

  private void enqueue(int u) {
    scan[u] = true;
    inQueue[u] = true;
    int nodes = n + 1;
    int tail = queueHead + queueSize;
    queue[tail >= nodes ? tail - nodes : tail] = u;
    queueSize++;
  }

  private void relax(int u, int v, int label) {
    if (label < pot[v]) {
      if (potStamp[v] != epoch) {
        potStamp[v] = epoch;
        undoNode[undoSize] = v;
        undoPot[undoSize] = pot[v];
        undoSize++;
        markNeighboursDirty(v);
      }
      pot[v] = label;
      relink(u, v);
      if (!inQueue[v]) {
        enqueue(v);
      } else {
        scan[v] = true;
      }
    }
  }

  private void markDirty(int u) {
    if (!dirty[u]) {
      dirty[u] = true;
      dirtyNodes[dirtySize++] = u;
    }
  }

  /** The edges into v and out of v change their slack when the label of v changes. */
  private void markNeighboursDirty(int v) {
    markDirty(v);
    if (v > 0) {
      markDirty(v - 1);
    }
    if (v < n) {
      markDirty(v + 1);
    }
    if (v >= q) {
      markDirty(v - q);
    }
    if (v + q <= n) {
      markDirty(v + q);
    }
  }

  /** It recomputes the tight edges of the nodes whose edges or labels changed. */
  private void updateTight() {
    for (int k = 0; k < dirtySize; k++) {
      int u = dirtyNodes[k];
      dirty[u] = false;
      int pu = pot[u];
      int mask = 0;
      if (u < n && pot[u + 1] - pu == ub[u]) {
        mask = 1;
      }
      if (u > 0 && pu - pot[u - 1] == lb[u - 1]) {
        mask |= 2;
      }
      if (u + q <= n && pot[u + q] - pu == max) {
        mask |= 4;
      }
      if (u >= q && pu - pot[u - q] == min) {
        mask |= 8;
      }
      tight[u] = mask;
    }
    dirtySize = 0;
  }

  private void insertAfter(int u, int v) {
    int after = threadNext[u];
    threadNext[u] = v;
    threadPrev[v] = u;
    threadNext[v] = after;
    threadPrev[after] = v;
    parent[v] = u;
    depth[v] = depth[u] + 1;
  }

  /** It makes v a child of u in the shortest path tree, detaching the old subtree of v. */
  private void relink(int u, int v) {
    if (treeStamp[v] == epoch && parent[v] >= 0) {
      int dv = depth[v];
      int x = threadNext[v];
      while (depth[x] > dv) {
        if (x == u) {
          // u reaches v through the tree and the edge u -> v closes a negative cycle
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
    treeStamp[v] = epoch;
    insertAfter(u, v);
  }

  /**
   * Tarjan's algorithm on the tight edges, without recursion, from the given roots or from every
   * node when roots is null. The nodes up to first are in one component, linked both ways by the
   * fixed variables before first, and so are the nodes from last on; each of these blocks is
   * visited as one node, first or last. A node is visited when visit[node] equals visitStamp, and
   * the components of the visited nodes are complete.
   */
  private void components(int first, int last, int[] roots, int rootCount) {

    if (++visitStamp == Integer.MAX_VALUE) {
      Arrays.fill(visit, 0);
      visitStamp = 1;
    }
    edgeCount = 0;
    int counter = 0;
    int stackSize = 0;
    int componentCount = 0;

    int rootsToTry = roots == null ? last - first + 1 : rootCount;
    for (int r = 0; r < rootsToTry; r++) {
      int root = roots == null ? first + r : rep(roots[r], first, last);
      if (visit[root] == visitStamp) {
        continue;
      }
      callStack[0] = root;
      visitNode(root, first, last);
      index[root] = low[root] = counter++;
      sccStack[stackSize++] = root;
      onStack[root] = true;
      int top = 0;

      while (top >= 0) {
        int u = callStack[top];
        if (nextEdge[u] < edgeEnd[u]) {
          int v = edges[nextEdge[u]++];
          if (visit[v] != visitStamp) {
            visitNode(v, first, last);
            index[v] = low[v] = counter++;
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

  private static int rep(int v, int first, int last) {
    return v < first ? first : v > last ? last : v;
  }

  /** It marks node u visited and lists its tight edges. */
  private void visitNode(int u, int first, int last) {
    visit[u] = visitStamp;
    int count = edgeCount;
    nextEdge[u] = count;
    if (u == first) {
      for (int w = Math.max(0, first - q); w <= first; w++) {
        count = addTightEdges(w, first, last, first, count);
      }
    } else if (u == last) {
      for (int w = last, end = Math.min(n, last + q); w <= end; w++) {
        count = addTightEdges(w, first, last, last, count);
      }
    } else {
      count = addTightEdges(u, first, last, u, count);
    }
    edgeEnd[u] = count;
    edgeCount = count;
  }

  /**
   * It adds the tight edges of node w, with their targets moved into first..last, for node self.
   */
  private int addTightEdges(int w, int first, int last, int self, int count) {
    int mask = tight[w];
    if ((mask & 1) != 0) {
      count = addEdge(w + 1, first, last, self, count);
    }
    if ((mask & 2) != 0) {
      count = addEdge(w - 1, first, last, self, count);
    }
    if ((mask & 4) != 0) {
      count = addEdge(w + q, first, last, self, count);
    }
    if ((mask & 8) != 0) {
      count = addEdge(w - q, first, last, self, count);
    }
    return count;
  }

  private int addEdge(int v, int first, int last, int self, int count) {
    int target = rep(v, first, last);
    if (target != self) {
      edges[count++] = target;
    }
    return count;
  }

  private boolean prune(Store store) {

    int firstFree = 0;
    while (firstFree < n && lb[firstFree] == ub[firstFree]) {
      firstFree++;
    }
    if (firstFree == n) {
      return false;
    }
    int lastFree = n - 1;
    while (lb[lastFree] == ub[lastFree]) {
      lastFree--;
    }
    updateTight();
    // The components are the classes of the cycles of weight 0, which depend on the weights only.
    // The last call left no free variable with both nodes in one component, so a new such pair is
    // in the component of a position whose weights changed since.
    components(firstFree, lastFree + 1, allComponents ? null : roots, rootCount);
    allComponents = false;
    rootCount = 0;

    boolean changed = false;
    for (int i = firstFree; i <= lastFree; i++) {
      if (lb[i] == ub[i]
          || visit[i] != visitStamp
          || visit[i + 1] != visitStamp
          || component[i] != component[i + 1]) {
        continue;
      }
      IntVar x = list[i];
      int value = pot[i + 1] - pot[i];
      if (value == 1) {
        x.domain.in(store.level, x, set);
      } else {
        x.domain.in(store.level, x, x.dom().subtract(set));
      }
      // the value agrees with the solution, so no window is violated
      trailAndSet(store.level, i, value, value);
      changed = true;
      if (hasDuplicates) {
        // the other positions of x are read again by the next round
        queueVariable(store.level, x);
      }
    }
    return changed;
  }

  @Override
  public boolean satisfied() {
    // it reads the domains itself, since lb and ub may be behind the latest changes
    int[] sureIn = new int[n];
    int[] canIn = new int[n];
    for (int i = 0; i < n; i++) {
      sureIn[i] = mustBeIn(list[i].dom()) ? 1 : 0;
      canIn[i] = sureIn[i] == 1 || canBeIn(list[i].dom()) ? 1 : 0;
    }
    int s = 0;
    int p = 0;
    for (int i = 0; i < n; i++) {
      s += sureIn[i];
      p += canIn[i];
      if (i >= q) {
        s -= sureIn[i - q];
        p -= canIn[i - q];
      }
      if (i >= q - 1 && (s < min || p > max)) {
        return false;
      }
    }
    return true;
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

  @Override
  public AmongSeq copy(VarMap map) {
    return new AmongSeq(map.get(list), set, q, min, max);
  }
}
