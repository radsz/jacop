/*
 * ColouredSpanningTreeBound.java
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
import java.util.Comparator;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.IntStream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.SolutionHint;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Spanning tree with colour limits: the selected edges form a spanning tree of all nodes, at most
 * {@code caps[c]} of them have colour {@code c}, and {@code cost >= sum(w[e] * es[e])}. The trees
 * are the common bases of two matroids, the graphic matroid of the graph and the partition matroid
 * of the colour classes, so both the feasibility of the limits and the minimum cost are matroid
 * intersection problems, solvable in polynomial time (Edmonds, Submodular functions, matroids, and
 * certain polyhedra, 1970; Gabow and Tarjan, Efficient algorithms for a family of matroid
 * intersection problems, J. Algorithms 5, 1984). It is a redundant constraint, posted next to
 * {@link WeightedSpanningTree} and the colour sums, which on their own see the limits only one at a
 * time.
 *
 * <p>Feasibility: the edges already selected are contracted and the colour limits reduced by them;
 * a maximum common independent set of the remaining edges is grown by shortest augmenting paths in
 * the exchange graph (Edmonds 1970; Cunningham, Improved bounds for matroid partition and
 * intersection algorithms, SIAM J. Computing 15, 1986) and the constraint fails when it cannot
 * connect the components. The set is kept between calls and repaired, so a call usually needs few
 * augmentations.
 *
 * <p>Cost: the colour limits are relaxed with Lagrange multipliers {@code lambda[c] >= 0}, so that
 * every spanning tree T gives {@code cost >= sum_{e in T} (w[e] + lambda[col e]) - sum_c lambda[c]
 * caps[c]}, and the minimum over T is a minimum spanning tree for the shifted weights (Held and
 * Karp, The traveling-salesman problem and minimum spanning trees, Operations Research 18, 1970).
 * The multipliers are improved by subgradient steps and kept between calls. Because the
 * intersection of the spanning tree polytope with the colour limits is integral (Edmonds 1970), the
 * best multipliers give the exact minimum cost. The bound is computed in exact integer arithmetic
 * with the multipliers rounded down to multiples of 1/{@value #SCALE}, so it is sound whatever the
 * multipliers. With the shifted weights the edges are filtered as in {@link SpanningTreeBound}
 * (Régin, Rousseau, Rueher and van Hoeve, The weighted spanning tree constraint revisited, CPAIOR
 * 2010), which is valid reduced-cost filtering of a Lagrangian relaxation (Sellmann, Theoretical
 * foundations of CP-based Lagrangian relaxation, CP 2004).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ColouredSpanningTreeBound extends Constraint
    implements SatisfiedPresent, SolutionHint, Explainable, Copyable<ColouredSpanningTreeBound> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The multipliers are rounded down to multiples of 1/SCALE when the bound is computed. */
  static final long SCALE = 1024;

  /** The multiplier vectors kept for explanations, newest first. */
  static final int HISTORY = 16;

  /** Subgradient steps at the first call. */
  static final int FIRST_STEPS = 300;

  /** Subgradient steps at later calls. */
  static final int STEPS = 12;

  final int n;
  final int[] from;
  final int[] to;
  final int[] weights;
  final int[] colours;
  final int[] caps;
  final IntVar[] es;
  final IntVar cost;
  final int base;

  private final int m;
  private final int colourNo;
  private final int[] tail;
  private final int[] head;
  // the edges of each colour by increasing weight; list colourNo holds the edges without a limit
  private final int[][] byColour;

  // union-find over the nodes
  private final int[] parent;
  // components of the selected edges, numbered 0..k-1
  private final int[] component;

  // feasibility: the common independent set kept between calls
  private final boolean[] inSet;
  private final int[] colourCount;
  private final int[] residual;
  private final int[] candidates;
  private final int[] candA;
  private final int[] candB;
  private final int[] pred;
  private final int[] bfs;
  private final int[] forestAdjStart;
  private final int[] forestAdj;
  private final int[] tin;
  private final int[] tout;
  private final int[] tree;
  private final int[] forestParentEdge;
  private final int[] stack;
  private final int[] lowerEnd;

  // Lagrangian relaxation
  private final double[] lambda;
  private final double[] bestLambda;
  private final int[] gradient;
  private final int[] heap;
  private final boolean[] inTree;
  private final long[] shifted;

  // the scaled multipliers of the last bounds, a ring, for explanations
  private final long[][] history = new long[HISTORY][];
  private int historySize;
  private int historyNext;
  // the weight of the selected edges at the last contraction
  private long contractedWeight;
  private TreeExplanation explanation;
  private long[] explainWeights;
  private boolean firstCall = true;

  // the tree of the first call, the Lagrangian tree repaired into a common base: its edges first
  private IntVar[] hintVars;
  private int[] hint;

  // edge filtering on the tree of the shifted weights
  private final TreeReducedCosts reducedCosts;

  /**
   * It constructs the constraint.
   *
   * @param n the number of nodes.
   * @param from the first node of each edge, a node number from base.
   * @param to the second node of each edge, a node number from base.
   * @param weights the weight of each edge, at least 0.
   * @param colours the colour of each edge, 0..caps.length-1, or -1 for an edge without a limit.
   * @param caps the largest number of tree edges of each colour.
   * @param es the Boolean of each edge.
   * @param cost bounded from below by the weight of the selected edges.
   * @param base the number of the first node.
   */
  public ColouredSpanningTreeBound(
      int n,
      int[] from,
      int[] to,
      int[] weights,
      int[] colours,
      int[] caps,
      IntVar[] es,
      IntVar cost,
      int base) {
    checkInputForNullness("es", es);
    checkInputForNullness(new String[] {"cost"}, new Object[] {cost});
    this.m = es.length;
    if (from.length != m || to.length != m || weights.length != m || colours.length != m) {
      throw new IllegalArgumentException(
          "ColouredSpanningTreeBound: from, to, weights, colours and es must have the same length");
    }
    for (int e = 0; e < m; e++) {
      if (from[e] < base || from[e] >= base + n || to[e] < base || to[e] >= base + n) {
        throw new IllegalArgumentException(
            "ColouredSpanningTreeBound: edge "
                + e
                + " has a node outside "
                + base
                + ".."
                + (base + n - 1));
      }
      if (colours[e] < -1 || colours[e] >= caps.length) {
        throw new IllegalArgumentException(
            "ColouredSpanningTreeBound: edge " + e + " has colour " + colours[e]);
      }
      if (weights[e] < 0) {
        throw new IllegalArgumentException(
            "ColouredSpanningTreeBound: edge " + e + " has a negative weight");
      }
    }
    for (int c = 0; c < caps.length; c++) {
      if (caps[c] < 0) {
        throw new IllegalArgumentException(
            "ColouredSpanningTreeBound: colour " + c + " has a negative limit");
      }
    }
    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 3;
    this.n = n;
    this.from = Arrays.copyOf(from, m);
    this.to = Arrays.copyOf(to, m);
    this.weights = Arrays.copyOf(weights, m);
    this.colours = Arrays.copyOf(colours, m);
    this.caps = Arrays.copyOf(caps, caps.length);
    this.es = Arrays.copyOf(es, m);
    this.cost = cost;
    this.base = base;
    this.colourNo = caps.length;

    tail = new int[m];
    head = new int[m];
    for (int e = 0; e < m; e++) {
      tail[e] = from[e] - base;
      head[e] = to[e] - base;
    }
    int[] order =
        IntStream.range(0, m)
            .boxed()
            .sorted(Comparator.comparingInt((Integer e) -> weights[e]))
            .mapToInt(Integer::intValue)
            .toArray();
    int[] sizes = new int[colourNo + 1];
    for (int e = 0; e < m; e++) {
      sizes[list(e)]++;
    }
    byColour = new int[colourNo + 1][];
    for (int c = 0; c <= colourNo; c++) {
      byColour[c] = new int[sizes[c]];
    }
    Arrays.fill(sizes, 0);
    for (int e : order) {
      byColour[list(e)][sizes[list(e)]++] = e;
    }

    parent = new int[n];
    component = new int[n];
    inSet = new boolean[m];
    colourCount = new int[colourNo];
    residual = new int[colourNo];
    candidates = new int[m];
    candA = new int[m];
    candB = new int[m];
    pred = new int[m];
    bfs = new int[m];
    forestAdjStart = new int[n + 1];
    forestAdj = new int[2 * m];
    tin = new int[n];
    tout = new int[n];
    tree = new int[n];
    forestParentEdge = new int[n];
    stack = new int[n];
    lowerEnd = new int[m];

    lambda = new double[colourNo];
    bestLambda = new double[colourNo];
    gradient = new int[colourNo];
    heap = new int[colourNo + 1];
    inTree = new boolean[m];
    shifted = new long[m];

    reducedCosts = new TreeReducedCosts(n, m);

    setScope(es, new IntVar[] {cost});
  }

  private int list(int e) {
    return colours[e] < 0 ? colourNo : colours[e];
  }

  @Override
  public void consistency(Store store) {

    if (n == 0) {
      return;
    }

    int k = contract();
    long selectedWeight = contractedWeight;
    if (k > 1) {
      long feasibleWeight = feasibility(k);
      boolean first = firstCall;
      firstCall = false;
      lagrangian(store, feasibleWeight + selectedWeight, first ? FIRST_STEPS : STEPS);
      if (first) {
        // the filtering may have selected edges, so the components are made again
        hintFrom(repairedTree(contract()));
      }
    } else if (selectedWeight > cost.max()) {
      throw Store.failException;
    } else {
      cost.domain.inMin(store.level, cost, (int) selectedWeight);
    }
  }

  // contracts the selected edges: components, colour counts and residual limits; fails on a cycle
  // or a colour over its limit; returns the number of components
  private int contract() {
    for (int v = 0; v < n; v++) {
      parent[v] = v;
    }
    Arrays.fill(colourCount, 0);
    long selectedWeight = 0;
    for (int e = 0; e < m; e++) {
      if (es[e].min() == 1) {
        if (!TreeReducedCosts.union(parent, tail[e], head[e])) {
          throw Store.failException;
        }
        selectedWeight += weights[e];
        if (colours[e] >= 0 && ++colourCount[colours[e]] > caps[colours[e]]) {
          throw Store.failException;
        }
      }
    }
    for (int c = 0; c < colourNo; c++) {
      residual[c] = caps[c] - colourCount[c];
    }
    int k = 0;
    for (int v = 0; v < n; v++) {
      if (TreeReducedCosts.find(parent, v) == v) {
        component[v] = k++;
      }
    }
    for (int v = 0; v < n; v++) {
      component[v] = component[TreeReducedCosts.find(parent, v)];
    }
    contractedWeight = selectedWeight;
    return k;
  }

  // ---------------------------------------------------------------------------------------------
  // feasibility: a maximum common independent set of the graphic and partition matroids

  // the weight of a common base of the contracted graph; fails when there is none
  private long feasibility(int k) {

    // candidates: free edges between two components
    int cn = 0;
    for (int e = 0; e < m; e++) {
      if (es[e].min() == 0 && es[e].max() == 1) {
        int a = component[tail[e]];
        int b = component[head[e]];
        if (a != b) {
          candA[cn] = a;
          candB[cn] = b;
          candidates[cn++] = e;
          continue;
        }
      }
      inSet[e] = false;
    }

    // repair the set kept from the last call, then add edges greedily
    for (int v = 0; v < k; v++) {
      parent[v] = v;
    }
    Arrays.fill(colourCount, 0);
    int size = 0;
    for (int pass = 0; pass < 2; pass++) {
      for (int i = 0; i < cn; i++) {
        int e = candidates[i];
        boolean want = pass == 0 ? inSet[e] : !inSet[e];
        if (!want) {
          continue;
        }
        int c = colours[e];
        if ((c < 0 || colourCount[c] < residual[c])
            && TreeReducedCosts.union(parent, candA[i], candB[i])) {
          inSet[e] = true;
          if (c >= 0) {
            colourCount[c]++;
          }
          size++;
        } else {
          inSet[e] = false;
        }
      }
    }

    while (size < k - 1) {
      if (!augment(k, cn)) {
        throw Store.failException;
      }
      size++;
    }

    long weight = 0;
    for (int i = 0; i < cn; i++) {
      if (inSet[candidates[i]]) {
        weight += weights[candidates[i]];
      }
    }
    return weight;
  }

  // one shortest augmenting path in the exchange graph; false when the set is maximum
  private boolean augment(int k, int cn) {

    // the forest of the set over the components, with an Euler tour of each tree
    Arrays.fill(forestAdjStart, 0, k + 1, 0);
    for (int i = 0; i < cn; i++) {
      if (inSet[candidates[i]]) {
        forestAdjStart[candA[i] + 1]++;
        forestAdjStart[candB[i] + 1]++;
      }
    }
    for (int v = 0; v < k; v++) {
      forestAdjStart[v + 1] += forestAdjStart[v];
    }
    int[] fill = Arrays.copyOf(forestAdjStart, k);
    for (int i = 0; i < cn; i++) {
      if (inSet[candidates[i]]) {
        forestAdj[fill[candA[i]]++] = i;
        forestAdj[fill[candB[i]]++] = i;
      }
    }
    Arrays.fill(tree, 0, k, -1);
    int clock = 0;
    for (int r = 0; r < k; r++) {
      if (tree[r] >= 0) {
        continue;
      }
      // iterative depth-first search; stack holds nodes, fill[v] the next adjacency to visit
      int sp = 0;
      stack[sp++] = r;
      tree[r] = r;
      forestParentEdge[r] = -1;
      tin[r] = clock++;
      fill[r] = forestAdjStart[r];
      while (sp > 0) {
        int v = stack[sp - 1];
        if (fill[v] < forestAdjStart[v + 1]) {
          int i = forestAdj[fill[v]++];
          int w = candA[i] == v ? candB[i] : candA[i];
          if (tree[w] < 0) {
            tree[w] = r;
            forestParentEdge[w] = i;
            tin[w] = clock++;
            fill[w] = forestAdjStart[w];
            stack[sp++] = w;
          }
        } else {
          tout[v] = clock++;
          sp--;
        }
      }
    }
    // for a set edge, the end that is the child in the forest
    for (int v = 0; v < k; v++) {
      if (forestParentEdge[v] >= 0) {
        lowerEnd[forestParentEdge[v]] = v;
      }
    }

    // breadth-first search from the edges that join two trees (indices into candidates)
    Arrays.fill(pred, 0, cn, -2);
    int qh = 0;
    int qt = 0;
    for (int i = 0; i < cn; i++) {
      if (!inSet[candidates[i]] && tree[candA[i]] != tree[candB[i]]) {
        pred[i] = -1;
        bfs[qt++] = i;
      }
    }
    while (qh < qt) {
      int i = bfs[qh++];
      int e = candidates[i];
      if (!inSet[e]) {
        int c = colours[e];
        if (c < 0 || colourCount[c] < residual[c]) {
          flip(i, cn);
          return true;
        }
        // exchange with a set edge of the same colour
        for (int j = 0; j < cn; j++) {
          if (pred[j] == -2 && inSet[candidates[j]] && colours[candidates[j]] == c) {
            pred[j] = i;
            bfs[qt++] = j;
          }
        }
      } else {
        // exchange with an edge outside the set whose cycle goes through this set edge
        int child = lowerEnd[i];
        for (int j = 0; j < cn; j++) {
          if (pred[j] == -2 && !inSet[candidates[j]]) {
            int a = candA[j];
            int b = candB[j];
            if (tree[a] == tree[child]
                && tree[b] == tree[child]
                && inSubtree(child, a) != inSubtree(child, b)) {
              pred[j] = i;
              bfs[qt++] = j;
            }
          }
        }
      }
    }
    return false;
  }

  private boolean inSubtree(int root, int v) {
    return tin[root] <= tin[v] && tout[v] <= tout[root];
  }

  // flips the set along the path ending at candidate i and updates the colour counts
  private void flip(int i, int cn) {
    for (int j = i; j >= 0; j = pred[j]) {
      int e = candidates[j];
      int c = colours[e];
      inSet[e] = !inSet[e];
      if (c >= 0) {
        colourCount[c] += inSet[e] ? 1 : -1;
      }
    }
  }

  // ---------------------------------------------------------------------------------------------
  // the Lagrangian bound

  private void lagrangian(Store store, long upperHint, int steps) {

    long upper = Math.min(cost.max(), upperHint);
    double best = Double.NEGATIVE_INFINITY;
    double mu = 2.0;
    int stall = 0;
    System.arraycopy(lambda, 0, bestLambda, 0, colourNo);
    for (int step = 0; step < steps && colourNo > 0; step++) {
      double value = shiftedTree(lambda);
      for (int c = 0; c < colourNo; c++) {
        value -= lambda[c] * caps[c];
      }
      if (value > best + 1e-9) {
        best = value;
        System.arraycopy(lambda, 0, bestLambda, 0, colourNo);
        stall = 0;
      } else if (++stall > 5) {
        mu /= 2;
        stall = 0;
      }
      long norm = 0;
      Arrays.fill(gradient, 0);
      for (int e = 0; e < m; e++) {
        if (inTree[e] && colours[e] >= 0) {
          gradient[colours[e]]++;
        }
      }
      for (int c = 0; c < colourNo; c++) {
        gradient[c] -= caps[c];
        if (gradient[c] > 0 || lambda[c] > 0) {
          norm += (long) gradient[c] * gradient[c];
        }
      }
      if (norm == 0 || upper - value < 1e-6 || mu < 1e-4) {
        break;
      }
      double t = mu * Math.max(upper - value, 1.0) / norm;
      for (int c = 0; c < colourNo; c++) {
        lambda[c] = Math.max(0.0, lambda[c] + t * gradient[c]);
      }
    }
    System.arraycopy(bestLambda, 0, lambda, 0, colourNo);

    // the bound in exact arithmetic with the multipliers rounded down
    long[] scaled = new long[colourNo];
    long offset = 0;
    for (int c = 0; c < colourNo; c++) {
      scaled[c] = (long) Math.floor(bestLambda[c] * SCALE);
      offset += scaled[c] * caps[c];
    }
    for (int e = 0; e < m; e++) {
      shifted[e] = weights[e] * SCALE + (colours[e] < 0 ? 0 : scaled[colours[e]]);
    }
    remember(scaled);
    long lower = exactTree();
    long bound = Math.ceilDiv(lower - offset, SCALE);
    if (bound > cost.max()) {
      throw Store.failException;
    }
    cost.domain.inMin(store.level, cost, (int) Math.max(bound, Integer.MIN_VALUE));
    if (offset > 0) {
      reducedCosts.filter(
          store, es, tail, head, inTree, shifted, lower, cost.max() * SCALE + offset);
    }
  }

  private void remember(long[] scaled) {
    if (historySize > 0 && Arrays.equals(history[(historyNext + HISTORY - 1) % HISTORY], scaled)) {
      return;
    }
    history[historyNext] = scaled;
    historyNext = (historyNext + 1) % HISTORY;
    historySize = Math.min(historySize + 1, HISTORY);
  }

  // ---------------------------------------------------------------------------------------------
  // explanations: the cut and cycle sets of the bound, for each kept multiplier vector and the zero
  // one, newest first, until one implies the atom

  // the shifted weights of multiplier vector h (h == historySize: zero) in explainWeights; returns
  // the offset
  private long shiftWeights(int h) {
    if (explanation == null) {
      explanation = new TreeExplanation(n, es, tail, head, cost);
      explainWeights = new long[m];
    }
    long[] scaled = h < historySize ? history[(historyNext + HISTORY - 1 - h) % HISTORY] : null;
    long offset = 0;
    for (int c = 0; scaled != null && c < colourNo; c++) {
      offset += scaled[c] * caps[c];
    }
    for (int e = 0; e < m; e++) {
      explainWeights[e] =
          weights[e] * SCALE + (scaled == null || colours[e] < 0 ? 0 : scaled[colours[e]]);
    }
    return offset;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    for (int h = 0; h <= historySize; h++) {
      long offset = shiftWeights(h);
      if (explanation.explain(trail, entry, explainWeights, offset, SCALE, out)) {
        return true;
      }
    }
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    shiftWeights(historySize);
    if (explanation.addForcedConflict(trail, trail.size(), colours, caps, out)) {
      return true;
    }
    for (int h = 0; h <= historySize; h++) {
      long offset = shiftWeights(h);
      if (explanation.explainFailure(trail, explainWeights, offset, SCALE, out)) {
        return true;
      }
    }
    return false;
  }

  // minimum spanning tree with the selected edges first and the weights shifted by the
  // multipliers; marks inTree and returns its shifted weight
  private double shiftedTree(double[] mult) {
    resetSelected();
    double total = 0;
    for (int e = 0; e < m; e++) {
      if (inTree[e]) {
        total += weights[e] + (colours[e] < 0 ? 0 : mult[colours[e]]);
      }
    }
    // merge the colour lists by shifted weight
    int[] next = new int[colourNo + 1];
    int hs = 0;
    for (int c = 0; c <= colourNo; c++) {
      if (byColour[c].length > 0) {
        heap[hs] = c;
        hs++;
        siftUp(hs - 1, next, mult);
      }
    }
    while (hs > 0) {
      int c = heap[0];
      int e = byColour[c][next[c]++];
      if (es[e].min() == 0
          && es[e].max() == 1
          && TreeReducedCosts.union(parent, tail[e], head[e])) {
        inTree[e] = true;
        total += weights[e] + (c == colourNo ? 0 : mult[c]);
      }
      if (next[c] == byColour[c].length) {
        heap[0] = heap[--hs];
      }
      siftDown(0, hs, next, mult);
    }
    return total;
  }

  private double key(int c, int[] next, double[] mult) {
    int e = byColour[c][next[c]];
    return weights[e] + (c == colourNo ? 0 : mult[c]);
  }

  private void siftUp(int i, int[] next, double[] mult) {
    while (i > 0) {
      int p = (i - 1) / 2;
      if (key(heap[p], next, mult) <= key(heap[i], next, mult)) {
        return;
      }
      int t = heap[p];
      heap[p] = heap[i];
      heap[i] = t;
      i = p;
    }
  }

  private void siftDown(int i, int hs, int[] next, double[] mult) {
    while (true) {
      int l = 2 * i + 1;
      if (l >= hs) {
        return;
      }
      int r = l + 1;
      int s = r < hs && key(heap[r], next, mult) < key(heap[l], next, mult) ? r : l;
      if (key(heap[i], next, mult) <= key(heap[s], next, mult)) {
        return;
      }
      int t = heap[s];
      heap[s] = heap[i];
      heap[i] = t;
      i = s;
    }
  }

  // minimum spanning tree with the selected edges first for the weights in shifted; marks inTree
  // and returns its weight
  private long exactTree() {
    resetSelected();
    long total = 0;
    for (int e = 0; e < m; e++) {
      if (inTree[e]) {
        total += shifted[e];
      }
    }
    Integer[] free = new Integer[m];
    int fn = 0;
    for (int e = 0; e < m; e++) {
      if (es[e].min() == 0 && es[e].max() == 1) {
        free[fn++] = e;
      }
    }
    Arrays.sort(free, 0, fn, Comparator.comparingLong((Integer e) -> shifted[e]));
    for (int i = 0; i < fn; i++) {
      int e = free[i];
      if (TreeReducedCosts.union(parent, tail[e], head[e])) {
        inTree[e] = true;
        total += shifted[e];
      }
    }
    return total;
  }

  // the Lagrangian tree in inTree made a common base: its edges between components first, then the
  // other free ones, each by increasing shifted weight, taken greedily within the residual limits
  // and completed by augmenting paths; 0/1 per edge
  private int[] repairedTree(int k) {
    Integer[] order = new Integer[m];
    int on = 0;
    for (int e = 0; e < m; e++) {
      if (es[e].min() == 0 && es[e].max() == 1 && component[tail[e]] != component[head[e]]) {
        order[on++] = e;
      }
    }
    Arrays.sort(
        order,
        0,
        on,
        Comparator.comparing((Integer e) -> !inTree[e]).thenComparingLong(e -> shifted[e]));
    for (int v = 0; v < k; v++) {
      parent[v] = v;
    }
    Arrays.fill(colourCount, 0);
    Arrays.fill(inSet, false);
    for (int i = 0; i < on; i++) {
      int e = order[i];
      int c = colours[e];
      if ((c < 0 || colourCount[c] < residual[c])
          && TreeReducedCosts.union(parent, component[tail[e]], component[head[e]])) {
        inSet[e] = true;
        if (c >= 0) {
          colourCount[c]++;
        }
      }
    }
    feasibility(k);
    int[] values = new int[m];
    for (int e = 0; e < m; e++) {
      values[e] = es[e].min() == 1 || inSet[e] ? 1 : 0;
    }
    improveBySwaps(values);
    return values;
  }

  /** The most improving swaps the hint makes, per node. */
  static final int SWAPS_PER_NODE = 4;

  // local search on a spanning tree (0/1 per edge): the best swap of a free tree edge for a
  // cheaper edge outside the tree that closes a cycle through it, within the colour limits, until
  // there is none
  private void improveBySwaps(int[] tree) {
    int[] count = new int[colourNo];
    for (int e = 0; e < m; e++) {
      if (tree[e] == 1 && colours[e] >= 0) {
        count[colours[e]]++;
      }
    }
    int[] adjStart = new int[n + 1];
    int[] adjEdge = new int[2 * (n - 1)];
    int[] up = new int[n];
    int[] upEdge = new int[n];
    int[] depth = new int[n];
    int[] queue = new int[n];
    for (int swaps = 0; swaps < SWAPS_PER_NODE * n; swaps++) {
      if (!rootTree(tree, adjStart, adjEdge, up, upEdge, depth, queue)) {
        return;
      }
      int bestIn = -1;
      int bestOut = -1;
      long bestGain = 0;
      for (int e = 0; e < m; e++) {
        if (tree[e] == 1 || es[e].max() == 0 || tail[e] == head[e]) {
          continue;
        }
        int ce = colours[e];
        int u = tail[e];
        int v = head[e];
        while (u != v) {
          if (depth[u] < depth[v]) {
            int t = u;
            u = v;
            v = t;
          }
          int f = upEdge[u];
          long gain = (long) weights[f] - weights[e];
          if (es[f].min() == 0
              && gain > bestGain
              && (ce < 0 || ce == colours[f] || count[ce] < caps[ce])) {
            bestGain = gain;
            bestIn = e;
            bestOut = f;
          }
          u = up[u];
        }
      }
      if (bestIn < 0) {
        return;
      }
      tree[bestIn] = 1;
      tree[bestOut] = 0;
      if (colours[bestIn] >= 0) {
        count[colours[bestIn]]++;
      }
      if (colours[bestOut] >= 0) {
        count[colours[bestOut]]--;
      }
    }
  }

  // roots the tree at node 0 (parent up, edge upEdge, depth); false when it is not spanning
  private boolean rootTree(
      int[] tree, int[] adjStart, int[] adjEdge, int[] up, int[] upEdge, int[] depth, int[] queue) {
    Arrays.fill(adjStart, 0);
    for (int e = 0; e < m; e++) {
      if (tree[e] == 1) {
        adjStart[tail[e] + 1]++;
        adjStart[head[e] + 1]++;
      }
    }
    for (int v = 0; v < n; v++) {
      adjStart[v + 1] += adjStart[v];
    }
    if (adjStart[n] != 2 * (n - 1)) {
      return false;
    }
    int[] fill = Arrays.copyOf(adjStart, n);
    for (int e = 0; e < m; e++) {
      if (tree[e] == 1) {
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
        int e = adjEdge[i];
        int w = tail[e] == v ? head[e] : tail[e];
        if (up[w] < 0) {
          up[w] = v;
          upEdge[w] = e;
          depth[w] = depth[v] + 1;
          queue[qt++] = w;
        }
      }
    }
    return qt == n;
  }

  private void hintFrom(int[] tree) {
    hintVars = new IntVar[m];
    hint = new int[m];
    int i = 0;
    for (int value = 1; value >= 0; value--) {
      for (int e = 0; e < m; e++) {
        if (tree[e] == value) {
          hintVars[i] = es[e];
          hint[i++] = value;
        }
      }
    }
  }

  @Override
  public IntVar[] hintVariables() {
    return hintVars == null ? es : hintVars;
  }

  @Override
  public int[] hintValues() {
    return hint;
  }

  private void resetSelected() {
    for (int v = 0; v < n; v++) {
      parent[v] = v;
    }
    for (int e = 0; e < m; e++) {
      inTree[e] = es[e].min() == 1;
      if (inTree[e]) {
        TreeReducedCosts.union(parent, tail[e], head[e]);
      }
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    if (!cost.singleton()) {
      return false;
    }
    for (IntVar e : es) {
      if (!e.singleton()) {
        return false;
      }
    }
    // the selected edges: a forest of n-1 edges within the colour limits, of weight at most cost
    int[] count = new int[colourNo];
    long sum = 0;
    int selected = 0;
    Arrays.setAll(parent, v -> v);
    for (int e = 0; e < m; e++) {
      if (es[e].value() == 0) {
        continue;
      }
      if (!TreeReducedCosts.union(parent, tail[e], head[e])) {
        return false;
      }
      int c = colours[e];
      if (c >= 0) {
        count[c]++;
        if (count[c] > caps[c]) {
          return false;
        }
      }
      sum += weights[e];
      selected++;
    }
    return selected == Math.max(n - 1, 0) && cost.value() >= sum;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : ColouredSpanningTreeBound(").append(n).append(", ");
    result.append(Arrays.toString(from)).append(", ").append(Arrays.toString(to)).append(", ");
    result.append(Arrays.toString(weights)).append(", ");
    result.append(Arrays.toString(colours)).append(", ").append(Arrays.toString(caps));
    result.append(", ");
    appendArrayToString(result, es);
    result.append(", ").append(cost).append(", ").append(base).append(")");
    return result.toString();
  }

  @Override
  public ColouredSpanningTreeBound copy(VarMap map) {
    return new ColouredSpanningTreeBound(
        n, from, to, weights, colours, caps, map.get(es), map.get(cost), base);
  }
}
