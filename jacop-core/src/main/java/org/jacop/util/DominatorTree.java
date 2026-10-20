/*
 * DominatorTree.java
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

package org.jacop.util;

import java.util.Arrays;

/**
 * Dominator tree of a directed graph, computed with the Lengauer-Tarjan algorithm (path compression
 * variant). Arcs and all working data live in int arrays that are reused between computations, so a
 * computation allocates nothing once the arc arrays have grown to the graph size. After {@link
 * #compute(int)} the query {@link #dominates(int, int)} takes constant time.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class DominatorTree {

  private static final int NONE = -1;

  private final int n;

  // arcs as linked lists: outgoing arcs of u start at outHead[u], incoming arcs of v at inHead[v]
  private final int[] outHead;
  private final int[] inHead;
  private int[] arcFrom;
  private int[] arcTo;
  private int[] outNext;
  private int[] inNext;
  private int arcs;

  // dfs numbering; number[v] is NONE for a vertex the dfs has not reached
  private final int[] number;
  private final int[] vertex;
  private final int[] parent;
  private final int[] semi;
  private final int[] label;
  private final int[] ancestor;
  private final int[] idom;
  private final int[] bucketHead;
  private final int[] bucketNext;
  private final int[] stack;
  private final int[] stackArc;

  // pre and post order of the dominator tree, so a dominates b iff pre[a] <= pre[b] < post[a]
  private final int[] pre;
  private final int[] post;
  private final int[] childHead;
  private final int[] childNext;

  /**
   * Creates the structure for graphs with vertices 0..n-1.
   *
   * @param n the number of vertices.
   */
  public DominatorTree(int n) {
    this.n = n;
    outHead = new int[n];
    inHead = new int[n];
    int capacity = Math.max(4, 2 * n);
    arcFrom = new int[capacity];
    arcTo = new int[capacity];
    outNext = new int[capacity];
    inNext = new int[capacity];
    number = new int[n];
    vertex = new int[n];
    parent = new int[n];
    semi = new int[n];
    label = new int[n];
    ancestor = new int[n];
    idom = new int[n];
    bucketHead = new int[n];
    bucketNext = new int[n];
    stack = new int[n];
    stackArc = new int[n];
    pre = new int[n];
    post = new int[n];
    childHead = new int[n];
    childNext = new int[n];
    clear();
  }

  /** Removes all arcs. */
  public final void clear() {
    Arrays.fill(outHead, NONE);
    Arrays.fill(inHead, NONE);
    arcs = 0;
  }

  /**
   * Adds the arc from u to v.
   *
   * @param u the source of the arc.
   * @param v the target of the arc.
   */
  public void addArc(int u, int v) {
    if (arcs == arcTo.length) {
      int capacity = 2 * arcs;
      arcFrom = Arrays.copyOf(arcFrom, capacity);
      arcTo = Arrays.copyOf(arcTo, capacity);
      outNext = Arrays.copyOf(outNext, capacity);
      inNext = Arrays.copyOf(inNext, capacity);
    }
    arcFrom[arcs] = u;
    arcTo[arcs] = v;
    outNext[arcs] = outHead[u];
    outHead[u] = arcs;
    inNext[arcs] = inHead[v];
    inHead[v] = arcs;
    arcs++;
  }

  /**
   * Computes the dominators of all vertices for the given root.
   *
   * @param root the root of the graph.
   * @return false if some vertex cannot be reached from the root, true otherwise.
   */
  public boolean compute(int root) {

    int reached = depthFirstSearch(root);
    if (reached != n) {
      return false;
    }

    Arrays.fill(bucketHead, NONE);
    for (int i = reached - 1; i > 0; i--) {
      int w = vertex[i];
      for (int a = inHead[w]; a != NONE; a = inNext[a]) {
        int u = eval(arcFrom[a]);
        if (semi[u] < semi[w]) {
          semi[w] = semi[u];
        }
      }
      int s = vertex[semi[w]];
      bucketNext[w] = bucketHead[s];
      bucketHead[s] = w;
      int p = parent[w];
      ancestor[w] = p;
      for (int v = bucketHead[p]; v != NONE; v = bucketNext[v]) {
        int u = eval(v);
        idom[v] = semi[u] < semi[v] ? u : p;
      }
      bucketHead[p] = NONE;
    }
    for (int i = 1; i < reached; i++) {
      int w = vertex[i];
      if (idom[w] != vertex[semi[w]]) {
        idom[w] = idom[idom[w]];
      }
    }
    idom[root] = root;

    numberDominatorTree(root);
    return true;
  }

  /**
   * Tells whether a dominates b, that is every path from the root to b goes through a. Every vertex
   * dominates itself. Valid after a successful {@link #compute(int)}.
   *
   * @param a the dominating vertex.
   * @param b the dominated vertex.
   * @return true if a dominates b.
   */
  public boolean dominates(int a, int b) {
    return pre[a] <= pre[b] && pre[b] < post[a];
  }

  private int depthFirstSearch(int root) {
    Arrays.fill(number, NONE);
    int count = 0;
    int top = 0;
    stack[top] = root;
    stackArc[top] = outHead[root];
    visit(root, root, count++);
    while (top >= 0) {
      int v = stack[top];
      int a = stackArc[top];
      if (a == NONE) {
        top--;
        continue;
      }
      stackArc[top] = outNext[a];
      int w = arcTo[a];
      if (number[w] == NONE) {
        visit(w, v, count++);
        top++;
        stack[top] = w;
        stackArc[top] = outHead[w];
      }
    }
    return count;
  }

  private void visit(int v, int from, int dfsNumber) {
    number[v] = dfsNumber;
    vertex[dfsNumber] = v;
    semi[v] = dfsNumber;
    label[v] = v;
    ancestor[v] = NONE;
    parent[v] = from;
  }

  private int eval(int v) {
    if (ancestor[v] == NONE) {
      return v;
    }
    compress(v);
    return label[v];
  }

  // path compression without recursion: the path is collected on the stack first
  private void compress(int v) {
    int top = 0;
    int u = v;
    while (ancestor[ancestor[u]] != NONE) {
      stack[top++] = u;
      u = ancestor[u];
    }
    while (top > 0) {
      int w = stack[--top];
      int a = ancestor[w];
      if (semi[label[a]] < semi[label[w]]) {
        label[w] = label[a];
      }
      ancestor[w] = ancestor[a];
    }
  }

  private void numberDominatorTree(int root) {
    Arrays.fill(childHead, NONE);
    for (int v = 0; v < n; v++) {
      if (v != root) {
        int d = idom[v];
        childNext[v] = childHead[d];
        childHead[d] = v;
      }
    }
    int counter = 0;
    int top = 0;
    stack[top] = root;
    stackArc[top] = childHead[root];
    pre[root] = counter++;
    while (top >= 0) {
      int v = stack[top];
      int c = stackArc[top];
      if (c == NONE) {
        post[v] = counter;
        top--;
        continue;
      }
      stackArc[top] = childNext[c];
      pre[c] = counter++;
      top++;
      stack[top] = c;
      stackArc[top] = childHead[c];
    }
  }
}
