/*
 * AlldifferentExceptFilter.java
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
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * Domain consistent filtering for {@link AlldifferentExcept}, with the exception values as "joker"
 * values that any number of variables can take.
 *
 * <p>Let N be the variables that cannot take an exception value. The constraint is satisfiable iff
 * N has a matching into the values that covers N. Every other variable can always take an exception
 * value, so it constrains nobody. A value v of a variable x is supported iff
 *
 * <ul>
 *   <li>x is in N and some matching covering N assigns v to x (Régin's test: v is matched to x, v's
 *       owner can be displaced towards a free value, or x and v's owner are in one strongly
 *       connected component of the alternating graph);
 *   <li>x is not in N, and v is an exception value or some matching covering N leaves v free (v is
 *       free, or its owner can be displaced towards a free value).
 * </ul>
 *
 * <p>The matching is kept between calls as a warm start, so a call usually needs no augmenting
 * path. One call costs O(sum of domain sizes) plus the augmenting paths. When the values of N span
 * more than {@link #MAX_RANGE} or the domains of N hold more than {@link #MAX_EDGES} values, the
 * filter declines and the caller falls back to a feasibility check.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
final class AlldifferentExceptFilter {

  static final int MAX_RANGE = 1 << 16;
  static final int MAX_EDGES = 1 << 20;

  /** Variables in the matching graph: 0..nVars-1 are N, nVars..nVars+nJokers-1 the rest. */
  private IntVar[] vars = new IntVar[0];

  /** Position in the constraint's list of every variable in the graph. */
  private int[] position = new int[0];

  private int nVars;
  private int nJokers;

  /** Value offset: value index w stands for value base + w. */
  private int base;

  /** Domains of N in CSR form, as value indices. */
  private int[] adjStart = new int[1];

  private int[] adj = new int[0];

  /** Owner (index in N) of each value index, -1 when free. All -1 between calls. */
  private int[] owner = new int[0];

  /** Matched value index of each variable of N. */
  private int[] mate = new int[0];

  /** Warm start: last matched value of the variable that was at a list position. */
  private int[] lastMate = new int[0];

  private IntVar[] lastMateVar = new IntVar[0];

  // Breadth first search for augmenting paths.
  private int[] queue = new int[0];
  private int[] parent = new int[0];
  private int[] visited = new int[0];
  private int visitStamp;

  // Tarjan's strongly connected components, iterative.
  private int[] num = new int[0];
  private int[] low = new int[0];
  private int[] scc = new int[0];
  private int[] sccStack = new int[0];
  private int[] callNode = new int[0];
  private int[] callEdge = new int[0];
  private boolean[] onStack = new boolean[0];
  private boolean[] freeAdjacent = new boolean[0];
  private boolean[] escapes = new boolean[0];

  private int[] removed = new int[0];

  /**
   * Prunes the variables from position {@code from} of {@code list} to domain consistency.
   *
   * @param store the store
   * @param list the variables of the constraint
   * @param from the first variable not yet processed by value propagation
   * @param c the constraint, which defines the exception values
   * @return false if the filter declined (too large domains), so nothing was done
   */
  boolean filter(Store store, IntVar[] list, int from, AlldifferentExcept c) {

    ensureCapacity(list.length);

    nVars = 0;
    nJokers = 0;
    int min = Integer.MAX_VALUE;
    int max = Integer.MIN_VALUE;
    long edges = 0;
    int jokerEnd = list.length;
    for (int i = from; i < list.length; i++) {
      IntVar v = list[i];
      IntDomain d = v.dom();
      if (c.hasExceptionValues(v)) {
        jokerEnd--;
        vars[jokerEnd] = v;
        position[jokerEnd] = i;
      } else {
        vars[nVars] = v;
        position[nVars] = i;
        nVars++;
        min = Math.min(min, d.min());
        max = Math.max(max, d.max());
        edges += d.getSize();
      }
    }
    nJokers = list.length - jokerEnd;
    // Move the joker variables right after N.
    if (jokerEnd > nVars) {
      System.arraycopy(vars, jokerEnd, vars, nVars, nJokers);
      System.arraycopy(position, jokerEnd, position, nVars, nJokers);
    }

    if (nVars == 0) {
      return true;
    }
    if ((long) max - min + 1 > MAX_RANGE || edges > MAX_EDGES) {
      return false;
    }

    base = min;
    int range = max - min + 1;
    if (owner.length < range) {
      owner = new int[range];
      Arrays.fill(owner, -1);
    }
    if (adj.length < edges) {
      adj = new int[(int) edges];
    }

    buildAdjacency();

    try {
      match();
      findComponents();
      pruneMatchedVariables(store);
      pruneJokerVariables(store);
    } finally {
      for (int k = 0; k < nVars; k++) {
        if (mate[k] >= 0) {
          owner[mate[k]] = -1;
        }
      }
    }
    return true;
  }

  private void ensureCapacity(int n) {
    if (vars.length >= n) {
      return;
    }
    vars = new IntVar[n];
    position = new int[n];
    adjStart = new int[n + 1];
    mate = new int[n];
    lastMate = new int[n];
    lastMateVar = new IntVar[n];
    queue = new int[n];
    parent = new int[n];
    visited = new int[n];
    num = new int[n];
    low = new int[n];
    scc = new int[n];
    sccStack = new int[n];
    callNode = new int[n];
    callEdge = new int[n];
    onStack = new boolean[n];
    freeAdjacent = new boolean[n];
    escapes = new boolean[n];
  }

  private void buildAdjacency() {
    int e = 0;
    for (int k = 0; k < nVars; k++) {
      adjStart[k] = e;
      IntDomain d = vars[k].dom();
      if (d instanceof IntervalDomain) {
        IntervalDomain id = (IntervalDomain) d;
        for (int j = 0; j < id.size; j++) {
          Interval interval = id.intervals[j];
          for (int w = interval.min(); w <= interval.max(); w++) {
            adj[e++] = w - base;
          }
        }
      } else {
        for (ValueEnumeration en = d.valueEnumeration(); en.hasMoreElements(); ) {
          adj[e++] = en.nextElement() - base;
        }
      }
    }
    adjStart[nVars] = e;
  }

  /** Finds a matching that covers N, starting from the last one, or fails. */
  private void match() {
    int unmatched = 0;
    for (int k = 0; k < nVars; k++) {
      mate[k] = -1;
      int pos = position[k];
      if (lastMateVar[pos] == vars[k]) {
        int w = lastMate[pos] - base;
        if (w >= 0 && w < owner.length && owner[w] < 0 && vars[k].domain.contains(lastMate[pos])) {
          mate[k] = w;
          owner[w] = k;
          continue;
        }
      }
      // Keep the unmatched variables in queue, it is free until augmenting starts.
      queue[unmatched++] = k;
    }
    // Greedy pass, then augmenting paths for the rest.
    int left = 0;
    for (int u = 0; u < unmatched; u++) {
      int k = queue[u];
      boolean done = false;
      for (int e = adjStart[k]; e < adjStart[k + 1]; e++) {
        int w = adj[e];
        if (owner[w] < 0) {
          mate[k] = w;
          owner[w] = k;
          done = true;
          break;
        }
      }
      if (!done) {
        queue[left++] = k;
      }
    }
    if (left > 0) {
      int[] pending = Arrays.copyOf(queue, left);
      for (int k : pending) {
        if (!augment(k)) {
          throw Store.failException;
        }
      }
    }
    for (int k = 0; k < nVars; k++) {
      lastMate[position[k]] = mate[k] + base;
      lastMateVar[position[k]] = vars[k];
    }
  }

  /** Breadth first search for an augmenting path from the free variable root. */
  private boolean augment(int root) {
    if (++visitStamp == Integer.MAX_VALUE) {
      Arrays.fill(visited, 0);
      visitStamp = 1;
    }
    int head = 0;
    int tail = 0;
    queue[tail++] = root;
    visited[root] = visitStamp;
    while (head < tail) {
      int u = queue[head++];
      for (int e = adjStart[u]; e < adjStart[u + 1]; e++) {
        int w = adj[e];
        int o = owner[w];
        if (o < 0) {
          // Flip the path: u takes w, each parent takes the value of its child.
          int cur = u;
          int val = w;
          while (true) {
            int old = mate[cur];
            mate[cur] = val;
            owner[val] = cur;
            if (cur == root) {
              return true;
            }
            cur = parent[cur];
            val = old;
          }
        }
        if (visited[o] != visitStamp) {
          visited[o] = visitStamp;
          parent[o] = u;
          queue[tail++] = o;
        }
      }
    }
    return false;
  }

  /**
   * Strongly connected components of the graph over N with an arc u to o when u can take the value
   * matched to o. A variable escapes when it, or a variable it reaches, can take a free value: then
   * its matched value can be freed.
   */
  private void findComponents() {
    for (int k = 0; k < nVars; k++) {
      num[k] = -1;
      onStack[k] = false;
      boolean free = false;
      for (int e = adjStart[k]; e < adjStart[k + 1]; e++) {
        if (owner[adj[e]] < 0) {
          free = true;
          break;
        }
      }
      freeAdjacent[k] = free;
    }
    int counter = 0;
    int sp = 0;
    int components = 0;
    for (int r = 0; r < nVars; r++) {
      if (num[r] >= 0) {
        continue;
      }
      int depth = 0;
      callNode[0] = r;
      callEdge[0] = adjStart[r];
      num[r] = low[r] = counter++;
      sccStack[sp++] = r;
      onStack[r] = true;
      while (depth >= 0) {
        int u = callNode[depth];
        int e = callEdge[depth];
        boolean descended = false;
        while (e < adjStart[u + 1]) {
          int o = owner[adj[e++]];
          if (o < 0 || o == u) {
            continue;
          }
          if (num[o] < 0) {
            callEdge[depth] = e;
            depth++;
            callNode[depth] = o;
            callEdge[depth] = adjStart[o];
            num[o] = low[o] = counter++;
            sccStack[sp++] = o;
            onStack[o] = true;
            descended = true;
            break;
          } else if (onStack[o]) {
            low[u] = Math.min(low[u], num[o]);
          }
        }
        if (descended) {
          continue;
        }
        if (low[u] == num[u]) {
          // u is the root of a component; its successors outside it are finished.
          int id = components++;
          int top = sp;
          int w;
          do {
            w = sccStack[--sp];
            onStack[w] = false;
            scc[w] = id;
          } while (w != u);
          boolean esc = false;
          for (int i = sp; i < top && !esc; i++) {
            int m = sccStack[i];
            if (freeAdjacent[m]) {
              esc = true;
              break;
            }
            for (int f = adjStart[m]; f < adjStart[m + 1]; f++) {
              int o = owner[adj[f]];
              if (o >= 0 && scc[o] != id && escapes[scc[o]]) {
                esc = true;
                break;
              }
            }
          }
          escapes[id] = esc;
        }
        depth--;
        if (depth >= 0) {
          int p = callNode[depth];
          low[p] = Math.min(low[p], low[u]);
        }
      }
    }
  }

  private void pruneMatchedVariables(Store store) {
    for (int k = 0; k < nVars; k++) {
      int count = 0;
      for (int e = adjStart[k]; e < adjStart[k + 1]; e++) {
        int o = owner[adj[e]];
        if (o >= 0 && o != k && scc[o] != scc[k] && !escapes[scc[o]]) {
          removed = append(removed, count++, adj[e] + base);
        }
      }
      removeValues(store, vars[k], count);
    }
  }

  private void pruneJokerVariables(Store store) {
    for (int j = nVars; j < nVars + nJokers; j++) {
      IntVar v = vars[j];
      IntDomain d = v.domain;
      int count = 0;
      if (d.getSize() > nVars) {
        for (int k = 0; k < nVars; k++) {
          int value = mate[k] + base;
          if (!escapes[scc[k]] && d.contains(value)) {
            removed = append(removed, count++, value);
          }
        }
      } else if (d instanceof IntervalDomain) {
        IntervalDomain id = (IntervalDomain) d;
        for (int i = 0; i < id.size; i++) {
          Interval interval = id.intervals[i];
          for (int value = interval.min(); value <= interval.max(); value++) {
            count = removeIfUnsupported(value, count);
          }
        }
      } else {
        for (ValueEnumeration en = d.valueEnumeration(); en.hasMoreElements(); ) {
          count = removeIfUnsupported(en.nextElement(), count);
        }
      }
      removeValues(store, v, count);
    }
  }

  /** Records value for removal from a joker variable when no matching covering N leaves it free. */
  private int removeIfUnsupported(int value, int count) {
    long w = (long) value - base;
    if (w >= 0 && w < owner.length) {
      int o = owner[(int) w];
      if (o >= 0 && !escapes[scc[o]]) {
        removed = append(removed, count, value);
        return count + 1;
      }
    }
    return count;
  }

  private void removeValues(Store store, IntVar v, int count) {
    for (int i = 0; i < count; i++) {
      v.domain.inComplement(store.level, v, removed[i]);
    }
  }

  private static int[] append(int[] a, int i, int value) {
    if (i == a.length) {
      a = Arrays.copyOf(a, Math.max(8, 2 * a.length));
    }
    a[i] = value;
    return a;
  }
}
