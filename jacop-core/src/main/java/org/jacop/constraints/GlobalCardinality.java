/*
 * GlobalCardinality.java
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
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * GlobalCardinality constraint: for each i, the number of variables of list equal to values[i] lies
 * in [low[i], up[i]], or equals counters[i]. Values that are not in values are not restricted.
 *
 * <p>It enforces generalized arc consistency (domain consistency) on the list variables, with the
 * counters seen as the intervals of their domains, using the flow algorithm of J.-C. Régin,
 * "Generalized arc consistency for global cardinality constraint", AAAI 1996. The flow network has
 * an arc from each variable to each value of its domain and an arc from each value to a sink whose
 * flow lies within the bounds of the counter of the value. All values that are not counted share
 * one node of capacity [0, n]. A feasible flow is kept between executions (domains and counter
 * bounds only grow on backtracking, so it stays feasible) and repaired by augmenting paths, first
 * for variables without a value and then for values below their lower bound (as in C.-G. Quimper,
 * P. van Beek, A. López-Ortiz, A. Golynski and S. Sadjad, "An efficient bounds consistency
 * algorithm for the global cardinality constraint", CP 2003). Fixed variables are left out of the
 * flow and lower the bounds of their values instead. A variable-value arc outside the flow belongs
 * to some feasible flow if and only if both ends lie in the same strongly connected component of
 * the residual graph. Since a variable has a single incoming arc, from its value, the components
 * are computed on the graph of the values alone, with an arc from a to b when a variable of a can
 * take b.
 *
 * <p>The counters are pruned by counting: a counter lies between the number of variables fixed to
 * its value and the number of variables that can take it, and within what the other counters leave
 * of n. This is the cardinality pruning of Gecode's domain consistent gcc; bounds consistency on
 * the counters needs more flow computations (Quimper et al.) and is not done.
 *
 * <p>The cost of an execution is linear in the total size of the domains restricted to the counted
 * values, plus the augmenting paths that repair the flow. It explores the search tree of Gecode's
 * domain consistent gcc. CountValues prunes less and costs less, and on most models explores nearly
 * as many nodes, so this constraint is meant for models that ask for domain consistency.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class GlobalCardinality extends Constraint
    implements SatisfiedPresent, Copyable<GlobalCardinality> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The counted variables. */
  private final IntVar[] list;

  /** The counted values, in increasing order. */
  private final int[] values;

  /** Whether the bounds of the values are fixed instead of given by counters. */
  private final boolean fixedBounds;

  /** The counter of each value of values, empty when the bounds are fixed. */
  private final IntVar[] counters;

  /** The fixed lower and upper bounds of each value, empty when there are counters. */
  private final int[] fixedLow;

  private final int[] fixedUp;

  /** The counted values as a domain. */
  private final IntervalDomain valuesDomain;

  // node numbering: variables 0..n-1, values n..n+m-1, the uncounted values n+m, the sink n+m+1
  private final int n;
  private final int m;

  // values[valueIndexOffset[v - minValue]] == v, or null if binary search is used
  private final int[] valueIndexOffset;
  private final int minValue;

  // bounds of the values (m is the uncounted values), read from the counters at each round, and the
  // capacities left for the variables that are not fixed
  private final int[] low;
  private final int[] up;
  private final int[] capLow;
  private final int[] capUp;

  // the feasible flow: the value of each variable (-1 if none), the number of variables of each
  // value and doubly linked lists of the variables of each value; it is not trailed
  private final int[] varMatch;
  private final int[] flow;
  private final int[] head;
  private final int[] next;
  private final int[] prev;

  // the values (indexes) each variable that is not fixed can take, m for an uncounted value, and
  // the reverse lists; a fixed variable has no values and is not in the flow
  private final int[] adjStart;
  private int[] adj;
  private final int[] revStart;
  private int[] rev;
  private final int[] revFill;

  // number of variables fixed to each value and number of variables not fixed that can take it
  private final int[] fixed;
  private final int[] possible;

  // augmenting path search
  private final int[] queue;
  private final int[] visited;
  private final int[] pred;
  private final int[] moveTo;
  private int generation;

  // arcs of the value graph and Tarjan algorithm over the values and the sink
  private final int[] valueAdjStart;
  private int[] valueAdj;
  private final int[] dfsNumber;
  private final int[] lowLink;
  private final int[] component;
  private final int[] cursor;
  private final int[] callStack;
  private final int[] sccStack;
  private final boolean[] onStack;

  /**
   * It constructs a global cardinality constraint with variable counters.
   *
   * @param list the counted variables.
   * @param values the counted values, without repetitions.
   * @param counters counters[i] is the number of variables equal to values[i].
   */
  public GlobalCardinality(IntVar[] list, int[] values, IntVar[] counters) {
    this(list, values, counters, new int[0], new int[0], false);
  }

  /**
   * It constructs a global cardinality constraint with fixed bounds.
   *
   * @param list the counted variables.
   * @param values the counted values, without repetitions.
   * @param low low[i] is the smallest number of variables equal to values[i].
   * @param up up[i] is the largest number of variables equal to values[i].
   */
  public GlobalCardinality(IntVar[] list, int[] values, int[] low, int[] up) {
    this(list, values, new IntVar[0], low, up, true);
  }

  /**
   * It constructs a global cardinality constraint with variable counters.
   *
   * @param list the counted variables.
   * @param values the counted values, without repetitions.
   * @param counters counters[i] is the number of variables equal to values[i].
   */
  public GlobalCardinality(List<? extends IntVar> list, int[] values, IntVar[] counters) {
    this(list.toArray(new IntVar[0]), values, counters);
  }

  private GlobalCardinality(
      IntVar[] list, int[] values, IntVar[] counters, int[] low, int[] up, boolean fixedBounds) {

    checkInputForNullness("list", list);
    checkInputForNullness("values", values);
    int length = values.length;
    if (!fixedBounds) {
      checkInputForNullness("counters", counters);
      if (counters.length != length) {
        throw new IllegalArgumentException(
            "Constraint GlobalCardinality has "
                + counters.length
                + " counters for "
                + length
                + " values.");
      }
    } else {
      checkInputForNullness("low", low);
      checkInputForNullness("up", up);
      if (low.length != length || up.length != length) {
        throw new IllegalArgumentException(
            "Constraint GlobalCardinality needs one lower and one upper bound for each value.");
      }
    }

    queueIndex = 2;
    numberId = idNumber.incrementAndGet();

    this.list = Arrays.copyOf(list, list.length);

    // values are kept sorted, with their counters or bounds
    Integer[] order = new Integer[length];
    for (int i = 0; i < length; i++) {
      order[i] = i;
    }
    Arrays.sort(order, (a, b) -> Integer.compare(values[a], values[b]));
    this.fixedBounds = fixedBounds;
    this.values = new int[length];
    this.counters = new IntVar[fixedBounds ? 0 : length];
    this.fixedLow = new int[fixedBounds ? length : 0];
    this.fixedUp = new int[fixedBounds ? length : 0];
    for (int i = 0; i < length; i++) {
      int k = order[i];
      this.values[i] = values[k];
      if (i > 0 && this.values[i] == this.values[i - 1]) {
        throw new IllegalArgumentException(
            "Constraint GlobalCardinality has value " + values[k] + " twice.");
      }
      if (!fixedBounds) {
        this.counters[i] = counters[k];
      } else {
        this.fixedLow[i] = low[k];
        this.fixedUp[i] = up[k];
      }
    }

    valuesDomain = new IntervalDomain();
    for (int v : this.values) {
      valuesDomain.unionAdapt(v, v);
    }

    n = list.length;
    m = length;
    if (m > 0 && (long) this.values[m - 1] - this.values[0] + 1 <= 4L * m + 64) {
      minValue = this.values[0];
      valueIndexOffset = new int[this.values[m - 1] - minValue + 1];
      Arrays.fill(valueIndexOffset, -1);
      for (int a = 0; a < m; a++) {
        valueIndexOffset[this.values[a] - minValue] = a;
      }
    } else {
      minValue = 0;
      valueIndexOffset = null;
    }
    this.low = new int[m + 1];
    this.up = new int[m + 1];
    capLow = new int[m + 1];
    capUp = new int[m + 1];
    varMatch = new int[n];
    Arrays.fill(varMatch, -1);
    flow = new int[m + 1];
    head = new int[m + 1];
    Arrays.fill(head, -1);
    next = new int[n];
    prev = new int[n];
    adjStart = new int[n + 1];
    adj = new int[Math.max(4, n)];
    revStart = new int[m + 2];
    rev = new int[Math.max(4, n)];
    revFill = new int[m + 1];
    fixed = new int[m + 1];
    possible = new int[m + 1];

    int nodes = n + m + 2;
    queue = new int[nodes];
    visited = new int[nodes];
    pred = new int[nodes];
    moveTo = new int[n];
    valueAdjStart = new int[m + 2];
    valueAdj = new int[Math.max(4, m + 1)];
    dfsNumber = new int[nodes];
    lowLink = new int[nodes];
    component = new int[nodes];
    cursor = new int[nodes];
    callStack = new int[nodes];
    sccStack = new int[nodes];
    onStack = new boolean[nodes];

    if (fixedBounds) {
      setScope(this.list);
    } else {
      setScope(Stream.concat(Arrays.stream(this.list), Arrays.stream(this.counters)));
    }
  }

  @Override
  public int getConsistencyPruningEvent(Var var) {
    Integer event = getConsistencyPruningEventFromMap(var);
    if (event != null) {
      return event;
    }
    for (IntVar v : list) {
      if (v == var) {
        return IntDomain.ANY;
      }
    }
    return IntDomain.BOUND;
  }

  @Override
  public void consistency(Store store) {

    boolean full = true;
    while (true) {
      boolean capacitiesChanged = readCapacities();
      buildAdjacency();
      boolean countersChanged = pruneCounters(store);
      if (!full && !capacitiesChanged && !countersChanged) {
        // only this execution's own pruning of the list happened since the last round, and the
        // filtering is idempotent for unchanged capacities
        return;
      }
      if (countersChanged) {
        full = true;
        continue;
      }
      if (!repairFlow()) {
        throw Store.failException;
      }
      if (computeComponents() == 1 || !prune(store)) {
        return;
      }
      full = false;
    }
  }

  /** It reads the capacities of the values and tells whether they changed. */
  private boolean readCapacities() {
    boolean changed = false;
    for (int a = 0; a < m; a++) {
      int l = fixedBounds ? fixedLow[a] : counters[a].min();
      int u = fixedBounds ? fixedUp[a] : counters[a].max();
      if (l != low[a] || u != up[a]) {
        low[a] = l;
        up[a] = u;
        changed = true;
      }
    }
    low[m] = 0;
    up[m] = n;
    return changed;
  }

  /** It builds the value lists of the variables, their reverse lists and the value counts. */
  private void buildAdjacency() {
    Arrays.fill(fixed, 0);
    Arrays.fill(possible, 0);
    int size = 0;
    for (int i = 0; i < n; i++) {
      adjStart[i] = size;
      IntDomain d = list[i].dom();
      if (d.singleton()) {
        int a = index(d.min());
        fixed[a < 0 ? m : a]++;
        if (varMatch[i] >= 0) {
          match(i, -1);
        }
        continue;
      }
      int domainSize = d.getSize();
      int inValues = 0;
      if (domainSize <= m) {
        for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
          int a = index(e.nextElement());
          if (a >= 0) {
            size = add(size, a);
            inValues++;
          }
        }
      } else {
        int from = lowerIndex(d.min());
        int to = lowerIndex(d.max() + 1L);
        for (int a = from; a < to; a++) {
          if (d.contains(values[a])) {
            size = add(size, a);
            inValues++;
          }
        }
      }
      if (inValues < domainSize) {
        size = add(size, m);
      }
    }
    adjStart[n] = size;

    // reverse lists: the variables that can take each value
    if (rev.length < size) {
      rev = new int[Math.max(size, 2 * rev.length)];
    }
    int start = 0;
    for (int a = 0; a <= m; a++) {
      revStart[a] = start;
      revFill[a] = start;
      start += possible[a];
    }
    revStart[m + 1] = start;
    for (int i = 0; i < n; i++) {
      for (int k = adjStart[i]; k < adjStart[i + 1]; k++) {
        rev[revFill[adj[k]]++] = i;
      }
    }
  }

  private int add(int size, int a) {
    if (size == adj.length) {
      adj = Arrays.copyOf(adj, 2 * size);
    }
    adj[size] = a;
    possible[a]++;
    return size + 1;
  }

  /** It returns the index of value v, or -1 if v is not counted. */
  private int index(int v) {
    if (valueIndexOffset != null) {
      long k = (long) v - minValue;
      return k >= 0 && k < valueIndexOffset.length ? valueIndexOffset[(int) k] : -1;
    }
    int a = Arrays.binarySearch(values, v);
    return a >= 0 ? a : -1;
  }

  /** It returns the index of the first value not smaller than v. */
  private int lowerIndex(long v) {
    int lo = 0;
    int hi = m;
    while (lo < hi) {
      int mid = (lo + hi) >>> 1;
      if (values[mid] < v) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    return lo;
  }

  /**
   * It prunes the counters by counting and tells whether a counter changed. A counter lies between
   * the number of variables fixed to its value and the number of variables that can take it, and
   * the counters together with the variables taking uncounted values make n.
   */
  private boolean pruneCounters(Store store) {
    long sumLow = 0;
    long sumUp = 0;
    for (int a = 0; a < m; a++) {
      int l = Math.max(low[a], fixed[a]);
      int u = Math.min(up[a], fixed[a] + possible[a]);
      if (l > u) {
        throw Store.failException;
      }
      sumLow += l;
      sumUp += u;
    }
    // variables that must take a counted value and variables that may take an uncounted one
    int mustCount = n - fixed[m] - possible[m];
    if (sumLow > n || sumUp < mustCount) {
      throw Store.failException;
    }
    if (fixedBounds) {
      return false;
    }
    boolean changed = false;
    for (int a = 0; a < m; a++) {
      int l = Math.max(low[a], fixed[a]);
      int u = Math.min(up[a], fixed[a] + possible[a]);
      long newLow = Math.max(l, mustCount - (sumUp - u));
      long newUp = Math.min(u, n - (sumLow - l));
      if (newLow != low[a] || newUp != up[a]) {
        IntVar c = counters[a];
        c.domain.in(store.level, c, (int) newLow, (int) newUp);
        changed = true;
      }
    }
    return changed;
  }

  private void match(int i, int a) {
    int old = varMatch[i];
    if (old >= 0) {
      flow[old]--;
      if (prev[i] >= 0) {
        next[prev[i]] = next[i];
      } else {
        head[old] = next[i];
      }
      if (next[i] >= 0) {
        prev[next[i]] = prev[i];
      }
    }
    varMatch[i] = a;
    if (a >= 0) {
      flow[a]++;
      prev[i] = -1;
      next[i] = head[a];
      if (head[a] >= 0) {
        prev[head[a]] = i;
      }
      head[a] = i;
    }
  }

  private boolean canTake(int i, int a) {
    int end = adjStart[i + 1];
    if (a == m) {
      // the uncounted values come last
      return end > adjStart[i] && adj[end - 1] == m;
    }
    return end > adjStart[i] && list[i].domain.contains(values[a]);
  }

  /**
   * It makes the kept flow feasible again, or tells that there is no feasible flow. Variables lose
   * values they can no longer take and values above their upper bound lose variables; then every
   * variable gets a value within the upper bounds, and values below their lower bounds take
   * variables from values above theirs.
   */
  private boolean repairFlow() {
    // the fixed variables are not in the flow, so they take their part of the bounds
    for (int a = 0; a <= m; a++) {
      capLow[a] = Math.max(0, low[a] - fixed[a]);
      capUp[a] = up[a] - fixed[a];
    }
    for (int i = 0; i < n; i++) {
      int a = varMatch[i];
      if (a >= 0 && !canTake(i, a)) {
        match(i, -1);
      }
    }
    for (int a = 0; a <= m; a++) {
      while (flow[a] > capUp[a]) {
        match(head[a], -1);
      }
    }
    for (int i = 0; i < n; i++) {
      if (varMatch[i] < 0 && adjStart[i] < adjStart[i + 1] && !augmentVariable(i)) {
        return false;
      }
    }
    for (int a = 0; a < m; a++) {
      while (flow[a] < capLow[a]) {
        if (!augmentValue(a)) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * It gives variable start a value by an augmenting path: a variable moves to a value below its
   * upper bound, or to a full value whose variables move on.
   */
  private boolean augmentVariable(int start) {
    generation++;
    int qHead = 0;
    int qTail = 0;
    queue[qTail++] = start;
    visited[start] = generation;
    while (qHead < qTail) {
      int i = queue[qHead++];
      for (int k = adjStart[i]; k < adjStart[i + 1]; k++) {
        int a = adj[k];
        int node = n + a;
        if (a == varMatch[i] || visited[node] == generation) {
          continue;
        }
        visited[node] = generation;
        pred[node] = i;
        if (flow[a] < capUp[a]) {
          // move every variable of the path one value on
          while (true) {
            int j = pred[n + a];
            int old = varMatch[j];
            match(j, a);
            if (j == start) {
              return true;
            }
            a = old;
          }
        }
        for (int j = head[a]; j >= 0; j = next[j]) {
          if (visited[j] != generation) {
            visited[j] = generation;
            queue[qTail++] = j;
          }
        }
      }
    }
    return false;
  }

  /**
   * It raises the flow of value start, below its lower bound, by an augmenting path: a variable
   * that can take start leaves a value above its lower bound, or leaves a value that takes another
   * variable in turn.
   */
  private boolean augmentValue(int start) {
    generation++;
    int qHead = 0;
    int qTail = 0;
    queue[qTail++] = n + start;
    visited[n + start] = generation;
    while (qHead < qTail) {
      int b = queue[qHead++] - n;
      for (int k = revStart[b]; k < revStart[b + 1]; k++) {
        int j = rev[k];
        int c = varMatch[j];
        int node = n + c;
        if (c == b || visited[node] == generation) {
          continue;
        }
        visited[node] = generation;
        pred[node] = j;
        moveTo[j] = b;
        if (flow[c] > capLow[c]) {
          while (true) {
            int i = pred[n + c];
            int target = moveTo[i];
            match(i, target);
            if (target == start) {
              return true;
            }
            c = target;
          }
        }
        queue[qTail++] = node;
      }
    }
    return false;
  }

  /**
   * It computes the strongly connected components of the residual graph, projected on the values.
   * In the residual graph a value leads to its variables, a variable to the other values it can
   * take, a value to the sink below its upper capacity and the sink to the values above their lower
   * capacity. A variable has one incoming arc, from its value, so the graph is reduced to the
   * values and the sink, with an arc from a to b when a variable of a can take b. A variable lies
   * in the component of its value exactly when it can take another value of that component;
   * otherwise it is a component of its own.
   *
   * @return the number of components.
   */
  private int computeComponents() {
    // arcs between values, without repetitions
    int size = 0;
    generation++;
    for (int a = 0; a <= m; a++) {
      valueAdjStart[a] = size;
      generation++;
      for (int i = head[a]; i >= 0; i = next[i]) {
        for (int k = adjStart[i]; k < adjStart[i + 1]; k++) {
          int b = adj[k];
          if (b != a && visited[b] != generation) {
            visited[b] = generation;
            if (size == valueAdj.length) {
              valueAdj = Arrays.copyOf(valueAdj, 2 * size);
            }
            valueAdj[size++] = b;
          }
        }
      }
    }
    valueAdjStart[m + 1] = size;

    int nodes = m + 2;
    int sink = m + 1;
    Arrays.fill(dfsNumber, 0, nodes, 0);
    int counter = 0;
    int components = 0;
    int sccTop = 0;
    for (int root = 0; root < nodes; root++) {
      if (dfsNumber[root] != 0) {
        continue;
      }
      int callTop = 0;
      callStack[callTop++] = root;
      dfsNumber[root] = lowLink[root] = ++counter;
      sccStack[sccTop++] = root;
      onStack[root] = true;
      cursor[root] = root == sink ? 0 : valueAdjStart[root];
      while (callTop > 0) {
        int v = callStack[callTop - 1];
        int w = nextEdge(v, sink);
        if (w >= 0) {
          if (dfsNumber[w] == 0) {
            dfsNumber[w] = lowLink[w] = ++counter;
            sccStack[sccTop++] = w;
            onStack[w] = true;
            cursor[w] = w == sink ? 0 : valueAdjStart[w];
            callStack[callTop++] = w;
          } else if (onStack[w] && dfsNumber[w] < lowLink[v]) {
            lowLink[v] = dfsNumber[w];
          }
          continue;
        }
        callTop--;
        if (lowLink[v] == dfsNumber[v]) {
          int u;
          do {
            u = sccStack[--sccTop];
            onStack[u] = false;
            component[u] = components;
          } while (u != v);
          components++;
        }
        if (callTop > 0) {
          int parent = callStack[callTop - 1];
          if (lowLink[v] < lowLink[parent]) {
            lowLink[parent] = lowLink[v];
          }
        }
      }
    }
    return components;
  }

  /** It returns the next neighbour of node v of the value graph, advancing its cursor, or -1. */
  private int nextEdge(int v, int sink) {
    if (v < sink) {
      int c = cursor[v];
      if (c < valueAdjStart[v + 1]) {
        cursor[v] = c + 1;
        return valueAdj[c];
      }
      if (c == valueAdjStart[v + 1]) {
        cursor[v] = c + 1;
        if (flow[v] < capUp[v]) {
          return sink;
        }
      }
      return -1;
    }
    while (cursor[v] <= m) {
      int a = cursor[v]++;
      if (flow[a] > capLow[a]) {
        return a;
      }
    }
    return -1;
  }

  /**
   * It removes the values outside the component of their variable and tells if it removed any. A
   * variable that can take no other value of the component of its value is fixed to its value.
   */
  private boolean prune(Store store) {
    boolean pruned = false;
    for (int i = 0; i < n; i++) {
      int matched = varMatch[i];
      if (matched < 0) {
        continue;
      }
      int ci = component[matched];
      boolean inComponent = false;
      int outside = 0;
      for (int k = adjStart[i]; k < adjStart[i + 1]; k++) {
        int a = adj[k];
        if (a != matched) {
          if (component[a] == ci) {
            inComponent = true;
          } else {
            outside++;
          }
        }
      }
      if (outside == 0) {
        continue;
      }
      pruned = true;
      IntVar x = list[i];
      if (!inComponent) {
        if (matched == m) {
          x.domain.in(store.level, x, x.dom().subtract(valuesDomain));
        } else {
          x.domain.in(store.level, x, values[matched], values[matched]);
        }
        continue;
      }
      int removed = -1;
      IntervalDomain removedValues = null;
      boolean removeUncounted = false;
      for (int k = adjStart[i]; k < adjStart[i + 1]; k++) {
        int a = adj[k];
        if (a == matched || component[a] == ci) {
          continue;
        }
        if (a == m) {
          removeUncounted = true;
        } else if (removed < 0) {
          removed = values[a];
        } else {
          if (removedValues == null) {
            removedValues = new IntervalDomain();
            removedValues.unionAdapt(removed, removed);
          }
          removedValues.unionAdapt(values[a], values[a]);
        }
      }
      if (removeUncounted) {
        x.domain.in(store.level, x, valuesDomain);
      }
      if (removedValues != null) {
        x.domain.in(store.level, x, x.dom().subtract(removedValues));
      } else if (removed >= 0) {
        x.domain.inComplement(store.level, x, removed);
      }
    }
    return pruned;
  }

  @Override
  public boolean satisfied() {
    int[] count = new int[m];
    for (IntVar x : list) {
      if (!x.singleton()) {
        return false;
      }
      int a = Arrays.binarySearch(values, x.value());
      if (a >= 0) {
        count[a]++;
      }
    }
    for (int a = 0; a < m; a++) {
      if (fixedBounds) {
        if (count[a] < fixedLow[a] || count[a] > fixedUp[a]) {
          return false;
        }
      } else if (!counters[a].singleton(count[a])) {
        return false;
      }
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder buf = new StringBuilder(id());
    buf.append(" : GlobalCardinality(").append(Arrays.asList(list));
    buf.append(", ").append(Arrays.toString(values));
    if (!fixedBounds) {
      buf.append(", ").append(Arrays.asList(counters));
    } else {
      buf.append(", ").append(Arrays.toString(fixedLow));
      buf.append(", ").append(Arrays.toString(fixedUp));
    }
    return buf.append(")").toString();
  }

  @Override
  public GlobalCardinality copy(VarMap map) {
    return fixedBounds
        ? new GlobalCardinality(map.get(list), values, fixedLow, fixedUp)
        : new GlobalCardinality(map.get(list), values, map.get(counters));
  }
}
