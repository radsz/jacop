/*
 * AllDisjoint.java
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

package org.jacop.set.constraints;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * All-disjoint constraint over set variables: the sets s[0], ..., s[n-1] are pairwise disjoint.
 *
 * <p>Besides the pairwise reasoning of {@link AdisjointB} (an element of one lower bound leaves the
 * upper bounds of the other sets) it uses the cardinalities of the sets, which the pairwise
 * decomposition cannot. Following Bessiere, Hebrard, Hnich and Walsh ("Disjoint, partition and
 * intersection constraints for set and multiset variables", CP 2004), every element of the upper
 * bounds is a dual variable whose value is the set that takes it, or a dummy set when no set takes
 * it. The cardinality bounds of the sets become the count bounds of a global cardinality constraint
 * on these dual variables, and domain consistency on it (a feasible flow and the strongly connected
 * components of its residual graph, as in Regin's GCC) gives bounds consistency on the sets: an
 * element leaves the upper bound of a set when no assignment that meets the cardinalities gives it
 * to that set, and joins its lower bound when every such assignment does. The paper proves this for
 * fixed cardinalities (FCDisjoint); here a cardinality is the interval of the set's cardinality
 * domain. In addition, the cardinality of each set is bounded by the size of the union of the upper
 * bounds minus the minimal cardinalities of the other sets.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class AllDisjoint extends Constraint implements SatisfiedPresent, Copyable<AllDisjoint> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The sets that are pairwise disjoint. */
  final SetVar[] s;

  final int n;

  /** Every element of the initial upper bounds, sorted; dual variables are indexed by position. */
  private final int[] values;

  /**
   * The set (0..n-1) or the dummy set (n) each element was given in the last feasible assignment.
   * It is not trailed: a stale entry is only a starting point and is repaired on the next call.
   */
  private final int[] match;

  /** Position of each element in values, by element minus values[0], when the range is small. */
  private final int[] position;

  private final int[] owner;
  private final int[] load;
  private final int[] low;
  private final int[] high;

  // Candidate elements of each set (lub minus glb) in compressed rows, and the sets of each
  // element.
  private final int[] candStart;
  private int[] cand;
  private final int[] elemStart;
  private int[] elemSets;
  private final int[] elemFill;

  // Breadth-first search over sets for augmenting paths.
  private final int[] queue;
  private final int[] prevSet;
  private final int[] viaElem;
  private final int[] visited;
  private int stamp;

  // Tarjan's strongly connected components on the residual graph.
  private final int[] index;
  private final int[] lowLink;
  private final int[] comp;
  private final int[] stack;
  private final boolean[] onStack;
  private final int[] callStack;
  private final int[] edgePos;

  /**
   * It constructs an all-disjoint constraint.
   *
   * @param s set variables that are pairwise disjoint.
   */
  public AllDisjoint(SetVar[] s) {

    checkInputForNullness("s", s);

    numberId = idNumber.incrementAndGet();

    this.s = Arrays.copyOf(s, s.length);
    this.n = s.length;

    IntDomain all = new IntervalDomain();
    for (SetVar v : s) {
      all = all.union(v.domain.lub());
    }
    values = new int[all.getSize()];
    int k = 0;
    for (ValueEnumeration e = all.valueEnumeration(); e.hasMoreElements(); ) {
      values[k++] = e.nextElement();
    }
    int d = values.length;
    long range = d == 0 ? 0 : (long) values[d - 1] - values[0] + 1;
    if (d > 0 && range <= 4L * d + 64) {
      position = new int[(int) range];
      Arrays.fill(position, -1);
      for (int i = 0; i < d; i++) {
        position[values[i] - values[0]] = i;
      }
    } else {
      position = null;
    }

    match = new int[d];
    Arrays.fill(match, n);
    owner = new int[d];
    load = new int[n + 1];
    low = new int[n + 1];
    high = new int[n + 1];
    candStart = new int[n + 1];
    cand = new int[16];
    elemStart = new int[d + 1];
    elemSets = new int[16];
    elemFill = new int[d];
    queue = new int[n + 1];
    prevSet = new int[n + 1];
    viaElem = new int[n + 1];
    visited = new int[n + 1];

    int nodes = d + n + 2;
    index = new int[nodes];
    lowLink = new int[nodes];
    comp = new int[nodes];
    stack = new int[nodes];
    onStack = new boolean[nodes];
    callStack = new int[nodes];
    edgePos = new int[nodes];

    setScope(this.s);
  }

  @Override
  public void consistency(Store store) {
    // Pruning a set changes what the others may take, and the store does not re-queue this
    // constraint for its own changes, so iterate to a fixpoint. The pruning of the assignment
    // keeps it feasible and leaves no further pruning of its own, so it is redone only after the
    // other rules change a domain.
    boolean assignmentDone = false;
    do {
      store.propagationHasOccurred = false;
      boolean needsAssignment = propagate(store);
      if (store.propagationHasOccurred) {
        assignmentDone = false;
      } else if (needsAssignment && !assignmentDone) {
        findAssignment();
        prune(store);
        assignmentDone = true;
      }
    } while (store.propagationHasOccurred);
  }

  private int elementIndex(int value) {
    return position != null ? position[value - values[0]] : Arrays.binarySearch(values, value);
  }

  /**
   * Applies the pairwise rule and the cardinality bound, and prepares the candidates of the
   * assignment.
   *
   * @return true when some set must still take elements, so the assignment can prune.
   */
  private boolean propagate(Store store) {

    int d = values.length;

    // An element of a lower bound belongs to that set only.
    Arrays.fill(owner, -1);
    for (int i = 0; i < n; i++) {
      for (ValueEnumeration e = s[i].domain.glb().valueEnumeration(); e.hasMoreElements(); ) {
        int k = elementIndex(e.nextElement());
        if (owner[k] >= 0) {
          throw Store.failException;
        }
        owner[k] = i;
      }
    }
    for (int i = 0; i < n; i++) {
      SetDomain dom = s[i].domain;
      if (dom.lub().getSize() == dom.glb().getSize()) {
        continue;
      }
      IntDomain taken = null;
      for (ValueEnumeration e = dom.lub().valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        int o = owner[elementIndex(v)];
        if (o >= 0 && o != i) {
          if (taken == null) {
            taken = new IntervalDomain();
          }
          taken.unionAdapt(v, v);
        }
      }
      if (taken != null) {
        dom.inLub(store.level, s[i], dom.lub().subtract(taken));
      }
    }
    if (store.propagationHasOccurred) {
      return false;
    }

    // Candidate elements of each set: its upper bound minus its lower bound. After the pruning
    // above, all of them are free (in no lower bound).
    Arrays.fill(elemFill, 0);
    int total = 0;
    int sumLow = 0;
    for (int i = 0; i < n; i++) {
      SetDomain dom = s[i].domain;
      int glbSize = dom.glb().getSize();
      low[i] = dom.card().min() - glbSize;
      high[i] = dom.card().max() - glbSize;
      sumLow += Math.max(0, low[i]);
      candStart[i] = total;
      total += dom.lub().getSize() - glbSize;
    }
    candStart[n] = total;
    if (cand.length < total) {
      cand = new int[Math.max(total, 2 * cand.length)];
      elemSets = new int[cand.length];
    }
    for (int i = 0; i < n; i++) {
      SetDomain dom = s[i].domain;
      int p = candStart[i];
      for (ValueEnumeration e = dom.lub().valueEnumeration(); e.hasMoreElements(); ) {
        int k = elementIndex(e.nextElement());
        if (owner[k] != i) {
          cand[p++] = k;
          elemFill[k]++;
        }
      }
    }

    // Disjoint sets fit in the union of the upper bounds.
    int free = 0;
    for (int k = 0; k < d; k++) {
      if (elemFill[k] > 0) {
        free++;
      }
    }
    int sumCardMin = 0;
    int union = free;
    for (int i = 0; i < n; i++) {
      sumCardMin += s[i].domain.card().min();
      union += s[i].domain.glb().getSize();
    }
    if (sumCardMin > union) {
      throw Store.failException;
    }
    for (int i = 0; i < n; i++) {
      IntDomain card = s[i].domain.card();
      int max = union - sumCardMin + card.min();
      if (max < card.max()) {
        s[i].domain.inCardinality(store.level, s[i], card.min(), max);
      }
    }
    if (store.propagationHasOccurred || sumLow == 0) {
      // With no cardinality to reach, the dummy set takes every free element and no other
      // assignment is constrained.
      return false;
    }

    elemStart[0] = 0;
    for (int k = 0; k < d; k++) {
      elemStart[k + 1] = elemStart[k] + elemFill[k];
      elemFill[k] = elemStart[k];
    }
    for (int i = 0; i < n; i++) {
      for (int p = candStart[i]; p < candStart[i + 1]; p++) {
        elemSets[elemFill[cand[p]]++] = i;
      }
    }
    return true;
  }

  /**
   * Gives each set at least low[i] and at most high[i] of its candidates, the rest to the dummy.
   */
  private void findAssignment() {
    int d = values.length;
    Arrays.fill(load, 0);
    for (int k = 0; k < d; k++) {
      if (elemStart[k] == elemStart[k + 1]) {
        match[k] = -1;
        continue;
      }
      int j = match[k];
      if (j >= 0 && j < n && load[j] < high[j] && isCandidate(k, j)) {
        load[j]++;
      } else {
        match[k] = n;
        load[n]++;
      }
    }
    for (int j = 0; j < n; j++) {
      while (load[j] < low[j]) {
        if (!augment(j)) {
          throw Store.failException;
        }
      }
    }
  }

  private boolean isCandidate(int k, int j) {
    for (int p = elemStart[k]; p < elemStart[k + 1]; p++) {
      if (elemSets[p] == j) {
        return true;
      }
    }
    return false;
  }

  /**
   * Finds an alternating path that gives set j one more element: j takes an element from a set that
   * takes one from another, and so on, until the dummy or a set above its minimum gives one.
   */
  private boolean augment(int j) {
    stamp++;
    int head = 0;
    int tail = 0;
    queue[tail++] = j;
    visited[j] = stamp;
    while (head < tail) {
      int x = queue[head++];
      for (int p = candStart[x]; p < candStart[x + 1]; p++) {
        int k = cand[p];
        int y = match[k];
        if (y == x) {
          continue;
        }
        if (y == n || load[y] > low[y]) {
          load[y]--;
          // x takes k; then every set on the path takes the element its successor gave up.
          match[k] = x;
          while (x != j) {
            int via = viaElem[x];
            int prev = prevSet[x];
            match[via] = prev;
            x = prev;
          }
          load[j]++;
          return true;
        }
        if (visited[y] != stamp) {
          visited[y] = stamp;
          prevSet[y] = x;
          viaElem[y] = k;
          queue[tail++] = y;
        }
      }
    }
    return false;
  }

  /*
   * Residual graph of the assignment, as in Regin's GCC: node k for element k, d + j for set j,
   * d + n for the dummy set and d + n + 1 for the sink. An element points to every set it may
   * take but does not, its set points to it; a set points to the sink while it is below its
   * maximum and the sink points to it while it is above its minimum. An element may go to a set it
   * does not take exactly when both are in the same strongly connected component.
   */
  private int successors(int node, int pos) {
    int d = values.length;
    int sink = d + n + 1;
    if (node < d) {
      int k = node;
      int from = elemStart[k];
      int count = elemStart[k + 1] - from;
      // positions 0..count-1: sets, count: the dummy
      while (pos < count) {
        int j = elemSets[from + pos];
        if (match[k] != j) {
          return pos;
        }
        pos++;
      }
      if (pos == count && match[k] != n) {
        return pos;
      }
      return -1;
    }
    if (node < sink) {
      int j = node - d;
      int from = j < n ? candStart[j] : 0;
      int count = j < n ? candStart[j + 1] - from : d;
      while (pos < count) {
        int k = j < n ? cand[from + pos] : pos;
        if (match[k] == j) {
          return pos;
        }
        pos++;
      }
      if (pos == count && (j == n || load[j] < high[j])) {
        return pos;
      }
      return -1;
    }
    while (pos <= n) {
      if (pos == n ? load[n] > 0 : load[pos] > low[pos]) {
        return pos;
      }
      pos++;
    }
    return -1;
  }

  private int target(int node, int pos) {
    int d = values.length;
    int sink = d + n + 1;
    if (node < d) {
      int count = elemStart[node + 1] - elemStart[node];
      return pos < count ? d + elemSets[elemStart[node] + pos] : d + n;
    }
    if (node < sink) {
      int j = node - d;
      int count = j < n ? candStart[j + 1] - candStart[j] : d;
      if (pos < count) {
        return j < n ? cand[candStart[j] + pos] : pos;
      }
      return sink;
    }
    return d + pos;
  }

  private void components() {
    int nodes = values.length + n + 2;
    Arrays.fill(index, -1);
    int counter = 0;
    int top = 0;
    int compCount = 0;
    for (int root = 0; root < nodes; root++) {
      if (index[root] >= 0) {
        continue;
      }
      int depth = 0;
      callStack[depth] = root;
      edgePos[root] = 0;
      index[root] = lowLink[root] = counter++;
      stack[top++] = root;
      onStack[root] = true;
      while (depth >= 0) {
        int v = callStack[depth];
        int pos = successors(v, edgePos[v]);
        if (pos >= 0) {
          edgePos[v] = pos + 1;
          int w = target(v, pos);
          if (index[w] < 0) {
            index[w] = lowLink[w] = counter++;
            stack[top++] = w;
            onStack[w] = true;
            edgePos[w] = 0;
            callStack[++depth] = w;
          } else if (onStack[w] && index[w] < lowLink[v]) {
            lowLink[v] = index[w];
          }
        } else {
          if (lowLink[v] == index[v]) {
            int w;
            do {
              w = stack[--top];
              onStack[w] = false;
              comp[w] = compCount;
            } while (w != v);
            compCount++;
          }
          depth--;
          if (depth >= 0) {
            int u = callStack[depth];
            if (lowLink[v] < lowLink[u]) {
              lowLink[u] = lowLink[v];
            }
          }
        }
      }
    }
  }

  private void prune(Store store) {
    int d = values.length;
    components();
    int dummy = d + n;
    for (int j = 0; j < n; j++) {
      IntDomain removed = null;
      for (int p = candStart[j]; p < candStart[j + 1]; p++) {
        int k = cand[p];
        if (match[k] != j && comp[k] != comp[d + j]) {
          if (removed == null) {
            removed = new IntervalDomain();
          }
          removed.unionAdapt(values[k], values[k]);
        }
      }
      if (removed != null) {
        s[j].domain.inLub(store.level, s[j], s[j].domain.lub().subtract(removed));
      }
    }
    for (int k = 0; k < d; k++) {
      int j = match[k];
      if (j < 0 || j == n || comp[k] == comp[dummy]) {
        continue;
      }
      boolean forced = true;
      for (int p = elemStart[k]; p < elemStart[k + 1]; p++) {
        int other = elemSets[p];
        if (other != j && comp[k] == comp[d + other]) {
          forced = false;
          break;
        }
      }
      if (forced) {
        s[j].domain.inGlb(store.level, s[j], values[k]);
      }
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return SetDomain.ANY;
  }

  @Override
  public boolean satisfied() {
    int sum = 0;
    IntDomain all = new IntervalDomain();
    for (SetVar v : s) {
      IntDomain lub = v.domain.lub();
      sum += lub.getSize();
      all = all.union(lub);
    }
    return all.getSize() == sum;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : AllDisjoint([");
    for (int i = 0; i < n; i++) {
      result.append(s[i]);
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("])");
    return result.toString();
  }

  @Override
  public AllDisjoint copy(VarMap map) {
    return new AllDisjoint(map.get(s));
  }
}
