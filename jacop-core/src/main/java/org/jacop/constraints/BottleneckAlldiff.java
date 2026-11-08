/*
 * BottleneckAlldiff.java
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
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Bottleneck all different: the variables {@code x[i]} take pairwise different values and {@code z
 * >= max_i cost[i][x[i] - offset]}. A value v of x[i] is allowed only when {@code 0 <= v - offset <
 * cost[i].length}. Minimising z gives the bottleneck (min-max) assignment problem.
 *
 * <p>Posted as an all different constraint and one element constraint per variable under a maximum,
 * the parts are independent: the lower bound of z is the largest of the smallest costs of the
 * variables, which ignores that two variables cannot take the same cheap value. Here the lower
 * bound of z is the bottleneck value of the bipartite graph of the domains: the smallest threshold
 * t such that the edges of cost at most t still hold a matching of all variables. It is computed by
 * the threshold method of Gabow and Tarjan: keep a maximum matching of the edges up to t, and when
 * the search for an augmenting path of a free variable fails, its alternating tree is a Hall set
 * whose cheapest edge out of the tree is the next threshold that can help, which is a lower bound
 * of the bottleneck value (Hall's theorem). The matching of the last call is kept as the start of
 * the next one, so a call usually needs a few augmenting paths only.
 *
 * <p>The values of cost above max(z) are removed, and the values without a support are removed as
 * in Régin's filtering of all different on the graph of the edges up to max(z): a value is kept
 * when its edge is in the matching, lies on an alternating cycle (both ends in one strongly
 * connected component), or starts an alternating path to a free value. The constraint is then
 * domain consistent on x and z (every value of z from the bottleneck value up has a support).
 *
 * <p>Explanations for lazy clause generation are Hall sets (Downing, Feydy and Stuckey): a set S of
 * variables whose edges up to a threshold reach only |S| - 1 values. The bound z >= t + 1 is
 * explained by the removed values of S of cost at most t; a failure, and a value of x[i] that no
 * matching of the other variables leaves free, by the removed values of the Hall set and an upper
 * bound of z below the cheapest edge left out by cost.
 *
 * <p>References:
 *
 * <ul>
 *   <li>Harold N. Gabow and Robert E. Tarjan. Algorithms for two bottleneck optimization problems.
 *       Journal of Algorithms 9(3), pages 411-417, 1988. doi: 10.1016/0196-6774(88)90031-4
 *   <li>Philip Hall. On representatives of subsets. Journal of the London Mathematical Society
 *       10(1), pages 26-30, 1935.
 *   <li>Jean-Charles Régin. A filtering algorithm for constraints of difference in CSPs. In AAAI
 *       1994, pages 362-367, 1994.
 *   <li>Nicholas Downing, Thibaut Feydy and Peter J. Stuckey. Explaining alldifferent. In ACSC
 *       2012, CRPIT 122, pages 115-124, 2012.
 * </ul>
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class BottleneckAlldiff extends Constraint
    implements SatisfiedPresent, Copyable<BottleneckAlldiff>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The most removed values of one atom explained one by one. */
  private static final int REMOVED_LIMIT = 256;

  /** The variables. */
  final IntVar[] list;

  /** The costs: cost[i][v - offset] is the cost of x[i] = v. */
  final int[][] cost;

  /** The value of cost index 0. */
  final int offset;

  /** The bound of the largest cost. */
  final IntVar z;

  private final boolean domainConsistent;
  private final int n;
  private final int values;
  private final boolean duplicates;

  // the matching: the value index of each variable and the variable of each value, or -1; kept
  // between calls as a start, checked against the domains, never trailed
  private final int[] varMate;
  private final int[] valMate;

  // the edges of the current graph: those of variable i are adjStart[i] .. adjStart[i + 1] - 1
  private final int[] adjStart;
  private final int[] adjVal;
  private final int[] adjCost;

  // the augmenting path search
  private final int[] varStamp;
  private final int[] valStamp;
  private int stamp;
  private final int[] stackVar;
  private final int[] stackPos;
  private int nextThreshold;

  // the strongly connected components of the alternating graph
  private final int[] index;
  private final int[] low;
  private final int[] component;
  private final boolean[] onStack;
  private final boolean[] reachesFree;
  private final int[] sccStack;
  private final int[] callVar;
  private final int[] callPos;

  /** The number of calls that raised the lower bound of z above what the costs alone give. */
  public long boundsRaised;

  /**
   * It constructs a domain consistent bottleneck all different constraint.
   *
   * @param list the variables
   * @param cost cost[i][v - offset] is the cost of x[i] = v; values out of the row are not allowed
   * @param offset the value of cost index 0
   * @param z the variable that bounds the largest cost from above
   */
  public BottleneckAlldiff(IntVar[] list, int[][] cost, int offset, IntVar z) {
    this(list, cost, offset, z, true);
  }

  /**
   * It constructs a bottleneck all different constraint.
   *
   * @param list the variables
   * @param cost cost[i][v - offset] is the cost of x[i] = v; values out of the row are not allowed
   * @param offset the value of cost index 0
   * @param z the variable that bounds the largest cost from above
   * @param domainConsistent whether the values without a matching support are removed (one strongly
   *     connected components pass per call); otherwise only the bound of z, the costs above max(z)
   *     and the failure are propagated
   */
  public BottleneckAlldiff(
      IntVar[] list, int[][] cost, int offset, IntVar z, boolean domainConsistent) {
    checkInputForNullness("list", list);
    checkInputForNullness("z", new Object[] {z});
    if (cost == null || cost.length != list.length) {
      throw new IllegalArgumentException("BottleneckAlldiff needs one cost row per variable");
    }
    for (int[] row : cost) {
      if (row == null) {
        throw new IllegalArgumentException("BottleneckAlldiff cost rows must not be null");
      }
    }
    for (IntVar x : list) {
      if (x == z) {
        throw new IllegalArgumentException("BottleneckAlldiff z must not be one of the variables");
      }
    }
    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.cost = new int[cost.length][];
    int width = 0;
    int edges = 0;
    for (int i = 0; i < cost.length; i++) {
      this.cost[i] = cost[i].clone();
      width = Math.max(width, cost[i].length);
      edges += cost[i].length;
    }
    this.offset = offset;
    this.z = z;
    this.domainConsistent = domainConsistent;
    this.n = list.length;
    this.values = width;
    this.duplicates = Arrays.stream(list).distinct().count() < n;
    this.varMate = new int[n];
    this.valMate = new int[width];
    Arrays.fill(varMate, -1);
    Arrays.fill(valMate, -1);
    this.adjStart = new int[n + 1];
    this.adjVal = new int[edges];
    this.adjCost = new int[edges];
    this.varStamp = new int[n];
    this.valStamp = new int[width];
    this.stackVar = new int[n + 1];
    this.stackPos = new int[n + 1];
    this.index = new int[n];
    this.low = new int[n];
    this.component = new int[n];
    this.onStack = new boolean[n];
    this.reachesFree = new boolean[n + 1];
    this.sccStack = new int[n];
    this.callVar = new int[n];
    this.callPos = new int[n];
    this.queueIndex = 2;
    IntVar[] scope = Arrays.copyOf(list, n + 1);
    scope[n] = z;
    setScope(scope);
  }

  /**
   * It constructs a domain consistent bottleneck all different constraint whose cost rows start at
   * value 1.
   *
   * @param list the variables
   * @param cost cost[i][v - 1] is the cost of x[i] = v
   * @param z the variable that bounds the largest cost from above
   */
  public BottleneckAlldiff(IntVar[] list, int[][] cost, IntVar z) {
    this(list, cost, 1, z);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }
    return v == z ? IntDomain.BOUND : IntDomain.ANY;
  }

  @Override
  public void consistency(Store store) {
    if (duplicates && n > 1) {
      throw Store.failException;
    }
    if (n == 0) {
      return;
    }
    int zMax = z.max();
    int lower = Integer.MIN_VALUE;
    for (int i = 0; i < n; i++) {
      IntVar x = list[i];
      int[] row = cost[i];
      x.domain.in(store.level, x, offset, offset + row.length - 1);
      int start = i == 0 ? 0 : adjStart[i];
      int k = start;
      int smallest = Integer.MAX_VALUE;
      boolean tooExpensive = false;
      for (ValueEnumeration e = x.domain.valueEnumeration(); e.hasMoreElements(); ) {
        int w = e.nextElement() - offset;
        if (row[w] > zMax) {
          tooExpensive = true;
          continue;
        }
        adjVal[k] = w;
        adjCost[k] = row[w];
        smallest = Math.min(smallest, row[w]);
        k++;
      }
      if (tooExpensive) {
        // removed after the enumeration, which a change of the domain would spoil
        IntervalDomain kept = new IntervalDomain(k - start + 1);
        for (int e = start; e < k; e++) {
          kept.unionAdapt(adjVal[e] + offset, adjVal[e] + offset);
        }
        x.domain.in(store.level, x, kept);
      }
      adjStart[i] = start;
      adjStart[i + 1] = k;
      lower = Math.max(lower, smallest);
    }
    int t = Math.max(lower, z.min());
    int bound = matchUpTo(t, zMax);
    if (bound > z.min()) {
      if (bound > lower) {
        boundsRaised++;
      }
      z.domain.inMin(store.level, z, bound);
    }
    if (domainConsistent) {
      filter(store);
    }
  }

  /**
   * Makes the matching perfect with edges of cost at most a threshold, raised from t as far as
   * needed; fails when even the edges up to max returned by the domains leave a Hall set.
   *
   * @return the threshold reached, the bottleneck value when t is at most it
   */
  private int matchUpTo(int t, int max) {
    for (int i = 0; i < n; i++) {
      int w = varMate[i];
      if (w >= 0 && (valMate[w] != i || !hasEdge(i, w, t))) {
        varMate[i] = -1;
        if (valMate[w] == i) {
          valMate[w] = -1;
        }
      }
    }
    for (int w = 0; w < values; w++) {
      int i = valMate[w];
      if (i >= 0 && varMate[i] != w) {
        valMate[w] = -1;
      }
    }
    for (int i = 0; i < n; i++) {
      if (varMate[i] >= 0) {
        continue;
      }
      while (!augment(i, t, -1)) {
        if (nextThreshold == Integer.MAX_VALUE || nextThreshold > max) {
          throw Store.failException;
        }
        t = nextThreshold;
      }
    }
    return t;
  }

  private boolean hasEdge(int i, int w, int t) {
    for (int k = adjStart[i]; k < adjStart[i + 1]; k++) {
      if (adjVal[k] == w) {
        return adjCost[k] <= t;
      }
    }
    return false;
  }

  /**
   * Searches an augmenting path from the free variable u over edges of cost at most t, avoiding
   * value skip, and augments the matching along it. When it fails, the variables and values with
   * the current stamp are the alternating tree (a Hall set and its neighbours) and nextThreshold is
   * the cheapest edge of the tree above t.
   */
  private boolean augment(int u, int t, int skip) {
    stamp++;
    nextThreshold = Integer.MAX_VALUE;
    int top = 0;
    stackVar[0] = u;
    stackPos[0] = adjStart[u];
    varStamp[u] = stamp;
    while (top >= 0) {
      int a = stackVar[top];
      if (stackPos[top] == adjStart[a + 1]) {
        top--;
        continue;
      }
      int e = stackPos[top]++;
      int w = adjVal[e];
      if (w == skip || valStamp[w] == stamp) {
        continue;
      }
      if (adjCost[e] > t) {
        nextThreshold = Math.min(nextThreshold, adjCost[e]);
        continue;
      }
      valStamp[w] = stamp;
      int b = valMate[w];
      if (b < 0) {
        for (int k = top; k >= 0; k--) {
          int var = stackVar[k];
          int val = adjVal[stackPos[k] - 1];
          varMate[var] = val;
          valMate[val] = var;
        }
        return true;
      }
      if (varStamp[b] != stamp) {
        varStamp[b] = stamp;
        top++;
        stackVar[top] = b;
        stackPos[top] = adjStart[b];
      }
    }
    return false;
  }

  /**
   * Removes the edges in no perfect matching (Régin): the alternating graph has an arc from
   * variable a to variable b when a may take the value matched to b; an edge from i to the value of
   * b is kept when b reaches a free value or lies in the component of i.
   */
  private void filter(Store store) {
    Arrays.fill(index, -1);
    Arrays.fill(onStack, false);
    int counter = 0;
    int components = 0;
    int sp = 0;
    for (int root = 0; root < n; root++) {
      if (index[root] >= 0) {
        continue;
      }
      int depth = 0;
      callVar[0] = root;
      callPos[0] = adjStart[root];
      index[root] = low[root] = counter++;
      sccStack[sp++] = root;
      onStack[root] = true;
      while (depth >= 0) {
        int a = callVar[depth];
        if (callPos[depth] < adjStart[a + 1]) {
          int w = adjVal[callPos[depth]++];
          int b = valMate[w];
          if (b < 0 || b == a) {
            continue;
          }
          if (index[b] < 0) {
            index[b] = low[b] = counter++;
            sccStack[sp++] = b;
            onStack[b] = true;
            depth++;
            callVar[depth] = b;
            callPos[depth] = adjStart[b];
          } else if (onStack[b]) {
            low[a] = Math.min(low[a], index[b]);
          }
          continue;
        }
        if (low[a] == index[a]) {
          int c = components++;
          int bottom = sp;
          do {
            bottom--;
            component[sccStack[bottom]] = c;
            onStack[sccStack[bottom]] = false;
          } while (sccStack[bottom] != a);
          // every arc out of the component goes to a component already closed
          boolean free = false;
          for (int s = bottom; s < sp && !free; s++) {
            int m = sccStack[s];
            for (int k = adjStart[m]; k < adjStart[m + 1]; k++) {
              int b = valMate[adjVal[k]];
              if (b < 0 || b != m && component[b] != c && reachesFree[component[b]]) {
                free = true;
                break;
              }
            }
          }
          reachesFree[c] = free;
          sp = bottom;
        }
        depth--;
        if (depth >= 0) {
          int parent = callVar[depth];
          low[parent] = Math.min(low[parent], low[a]);
        }
      }
    }
    for (int i = 0; i < n; i++) {
      IntVar x = list[i];
      for (int k = adjStart[i]; k < adjStart[i + 1]; k++) {
        int w = adjVal[k];
        int b = valMate[w];
        if (b < 0 || b == i || component[b] == component[i] || reachesFree[component[b]]) {
          continue;
        }
        x.domain.inComplement(store.level, x, w + offset);
      }
    }
  }

  @Override
  public boolean satisfied() {
    if (duplicates && n > 1) {
      return false;
    }
    int largest = Integer.MIN_VALUE;
    for (int i = 0; i < n; i++) {
      if (!list[i].singleton()) {
        return false;
      }
      int w = list[i].value() - offset;
      if (w < 0 || w >= cost[i].length) {
        return false;
      }
      largest = Math.max(largest, cost[i][w]);
    }
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (list[i].value() == list[j].value()) {
          return false;
        }
      }
    }
    return z.min() >= largest;
  }

  // ---------------------------------------------------------------------------------------------
  // explanations

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (getClass() != BottleneckAlldiff.class || duplicates) {
      return false;
    }
    IntVar x = trail.variable(entry);
    int mark = out.size();
    if (x == z) {
      if (trail.kind(entry) != AtomicTrail.GE) {
        return false;
      }
      int threshold = trail.value(entry) - 1;
      if (!hallReason(trail, entry, -1, -1, threshold, false, out)) {
        out.truncate(mark);
        return false;
      }
      out.sortUnique(mark);
      return true;
    }
    int i = indexOf(x);
    if (i < 0) {
      return false;
    }
    int lo = trail.removedMin(entry);
    int hi = trail.removedMax(entry);
    int[] row = cost[i];
    // values out of the cost row need no reason
    int from = Math.max(lo, offset);
    int to = Math.min(hi, offset + row.length - 1);
    if (to >= from && (long) to - from + 1 > REMOVED_LIMIT) {
      return false;
    }
    int zMax = trail.maxBefore(z, entry);
    IntDomain root = trail.rootDomain(x);
    for (int v = from; v <= to; v++) {
      if (!root.contains(v) || trail.excludedBefore(x, v, entry, out)) {
        continue;
      }
      int c = row[v - offset];
      if (c > zMax) {
        if (!addCostBound(trail, entry, c, out)) {
          out.truncate(mark);
          return false;
        }
        continue;
      }
      if (!hallReason(trail, entry, i, v - offset, zMax, true, out)) {
        out.truncate(mark);
        return false;
      }
    }
    out.sortUnique(mark);
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (getClass() != BottleneckAlldiff.class || duplicates || n == 0) {
      return false;
    }
    int now = trail.size();
    int mark = out.size();
    if (!hallReason(trail, now, -1, -1, trail.maxBefore(z, now), true, out)) {
      out.truncate(mark);
      return false;
    }
    out.sortUnique(mark);
    return true;
  }

  // the atom z <= c - 1, the weakest upper bound of z that rules out an edge of cost c
  private boolean addCostBound(AtomicTrail trail, int position, int c, EntryList out) {
    int e = trail.earliestUpperBound(z, (long) c - 1, position);
    if (e == Integer.MAX_VALUE) {
      return false;
    }
    if (e >= 0) {
      out.add(e);
    }
    return true;
  }

  /**
   * Adds a Hall set reason over the graph of the domains just before a position, with the edges of
   * cost at most threshold: the variables other than skipVar cannot all be matched to values other
   * than skipValue. The reason is the removed values of the Hall set; with useZ also the upper
   * bound of z that leaves out its edges above the threshold.
   */
  private boolean hallReason(
      AtomicTrail trail,
      int position,
      int skipVar,
      int skipValue,
      int threshold,
      boolean useZ,
      EntryList out) {
    buildBefore(trail, position);
    Arrays.fill(varMate, -1);
    Arrays.fill(valMate, -1);
    int failed = -1;
    for (int i = 0; i < n && failed < 0; i++) {
      if (i != skipVar && !augment(i, threshold, skipValue)) {
        failed = i;
      }
    }
    // the matching was spoiled for the search; the next call rebuilds it
    Arrays.fill(varMate, -1);
    Arrays.fill(valMate, -1);
    if (failed < 0) {
      return false;
    }
    int cheapest = Integer.MAX_VALUE;
    for (int k = 0; k < n; k++) {
      if (varStamp[k] != stamp) {
        continue;
      }
      IntVar x = list[k];
      int[] row = cost[k];
      IntDomain root = trail.rootDomain(x);
      int from = Math.max(root.min(), offset);
      int to = Math.min(root.max(), offset + row.length - 1);
      if ((long) to - from + 1 > 4L * REMOVED_LIMIT * REMOVED_LIMIT) {
        return false;
      }
      for (int v = from; v <= to; v++) {
        int w = v - offset;
        if (w == skipValue || valStamp[w] == stamp || !root.contains(v)) {
          continue;
        }
        if (row[w] > threshold) {
          cheapest = Math.min(cheapest, row[w]);
          continue;
        }
        if (!trail.excludedBefore(x, v, position, out)) {
          return false;
        }
      }
    }
    return !useZ || cheapest == Integer.MAX_VALUE || addCostBound(trail, position, cheapest, out);
  }

  // the edges of the domains just before a trail position, all costs included
  private void buildBefore(AtomicTrail trail, int position) {
    EntryList scratch = new EntryList();
    int k = 0;
    for (int i = 0; i < n; i++) {
      adjStart[i] = k;
      IntVar x = list[i];
      int[] row = cost[i];
      IntDomain root = trail.rootDomain(x);
      int min = Math.max(trail.minBefore(x, position), offset);
      int max = Math.min(trail.maxBefore(x, position), offset + row.length - 1);
      for (int v = min; v <= max; v++) {
        if (root.contains(v)) {
          scratch.clear();
          if (!trail.excludedBefore(x, v, position, scratch)) {
            adjVal[k] = v - offset;
            adjCost[k] = row[v - offset];
            k++;
          }
        }
      }
    }
    adjStart[n] = k;
  }

  private int indexOf(IntVar x) {
    for (int i = 0; i < n; i++) {
      if (list[i] == x) {
        return i;
      }
    }
    return -1;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : BottleneckAlldiff([");
    appendArrayToString(result, list);
    result.append("], [");
    for (int i = 0; i < n; i++) {
      result.append(Arrays.toString(cost[i]));
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(offset).append(", ").append(z).append(')');
    return result.toString();
  }

  @Override
  public BottleneckAlldiff copy(VarMap map) {
    return new BottleneckAlldiff(map.get(list), cost, offset, map.get(z), domainConsistent);
  }
}
