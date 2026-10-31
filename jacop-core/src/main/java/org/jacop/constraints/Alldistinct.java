/*
 * Alldistinct.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.ToIntFunction;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Simplifiable;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.api.Violation;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.SmallDenseDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;

/**
 * Alldistinct constraint assures that all FDVs have different values.
 *
 * <p>It enforces generalized arc consistency (domain consistency) using Regin's algorithm. A
 * maximum matching of the variable-value graph is kept between executions and repaired by
 * augmenting paths only for variables which lost their matched value. Strongly connected components
 * of the residual graph are computed with Tarjan's algorithm, where every free value points to a
 * sink and the sink points to every variable, so an edge between a variable and a value is
 * consistent if and only if both ends lie in the same component. Assigned variables are propagated
 * first (value consistency) and the matching based pruning is executed in a later queue.
 *
 * <p>All data structures are indexed by the variable position and by the position of the value in
 * the sorted union of initial domains. One variable with domain 0..1000000 makes the value graph
 * huge and the constraint very ineffective, so use it with care.
 *
 * <p>When the union of initial domains spans at most 512 values, or has at most 512 values, the
 * graph is kept in bit sets instead, in the spirit of Li et al. (A Bitwise GAC Algorithm for
 * Alldifferent Constraints, IJCAI 2023). A variable is represented by the bit of its matched value,
 * so the residual graph is read directly from the domain bits. The component of the free values is
 * computed first (Zhang et al., A Fast Algorithm for Generalized Arc Consistency of the
 * Alldifferent Constraint, IJCAI 2018), and an execution stops as soon as the remaining variables
 * are found to form a single component, as they do in most executions during search (Zhang et al.,
 * Early and Efficient Identification of Useless Constraint Propagation for Alldifferent
 * Constraints, IJCAI 2020).
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class Alldistinct extends Constraint
    implements Violation,
        Simplifiable,
        UsesQueueVariable,
        Stateful,
        SatisfiedPresent,
        Copyable<Alldistinct>,
        Explainable,
        PbEncodable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  static final boolean GREEDY = true;

  // Values are mapped to indexes with an offset table when the union of domains is not sparser
  // than this factor.
  private static final int DENSE_FACTOR = 4;

  // The bit set representation is used when the union of initial domains spans, or has, at most
  // this many 64 bit words of values.
  static final int MAX_BIT_WORDS = 8;

  /** It specifies all variables which have to have different values. */
  final IntVar[] list;

  // Sorted union of the initial domains; value index a stands for values[a].
  private final int[] values;

  // values[valueIndexOffset[v - minValue]] == v, or null if binary search is used.
  private final int[] valueIndexOffset;

  private final int minValue;

  // Maximum matching, it is not trailed. Any maximum matching can be used for pruning, so after
  // backtracking (domains only grow) the matching is still valid and is reused. In bit mode values
  // are given by their bit number.
  private final int[] varMatch;
  private final int[] valMatch;

  // Number of 64 bit words of the bit mode, 0 if it is not used. Bit k of word w stands for value
  // minValue + 64 * w + k if bitOffsets holds, otherwise for the value of index 64 * w + k.
  private final int words;
  private final boolean bitOffsets;

  // Domains of not grounded variables, words per variable, read at each execution (bit mode).
  private final long[] domainBits;

  // Bit mode work sets of words each: values matched with any variable, values matched with not
  // grounded variables, free values, not yet classified variables, and reachability search sets.
  // Variables are given by the bit of their matched value.
  private final long[] taken;
  private final long[] matched;
  private final long[] free;
  private final long[] alive;
  private final long[] reach;
  private final long[] frontier;
  private final long[] back;

  // Variables (indexes) on positions 0..notGrounded-1 are not yet processed as grounded.
  private final int[] position;
  private TimeStamp<Integer> notGrounded;

  // Adjacency lists (value indexes) of not grounded variables, rebuilt at each execution.
  private final int[][] adjacency;
  private final int[] degree;

  // Tarjan algorithm data; nodes are variables 0..n-1, values n..n+m-1 and the sink n+m.
  private final int[] dfsNumber;
  private final int[] lowLink;
  private final int[] component;
  private final int[] edgeCursor;
  private final int[] callStack;
  private final int[] sccStack;
  private final boolean[] onStack;

  // Value marks for augmenting path search.
  private final int[] visitedValue;
  private int visitGeneration;

  private final int[] freeVariables;

  // Variables reported by queueVariable since last execution.
  private IntVar[] pendingVariables;
  private int pendingSize;

  // failure (inconsistency) discovered during imposition
  private boolean impositionFailure;

  IntVar guideVariable;
  int guideValue;

  /**
   * It constructs an alldistinct constraint.
   *
   * @param list an array of variables.
   */
  public Alldistinct(IntVar[] list) {

    checkInputForNullness("list", list);
    checkInputForDuplication("list", list);

    queueIndex = 2;

    numberId = idNumber.incrementAndGet();

    this.list = Arrays.copyOf(list, list.length);

    IntDomain sum = new IntervalDomain(5);
    for (IntVar v : this.list) {
      sum.addDom(v.dom());
    }

    int noValues = sum.getSize();
    values = new int[noValues];
    int m = 0;
    for (ValueEnumeration enumer = sum.valueEnumeration(); enumer.hasMoreElements(); ) {
      values[m++] = enumer.nextElement();
    }

    if (noValues > 0) {
      minValue = values[0];
      long span = (long) values[noValues - 1] - minValue + 1;
      if (span <= (long) DENSE_FACTOR * noValues + 64) {
        valueIndexOffset = new int[(int) span];
        Arrays.fill(valueIndexOffset, -1);
        for (int a = 0; a < noValues; a++) {
          valueIndexOffset[values[a] - minValue] = a;
        }
      } else {
        valueIndexOffset = null;
      }
    } else {
      minValue = 0;
      valueIndexOffset = null;
    }

    int n = this.list.length;
    long valueSpan = noValues > 0 ? (long) values[noValues - 1] - minValue + 1 : 0;
    bitOffsets = valueSpan <= 64L * MAX_BIT_WORDS;
    long bitValues = bitOffsets ? valueSpan : noValues;
    words = noValues > 0 && bitValues <= 64L * MAX_BIT_WORDS ? (int) ((bitValues + 63) / 64) : 0;
    domainBits = new long[n * words];
    taken = new long[words];
    matched = new long[words];
    free = new long[words];
    alive = new long[words];
    reach = new long[words];
    frontier = new long[words];
    back = new long[words];

    varMatch = new int[n];
    valMatch = new int[words > 0 ? (int) bitValues : noValues];
    Arrays.fill(varMatch, -1);
    Arrays.fill(valMatch, -1);

    position = new int[n];
    for (int i = 0; i < n; i++) {
      position[i] = i;
    }

    // adjacency lists and Tarjan algorithm data are only used without bit mode
    int listed = words > 0 ? 0 : n;
    adjacency = new int[listed][];
    degree = new int[listed];
    for (int i = 0; i < listed; i++) {
      adjacency[i] = new int[this.list[i].getSize()];
    }

    int noNodes = words > 0 ? 0 : n + 1;
    dfsNumber = new int[noNodes];
    lowLink = new int[noNodes];
    component = new int[noNodes];
    edgeCursor = new int[noNodes];
    callStack = new int[noNodes];
    sccStack = new int[noNodes];
    onStack = new boolean[noNodes];

    visitedValue = new int[words > 0 ? 0 : noValues];
    freeVariables = new int[n];
    pendingVariables = new IntVar[Math.max(4, n)];

    setScope(list);
  }

  /**
   * It constructs an alldistinct constraint.
   *
   * @param list arraylist of variables.
   */
  public Alldistinct(List<? extends IntVar> list) {

    this(list.toArray(new IntVar[0]));
  }

  @Override
  public void impose(Store store) {

    super.impose(store);

    notGrounded = new TimeStamp<>(store, list.length);

    // the initial maximum matching needs to be computed, failure is reported by consistency
    if (words > 0) {
      Arrays.fill(taken, 0);
      for (int i = 0; i < list.length; i++) {
        readBits(i);
      }
      for (int i = 0; i < list.length; i++) {
        if (!findMatchBits(i)) {
          impositionFailure = true;
          break;
        }
      }
    } else {
      for (int i = 0; i < list.length; i++) {
        buildAdjacency(i);
      }
      for (int i = 0; i < list.length; i++) {
        if (!findMatch(i)) {
          impositionFailure = true;
          break;
        }
      }
    }

    store.raiseLevelBeforeConsistency = true;
  }

  @Override
  public void removeLevel(int level) {
    pendingSize = 0;
  }

  @Override
  public void queueVariable(int level, Var v) {
    if (pendingSize == pendingVariables.length) {
      pendingVariables = Arrays.copyOf(pendingVariables, 2 * pendingSize);
    }
    pendingVariables[pendingSize++] = (IntVar) v;
  }

  @Override
  public void consistency(Store store) {

    if (impositionFailure) {
      throw Store.failException;
    }

    if (store.currentQueue == queueIndex) {

      propagateGroundedPending(store);

      if (queueIndex + 2 < store.queueNo) {
        store.addChanged(this, queueIndex + 2);
        return;
      }
    }

    pendingSize = 0;

    int notGroundedNo = removeGrounded(store);

    if (notGroundedNo > 1) {
      if (words > 0) {
        if (!repairMatchingBits(notGroundedNo)) {
          throw Store.failException;
        }
        filterBits(store, notGroundedNo);
      } else {
        if (!repairMatching(notGroundedNo)) {
          throw Store.failException;
        }
        if (computeComponents(notGroundedNo) > 1) {
          prune(store, notGroundedNo);
        }
      }
    }

    // Regin's filtering is idempotent, all events caused by this execution are already handled.
    pendingSize = 0;
  }

  /**
   * It removes values of grounded variables reported by queueVariable from all other variables.
   * Variables grounded by this pruning are appended to the pending list and processed as well.
   */
  private void propagateGroundedPending(Store store) {

    int notGroundedNo = notGrounded.value();

    for (int k = 0; k < pendingSize; k++) {
      IntVar q = pendingVariables[k];
      if (q.singleton()) {
        int qValue = q.value();
        for (int j = 0; j < notGroundedNo; j++) {
          IntVar x = list[position[j]];
          if (x != q) {
            x.domain.inComplement(store.level, x, qValue);
          }
        }
      }
    }
    pendingSize = 0;
  }

  /**
   * It moves all grounded variables out of the not grounded part, matches them with their values
   * and removes their values from all not grounded variables until no new variable is grounded.
   *
   * @return the number of not grounded variables.
   */
  private int removeGrounded(Store store) {

    int notGroundedNo = notGrounded.value();
    int initialNotGroundedNo = notGroundedNo;

    boolean grounded = true;
    while (grounded) {
      grounded = false;
      for (int j = notGroundedNo - 1; j >= 0; j--) {
        int i = position[j];
        IntVar x = list[i];
        if (x.singleton()) {
          grounded = true;
          notGroundedNo--;
          position[j] = position[notGroundedNo];
          position[notGroundedNo] = i;

          int xValue = x.value();
          match(i, words > 0 && bitOffsets ? xValue - minValue : valueIndex(xValue));

          for (int k = 0; k < notGroundedNo; k++) {
            IntVar y = list[position[k]];
            y.domain.inComplement(store.level, y, xValue);
          }
        }
      }
    }

    if (notGroundedNo != initialNotGroundedNo) {
      notGrounded.update(notGroundedNo);
    }

    return notGroundedNo;
  }

  private void match(int i, int a) {
    int oldValue = varMatch[i];
    if (oldValue == a) {
      return;
    }
    if (oldValue >= 0) {
      valMatch[oldValue] = -1;
    }
    int oldVariable = valMatch[a];
    if (oldVariable >= 0) {
      varMatch[oldVariable] = -1;
    }
    varMatch[i] = a;
    valMatch[a] = i;
  }

  int valueIndex(int value) {
    if (valueIndexOffset != null) {
      return valueIndexOffset[value - minValue];
    }
    return Arrays.binarySearch(values, value);
  }

  /** It stores the value indexes of the current domain of variable i in its adjacency list. */
  private void buildAdjacency(int i) {

    IntDomain dom = list[i].dom();
    int[] adj = adjacency[i];
    int d = 0;

    if (dom.domainId() == IntDomain.SMALL_DENSE_DOMAIN_ID) {
      SmallDenseDomain sdd = (SmallDenseDomain) dom;
      long bits = sdd.bits;
      int base = sdd.minBound;
      while (bits != 0) {
        int shift = Long.numberOfLeadingZeros(bits);
        adj[d++] = valueIndex(base + shift);
        bits &= ~(Long.MIN_VALUE >>> shift);
      }
    } else if (dom.domainId() == IntDomain.INTERVAL_DOMAIN_ID) {
      IntervalDomain id = (IntervalDomain) dom;
      for (int k = 0; k < id.size; k++) {
        Interval interval = id.intervals[k];
        int max = interval.max();
        if (valueIndexOffset != null) {
          for (int v = interval.min(); v <= max; v++) {
            adj[d++] = valueIndexOffset[v - minValue];
          }
        } else {
          // consecutive values have consecutive indexes in the sorted union
          int a = Arrays.binarySearch(values, interval.min());
          for (int v = interval.min(); v <= max; v++) {
            adj[d++] = a++;
          }
        }
      }
    } else {
      for (ValueEnumeration enumer = dom.valueEnumeration(); enumer.hasMoreElements(); ) {
        adj[d++] = valueIndex(enumer.nextElement());
      }
    }

    degree[i] = d;
  }

  /**
   * It builds the adjacency lists of not grounded variables and repairs the maximum matching for
   * variables which lost their matched value.
   *
   * @return false if there is no matching covering all variables.
   */
  private boolean repairMatching(int notGroundedNo) {

    int noFree = 0;

    for (int j = 0; j < notGroundedNo; j++) {
      int i = position[j];
      buildAdjacency(i);
      int a = varMatch[i];
      if (a < 0 || !list[i].domain.contains(values[a])) {
        if (a >= 0) {
          valMatch[a] = -1;
          varMatch[i] = -1;
        }
        freeVariables[noFree++] = i;
      }
    }

    for (int k = 0; k < noFree; k++) {
      if (!findMatch(freeVariables[k])) {
        return false;
      }
    }

    return true;
  }

  /** It matches variable i, first with a free value, otherwise by an augmenting path. */
  private boolean findMatch(int i) {

    int[] adj = adjacency[i];
    int d = degree[i];
    for (int k = 0; k < d; k++) {
      int a = adj[k];
      if (valMatch[a] < 0) {
        varMatch[i] = a;
        valMatch[a] = i;
        return true;
      }
    }

    visitGeneration++;
    if (visitGeneration == Integer.MAX_VALUE) {
      Arrays.fill(visitedValue, 0);
      visitGeneration = 1;
    }
    return augment(i);
  }

  private boolean augment(int i) {

    int[] adj = adjacency[i];
    int d = degree[i];
    for (int k = 0; k < d; k++) {
      int a = adj[k];
      if (visitedValue[a] != visitGeneration) {
        visitedValue[a] = visitGeneration;
        int j = valMatch[a];
        if (j < 0 || augment(j)) {
          varMatch[i] = a;
          valMatch[a] = i;
          return true;
        }
      }
    }
    return false;
  }

  /**
   * It computes strongly connected components of the residual graph. In the residual graph a
   * variable points to all its values except the matched one, a matched value points to its
   * variable, a free value points to the sink, and the sink points to all variables. Each value has
   * exactly one successor, so value nodes are contracted: a variable points directly to the
   * variable matched with the value, or to the sink for a free value. A value matched with variable
   * y is in the same component as y.
   *
   * @return the number of components.
   */
  private int computeComponents(int notGroundedNo) {

    int sink = list.length;

    for (int j = 0; j < notGroundedNo; j++) {
      dfsNumber[position[j]] = 0;
    }
    dfsNumber[sink] = 0;

    int counter = 0;
    int sccTop = 0;
    int componentId = 0;

    for (int j = 0; j < notGroundedNo; j++) {

      int root = position[j];
      if (dfsNumber[root] != 0) {
        continue;
      }

      int callTop = 0;
      callStack[callTop++] = root;
      counter++;
      dfsNumber[root] = counter;
      lowLink[root] = counter;
      edgeCursor[root] = 0;
      sccStack[sccTop++] = root;
      onStack[root] = true;

      while (callTop > 0) {

        int node = callStack[callTop - 1];
        int next = -1;
        int cursor = edgeCursor[node];

        if (node != sink) {
          int[] adj = adjacency[node];
          int d = degree[node];
          int matched = varMatch[node];
          while (cursor < d) {
            int a = adj[cursor++];
            if (a != matched) {
              int holder = valMatch[a];
              next = holder >= 0 ? holder : sink;
              break;
            }
          }
        } else if (cursor < notGroundedNo) {
          next = position[cursor++];
        }
        edgeCursor[node] = cursor;

        if (next >= 0) {
          if (dfsNumber[next] == 0) {
            counter++;
            dfsNumber[next] = counter;
            lowLink[next] = counter;
            edgeCursor[next] = 0;
            sccStack[sccTop++] = next;
            onStack[next] = true;
            callStack[callTop++] = next;
          } else if (onStack[next] && dfsNumber[next] < lowLink[node]) {
            lowLink[node] = dfsNumber[next];
          }
          continue;
        }

        callTop--;

        if (lowLink[node] == dfsNumber[node]) {
          componentId++;
          int member;
          do {
            member = sccStack[--sccTop];
            onStack[member] = false;
            component[member] = componentId;
          } while (member != node);
        }

        if (callTop > 0) {
          int parent = callStack[callTop - 1];
          if (lowLink[node] < lowLink[parent]) {
            lowLink[parent] = lowLink[node];
          }
        }
      }
    }

    return componentId;
  }

  /** It reads the domain of variable i into its words of domainBits (bit mode). */
  private void readBits(int i) {
    IntDomain dom = list[i].domain;
    int base = i * words;
    if (bitOffsets) {
      for (int w = 0; w < words; w++) {
        domainBits[base + w] = dom.bitsFrom(minValue + 64 * w);
      }
      return;
    }

    Arrays.fill(domainBits, base, base + words, 0);
    if (dom.domainId() == IntDomain.INTERVAL_DOMAIN_ID) {
      IntervalDomain id = (IntervalDomain) dom;
      for (int k = 0; k < id.size; k++) {
        Interval interval = id.intervals[k];
        // consecutive values have consecutive indexes in the sorted union
        int a = valueIndex(interval.min());
        for (int last = a + interval.max() - interval.min(); a <= last; a++) {
          domainBits[base + (a >>> 6)] |= 1L << a;
        }
      }
    } else {
      for (ValueEnumeration enumer = dom.valueEnumeration(); enumer.hasMoreElements(); ) {
        int a = valueIndex(enumer.nextElement());
        domainBits[base + (a >>> 6)] |= 1L << a;
      }
    }
  }

  /**
   * It reads the domains of not grounded variables and repairs the maximum matching for variables
   * which lost their matched value (bit mode).
   *
   * @return false if there is no matching covering all variables.
   */
  private boolean repairMatchingBits(int notGroundedNo) {

    Arrays.fill(taken, 0);
    for (int i = 0; i < list.length; i++) {
      int a = varMatch[i];
      if (a >= 0) {
        taken[a >>> 6] |= 1L << a;
      }
    }

    int noFree = 0;
    for (int j = 0; j < notGroundedNo; j++) {
      int i = position[j];
      readBits(i);
      int a = varMatch[i];
      if (a < 0 || (domainBits[i * words + (a >>> 6)] & (1L << a)) == 0) {
        if (a >= 0) {
          valMatch[a] = -1;
          varMatch[i] = -1;
          taken[a >>> 6] &= ~(1L << a);
        }
        freeVariables[noFree++] = i;
      }
    }

    for (int k = 0; k < noFree; k++) {
      if (!findMatchBits(freeVariables[k])) {
        return false;
      }
    }

    return true;
  }

  /** It matches variable i, first with a free value, otherwise by an augmenting path (bit mode). */
  private boolean findMatchBits(int i) {

    int base = i * words;
    for (int w = 0; w < words; w++) {
      long available = domainBits[base + w] & ~taken[w];
      if (available != 0) {
        int a = (w << 6) + Long.numberOfTrailingZeros(available);
        varMatch[i] = a;
        valMatch[a] = i;
        taken[w] |= available & -available;
        return true;
      }
    }

    // reach is used as the set of visited values
    Arrays.fill(reach, 0);
    return augmentBits(i);
  }

  private boolean augmentBits(int i) {

    int base = i * words;
    for (int w = 0; w < words; w++) {
      long available = domainBits[base + w] & ~taken[w];
      if (available != 0) {
        int a = (w << 6) + Long.numberOfTrailingZeros(available);
        varMatch[i] = a;
        valMatch[a] = i;
        taken[w] |= available & -available;
        return true;
      }
    }
    for (int w = 0; w < words; w++) {
      long candidates = domainBits[base + w] & ~reach[w];
      while (candidates != 0) {
        long bit = candidates & -candidates;
        candidates ^= bit;
        if ((reach[w] & bit) != 0) {
          continue;
        }
        reach[w] |= bit;
        int a = (w << 6) + Long.numberOfTrailingZeros(bit);
        if (augmentBits(valMatch[a])) {
          varMatch[i] = a;
          valMatch[a] = i;
          return true;
        }
      }
    }
    return false;
  }

  /**
   * It removes the values of not grounded variables which belong to no maximum matching (bit mode).
   * The variables are partitioned into strongly connected components of the residual graph, where a
   * variable points to the variables matched with its other values and to the free values, and the
   * free values point to all variables. A value is kept if it is free or matched with a variable of
   * the same component. Components are computed one at a time by forward and backward reachability,
   * starting with the component of the free values, and the computation stops when the remaining
   * variables form a single component.
   */
  private void filterBits(Store store, int notGroundedNo) {

    Arrays.fill(matched, 0);
    Arrays.fill(free, 0);
    for (int j = 0; j < notGroundedNo; j++) {
      int i = position[j];
      int a = varMatch[i];
      matched[a >>> 6] |= 1L << a;
      int base = i * words;
      for (int w = 0; w < words; w++) {
        free[w] |= domainBits[base + w];
      }
    }
    boolean anyFree = false;
    for (int w = 0; w < words; w++) {
      free[w] &= ~matched[w];
      alive[w] = matched[w];
      anyFree |= free[w] != 0;
    }

    boolean first = true;
    if (anyFree) {
      // the variables which reach a free value form one component with the free values
      Arrays.fill(back, 0);
      reachBackward(free);
      if (pruneComponent(store, back, true)) {
        return;
      }
      first = false;
    }

    while (true) {
      int w0 = 0;
      while (alive[w0] == 0) {
        w0++;
      }
      long rootBit = alive[w0] & -alive[w0];
      reachForward(w0, rootBit);
      Arrays.fill(back, 0);
      back[w0] = rootBit;
      reachBackward(back);
      if (pruneComponent(store, back, first)) {
        return;
      }
      first = false;
    }
  }

  // It computes in reach the alive variables reachable from the variable matched with the value
  // given by word w and bit.
  private void reachForward(int w, long bit) {

    Arrays.fill(reach, 0);
    Arrays.fill(frontier, 0);
    reach[w] = bit;
    frontier[w] = bit;

    int word = w;
    while (word < words) {
      long f = frontier[word];
      if (f == 0) {
        word++;
        continue;
      }
      long b = f & -f;
      frontier[word] = f ^ b;
      int base = valMatch[(word << 6) + Long.numberOfTrailingZeros(b)] * words;
      int lowest = word;
      for (int v = 0; v < words; v++) {
        long next = domainBits[base + v] & alive[v] & ~reach[v];
        if (next != 0) {
          reach[v] |= next;
          frontier[v] |= next;
          if (v < lowest) {
            lowest = v;
          }
        }
      }
      word = lowest;
    }
  }

  // It adds to back the variables in reach (or all alive variables if target holds the free values)
  // which reach a variable of back or a value of target.
  private void reachBackward(long[] target) {

    long[] candidates = target == free ? alive : reach;
    boolean changed = true;
    while (changed) {
      changed = false;
      for (int w = 0; w < words; w++) {
        long c = candidates[w] & ~back[w];
        while (c != 0) {
          long b = c & -c;
          c ^= b;
          int base = valMatch[(w << 6) + Long.numberOfTrailingZeros(b)] * words;
          for (int v = 0; v < words; v++) {
            if ((domainBits[base + v] & (target[v] | back[v])) != 0) {
              back[w] |= b;
              changed = true;
              break;
            }
          }
        }
      }
    }
  }

  /**
   * It removes from the variables of the component the values matched with variables of other
   * components, and removes the component from the alive variables. The variables of the first
   * component have no such values if it contains all variables.
   *
   * @return true if the component contains all alive variables, it is the last one.
   */
  private boolean pruneComponent(Store store, long[] component, boolean first) {

    boolean all = true;
    for (int w = 0; w < words; w++) {
      if (component[w] != alive[w]) {
        all = false;
        break;
      }
    }
    if (all && first) {
      return true;
    }

    for (int w = 0; w < words; w++) {
      long c = component[w];
      while (c != 0) {
        long b = c & -c;
        c ^= b;
        int i = valMatch[(w << 6) + Long.numberOfTrailingZeros(b)];
        int base = i * words;
        for (int v = 0; v < words; v++) {
          // reach is not needed any more and keeps the values to remove
          reach[v] = domainBits[base + v] & matched[v] & ~component[v];
        }
        removeBits(store, i, reach);
      }
    }

    for (int w = 0; w < words; w++) {
      alive[w] &= ~component[w];
    }
    return all;
  }

  // It removes the values given by bits from variable i.
  private void removeBits(Store store, int i, long[] bits) {

    IntVar x = list[i];
    if (x.domain.domainId() == IntDomain.SMALL_DENSE_DOMAIN_ID) {
      SmallDenseDomain sdd = (SmallDenseDomain) x.domain;
      long removed;
      if (bitOffsets) {
        // the 64 values from sdd.minBound, lowest value first
        int offset = sdd.minBound - minValue;
        int w = offset >>> 6;
        int shift = offset & 63;
        long window = bits[w] >>> shift;
        if (shift != 0 && w + 1 < words) {
          window |= bits[w + 1] << (64 - shift);
        }
        removed = Long.reverse(window);
      } else {
        removed = 0;
        for (int w = 0; w < words; w++) {
          for (long r = bits[w]; r != 0; r &= r - 1) {
            removed |=
                Long.MIN_VALUE
                    >>> (values[(w << 6) + Long.numberOfTrailingZeros(r)] - sdd.minBound);
          }
        }
      }
      if (removed != 0) {
        sdd.in(store.level, x, ~removed);
      }
      return;
    }

    for (int w = 0; w < words; w++) {
      long r = bits[w];
      while (r != 0) {
        int low = Long.numberOfTrailingZeros(r);
        int high = low + Long.numberOfTrailingZeros(~(r >>> low)) - 1;
        r &= high == 63 ? 0 : -1L << (high + 1);
        if (bitOffsets) {
          int base = minValue + 64 * w;
          x.domain.inComplement(store.level, x, base + low, base + high);
        } else {
          for (int a = (w << 6) + low; a <= (w << 6) + high; a++) {
            x.domain.inComplement(store.level, x, values[a]);
          }
        }
      }
    }
  }

  /**
   * It removes all values matched with a variable from a different component. Values which are
   * matched with the variable itself or free are always consistent.
   */
  private void prune(Store store, int notGroundedNo) {

    for (int j = 0; j < notGroundedNo; j++) {
      int i = position[j];
      int xComponent = component[i];
      int matched = varMatch[i];
      int[] adj = adjacency[i];
      int d = degree[i];
      int first = -1;
      for (int k = 0; k < d; k++) {
        int a = adj[k];
        if (a != matched) {
          int holder = valMatch[a];
          if (holder >= 0 && component[holder] != xComponent) {
            first = k;
            break;
          }
        }
      }
      if (first < 0) {
        continue;
      }

      IntVar x = list[i];
      if (x.domain.domainId() == IntDomain.SMALL_DENSE_DOMAIN_ID) {
        SmallDenseDomain sdd = (SmallDenseDomain) x.domain;
        int base = sdd.minBound;
        long removed = 0;
        for (int k = first; k < d; k++) {
          int a = adj[k];
          if (a != matched) {
            int holder = valMatch[a];
            if (holder >= 0 && component[holder] != xComponent) {
              removed |= Long.MIN_VALUE >>> (values[a] - base);
            }
          }
        }
        sdd.in(store.level, x, ~removed);
      } else {
        for (int k = first; k < d; k++) {
          int a = adj[k];
          if (a != matched) {
            int holder = valMatch[a];
            if (holder >= 0 && component[holder] != xComponent) {
              x.domain.inComplement(store.level, x, values[a]);
            }
          }
        }
      }
    }
  }

  @Override
  public boolean satisfied() {

    // Possible to use this check, fast but not accurate

    boolean sat = true;
    int i = 0;

    while (sat && i < list.length) {
      IntDomain vDom = list[i].dom();
      int vMin = vDom.min();
      int vMax = vDom.max();
      int j = 0;
      while (sat && j < list.length) {
        if (i != j) {
          IntDomain ljDom = list[j].dom();
          sat = vMin > ljDom.max() || vMax < ljDom.min();
        }
        j++;
      }
      i++;
    }
    return sat;
  }

  @Override
  public String toString() {

    StringBuilder buf = new StringBuilder(id());

    buf.append(" : alldistinct([");

    for (int i = 0; i < list.length; i++) {
      buf.append(list[i]);
      if (i < list.length - 1) {
        buf.append(", ");
      }
    }

    buf.append("]");
    return buf.toString();
  }

  @Override
  public Constraint getGuideConstraint() {
    return new XeqC(guideVariable, guideValue);
  }

  @Override
  public int getGuideValue() {
    return guideValue;
  }

  @Override
  public Var getGuideVariable() {

    int minCurrentPruning = 1;
    int maxCurrentPruning = 100000;

    // Look at all variables with domain size two, and find the one with
    // best pruning

    guideVariable = null;

    IntVar[] notGroundedVars = notGroundedVariables();

    for (int i = 0; i < notGroundedVars.length; i++) {
      if (notGroundedVars[i].getSize() == 2) {

        int firstValue = notGroundedVars[i].min();
        int secondValue = notGroundedVars[i].max();

        // Evaluate recursively.
        int pruningFirstValue = estimatePruning(notGroundedVars[i], firstValue);

        if (pruningFirstValue >= minCurrentPruning) {

          int pruningSecondValue = estimatePruning(notGroundedVars[i], secondValue);

          if (pruningFirstValue < pruningSecondValue) {

            if (pruningFirstValue > minCurrentPruning) {

              // Lack of equal sign means greedy in propagation
              if (valueCount(firstValue) < valueCount(secondValue)
                  || (valueCount(firstValue) == valueCount(secondValue) && !GREEDY)) {
                // Value with lower number of variables has a
                // higher change to have this value
                guideVariable = notGroundedVars[i];
                guideValue = firstValue;

              } else {
                guideVariable = notGroundedVars[i];
                guideValue = secondValue;
              }

              minCurrentPruning = pruningFirstValue;
              maxCurrentPruning = pruningSecondValue;
            } else if (pruningFirstValue == minCurrentPruning
                && pruningSecondValue > maxCurrentPruning) {

              // Lack of equal sign means greedy in propagation
              if (valueCount(firstValue) < valueCount(secondValue)
                  || (valueCount(firstValue) == valueCount(secondValue) && !GREEDY)) {
                // Value with lower number of variables has a
                // higher change to have this value

                guideVariable = notGroundedVars[i];
                guideValue = firstValue;

              } else {

                guideVariable = notGroundedVars[i];
                guideValue = secondValue;
              }
              maxCurrentPruning = pruningSecondValue;
            }
          } else {
            // FirstValuePruning > SecondValuePruning
            if (pruningSecondValue > minCurrentPruning) {

              // Lack of equal sign means no greedy in propagation
              // Equal sign means greedy in propagation
              if (valueCount(firstValue) <= valueCount(secondValue)
                  || (valueCount(firstValue) == valueCount(secondValue) && GREEDY)) {
                // Value with lower number of variables has a
                // higher change to have this value
                guideVariable = notGroundedVars[i];
                guideValue = firstValue;
              } else {

                guideVariable = notGroundedVars[i];
                guideValue = secondValue;
              }
              minCurrentPruning = pruningSecondValue;
              maxCurrentPruning = pruningFirstValue;
            } else if (pruningSecondValue == minCurrentPruning
                && pruningFirstValue > maxCurrentPruning) {

              // Equal sign means greedy in propagation
              if (valueCount(firstValue) <= valueCount(secondValue)
                  || (valueCount(firstValue) == valueCount(secondValue) && GREEDY)) {
                // Value with lower number of variables has a
                // higher change to have this value
                guideVariable = notGroundedVars[i];
                guideValue = firstValue;
              } else {
                guideVariable = notGroundedVars[i];
                guideValue = secondValue;
              }
              maxCurrentPruning = pruningFirstValue;
            }
          }
        }
      }
    }

    // Permutation only at this moment

    if (isPermutation()) {

      for (int value : activeValues()) {

        List<IntVar> currentList = variablesWithValue(value);

        // Value with two variables
        if (currentList.size() == 2) {

          int pruningFirstVariable = estimatePruning(currentList.get(0), value);

          if (pruningFirstVariable < minCurrentPruning) {
            continue;
          }

          int pruningSecondVariable = estimatePruning(currentList.get(1), value);

          if (pruningSecondVariable < minCurrentPruning) {
            continue;
          }

          if (pruningFirstVariable < pruningSecondVariable) {

            if (pruningFirstVariable > minCurrentPruning) {

              // Equals sign means no greedy in propagation
              // Lack of equal sign means greedy in propagation
              if (currentList.get(0).getSize() < currentList.get(1).getSize()
                  || (currentList.get(0).getSize() == currentList.get(1).getSize() && !GREEDY)) {

                guideVariable = currentList.getFirst();
                guideValue = value;

              } else {

                guideVariable = currentList.get(1);
                guideValue = value;
              }
              minCurrentPruning = pruningFirstVariable;
              maxCurrentPruning = pruningSecondVariable;
            } else if (pruningSecondVariable > maxCurrentPruning) {
              // Equals sign means no greedy in propagation in
              // case of tie break
              // Lack of equal sign means greedy in propagation
              if (currentList.get(0).getSize() < currentList.get(1).getSize()
                  || (currentList.get(0).getSize() == currentList.get(1).getSize() && !GREEDY)) {

                guideVariable = currentList.getFirst();
                guideValue = value;

              } else {

                guideVariable = currentList.get(1);
                guideValue = value;
              }

              maxCurrentPruning = pruningSecondVariable;
            }

          } else {
            // PruningFirstVariable > PruningSecondVariable
            if (pruningSecondVariable > minCurrentPruning) {

              // Equal sign means greedy in case of tie break
              if (currentList.get(0).getSize() <= currentList.get(1).getSize()
                  || (currentList.get(0).getSize() == currentList.get(1).getSize() && GREEDY)) {

                guideVariable = currentList.getFirst();
                guideValue = value;
              } else {

                guideVariable = currentList.get(1);
                guideValue = value;
              }

              minCurrentPruning = pruningSecondVariable;
              maxCurrentPruning = pruningFirstVariable;
            } else if (pruningFirstVariable > maxCurrentPruning) {

              // Equal sign means greedy in case of tie break
              if (currentList.get(0).getSize() <= currentList.get(1).getSize()
                  || (currentList.get(0).getSize() == currentList.get(1).getSize() && !GREEDY)) {

                guideVariable = currentList.getFirst();
                guideValue = value;

              } else {

                guideVariable = currentList.get(1);
                guideValue = value;
              }
              maxCurrentPruning = pruningFirstVariable;
            }
          }
        }
      }
    }

    return guideVariable;
  }

  int estimatePruning(IntVar x, Integer v) {

    List<IntVar> exploredX = new ArrayList<>();
    List<Integer> exploredV = new ArrayList<>();

    int pruning = estimatePruningRecursive(x, v, exploredX, exploredV);

    for (Integer value : exploredV) {

      List<IntVar> currentList = variablesWithValue(value);

      for (IntVar variable : currentList) {
        // Edge between variable and value was not counted yet
        if (!exploredX.contains(variable)) {
          pruning++;
        }
      }
    }

    return pruning;
  }

  int estimatePruningRecursive(
      IntVar xvar, Integer v, List<IntVar> exploredX, List<Integer> exploredV) {

    if (exploredX.contains(xvar)) {
      return 0;
    }

    exploredX.add(xvar);
    exploredV.add(v);

    int pruning;

    IntDomain xDom = xvar.dom();
    pruning = xDom.getSize() - 1;

    List<IntVar> currentList;
    ValueEnumeration enumer = xDom.valueEnumeration();

    // Permutation only
    if (isPermutation()) {
      for (int i = enumer.nextElement(); enumer.hasMoreElements(); i = enumer.nextElement()) {
        if (!exploredV.contains(i)) {
          currentList = variablesWithValue(i);

          // check if there is at most one variable for value
          if (currentList.size() <= exploredX.size() + 1) {

            IntVar singleVar = null;
            boolean single = true;

            for (IntVar variable : currentList) {
              if (!exploredX.contains(variable)) {
                if (singleVar == null) {
                  singleVar = variable;
                } else {
                  single = false;
                }
              }
            }

            if (single && singleVar != null) {
              pruning += estimatePruningRecursive(singleVar, i, exploredX, exploredV);
            }
          }
        }
      }
    }

    for (IntVar variable : variablesWithValue(v)) {

      // checks if there is at most one value for variable
      if (!exploredX.contains(variable) && variable.dom().getSize() < exploredV.size() + 2) {

        boolean single = true;
        Integer singleVal = null;

        for (ValueEnumeration enumerX = variable.dom().valueEnumeration();
            enumerX.hasMoreElements(); ) {
          Integer next = enumerX.nextElement();

          if (!exploredV.contains(next)) {
            if (singleVal == null) {
              singleVal = next;
            } else {
              single = false;
            }
          }
        }

        if (single) {
          pruning += estimatePruningRecursive(variable, singleVal, exploredX, exploredV);
        }
      }
    }

    return pruning;
  }

  private IntVar[] notGroundedVariables() {
    int notGroundedNo = notGrounded.value();
    IntVar[] result = new IntVar[notGroundedNo];
    for (int j = 0; j < notGroundedNo; j++) {
      result[j] = list[position[j]];
    }
    return result;
  }

  // It returns the number of variables (grounded or not) which have the value in their domain.
  private int valueCount(int value) {
    int count = 0;
    for (IntVar x : list) {
      if (x.domain.contains(value)) {
        count++;
      }
    }
    return count;
  }

  private List<IntVar> variablesWithValue(int value) {
    List<IntVar> result = new ArrayList<>();
    for (IntVar x : list) {
      if (x.domain.contains(value)) {
        result.add(x);
      }
    }
    return result;
  }

  // It returns the values which are in the domain of at least one not grounded variable.
  private List<Integer> activeValues() {
    IntVar[] notGroundedVars = notGroundedVariables();
    List<Integer> result = new ArrayList<>();
    for (int value : values) {
      for (IntVar x : notGroundedVars) {
        if (x.domain.contains(value)) {
          result.add(value);
          break;
        }
      }
    }
    return result;
  }

  // The number of values still available equals the number of not grounded variables.
  private boolean isPermutation() {
    return activeValues().size() == notGrounded.value();
  }

  /**
   * Writes the constraint as one at-most-one line per value; the solver derives the pigeonhole
   * steps its Hall set explanations need.
   */
  @Override
  public boolean encode(PbModel model) {
    if (getClass() != Alldistinct.class
        || new HashSet<>(Arrays.asList(list)).size() != list.length) {
      return false;
    }
    model.allDifferent(list);
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return getClass() == Alldistinct.class
        && AlldiffExplanation.explain(trail, entry, list, new IntervalDomain(), out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == Alldistinct.class
        && AlldiffExplanation.explainFailure(trail, list, new IntervalDomain(), out);
  }

  @Override
  public Optional<List<Constraint>> simplify() {
    if (getClass() != Alldistinct.class) {
      return Optional.empty();
    }
    return GlobalSimplification.allDifferent(list, Alldistinct::new);
  }

  @Override
  public Alldistinct copy(VarMap map) {
    return new Alldistinct(map.get(list));
  }

  @Override
  public long violation(ToIntFunction<IntVar> value) {
    return Violations.duplicates(list, value);
  }
}
