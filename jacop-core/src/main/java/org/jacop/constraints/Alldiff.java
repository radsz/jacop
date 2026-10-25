/*
 * Alldiff.java
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
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Alldiff constraint assures that all FDVs has different values. It uses bounds consistency
 * technique as described in the paper by Alejandro Lopez-Ortiz, Claude-Guy Quimper, John Tromp,
 * Peter van Beek, "A fast and simple algorithm for bounds consistency of the alldifferent
 * constraint", Proceedings of the 18th international joint conference on Artificial intelligence
 * (IJCAI'03), Pages 245-250. Before using bounds consistency it calls consistency method for ground
 * variables.
 *
 * <p>It extends basic functionality of Alldifferent constraint.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Alldiff extends Alldifferent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final int INSERTION_SORT_LIMIT = 256;
  private static final Comparator<Element> BY_MIN = Comparator.comparingInt(o -> o.min);
  private static final Comparator<Element> BY_MAX = Comparator.comparingInt(o -> o.max);
  // it stores the store locally so all the private functions which
  // are part of the consistency function can throw failure exception
  // without passing store argument every time their function is called.
  protected Store store;
  private int[] t; // holds the critical capacity pointers; that is, t[i] points to the
  // predecessor of i in the bounds list.
  private int[] d; // holds the differences between critical capacities; that is d[i] is
  // the difference of capacities between bounds[i] and its predecessor
  // element in the list bounds[t[i]].
  private int[] h; // holds the Hall interval pointers; that is, if h[i] < i then the
  // half-open interval [bounds[h[i]],bounds[i]) is contained in a Hall
  // interval, and otherwise holds a pointer to the Hall interval it
  // belongs to. This Hall interval is represented by a tree, with the
  // root containing the value of its right end.
  private int[] bounds; // is a sorted array of all min’s and max’s.

  private int nb; // holds the number of unique bounds.

  private Element[] minsorted;
  private Element[] maxsorted;

  // Alldiff is woken on bound changes, but only grounded variables need their value removed from
  // the others, so only those are queued, in the order they became grounded.
  private IntVar[] groundedQueue = new IntVar[8];
  private int groundedQueueSize;

  /** Protected constructor for subclassing purposes. */
  protected Alldiff() {}

  /**
   * It constructs the alldiff constraint for the supplied variable.
   *
   * @param variables variables which are constrained to take different values.
   */
  public Alldiff(IntVar[] variables) {

    checkInputForNullness("x", variables);

    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(variables, variables.length);
    this.queueIndex = 2;

    int n = list.length;
    t = new int[2 * n + 2];
    d = new int[2 * n + 2];
    h = new int[2 * n + 2];
    bounds = new int[2 * n + 2];

    minsorted = new Element[n];
    maxsorted = new Element[n];
    for (int i = 0; i < n; i++) {
      Element el = new Element();
      el.v = list[i];
      minsorted[i] = el;
      maxsorted[i] = el;
    }

    setScope(variables);
  }

  /**
   * It constructs the alldiff constraint for the supplied variable.
   *
   * @param variables variables which are constrained to take different values.
   */
  public Alldiff(List<? extends IntVar> variables) {
    this(variables.toArray(new IntVar[0]));
  }

  @Override
  protected boolean keepsMatching() {
    return false;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void impose(Store store) {

    if (list.length == 0) {
      return;
    }

    super.impose(store);
    this.store = store;
  }

  @Override
  public void consistency(Store store) {

    if (store.currentQueue == queueIndex) {

      grounded.update(processGroundedQueue(store, grounded.value()));

      if (queueIndex + 1 < store.queueNo) {
        store.addChanged(this, queueIndex + 1);
        return;
      }
    }

    // Bounds reasoning on domains with holes is not idempotent (a new bound can land on a hole) and
    // variables grounded by this pass are queued only for this constraint, so repeat until stable.
    do {
      store.propagationHasOccurred = false;

      init();
      updateLb();
      updateUb();

      if (groundedQueueSize > 0) {
        grounded.update(processGroundedQueue(store, grounded.value()));
      }
    } while (store.propagationHasOccurred);
  }

  @Override
  public void queueVariable(int level, Var v) {
    if (v.singleton()) {
      if (groundedQueueSize == groundedQueue.length) {
        groundedQueue = Arrays.copyOf(groundedQueue, 2 * groundedQueueSize);
      }
      groundedQueue[groundedQueueSize++] = (IntVar) v;
    }
  }

  /**
   * Removes the values of queued grounded variables from all not grounded variables. Variables
   * grounded by this pruning are queued and processed in the same call.
   *
   * @param store the constraint store
   * @param groundPos the position of the first not grounded variable in list
   * @return the updated position of the first not grounded variable
   */
  private int processGroundedQueue(Store store, int groundPos) {
    try {
      for (int k = 0; k < groundedQueueSize; k++) {
        IntVar q = groundedQueue[k];
        if (!q.singleton()) {
          continue;
        }
        int qPos = positionMapping.get(q);
        if (qPos > groundPos) {
          list[qPos] = list[groundPos];
          list[groundPos] = q;
          positionMapping.put(q, groundPos);
          positionMapping.put(list[qPos], qPos);
        } else if (qPos < groundPos) {
          continue;
        }
        groundPos++;
        int value = q.min();
        for (int i = groundPos; i < list.length; i++) {
          list[i].domain.inComplement(store.level, list[i], value);
        }
      }
    } finally {
      groundedQueueSize = 0;
    }
    return groundPos;
  }

  /**
   * Initializes the bounds consistency data structures by sorting variables and computing unique
   * bounds. This method prepares the bounds array and ranks for each variable's min and max values.
   */
  private void init() {
    int n = list.length;
    for (int i = 0; i < n; i++) {
      Element el = minsorted[i];
      el.min = el.v.min();
      el.max = el.v.max();
    }
    sortByMin(minsorted, n);
    sortByMax(maxsorted, n);

    int min = minsorted[0].min;
    int max = maxsorted[0].max + 1;
    int last = min - 2;
    int numBounds = 0;
    bounds[0] = last;
    int i = 0;
    int j = 0;
    while (true) {
      if (i < n && min <= max) {
        if (min != last) {
          bounds[++numBounds] = last = min;
        }

        minsorted[i].minrank = numBounds;
        if (++i < n) {
          min = minsorted[i].min;
        }

      } else {
        if (max != last) {
          bounds[++numBounds] = last = max;
        }

        maxsorted[j].maxrank = numBounds;
        if (++j == n) {
          break;
        }

        max = maxsorted[j].max + 1;
      }
    }
    this.nb = numBounds;
    bounds[numBounds + 1] = bounds[numBounds] + 2;
  }

  // Stable insertion sorts: the arrays keep their order between calls and bounds change little, so
  // they are almost sorted and these run in near linear time. The result is the same as a stable
  // sort by the same key.
  private static void sortByMin(Element[] a, int n) {
    if (n > INSERTION_SORT_LIMIT) {
      Arrays.sort(a, 0, n, BY_MIN);
      return;
    }
    for (int i = 1; i < n; i++) {
      Element el = a[i];
      int key = el.min;
      int j = i - 1;
      while (j >= 0 && a[j].min > key) {
        a[j + 1] = a[j];
        j--;
      }
      a[j + 1] = el;
    }
  }

  private static void sortByMax(Element[] a, int n) {
    if (n > INSERTION_SORT_LIMIT) {
      Arrays.sort(a, 0, n, BY_MAX);
      return;
    }
    for (int i = 1; i < n; i++) {
      Element el = a[i];
      int key = el.max;
      int j = i - 1;
      while (j >= 0 && a[j].max > key) {
        a[j + 1] = a[j];
        j--;
      }
      a[j + 1] = el;
    }
  }

  /**
   * Performs lower bound propagation using Hall intervals to enforce bounds consistency. This
   * method updates variable lower bounds based on capacity constraints and Hall intervals.
   */
  private void updateLb() {

    for (int i = 1; i <= nb + 1; i++) {
      t[i] = h[i] = i - 1;
      d[i] = bounds[i] - bounds[i - 1];
    }
    for (int i = 0; i < this.list.length; i++) {
      int x = maxsorted[i].minrank;
      int y = maxsorted[i].maxrank;
      int z = pathmax(t, x + 1);
      int j = t[z];

      if (--d[z] == 0) {
        t[z] = z + 1;
        z = pathmax(t, t[z]);
        t[z] = j;
      }
      pathset(t, x + 1, z, z);
      if (d[z] < bounds[z] - bounds[y]) {
        throw Store.failException;
      }
      if (h[x] > x) {
        int w = pathmax(h, h[x]);
        maxsorted[i].v.domain.inMin(store.level, maxsorted[i].v, bounds[w]);
        pathset(h, x, w, w);
      }
      if (d[z] == bounds[z] - bounds[y]) {
        pathset(h, h[y], j - 1, y);
        h[y] = j - 1;
      }
    }
  }

  /**
   * Performs upper bound propagation using Hall intervals to enforce bounds consistency. This
   * method updates variable upper bounds based on capacity constraints and Hall intervals.
   */
  private void updateUb() {

    for (int i = 0; i <= nb; i++) {
      t[i] = h[i] = i + 1;
      d[i] = bounds[i + 1] - bounds[i];
    }
    for (int i = this.list.length - 1; i >= 0; i--) {
      int x = minsorted[i].maxrank;
      int y = minsorted[i].minrank;
      int z = pathmin(t, x - 1);
      int j = t[z];
      if (--d[z] == 0) {
        t[z] = z - 1;
        z = pathmin(t, t[z]);
        t[z] = j;
      }
      pathset(t, x - 1, z, z);
      if (d[z] < bounds[y] - bounds[z]) {
        throw Store.failException;
      }
      if (h[x] < x) {
        int w = pathmin(h, h[x]);
        minsorted[i].v.domain.inMax(store.level, minsorted[i].v, bounds[w] - 1);
        pathset(h, x, w, w);
      }
      if (d[z] == bounds[y] - bounds[z]) {
        pathset(h, h[y], j + 1, y);
        h[y] = j + 1;
      }
    }
  }

  /**
   * Sets all elements in path from start to end to point to the given target value. This is a path
   * compression operation used in the union-find-like structure for Hall intervals.
   *
   * @param v the array representing the path structure
   * @param start the starting position in the path
   * @param end the ending position in the path
   * @param to the target value to set for all elements in the path
   */
  private void pathset(int[] v, int start, int end, int to) {
    int next = start;
    int prev = next;
    while (prev != end) {
      next = v[prev];
      v[prev] = to;
      prev = next;
    }
  }

  /**
   * Finds the minimum element in the path starting from the given index. Follows the path structure
   * downward until reaching a local minimum.
   *
   * @param v the array representing the path structure
   * @param i the starting index
   * @return the index of the minimum element in the path
   */
  private int pathmin(int[] v, int i) {
    while (v[i] < i) {
      i = v[i];
    }

    return i;
  }

  /**
   * Finds the maximum element in the path starting from the given index. Follows the path structure
   * upward until reaching a local maximum.
   *
   * @param v the array representing the path structure
   * @param i the starting index
   * @return the index of the maximum element in the path
   */
  private int pathmax(int[] v, int i) {
    while (v[i] > i) {
      i = v[i];
    }

    return i;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : Alldiff([");
    appendArrayToString(result, list);
    result.append("])");

    return result.toString();
  }

  /**
   * Propagates the alldifferent constraint for singleton variables by removing their values from
   * all other variable domains. This ensures that once a variable is assigned, no other variable
   * can take the same value.
   *
   * @param store the constraint store
   * @param fdvs the set of changed variables to process
   */
  protected void propagateAllDifferentOnSingletons(Store store, LinkedHashSet<IntVar> fdvs) {
    for (IntVar changedVar : fdvs) {
      if (changedVar.singleton()) {
        for (IntVar v : list) {
          if (v != changedVar) {
            v.domain.inComplement(store.level, v, changedVar.min());
          }
        }
      }
    }
  }

  /**
   * Internal data structure representing a variable with its ranking information. Used during
   * bounds consistency propagation.
   */
  private static class Element {
    private IntVar v;
    private int minrank;
    private int maxrank;
    // bounds of v cached for sorting
    private int min;
    private int max;
  }

  @Override
  public Alldiff copy(VarMap map) {
    return new Alldiff(map.get(list));
  }
}
