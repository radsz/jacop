/*
 * Sort.java
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
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Sort constraint (sortedness): y is x sorted in non-decreasing order, that is y is non-decreasing
 * and the multisets of the values of x and y are equal. With permutation variables z it also
 * requires x[i] = y[z[i] - zOffset] for every i, so z is a permutation that sorts x.
 *
 * <p>The propagator is bounds(Z) consistent for x and y and gives bounds consistent bounds to z
 * when z has no holes. It implements the algorithm of K. Mehlhorn and S. Thiel, "Faster algorithms
 * for bound-consistency of the sortedness and the alldifferent constraint", CP 2000, in the form of
 * the Gecode Sorted propagator: normalisation of the y bounds, Glover's matching between the x
 * intervals and the y positions in the convex intersection graph, the strongly connected components
 * of the oriented intersection graph computed with one stack in the order of the positions, and the
 * narrowing of every bound to its leftmost and rightmost position in a perfect matching. One pass
 * costs O(n log n). The permutation variables restrict the positions of every x to the bounds of
 * its z, which keeps the intersection graph convex.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class Sort extends Constraint implements SatisfiedPresent, Copyable<Sort> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The variables to sort. */
  final IntVar[] x;

  /** The sorted variables. */
  final IntVar[] y;

  /** The permutation variables, x[i] = y[z[i] - zOffset]; null without them. */
  final IntVar[] z;

  /** The value of z[i] that denotes the first position of y. */
  final int zOffset;

  final int n;

  // the bounds of one pass
  private final int[] xl;
  private final int[] xh;
  private final int[] yl;
  private final int[] yh;

  // the positions of y an x can take: lo[i]..hi[i]
  private final int[] lo;
  private final int[] hi;

  // the matching: phi[j] is the x at position j, pos[i] the position of x[i]
  private final int[] phi;
  private final int[] pos;

  private final int[] heap;
  private int[] heapKey;
  private int heapSign;
  private final int[] order;
  private final int[] bucket;
  private final int[] sorted;

  // components: the positions of each component, sorted, are compPos[compStart[c]..compEnd[c]]
  private final int[] comp;
  private final int[] compStart;
  private final int[] compEnd;
  private final int[] compPos;
  private final int[] indexOf;

  // the stack of the component algorithm and the linked lists of positions of its components
  private final int[] stackRight;
  private final int[] stackLeft;
  private final int[] stackReach;
  private final int[] stackMinLo;
  private final int[] next;
  private final int[] tail;

  // the first and the last position x[i] takes in some perfect matching
  private final int[] first;
  private final int[] last;

  // painting of the y bounds
  private final int[] paint;
  private final int[] skip;
  private final long[] keys;

  /**
   * It constructs sort(x, y): y is x sorted in non-decreasing order.
   *
   * @param x the variables to sort.
   * @param y the sorted variables, as many as x.
   */
  public Sort(IntVar[] x, IntVar[] y) {
    this(x, y, null, 0);
  }

  /**
   * It constructs sort(x, y): y is x sorted in non-decreasing order.
   *
   * @param x the variables to sort.
   * @param y the sorted variables, as many as x.
   */
  public Sort(List<? extends IntVar> x, List<? extends IntVar> y) {
    this(x.toArray(new IntVar[0]), y.toArray(new IntVar[0]));
  }

  /**
   * It constructs sort(x, y, z): y is x sorted in non-decreasing order and x[i] = y[z[i] - zOffset]
   * for every i.
   *
   * @param x the variables to sort.
   * @param y the sorted variables, as many as x.
   * @param z the position in y of every x, as many as x; null for none.
   * @param zOffset the value of z that denotes the first position of y.
   */
  public Sort(IntVar[] x, IntVar[] y, IntVar[] z, int zOffset) {

    checkInputForNullness("x", x);
    checkInputForNullness("y", y);
    if (x.length != y.length) {
      throw new IllegalArgumentException("Sort: x and y must have the same length");
    }
    if (z != null) {
      checkInputForNullness("z", z);
      if (z.length != x.length) {
        throw new IllegalArgumentException("Sort: x and z must have the same length");
      }
    }

    this.numberId = idNumber.incrementAndGet();
    this.n = x.length;
    this.x = Arrays.copyOf(x, n);
    this.y = Arrays.copyOf(y, n);
    this.z = z == null ? null : Arrays.copyOf(z, n);
    this.zOffset = zOffset;

    xl = new int[n];
    xh = new int[n];
    yl = new int[n];
    yh = new int[n];
    lo = new int[n];
    hi = new int[n];
    phi = new int[n];
    pos = new int[n];
    heap = new int[n];
    order = new int[n];
    bucket = new int[n + 1];
    sorted = new int[n];
    comp = new int[n];
    compStart = new int[n];
    compEnd = new int[n];
    compPos = new int[n];
    indexOf = new int[n];
    stackRight = new int[n];
    stackLeft = new int[n];
    stackReach = new int[n];
    stackMinLo = new int[n];
    next = new int[n];
    tail = new int[n];
    first = new int[n];
    last = new int[n];
    paint = new int[n];
    skip = new int[n + 1];
    keys = new long[n];

    this.queueIndex = 1;

    if (z == null) {
      setScope(Stream.concat(Arrays.stream(x), Arrays.stream(y)));
    } else {
      setScope(Stream.of(x, y, z).flatMap(Arrays::stream));
    }
  }

  /**
   * It constructs sort(x, y, z): y is x sorted in non-decreasing order and x[i] = y[z[i] - zOffset]
   * for every i.
   *
   * @param x the variables to sort.
   * @param y the sorted variables, as many as x.
   * @param z the position in y of every x, as many as x.
   * @param zOffset the value of z that denotes the first position of y.
   */
  public Sort(
      List<? extends IntVar> x, List<? extends IntVar> y, List<? extends IntVar> z, int zOffset) {
    this(x.toArray(new IntVar[0]), y.toArray(new IntVar[0]), z.toArray(new IntVar[0]), zOffset);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void consistency(Store store) {
    if (n == 0) {
      return;
    }
    // a pass narrows the bounds to the supports of the bounds it read; a bound moved onto a hole
    // or a repeated variable changes the graph, so passes repeat until nothing changes
    do {
      store.propagationHasOccurred = false;
      pass(store);
    } while (store.propagationHasOccurred);
  }

  private void pass(Store store) {
    readBounds();
    normalizeY();
    narrowYBySortedX();

    // y from the graph without z, which is weaker than the constraint and so gives sound bounds:
    // the matching from the left that takes the smallest maximum bounds y from above, the one
    // from the right that takes the largest minimum bounds it from below (Mehlhorn and Thiel)
    positions(false);
    match(xh);
    for (int j = 0; j < n; j++) {
      yh[j] = Math.min(yh[j], xh[phi[j]]);
    }
    matchFromRight();
    for (int j = 0; j < n; j++) {
      yl[j] = Math.max(yl[j], xl[phi[j]]);
    }
    if (applyY(store)) {
      // the graph changed
      return;
    }

    if (z != null) {
      positions(true);
      match(hi);
    } else {
      match(xh);
    }
    components();
    narrowX(store);
    if (z != null) {
      narrowYByComponents(store);
    }
  }

  /** It narrows y to yl..yh and tells whether a domain changed. */
  private boolean applyY(Store store) {
    boolean changed = false;
    for (int j = 0; j < n; j++) {
      if (yl[j] > yh[j]) {
        throw Store.failException;
      }
      IntVar yj = y[j];
      if (yl[j] > yj.min() || yh[j] < yj.max()) {
        yj.domain.in(store.level, yj, yl[j], yh[j]);
        changed = true;
      }
    }
    return changed;
  }

  private void readBounds() {
    for (int i = 0; i < n; i++) {
      xl[i] = x[i].min();
      xh[i] = x[i].max();
      yl[i] = y[i].min();
      yh[i] = y[i].max();
    }
  }

  /** y is non-decreasing: the minima rise from the left and the maxima fall from the right. */
  private void normalizeY() {
    for (int j = 1; j < n; j++) {
      if (yl[j] < yl[j - 1]) {
        yl[j] = yl[j - 1];
      }
    }
    for (int j = n - 2; j >= 0; j--) {
      if (yh[j] > yh[j + 1]) {
        yh[j] = yh[j + 1];
      }
    }
  }

  /**
   * The j-th smallest value of x lies between the j-th smallest minimum and the j-th smallest
   * maximum of x. Both sequences are non-decreasing, so y stays normalised.
   */
  private void narrowYBySortedX() {
    System.arraycopy(xl, 0, sorted, 0, n);
    Arrays.sort(sorted);
    for (int j = 0; j < n; j++) {
      if (yl[j] < sorted[j]) {
        yl[j] = sorted[j];
      }
    }
    System.arraycopy(xh, 0, sorted, 0, n);
    Arrays.sort(sorted);
    for (int j = 0; j < n; j++) {
      if (yh[j] > sorted[j]) {
        yh[j] = sorted[j];
      }
      if (yl[j] > yh[j]) {
        throw Store.failException;
      }
    }
  }

  /**
   * x[i] intersects y[j] for j in lo[i]..hi[i]: the maxima of y are non-decreasing, so lo[i] is the
   * first position whose maximum reaches the minimum of x[i], and hi[i] is the last position whose
   * minimum is at most the maximum of x[i]. With permutation, z[i] restricts the positions to its
   * bounds.
   */
  private void positions(boolean permutation) {
    for (int i = 0; i < n; i++) {
      int a = firstMaxAtLeast(xl[i]);
      int b = lastMinAtMost(xh[i]);
      if (permutation) {
        a = Math.max(a, z[i].min() - zOffset);
        b = Math.min(b, z[i].max() - zOffset);
      }
      if (a > b) {
        throw Store.failException;
      }
      lo[i] = a;
      hi[i] = b;
    }
  }

  private int firstMaxAtLeast(int v) {
    int a = 0;
    int b = n;
    while (a < b) {
      int m = (a + b) >>> 1;
      if (yh[m] >= v) {
        b = m;
      } else {
        a = m + 1;
      }
    }
    return a;
  }

  private int lastMinAtMost(int v) {
    int a = -1;
    int b = n - 1;
    while (a < b) {
      int m = (a + b + 1) >>> 1;
      if (yl[m] <= v) {
        a = m;
      } else {
        b = m - 1;
      }
    }
    return a;
  }

  /**
   * Glover's matching in the convex graph: the positions in increasing order, each taking the x
   * with the smallest key among the x that can already take it. With a key that orders the x as
   * their last positions do, it fails exactly when no perfect matching exists. phi[j] is the x at
   * position j and pos[i] the position of x[i].
   */
  private void match(int[] key) {
    // x in the order of their first positions (counting sort)
    Arrays.fill(bucket, 0);
    for (int i = 0; i < n; i++) {
      bucket[lo[i] + 1]++;
    }
    for (int j = 0; j < n; j++) {
      bucket[j + 1] += bucket[j];
    }
    for (int i = 0; i < n; i++) {
      order[bucket[lo[i]]++] = i;
    }

    heapKey = key;
    heapSign = 1;
    int size = 0;
    int k = 0;
    for (int j = 0; j < n; j++) {
      while (k < n && lo[order[k]] <= j) {
        size = heapPush(size, order[k++]);
      }
      if (size == 0) {
        throw Store.failException;
      }
      int i = heap[0];
      if (hi[i] < j) {
        throw Store.failException;
      }
      size = heapPop(size);
      phi[j] = i;
      pos[i] = j;
    }
  }

  /**
   * The symmetric matching: the positions in decreasing order, each taking the x with the largest
   * minimum among the x that can already take it. Only phi is set.
   */
  private void matchFromRight() {
    // x in decreasing order of their last positions (counting sort)
    Arrays.fill(bucket, 0);
    for (int i = 0; i < n; i++) {
      bucket[n - 1 - hi[i] + 1]++;
    }
    for (int j = 0; j < n; j++) {
      bucket[j + 1] += bucket[j];
    }
    for (int i = 0; i < n; i++) {
      order[bucket[n - 1 - hi[i]]++] = i;
    }

    heapKey = xl;
    heapSign = -1;
    int size = 0;
    int k = 0;
    for (int j = n - 1; j >= 0; j--) {
      while (k < n && hi[order[k]] >= j) {
        size = heapPush(size, order[k++]);
      }
      if (size == 0) {
        throw Store.failException;
      }
      int i = heap[0];
      if (lo[i] > j) {
        throw Store.failException;
      }
      size = heapPop(size);
      phi[j] = i;
    }
  }

  /** It tells whether x[a] comes out of the heap before x[b]. */
  private boolean before(int a, int b) {
    return heapSign * (long) heapKey[a] < heapSign * (long) heapKey[b];
  }

  private int heapPush(int size, int i) {
    int c = size;
    while (c > 0) {
      int p = (c - 1) >>> 1;
      if (!before(i, heap[p])) {
        break;
      }
      heap[c] = heap[p];
      c = p;
    }
    heap[c] = i;
    return size + 1;
  }

  private int heapPop(int size) {
    int s = size - 1;
    int i = heap[s];
    int c = 0;
    while (true) {
      int l = 2 * c + 1;
      if (l >= s) {
        break;
      }
      if (l + 1 < s && before(heap[l + 1], heap[l])) {
        l++;
      }
      if (!before(heap[l], i)) {
        break;
      }
      heap[c] = heap[l];
      c = l;
    }
    heap[c] = i;
    return s;
  }

  /**
   * The strongly connected components of the oriented intersection graph, as sets of positions;
   * position j stands for the matched pair of y[j] and x[phi[j]], and j reaches k when x[phi[j]]
   * can take position k. The positions are visited in increasing order with a stack of the open
   * components: a component that cannot reach the new position cannot reach any later one either
   * (the positions of an x are an interval), so it is closed; the new position merges with the
   * components on the top of the stack that it reaches, and these reach it through the components
   * above them.
   */
  private void components() {
    int top = -1;
    int components = 0;
    int filled = 0;
    for (int j = 0; j < n; j++) {
      while (top >= 0 && stackReach[top] < j) {
        filled = close(stackLeft[top], components++, filled);
        top--;
      }
      int i = phi[j];
      int left = j;
      int reach = hi[i];
      int minLo = lo[i];
      next[j] = -1;
      tail[j] = j;
      while (top >= 0 && minLo <= stackRight[top]) {
        // the component on the top comes first: its positions are smaller
        int l = stackLeft[top];
        next[tail[l]] = left;
        tail[l] = tail[left];
        left = l;
        reach = Math.max(reach, stackReach[top]);
        minLo = Math.min(minLo, stackMinLo[top]);
        top--;
      }
      top++;
      stackLeft[top] = left;
      stackRight[top] = j;
      stackReach[top] = reach;
      stackMinLo[top] = minLo;
    }
    while (top >= 0) {
      filled = close(stackLeft[top], components++, filled);
      top--;
    }
  }

  /** It lists the positions of the component that starts at position left, in increasing order. */
  private int close(int left, int c, int filled) {
    compStart[c] = filled;
    for (int j = left; j >= 0; j = next[j]) {
      comp[j] = c;
      indexOf[j] = filled;
      compPos[filled++] = j;
    }
    compEnd[c] = filled - 1;
    return filled;
  }

  /**
   * An edge between x[i] and position j is in some perfect matching exactly when it is the matching
   * edge or j is in the component of the position of x[i]. x[i] is narrowed to the first and the
   * last such position, whose y bounds are the smallest and the largest (y is normalised).
   */
  private void narrowX(Store store) {
    for (int i = 0; i < n; i++) {
      int c = comp[pos[i]];
      int a = firstIndexAtLeast(compStart[c], indexOf[pos[i]], lo[i]);
      int b = lastIndexAtMost(indexOf[pos[i]], compEnd[c], hi[i]);
      first[i] = a;
      last[i] = b;
      int min = Math.max(xl[i], yl[compPos[a]]);
      int max = Math.min(xh[i], yh[compPos[b]]);
      if (min > xl[i] || max < xh[i]) {
        x[i].domain.in(store.level, x[i], min, max);
      }
      if (z != null) {
        IntVar zi = z[i];
        int zmin = compPos[a] + zOffset;
        int zmax = compPos[b] + zOffset;
        if (zmin > zi.min() || zmax < zi.max()) {
          zi.domain.in(store.level, zi, zmin, zmax);
        }
      }
    }
  }

  /** The first index in compPos[from..to] whose position is at least p; to itself qualifies. */
  private int firstIndexAtLeast(int from, int to, int p) {
    int a = from;
    int b = to;
    while (a < b) {
      int m = (a + b) >>> 1;
      if (compPos[m] >= p) {
        b = m;
      } else {
        a = m + 1;
      }
    }
    return a;
  }

  /** The last index in compPos[from..to] whose position is at most p; from itself qualifies. */
  private int lastIndexAtMost(int from, int to, int p) {
    int a = from;
    int b = to;
    while (a < b) {
      int m = (a + b + 1) >>> 1;
      if (compPos[m] <= p) {
        a = m;
      } else {
        b = m - 1;
      }
    }
    return a;
  }

  /**
   * y[j] is narrowed to the smallest minimum and the largest maximum of the x that take position j
   * in some perfect matching. These x take the indices first[i]..last[i] of the positions of their
   * component, so each bound paints, in order of value, the indices not painted yet. Without z this
   * adds nothing to the matchings.
   */
  private void narrowYByComponents(Store store) {
    // minima: x in increasing order of their minimum
    sortIndices(xl, false);
    paintIndices(xl);
    for (int k = 0; k < n; k++) {
      int j = compPos[k];
      if (paint[k] > yl[j]) {
        yl[j] = paint[k];
      }
    }
    sortIndices(xh, true);
    paintIndices(xh);
    for (int k = 0; k < n; k++) {
      int j = compPos[k];
      if (paint[k] < yh[j]) {
        yh[j] = paint[k];
      }
    }
    // an x whose last position is at most j sits at or before j, so y[j] is at least its minimum;
    // one whose first position is at least j bounds y[j] from above
    Arrays.fill(sorted, Integer.MIN_VALUE);
    for (int i = 0; i < n; i++) {
      int b = compPos[last[i]];
      sorted[b] = Math.max(sorted[b], xl[i]);
    }
    for (int j = 0, m = Integer.MIN_VALUE; j < n; j++) {
      m = Math.max(m, sorted[j]);
      yl[j] = Math.max(yl[j], m);
    }
    Arrays.fill(sorted, Integer.MAX_VALUE);
    for (int i = 0; i < n; i++) {
      int a = compPos[first[i]];
      sorted[a] = Math.min(sorted[a], xh[i]);
    }
    for (int j = n - 1, m = Integer.MAX_VALUE; j >= 0; j--) {
      m = Math.min(m, sorted[j]);
      yh[j] = Math.min(yh[j], m);
    }
    applyY(store);
  }

  /** order[] gets the indices of x sorted by the given bound, decreasing when descending. */
  private void sortIndices(int[] bound, boolean descending) {
    for (int i = 0; i < n; i++) {
      long v = descending ? -(long) bound[i] : bound[i];
      keys[i] = (v << 32) | i;
    }
    Arrays.sort(keys);
    for (int i = 0; i < n; i++) {
      order[i] = (int) keys[i];
    }
  }

  private void paintIndices(int[] bound) {
    for (int k = 0; k <= n; k++) {
      skip[k] = k;
    }
    for (int k = 0; k < n; k++) {
      int i = order[k];
      int b = last[i];
      for (int f = find(first[i]); f <= b; f = find(f + 1)) {
        paint[f] = bound[i];
        skip[f] = f + 1;
      }
    }
  }

  /** The first index from k on that is not painted, with path halving. */
  private int find(int k) {
    while (skip[k] != k) {
      skip[k] = skip[skip[k]];
      k = skip[k];
    }
    return k;
  }

  @Override
  public boolean satisfied() {
    for (int i = 0; i < n; i++) {
      if (!x[i].singleton() || !y[i].singleton() || z != null && !z[i].singleton()) {
        return false;
      }
    }
    int[] xs = new int[n];
    for (int i = 0; i < n; i++) {
      xs[i] = x[i].value();
      if (i > 0 && y[i - 1].value() > y[i].value()) {
        return false;
      }
    }
    if (z != null) {
      boolean[] used = new boolean[n];
      for (int i = 0; i < n; i++) {
        int j = z[i].value() - zOffset;
        if (j < 0 || j >= n || used[j] || y[j].value() != xs[i]) {
          return false;
        }
        used[j] = true;
      }
      return true;
    }
    Arrays.sort(xs);
    for (int i = 0; i < n; i++) {
      if (xs[i] != y[i].value()) {
        return false;
      }
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : Sort(");
    append(result, x);
    result.append(", ");
    append(result, y);
    if (z != null) {
      result.append(", ");
      append(result, z);
      result.append(", ").append(zOffset);
    }
    result.append(")");
    return result.toString();
  }

  private static void append(StringBuilder result, Var[] vars) {
    result.append("[");
    for (int i = 0; i < vars.length; i++) {
      if (i > 0) {
        result.append(", ");
      }
      result.append(vars[i]);
    }
    result.append("]");
  }

  @Override
  public Sort copy(VarMap map) {
    return new Sort(map.get(x), map.get(y), z == null ? null : map.get(z), zOffset);
  }
}
