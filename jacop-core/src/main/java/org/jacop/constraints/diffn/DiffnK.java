/*
 * DiffnK.java This file is part of JaCoP.
 *
 * <p>JaCoP is a Java Constraint Programming solver.
 *
 * <p>Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 * <p>This program is free software: you can redistribute it and/or modify it under the terms of the
 * GNU Affero General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * <p>This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Affero General Public License for more details.
 *
 * <p>Notwithstanding any other provision of this License, the copyright owners of this work
 * supplement the terms of this License with terms prohibiting misrepresentation of the origin of
 * this work and requiring that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license terms is in accordance with
 * Section 7 of GNU Affero General Public License version 3.
 *
 * <p>You should have received a copy of the GNU Affero General Public License along with this
 * program. If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints.diffn;

import java.util.Arrays;
import java.util.BitSet;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;

/**
 * Non-overlapping k-dimensional boxes with variable origins and lengths (MiniZinc {@code diffn_k}
 * and {@code diffn_nonstrict_k}). Boxes i and j do not overlap if, in some dimension d, {@code
 * origin[i][d] + length[i][d] <= origin[j][d]} or {@code origin[j][d] + length[j][d] <=
 * origin[i][d]}.
 *
 * <p>Strict (the default): a box with length 0 in some dimension still may not overlap another box
 * (in that dimension it may not lie strictly inside the other box). Non-strict: a box with length 0
 * in any dimension is ignored.
 *
 * <p>Lengths are non-negative; negative values are removed when the constraint is imposed.
 *
 * <p>Propagation:
 *
 * <ul>
 *   <li>pairwise: two boxes that must overlap in all dimensions but one are separated in that
 *       dimension (bounds when one order is impossible, otherwise the origins that would overlap
 *       the other box's compulsory part are removed);
 *   <li>volume: the minimum volumes of a box and the boxes it may overlap must fit in their
 *       bounding box, and so must their number;
 *   <li>non-strict only: a box that cannot be placed at its smallest positive lengths is made
 *       absent, by setting to 0 its only length that can be 0 or its presence handle.
 * </ul>
 *
 * <p>A presence handle of box i is a variable such that, in every solution, the box is absent (some
 * length is 0) only if the handle is 0. Setting it to 0 is how the constraint removes a box whose
 * lengths can be 0 in several dimensions. A length of the box is a valid handle when any of its
 * lengths being 0 forces that length to 0, for example when all lengths are zero or positive
 * together.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class DiffnK extends Constraint implements SatisfiedPresent, Copyable<DiffnK> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final Box[] box;

  final int k;

  final boolean strict;

  /** Presence handle of each box, or null. Used only by the non-strict constraint. */
  IntVar[] handle;

  /** For each box, the boxes it may still overlap. */
  TimeStamp<BitSet>[] candidates;

  Store store;

  private boolean projection;

  private boolean slices;

  // work arrays of layers 4 and 5
  private long[] events;
  private boolean[] active;
  private long[] crossSection;
  private long[] segmentStart;
  private long[] segmentEnd;
  private long[] segmentHeight;

  /**
   * It creates a strict non-overlapping constraint.
   *
   * @param origin origin[i][d] is the origin of box i in dimension d.
   * @param length length[i][d] is the length of box i in dimension d.
   */
  public DiffnK(IntVar[][] origin, IntVar[][] length) {
    this(origin, length, true);
  }

  /**
   * It creates a non-overlapping constraint.
   *
   * @param origin origin[i][d] is the origin of box i in dimension d.
   * @param length length[i][d] is the length of box i in dimension d.
   * @param strict true: boxes with length 0 still may not overlap others; false: they are ignored.
   */
  public DiffnK(IntVar[][] origin, IntVar[][] length, boolean strict) {
    this(origin, length, strict, null);
  }

  /**
   * It creates a non-overlapping constraint with presence handles.
   *
   * @param origin origin[i][d] is the origin of box i in dimension d.
   * @param length length[i][d] is the length of box i in dimension d.
   * @param strict true: boxes with length 0 still may not overlap others; false: they are ignored.
   * @param handle presence handle of each box (null entries allowed), or null; see the class
   *     description. Used only when strict is false.
   */
  public DiffnK(IntVar[][] origin, IntVar[][] length, boolean strict, IntVar[] handle) {

    if (origin == null || length == null) {
      throw new IllegalArgumentException("DiffnK: origins or lengths are null");
    }
    if (origin.length != length.length) {
      throw new IllegalArgumentException(
          "DiffnK: " + origin.length + " origins but " + length.length + " lengths");
    }
    if (handle != null && handle.length != origin.length) {
      throw new IllegalArgumentException(
          "DiffnK: " + origin.length + " boxes but " + handle.length + " presence handles");
    }

    int dims = origin.length == 0 ? 1 : origin[0].length;
    if (dims < 1) {
      throw new IllegalArgumentException("DiffnK: boxes need at least one dimension");
    }

    this.queueIndex = 2;
    this.numberId = idNumber.incrementAndGet();
    this.k = dims;
    this.strict = strict;
    this.box = new Box[origin.length];
    for (int i = 0; i < origin.length; i++) {
      if (origin[i] == null || length[i] == null) {
        throw new IllegalArgumentException("DiffnK: box " + i + " is null");
      }
      if (origin[i].length != dims || length[i].length != dims) {
        throw new IllegalArgumentException(
            "DiffnK: box " + i + " does not have " + dims + " origins and " + dims + " lengths");
      }
      for (int d = 0; d < dims; d++) {
        if (origin[i][d] == null || length[i][d] == null) {
          throw new IllegalArgumentException("DiffnK: box " + i + " has a null variable");
        }
      }
      box[i] = new Box(origin[i].clone(), length[i].clone(), i);
    }
    this.handle = handle == null ? null : handle.clone();

    setScope(
        Stream.concat(
            Arrays.stream(box)
                .flatMap(b -> Stream.concat(Arrays.stream(b.origin), Arrays.stream(b.length))),
            this.handle == null
                ? Stream.<Var>empty()
                : Arrays.stream(this.handle).filter(h -> h != null)));
  }

  /**
   * It sets the presence handle of each box (see the class description). It is used by the FlatZinc
   * front end after it has proven the handles by probing, before search starts.
   *
   * @param handles presence handle of each box (null entries allowed).
   */
  public void setPresenceHandles(IntVar[] handles) {
    if (handles.length != box.length) {
      throw new IllegalArgumentException(
          "DiffnK: " + box.length + " boxes but " + handles.length + " presence handles");
    }
    for (IntVar h : handles) {
      if (h != null && !arguments().contains(h)) {
        throw new IllegalArgumentException(
            "DiffnK: a presence handle must be one of the lengths of the constraint, got " + h);
      }
    }
    this.handle = handles.clone();
  }

  /**
   * It returns the number of dimensions.
   *
   * @return the number of dimensions of the boxes.
   */
  public int dimensions() {
    return k;
  }

  /**
   * It returns whether boxes with length 0 still may not overlap other boxes.
   *
   * @return true for the strict constraint.
   */
  public boolean isStrict() {
    return strict;
  }

  /**
   * It returns the length variables of box i.
   *
   * @param i the box.
   * @return the lengths of box i, one per dimension.
   */
  public IntVar[] lengths(int i) {
    return box[i].length.clone();
  }

  /**
   * It returns the number of boxes.
   *
   * @return the number of boxes.
   */
  public int boxes() {
    return box.length;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  @SuppressWarnings("unchecked")
  public void impose(Store store) {

    this.store = store;
    super.impose(store);

    candidates = new TimeStamp[box.length];
    for (int i = 0; i < box.length; i++) {
      BitSet bs = new BitSet(box.length);
      bs.set(0, box.length);
      bs.clear(i);
      candidates[i] = new TimeStamp<>(store, bs);
      for (IntVar l : box[i].length) {
        l.domain.inMin(store.level, l, 0);
      }
    }
  }

  /**
   * It switches the cumulative projection per dimension on or off (off by default). For each
   * dimension d, the boxes crossing a hyperplane across d are disjoint in the other dimensions, so
   * their cross-sections (the products of their minimal lengths in the other dimensions) fit in the
   * cross-section of the space all boxes may take. It fails on an overloaded time-table of the
   * compulsory parts and moves the origins of the boxes away from where they would overload it.
   *
   * @param projection true to run the projection.
   */
  public void doProjection(boolean projection) {
    this.projection = projection;
  }

  /**
   * It switches the slice check on or off (off by default). For each dimension d and each point t,
   * the boxes whose compulsory part in d contains t are pairwise disjoint in the other dimensions,
   * so their cross-sections must fit in their own bounding box there. It only fails.
   *
   * @param slices true to run the slice check.
   */
  public void doSlices(boolean slices) {
    this.slices = slices;
  }

  @Override
  public void consistency(Store store) {
    this.store = store;
    do {
      store.propagationHasOccurred = false;
      pruning();
      if (!store.propagationHasOccurred && (projection || slices) && box.length > 1) {
        for (int d = 0; d < k && !store.propagationHasOccurred; d++) {
          int m = compulsoryParts(d);
          if (m == 0) {
            continue;
          }
          if (slices) {
            slices(d, m);
          }
          if (projection) {
            projection(d, m);
          }
        }
      }
    } while (store.propagationHasOccurred);
  }

  /**
   * Sorts the start and end events of the compulsory parts in dimension d into events, by date with
   * ends before starts at the same date.
   *
   * @return the number of events.
   */
  private int compulsoryParts(int d) {
    if (events == null) {
      events = new long[2 * box.length];
      active = new boolean[box.length];
      crossSection = new long[box.length];
      segmentStart = new long[2 * box.length];
      segmentEnd = new long[2 * box.length];
      segmentHeight = new long[2 * box.length];
    }
    int m = 0;
    for (int i = 0; i < box.length; i++) {
      Box b = box[i];
      long lst = b.lst(d);
      long ect = b.ect(d);
      if (lst < ect) {
        events[m++] = event(lst, true, i);
        events[m++] = event(ect, false, i);
      }
    }
    Arrays.sort(events, 0, m);
    return m;
  }

  // dates are origins and ends of boxes, so they fit in 32 bits with a sign
  private static long event(long date, boolean start, int i) {
    return (date << 32) | (start ? 1L << 31 : 0) | i;
  }

  private static long date(long event) {
    return event >> 32;
  }

  private static boolean start(long event) {
    return (event & (1L << 31)) != 0;
  }

  private static int boxOf(long event) {
    return (int) (event & Integer.MAX_VALUE);
  }

  /** The product of the minimal lengths of b in all dimensions but d. */
  private long crossSection(Box b, int d) {
    long v = 1;
    for (int e = 0; e < k && v > 0; e++) {
      if (e != d) {
        v = multiply(v, b.length[e].min());
      }
    }
    return v;
  }

  /**
   * Layer 4: the boxes as tasks in dimension d with their cross-sections as heights, against the
   * cross-section of the space all boxes may take (all boxes, not only the candidates, since any of
   * them may cross the hyperplane).
   */
  private void projection(int d, int m) {
    long capacity = 1;
    for (int e = 0; e < k && capacity > 0; e++) {
      if (e != d) {
        long low = Long.MAX_VALUE;
        long high = Long.MIN_VALUE;
        for (Box b : box) {
          low = Math.min(low, b.est(e));
          high = Math.max(high, b.lct(e));
        }
        capacity = multiply(capacity, Math.max(0, high - low));
      }
    }
    if (capacity == Long.MAX_VALUE) {
      return;
    }

    // the time-table: segments of constant height between consecutive dates
    int segments = 0;
    long height = 0;
    for (int t = 0; t < m; t++) {
      long e = events[t];
      int i = boxOf(e);
      if (start(e)) {
        crossSection[i] = crossSection(box[i], d);
        height = add(height, crossSection[i]);
      } else {
        height -= crossSection[i];
      }
      if (t + 1 < m && date(events[t + 1]) == date(e)) {
        continue;
      }
      if (height > capacity) {
        throw Store.failException;
      }
      if (height > 0 && t + 1 < m) {
        segmentStart[segments] = date(e);
        segmentEnd[segments] = date(events[t + 1]);
        segmentHeight[segments] = height;
        segments++;
      }
    }
    if (segments == 0) {
      return;
    }

    for (Box b : box) {
      long lengthMin = b.length[d].min();
      if (lengthMin == 0 || b.origin[d].singleton()) {
        continue;
      }
      long h = crossSection(b, d);
      if (h == 0) {
        continue;
      }
      long lst = b.lst(d);
      long ect = b.ect(d);
      // the box's own compulsory part is in the time-table
      long est = b.est(d);
      for (int s = 0; s < segments; s++) {
        if (segmentStart[s] >= est + lengthMin) {
          break;
        }
        if (segmentEnd[s] > est && overloads(s, h, lst, ect, capacity)) {
          est = segmentEnd[s];
        }
      }
      inMin(b.origin[d], est);

      long start = b.lst(d);
      for (int s = segments - 1; s >= 0; s--) {
        if (segmentEnd[s] <= start) {
          break;
        }
        if (segmentStart[s] < start + lengthMin && overloads(s, h, lst, ect, capacity)) {
          start = segmentStart[s] - lengthMin;
        }
      }
      inMax(b.origin[d], start);
    }
  }

  // whether a box of cross-section h, with compulsory part [lst, ect), cannot cover segment s
  private boolean overloads(int s, long h, long lst, long ect, long capacity) {
    long others = segmentHeight[s];
    if (lst <= segmentStart[s] && segmentEnd[s] <= ect) {
      others -= h;
    }
    return add(others, h) > capacity;
  }

  /**
   * Layer 5: the boxes whose compulsory parts in dimension d all contain a point are pairwise
   * disjoint in the other dimensions, so their cross-sections fit in their bounding box there.
   */
  private void slices(int d, int m) {
    Arrays.fill(active, false);
    int count = 0;
    for (int t = 0; t < m; t++) {
      long e = events[t];
      int i = boxOf(e);
      active[i] = start(e);
      count += start(e) ? 1 : -1;
      if (count < 2 || t + 1 < m && date(events[t + 1]) == date(e)) {
        continue;
      }
      long volume = 0;
      long space = 1;
      for (int dim = 0; dim < k && space > 0; dim++) {
        if (dim == d) {
          continue;
        }
        long low = Long.MAX_VALUE;
        long high = Long.MIN_VALUE;
        for (int j = 0; j < box.length; j++) {
          if (active[j]) {
            low = Math.min(low, box[j].est(dim));
            high = Math.max(high, box[j].lct(dim));
          }
        }
        space = multiply(space, Math.max(0, high - low));
      }
      for (int j = 0; j < box.length; j++) {
        if (active[j]) {
          volume = add(volume, crossSection(box[j], d));
        }
      }
      if (volume > space) {
        throw Store.failException;
      }
    }
  }

  private void pruning() {

    for (int i = 0; i < box.length; i++) {
      Box b = box[i];
      BitSet current = candidates[i].value();

      if (b.fixedBefore(store.level)) {
        // the other boxes still have b as a candidate and prune against it
        if (!current.isEmpty()) {
          candidates[i].update(new BitSet());
        }
        continue;
      }

      BitSet updated = null;
      for (int j = current.nextSetBit(0); j >= 0; j = current.nextSetBit(j + 1)) {
        if (apart(b, box[j])) {
          if (updated == null) {
            updated = (BitSet) current.clone();
          }
          updated.clear(j);
        }
      }
      if (updated != null) {
        candidates[i].update(updated);
        current = updated;
      }
      if (current.isEmpty()) {
        continue;
      }

      if (strict) {
        for (int j = current.nextSetBit(0); j >= 0; j = current.nextSetBit(j + 1)) {
          pairwise(b, box[j]);
        }
        volume(b, current);
      } else if (b.present()) {
        for (int j = current.nextSetBit(0); j >= 0; j = current.nextSetBit(j + 1)) {
          Box o = box[j];
          if (o.present()) {
            pairwise(b, o);
          }
        }
        volume(b, current);
      } else if (b.mayBePresent()) {
        excludeIfNoRoom(b, current);
      }
    }
  }

  /** True if the two boxes can never overlap again, whatever their remaining values. */
  private boolean apart(Box a, Box b) {
    for (int d = 0; d < k; d++) {
      if (a.lct(d) <= b.est(d) || b.lct(d) <= a.est(d)) {
        return true;
      }
      int aMax = a.length[d].max();
      int bMax = b.length[d].max();
      if (strict ? aMax == 0 && bMax == 0 : aMax == 0 || bMax == 0) {
        return true;
      }
    }
    return false;
  }

  /**
   * True if a and b overlap in dimension d whatever their remaining origins, with a's length at
   * least aLength and b's length at least bLength. A length of 0 overlaps only the strict interior
   * of the other box's compulsory part, as the strict semantics requires.
   */
  private static boolean mustOverlap(Box a, long aLength, Box b, long bLength, int d) {
    long aLst = a.lst(d);
    long aEct = a.est(d) + aLength;
    long bLst = b.lst(d);
    long bEct = b.est(d) + bLength;
    return (aLst < aEct || bLst < bEct) && bEct > aLst && aEct > bLst;
  }

  private void pairwise(Box a, Box b) {
    int free = -1;
    for (int d = 0; d < k; d++) {
      if (!mustOverlap(a, a.length[d].min(), b, b.length[d].min(), d)) {
        if (free >= 0) {
          return;
        }
        free = d;
      }
    }
    if (free < 0) {
      throw Store.failException;
    }
    separate(a, b, free);
  }

  /** Boxes a and b must be separated in dimension d. */
  private void separate(Box a, Box b, int d) {
    long aLst = a.lst(d);
    long aEct = a.ect(d);
    long bLst = b.lst(d);
    long bEct = b.ect(d);

    if (aLst < bEct) {
      // b cannot end before a starts, so a ends before b starts
      before(a, b, d);
    } else if (bLst < aEct) {
      before(b, a, d);
    } else {
      removeOverlapping(a, b, d);
      removeOverlapping(b, a, d);
    }
  }

  /** Box a ends before box b starts in dimension d. */
  private void before(Box a, Box b, int d) {
    long aEst = a.est(d);
    long aMinLength = a.length[d].min();
    long bLst = b.lst(d);
    inMin(b.origin[d], aEst + aMinLength);
    inMax(a.origin[d], bLst - aMinLength);
    inMax(a.length[d], bLst - aEst);
  }

  /** Removes the origins of a in dimension d at which a would overlap b's compulsory part. */
  private void removeOverlapping(Box a, Box b, int d) {
    long bLst = b.lst(d);
    long bEct = b.ect(d);
    if (bLst >= bEct) {
      return;
    }
    IntVar x = a.origin[d];
    long from = Math.max(bLst - a.length[d].min() + 1, x.min());
    long to = Math.min(bEct - 1, x.max());
    if (from <= to) {
      x.domain.inComplement(store.level, x, (int) from, (int) to);
    }
  }

  /** Non-strict only: box a must be absent. */
  private void exclude(Box a) {
    int zero = -1;
    for (int d = 0; d < k; d++) {
      if (a.length[d].min() == 0) {
        if (zero >= 0) {
          zero = -2;
          break;
        }
        zero = d;
      }
    }
    if (zero == -1) {
      throw Store.failException;
    }
    IntVar h = zero >= 0 ? a.length[zero] : handle == null ? null : handle[a.index];
    if (h != null) {
      h.domain.in(store.level, h, 0, 0);
    }
  }

  /**
   * The boxes that b may overlap and that take part (all of them for the strict constraint, the
   * present ones otherwise), together with b, must fit in their bounding box by volume and by
   * number.
   */
  private void volume(Box b, BitSet others) {
    long[] low = new long[k];
    long[] high = new long[k];
    long[] minLength = new long[k];
    for (int d = 0; d < k; d++) {
      low[d] = b.est(d);
      high[d] = b.lct(d);
      minLength[d] = b.length[d].min();
    }
    long volume = minVolume(b);
    int count = 1;

    for (int j = others.nextSetBit(0); j >= 0; j = others.nextSetBit(j + 1)) {
      Box o = box[j];
      if (!strict && !o.present()) {
        continue;
      }
      for (int d = 0; d < k; d++) {
        low[d] = Math.min(low[d], o.est(d));
        high[d] = Math.max(high[d], o.lct(d));
        minLength[d] = Math.min(minLength[d], o.length[d].min());
      }
      volume = add(volume, minVolume(o));
      count++;
      if (volume > space(low, high)) {
        throw Store.failException;
      }
    }

    long fit = 1;
    for (int d = 0; d < k && fit > 0; d++) {
      fit = minLength[d] > 0 ? multiply(fit, (high[d] - low[d]) / minLength[d]) : -1;
    }
    if (fit >= 0 && fit < count) {
      throw Store.failException;
    }
  }

  /**
   * Non-strict only: box a may still be absent. It must be absent if, at its smallest positive
   * lengths, it must overlap a present box in every dimension, or it does not fit by volume with
   * the present boxes it may overlap.
   */
  private void excludeIfNoRoom(Box a, BitSet others) {
    long[] low = new long[k];
    long[] high = new long[k];
    long volume = 1;
    for (int d = 0; d < k; d++) {
      low[d] = a.est(d);
      high[d] = a.lct(d);
      volume = multiply(volume, a.minPositiveLength(d));
    }
    for (int j = others.nextSetBit(0); j >= 0; j = others.nextSetBit(j + 1)) {
      Box o = box[j];
      if (!o.present()) {
        continue;
      }
      boolean overlap = true;
      for (int d = 0; d < k && overlap; d++) {
        overlap = mustOverlap(a, a.minPositiveLength(d), o, o.length[d].min(), d);
      }
      if (overlap) {
        exclude(a);
        return;
      }
      for (int d = 0; d < k; d++) {
        low[d] = Math.min(low[d], o.est(d));
        high[d] = Math.max(high[d], o.lct(d));
      }
      volume = add(volume, minVolume(o));
      if (volume > space(low, high)) {
        exclude(a);
        return;
      }
    }
  }

  private long minVolume(Box b) {
    long v = 1;
    for (int d = 0; d < k && v > 0; d++) {
      v = multiply(v, b.length[d].min());
    }
    return v;
  }

  private long space(long[] low, long[] high) {
    long v = 1;
    for (int d = 0; d < k && v > 0; d++) {
      v = multiply(v, Math.max(0, high[d] - low[d]));
    }
    return v;
  }

  /** Product of two non-negative longs, saturated at Long.MAX_VALUE. */
  static long multiply(long a, long b) {
    if (a == 0 || b == 0) {
      return 0;
    }
    long high = Math.multiplyHigh(a, b);
    long low = a * b;
    return high != 0 || low < 0 ? Long.MAX_VALUE : low;
  }

  /** Sum of two non-negative longs, saturated at Long.MAX_VALUE. */
  static long add(long a, long b) {
    long s = a + b;
    return s < 0 ? Long.MAX_VALUE : s;
  }

  private void inMin(IntVar x, long min) {
    if (min > x.max()) {
      throw Store.failException;
    }
    if (min > x.min()) {
      x.domain.inMin(store.level, x, (int) min);
    }
  }

  private void inMax(IntVar x, long max) {
    if (max < x.min()) {
      throw Store.failException;
    }
    if (max < x.max()) {
      x.domain.inMax(store.level, x, (int) max);
    }
  }

  /**
   * It checks whether every pair of boxes is certainly apart.
   *
   * @return true if the constraint is satisfied whatever the remaining values.
   */
  @Override
  public boolean satisfied() {
    for (int i = 0; i < box.length; i++) {
      for (int j = i + 1; j < box.length; j++) {
        if (!apart(box[i], box[j])) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * It checks whether two boxes must overlap whatever the remaining values.
   *
   * @return true if the constraint cannot be satisfied.
   */
  public boolean notSatisfied() {
    for (int i = 0; i < box.length; i++) {
      for (int j = i + 1; j < box.length; j++) {
        Box a = box[i];
        Box b = box[j];
        if (!strict && !(a.present() && b.present())) {
          continue;
        }
        boolean overlap = true;
        for (int d = 0; d < k && overlap; d++) {
          overlap = mustOverlap(a, a.length[d].min(), b, b.length[d].min(), d);
        }
        if (overlap) {
          return true;
        }
      }
    }
    return false;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id()).append(" : diffnK([");
    for (int i = 0; i < box.length; i++) {
      result.append(box[i]);
      if (i < box.length - 1) {
        result.append(", ");
      }
    }
    return result.append("], ").append(strict).append(")").toString();
  }

  @Override
  public DiffnK copy(VarMap map) {
    IntVar[][] origin = new IntVar[box.length][k];
    IntVar[][] length = new IntVar[box.length][k];
    for (int i = 0; i < box.length; i++) {
      for (int d = 0; d < k; d++) {
        origin[i][d] = map.get(box[i].origin[d]);
        length[i][d] = map.get(box[i].length[d]);
      }
    }
    IntVar[] h = null;
    if (handle != null) {
      h = new IntVar[box.length];
      for (int i = 0; i < box.length; i++) {
        h[i] = handle[i] == null ? null : map.get(handle[i]);
      }
    }
    DiffnK c = new DiffnK(origin, length, strict, h);
    c.projection = projection;
    c.slices = slices;
    return c;
  }
}
