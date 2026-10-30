/*
 * AffineDomain.java
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

package org.jacop.core;

import org.jacop.constraints.Constraint;

/**
 * The domain of an {@link AffineView}: the values a*u + b for the values u of the base variable.
 * The values are not stored; every query reads the base variable's current domain, and every
 * pruning is translated into a pruning of the base variable, whose change wakes the constraints of
 * the view as well (see {@link Store#addChanged(Var, int, int)}).
 *
 * <p>The domain object itself only holds the constraints attached to the view, and is copied per
 * store level like any other domain when they change, so {@link #stamp} and {@link #previousDomain}
 * describe the constraint lists. {@link #stamp()} and {@link #getPreviousDomain()} describe the
 * values, as constraints expect.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class AffineDomain extends IntDomain {

  /** The base variable. */
  final IntVar base;

  /** The factor, not 0. */
  final int a;

  /** The offset. */
  final int b;

  /**
   * Creates the domain of a*base + b.
   *
   * @param base the base variable.
   * @param a the factor, not 0.
   * @param b the offset.
   */
  AffineDomain(IntVar base, int a, int b) {
    if (a == 0) {
      throw new IllegalArgumentException("The factor of an affine view cannot be 0");
    }
    this.base = base;
    this.a = a;
    this.b = b;
  }

  private int image(int u) {
    return a * u + b;
  }

  /** The real (v - b) / a rounded up. */
  private long ceilPre(long v) {
    return Math.ceilDiv(v - b, (long) a);
  }

  /** The real (v - b) / a rounded down. */
  private long floorPre(long v) {
    return Math.floorDiv(v - b, (long) a);
  }

  /** The base values u with a*u + b in min..max, as {lo, hi}; empty when lo &gt; hi. */
  private long[] preimage(long min, long max) {
    if (a > 0) {
      return new long[] {ceilPre(min), floorPre(max)};
    }
    return new long[] {ceilPre(max), floorPre(min)};
  }

  private static int clamp(long v) {
    if (v < IntDomain.MIN_INT) {
      return IntDomain.MIN_INT;
    }
    if (v > IntDomain.MAX_INT) {
      return IntDomain.MAX_INT;
    }
    return (int) v;
  }

  /** Tells whether v is a*u + b for some integer u. */
  private boolean onLattice(long v) {
    return Math.floorMod(v - b, (long) a) == 0;
  }

  private int pre(long v) {
    return (int) ((v - b) / a);
  }

  /**
   * The values of the view as an interval domain.
   *
   * @return a new domain with the values a*u + b.
   */
  public IntervalDomain image() {
    IntDomain d = base.domain;
    IntervalDomain result = new IntervalDomain(Math.max(1, Math.abs(a) == 1 ? d.noIntervals() : 4));
    if (d.isEmpty()) {
      return result;
    }
    if (a == 1 || a == -1) {
      int n = d.noIntervals();
      for (int k = 0; k < n; k++) {
        Interval i = d.getInterval(a > 0 ? k : n - 1 - k);
        int x = image(i.min());
        int y = image(i.max());
        result.unionAdapt(Math.min(x, y), Math.max(x, y));
      }
      return result;
    }
    int[] values = d.toIntArray();
    int n = values.length;
    for (int k = 0; k < n; k++) {
      int v = image(values[a > 0 ? k : n - 1 - k]);
      result.unionAdapt(v, v);
    }
    return result;
  }

  /** The base values u with a*u + b in the given domain shifted by shift. */
  private IntervalDomain preimage(IntDomain domain, int shift) {
    return preimage(domain, shift, a, b);
  }

  /**
   * Returns the values u for which a*u + b is in a domain shifted by shift.
   *
   * @param domain the domain.
   * @param shift the shift of the domain's values.
   * @param a the factor, not 0.
   * @param b the offset.
   * @return a new interval domain with those values.
   */
  public static IntervalDomain preimage(IntDomain domain, int shift, int a, int b) {
    IntervalDomain result = new IntervalDomain(Math.max(1, domain.noIntervals()));
    if (domain.isEmpty()) {
      return result;
    }
    int n = domain.noIntervals();
    for (int k = 0; k < n; k++) {
      Interval i = domain.getInterval(a > 0 ? k : n - 1 - k);
      long lo = (long) i.min() + shift - b;
      long hi = (long) i.max() + shift - b;
      long from = a > 0 ? Math.ceilDiv(lo, (long) a) : Math.ceilDiv(hi, (long) a);
      long to = a > 0 ? Math.floorDiv(hi, (long) a) : Math.floorDiv(lo, (long) a);
      // values outside the range of domains are in no domain of the base
      from = Math.max(from, IntDomain.MIN_INT);
      to = Math.min(to, IntDomain.MAX_INT);
      if (from <= to) {
        result.unionAdapt((int) from, (int) to);
      }
    }
    return result;
  }

  @Override
  public int min() {
    return a > 0 ? image(base.min()) : image(base.max());
  }

  @Override
  public int max() {
    return a > 0 ? image(base.max()) : image(base.min());
  }

  @Override
  public int getSize() {
    return base.domain.getSize();
  }

  @Override
  public boolean isEmpty() {
    return base.domain.isEmpty();
  }

  @Override
  public boolean singleton() {
    return base.singleton();
  }

  @Override
  public boolean singleton(int c) {
    return onLattice(c) && base.domain.singleton(pre(c));
  }

  @Override
  public boolean contains(int value) {
    return onLattice(value) && base.domain.contains(pre(value));
  }

  @Override
  public boolean contains(int min, int max) {
    if (min > max) {
      return true;
    }
    if (a != 1 && a != -1 && min != max) {
      return false;
    }
    long[] r = preimage(min, max);
    return r[0] <= r[1]
        && r[0] >= IntDomain.MIN_INT
        && r[1] <= IntDomain.MAX_INT
        && base.domain.contains((int) r[0], (int) r[1]);
  }

  @Override
  public boolean isIntersecting(int min, int max) {
    long[] r = preimage(min, max);
    return r[0] <= r[1] && base.domain.isIntersecting(clamp(r[0]), clamp(r[1]));
  }

  @Override
  public int nextValue(int value) {
    // the smallest u with a*u + b > value when a > 0, the largest when a < 0
    int u = a > 0 ? atOrAbove(floorPre(value) + 1) : atOrBelow(ceilPre(value) - 1);
    return u == NO_VALUE ? value : image(u);
  }

  @Override
  public int previousValue(int value) {
    // the largest u with a*u + b < value when a > 0, the smallest when a < 0
    int u = a > 0 ? atOrBelow(ceilPre(value) - 1) : atOrAbove(floorPre(value) + 1);
    return u == NO_VALUE ? value : image(u);
  }

  private static final int NO_VALUE = Integer.MIN_VALUE;

  /** The smallest base value at or above w, or NO_VALUE. */
  private int atOrAbove(long w) {
    IntDomain d = base.domain;
    if (d.isEmpty() || w > d.max()) {
      return NO_VALUE;
    }
    if (w <= d.min()) {
      return d.min();
    }
    int x = (int) w;
    return d.contains(x) ? x : d.nextValue(x);
  }

  /** The largest base value at or below w, or NO_VALUE. */
  private int atOrBelow(long w) {
    IntDomain d = base.domain;
    if (d.isEmpty() || w < d.min()) {
      return NO_VALUE;
    }
    if (w >= d.max()) {
      return d.max();
    }
    int x = (int) w;
    return d.contains(x) ? x : d.previousValue(x);
  }

  @Override
  public int runEnd(int value) {
    if (a == 1) {
      return image(base.domain.runEnd(value - b));
    }
    if (a != -1) {
      return value;
    }
    // the run of the view from value upwards is the run of the base from -value + b downwards
    IntDomain d = base.domain;
    int u = pre(value);
    int start = u;
    while (start > d.min()) {
      int p = d.previousValue(start);
      if (p != start - 1) {
        break;
      }
      start = p;
    }
    return image(start);
  }

  @Override
  public ValueEnumeration valueEnumeration() {
    return image().valueEnumeration();
  }

  @Override
  public IntervalEnumeration intervalEnumeration() {
    return image().intervalEnumeration();
  }

  @Override
  public int noIntervals() {
    if (a == 1 || a == -1) {
      return base.domain.noIntervals();
    }
    return base.domain.getSize();
  }

  @Override
  public Interval getInterval(int position) {
    IntDomain d = base.domain;
    if (a == 1 || a == -1) {
      int n = d.noIntervals();
      if (position < 0 || position >= n) {
        return null;
      }
      Interval i = d.getInterval(a > 0 ? position : n - 1 - position);
      int x = image(i.min());
      int y = image(i.max());
      return new Interval(Math.min(x, y), Math.max(x, y));
    }
    int n = d.getSize();
    if (position < 0 || position >= n) {
      return null;
    }
    int v = getElementAt(position);
    return new Interval(v, v);
  }

  @Override
  public int getElementAt(int index) {
    IntDomain d = base.domain;
    return image(d.getElementAt(a > 0 ? index : d.getSize() - 1 - index));
  }

  @Override
  public IntDomain intersect(IntDomain dom) {
    return image().intersect(dom);
  }

  @Override
  public IntDomain intersect(int min, int max) {
    return image().intersect(min, max);
  }

  @Override
  public IntDomain subtract(int value) {
    return image().subtract(value);
  }

  @Override
  public IntDomain subtract(IntDomain domain) {
    return image().subtract(domain);
  }

  @Override
  public IntDomain subtract(int min, int max) {
    return image().subtract(min, max);
  }

  @Override
  public IntDomain union(IntDomain domain) {
    return image().union(domain);
  }

  @Override
  public IntDomain union(int min, int max) {
    return image().union(min, max);
  }

  @Override
  public IntDomain union(int value) {
    return image().union(value);
  }

  @Override
  public IntDomain complement() {
    return image().complement();
  }

  @Override
  public void in(int storeLevel, Var v, int min, int max) {
    long[] r = preimage(min, max);
    if (r[0] > r[1]) {
      throw failException;
    }
    base.domain.in(storeLevel, base, clamp(r[0]), clamp(r[1]));
  }

  @Override
  public void inMin(int storeLevel, Var v, int min) {
    if (a > 0) {
      long u = ceilPre(min);
      if (u > base.max()) {
        throw failException;
      }
      if (u > base.min()) {
        base.domain.inMin(storeLevel, base, (int) u);
      }
    } else {
      long u = floorPre(min);
      if (u < base.min()) {
        throw failException;
      }
      if (u < base.max()) {
        base.domain.inMax(storeLevel, base, (int) u);
      }
    }
  }

  @Override
  public void inMax(int storeLevel, Var v, int max) {
    if (a > 0) {
      long u = floorPre(max);
      if (u < base.min()) {
        throw failException;
      }
      if (u < base.max()) {
        base.domain.inMax(storeLevel, base, (int) u);
      }
    } else {
      long u = ceilPre(max);
      if (u > base.max()) {
        throw failException;
      }
      if (u > base.min()) {
        base.domain.inMin(storeLevel, base, (int) u);
      }
    }
  }

  @Override
  public void inValue(int level, IntVar v, int value) {
    if (!onLattice(value)) {
      throw failException;
    }
    long u = ((long) value - b) / a;
    if (u < base.min() || u > base.max()) {
      throw failException;
    }
    base.domain.inValue(level, base, (int) u);
  }

  @Override
  public void in(int storeLevel, Var v, IntDomain domain) {
    inShift(storeLevel, v, domain, 0);
  }

  @Override
  public void inShift(int storeLevel, Var v, IntDomain domain, int shift) {
    IntervalDomain p = preimage(domain, shift);
    if (p.isEmpty()) {
      throw failException;
    }
    base.domain.in(storeLevel, base, p);
  }

  @Override
  public void inComplement(int storeLevel, Var v, int complement) {
    if (onLattice(complement)) {
      long u = ((long) complement - b) / a;
      if (u >= base.min() && u <= base.max()) {
        base.domain.inComplement(storeLevel, base, (int) u);
      }
    }
  }

  @Override
  public void inComplement(int storeLevel, Var v, int min, int max) {
    long[] r = preimage(min, max);
    if (r[0] <= r[1]) {
      base.domain.inComplement(storeLevel, base, clamp(r[0]), clamp(r[1]));
    }
  }

  @Override
  public void inComplement(int storeLevel, Var v, IntDomain complement) {
    if (complement.isEmpty()) {
      return;
    }
    IntervalDomain p = preimage(complement, 0);
    if (!p.isEmpty()) {
      base.domain.inComplement(storeLevel, base, p);
    }
  }

  @Override
  public IntDomain recentDomainPruning(int currentStoreLevel) {
    IntDomain pruned = base.domain.recentDomainPruning(currentStoreLevel);
    if (pruned.isEmpty()) {
      return pruned;
    }
    return imageOf(pruned);
  }

  private IntervalDomain imageOf(IntDomain d) {
    IntervalDomain result = new IntervalDomain(4);
    int[] values = d.toIntArray();
    int n = values.length;
    for (int k = 0; k < n; k++) {
      int v = image(values[a > 0 ? k : n - 1 - k]);
      result.unionAdapt(v, v);
    }
    return result;
  }

  /**
   * Returns the values of the view before the last change of the base variable, or null if the base
   * variable has not changed since it was created.
   */
  @Override
  public IntDomain getPreviousDomain() {
    IntDomain previous = base.domain.getPreviousDomain();
    return previous == null ? null : imageOf(previous);
  }

  /** Returns the level of the last change of the values, the level of the base variable. */
  @Override
  public int stamp() {
    return base.domain.stamp;
  }

  @Override
  public void removeLevel(int level, Var v) {
    if (stamp == level) {
      ((IntVar) v).domain = previousDomain;
    }
  }

  @Override
  protected AffineDomain cloneForLevel() {
    return new AffineDomain(base, a, b);
  }

  /** Returns the values of the view as a new interval domain. */
  @Override
  public IntDomain cloneLight() {
    return image();
  }

  /** Returns the values of the view as a new interval domain. */
  @Override
  public IntDomain copy() {
    return image();
  }

  @Override
  public int domainId() {
    return AFFINE_VIEW_DOMAIN_ID;
  }

  @Override
  public boolean isSparseRepresentation() {
    return false;
  }

  @Override
  public void clear() {
    base.domain.clear();
  }

  @Override
  public void unionAdapt(int min, int max) {
    throw new UnsupportedOperationException("Values cannot be added to an affine view");
  }

  @Override
  public void setDomain(IntDomain domain) {
    base.domain.setDomain(preimage(domain, 0));
  }

  @Override
  public void setDomain(int min, int max) {
    long[] r = preimage(min, max);
    if (r[0] > r[1]) {
      base.domain.clear();
    } else {
      base.domain.setDomain(clamp(r[0]), clamp(r[1]));
    }
  }

  @Override
  public void subtractAdapt(int value) {
    if (onLattice(value)) {
      base.domain.subtractAdapt(pre(value));
    }
  }

  @Override
  public void subtractAdapt(int min, int max) {
    long[] r = preimage(min, max);
    if (r[0] <= r[1]) {
      base.domain.subtractAdapt(clamp(r[0]), clamp(r[1]));
    }
  }

  @Override
  public int intersectAdapt(IntDomain intersect) {
    return swap(base.domain.intersectAdapt(preimage(intersect, 0)));
  }

  @Override
  public int intersectAdapt(int min, int max) {
    long[] r = preimage(min, max);
    if (r[0] > r[1]) {
      base.domain.clear();
      return GROUND;
    }
    return swap(base.domain.intersectAdapt(clamp(r[0]), clamp(r[1])));
  }

  /**
   * Returns the event of the view for an event of the base variable: a decreasing view turns a
   * change of the minimum into a change of the maximum.
   *
   * @param event an event of the base variable.
   * @return the event of the view.
   */
  int swap(int event) {
    if (a > 0) {
      return event;
    }
    if (event == MIN_EVENT) {
      return MAX_EVENT;
    }
    if (event == MAX_EVENT) {
      return MIN_EVENT;
    }
    return event;
  }

  @Override
  public int sizeConstraintsOriginal() {
    IntDomain domain = this;
    while (domain.previousDomain != null) {
      domain = domain.previousDomain;
    }
    int sum = 0;
    for (int n : domain.modelConstraintsToEvaluate) {
      sum += n;
    }
    return sum;
  }

  @Override
  public String checkInvariants() {
    return null;
  }

  @Override
  public String toString() {
    return image().toString();
  }

  @Override
  public String toStringConstraints() {
    StringBuilder s = new StringBuilder();
    for (Constraint[] list : modelConstraints) {
      if (list != null) {
        for (Constraint c : list) {
          if (c != null) {
            s.append(c.id()).append(' ');
          }
        }
      }
    }
    return s.toString();
  }

  @Override
  public String toStringFull() {
    return a
        + "*"
        + base.id()
        + (b >= 0 ? "+" : "")
        + b
        + " = "
        + this
        + " "
        + toStringConstraints();
  }
}
