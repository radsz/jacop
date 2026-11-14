/*
 * BinaryTable.java
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

package org.jacop.constraints.table;

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.SmallDenseDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * BinaryTable is a table over two variables whose domains span at most 64 values: the allowed
 * pairs, or the complement of the forbidden ones. Each value of each variable has the bit mask of
 * the values of the other variable it is allowed with, and a value is removed when its mask does
 * not meet the other domain. This is arc consistency by bit-parallel support checks, as AC3bit (C.
 * Lecoutre and F. Hemery, A Study of Residual Supports in Arc Consistency, IJCAI 2007, and C.
 * Lecoutre and J. Vion, Enforcing Arc Consistency using Bitwise Operations, Constraint Programming
 * Letters 2, 2008, pp. 21-35), with domains of one machine word, so the constraint keeps no state
 * that backtracking restores, unlike Compact-Table, whose trailed bit-sets cost a binary table more
 * than its filtering: the XCSP3 random problems FRB (binary conflict tables over 21 to 26 values).
 *
 * <p>Under lazy clause generation a removed value u of one variable is explained by the values of
 * the other variable allowed with u, which were all removed before: the resolved form of the
 * support clause {@code x != u \/ OR(a allowed with u) y = a}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class BinaryTable extends Constraint
    implements SatisfiedPresent, Copyable<BinaryTable>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The largest span of a domain. */
  public static final int MAX_SPAN = 64;

  private final IntVar x;
  private final IntVar y;

  // the values of x are baseX + i, bit 63 - i; the same for y
  private final int baseX;
  private final int baseY;

  // the values of y allowed with x = baseX + i, as a mask over y; the same for y
  private final long[] supportsOfX;
  private final long[] supportsOfY;

  /**
   * It constructs a binary table.
   *
   * @param x the first variable.
   * @param y the second variable, not x.
   * @param tuples the pairs (x, y).
   * @param negative true when the pairs are forbidden, false when they are the allowed ones.
   */
  public BinaryTable(IntVar x, IntVar y, int[][] tuples, boolean negative) {
    checkInputForNullness(new String[] {"x", "y", "tuples"}, new Object[][] {{x}, {y}, tuples});
    if (x == y) {
      throw new IllegalArgumentException("BinaryTable needs two distinct variables");
    }
    if (!fits(x) || !fits(y)) {
      throw new IllegalArgumentException("BinaryTable needs domains spanning at most 64 values");
    }
    numberId = idNumber.incrementAndGet();
    this.x = x;
    this.y = y;
    this.baseX = x.min();
    this.baseY = y.min();
    this.supportsOfX = new long[x.max() - baseX + 1];
    this.supportsOfY = new long[y.max() - baseY + 1];
    for (int[] t : tuples) {
      if (t.length != 2) {
        throw new IllegalArgumentException("BinaryTable needs pairs");
      }
      int i = t[0] - baseX;
      int j = t[1] - baseY;
      if (i >= 0 && i < supportsOfX.length && j >= 0 && j < supportsOfY.length) {
        supportsOfX[i] |= bit(j);
        supportsOfY[j] |= bit(i);
      }
    }
    if (negative) {
      long allY = full(supportsOfY.length);
      long allX = full(supportsOfX.length);
      for (int i = 0; i < supportsOfX.length; i++) {
        supportsOfX[i] = ~supportsOfX[i] & allY;
      }
      for (int j = 0; j < supportsOfY.length; j++) {
        supportsOfY[j] = ~supportsOfY[j] & allX;
      }
    }
    setScope(x, y);
  }

  private BinaryTable(BinaryTable original, VarMap map) {
    numberId = idNumber.incrementAndGet();
    this.x = map.get(original.x);
    this.y = map.get(original.y);
    this.baseX = original.baseX;
    this.baseY = original.baseY;
    this.supportsOfX = original.supportsOfX;
    this.supportsOfY = original.supportsOfY;
    setScope(x, y);
  }

  /**
   * It tells whether a variable's domain is small enough for a binary table.
   *
   * @param v the variable.
   * @return true when its domain spans at most {@link #MAX_SPAN} values.
   */
  public static boolean fits(IntVar v) {
    return (long) v.max() - v.min() < MAX_SPAN;
  }

  private static long bit(int i) {
    return 1L << (63 - i);
  }

  // the masks of the first n values
  private static long full(int n) {
    return n == 64 ? -1L : -1L << (64 - n);
  }

  // the values of a domain as a mask over base .. base + span - 1
  private static long mask(IntDomain d, int base, int span) {
    if (d.domainId() == IntDomain.SMALL_DENSE_DOMAIN_ID) {
      SmallDenseDomain s = (SmallDenseDomain) d;
      int shift = s.minBound - base;
      long bits;
      if (shift >= 0) {
        bits = shift < 64 ? s.bits >>> shift : 0L;
      } else {
        bits = -shift < 64 ? s.bits << -shift : 0L;
      }
      return bits & full(span);
    }
    long m = 0;
    for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
      int i = e.nextElement() - base;
      if (i >= 0 && i < span) {
        m |= bit(i);
      }
    }
    return m;
  }

  // the values of own that some value of other is allowed with
  private static long supported(long own, long other, long[] supports) {
    long keep = own;
    for (long rest = own; rest != 0; rest ^= Long.highestOneBit(rest)) {
      int i = Long.numberOfLeadingZeros(rest);
      if ((supports[i] & other) == 0) {
        keep &= ~bit(i);
      }
    }
    return keep;
  }

  @Override
  public void consistency(Store store) {
    long mx = mask(x.dom(), baseX, supportsOfX.length);
    long my = mask(y.dom(), baseY, supportsOfY.length);
    long ky = supported(my, mx, supportsOfY);
    if (ky != my) {
      prune(store, y, baseY, ky);
      my = ky;
    }
    long kx = supported(mx, my, supportsOfX);
    if (kx != mx) {
      prune(store, x, baseX, kx);
    }
    if (x.singleton() || y.singleton()) {
      // arc consistent with one value fixed: every pair left is allowed
      removeConstraint();
    }
  }

  private static void prune(Store store, IntVar v, int base, long keep) {
    if (keep == 0) {
      throw Store.failException;
    }
    v.domain.in(store.level, v, new SmallDenseDomain(base, keep));
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {
    long mx = mask(x.dom(), baseX, supportsOfX.length);
    long my = mask(y.dom(), baseY, supportsOfY.length);
    for (long rest = mx; rest != 0; rest ^= Long.highestOneBit(rest)) {
      if ((my & ~supportsOfX[Long.numberOfLeadingZeros(rest)]) != 0) {
        return false;
      }
    }
    return mx != 0 && my != 0;
  }

  // whether value u of v (x when first) was excluded before a position, by v itself or by every
  // value of the other variable allowed with it, adding the atoms that excluded it
  private boolean excluded(AtomicTrail trail, boolean first, int u, int position, EntryList out) {
    IntVar v = first ? x : y;
    if (trail.excludedBefore(v, u, position, out)) {
      return true;
    }
    int base = first ? baseX : baseY;
    long[] supports = first ? supportsOfX : supportsOfY;
    int i = u - base;
    if (i < 0 || i >= supports.length) {
      return false;
    }
    IntVar o = first ? y : x;
    int otherBase = first ? baseY : baseX;
    int mark = out.size();
    for (long rest = supports[i]; rest != 0; rest ^= Long.highestOneBit(rest)) {
      if (!trail.excludedBefore(o, otherBase + Long.numberOfLeadingZeros(rest), position, out)) {
        out.truncate(mark);
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (getClass() != BinaryTable.class) {
      return false;
    }
    IntVar v = trail.variable(entry);
    if (v != x && v != y) {
      return false;
    }
    boolean first = v == x;
    int kind = trail.kind(entry);
    int a = trail.value(entry);
    IntDomain root = trail.rootDomain(v);
    for (ValueEnumeration e = root.valueEnumeration(); e.hasMoreElements(); ) {
      int u = e.nextElement();
      boolean violates =
          switch (kind) {
            case AtomicTrail.GE -> u < a;
            case AtomicTrail.LE -> u > a;
            default -> u == a;
          };
      if (violates && !excluded(trail, first, u, entry, out)) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (getClass() != BinaryTable.class) {
      return false;
    }
    int now = trail.size();
    for (boolean first : new boolean[] {false, true}) {
      int mark = out.size();
      boolean all = true;
      IntDomain root = trail.rootDomain(first ? x : y);
      for (ValueEnumeration e = root.valueEnumeration(); all && e.hasMoreElements(); ) {
        all = excluded(trail, first, e.nextElement(), now, out);
      }
      if (all) {
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder(id()).append(" : binaryTable(").append(x).append(", ");
    s.append(y).append(", [");
    boolean any = false;
    for (int i = 0; i < supportsOfX.length; i++) {
      for (long rest = supportsOfX[i]; rest != 0; rest ^= Long.highestOneBit(rest)) {
        s.append(any ? ", " : "").append('[').append(baseX + i).append(", ");
        s.append(baseY + Long.numberOfLeadingZeros(rest)).append(']');
        any = true;
      }
    }
    return s.append("])").toString();
  }

  @Override
  public BinaryTable copy(VarMap map) {
    return new BinaryTable(this, map);
  }
}
