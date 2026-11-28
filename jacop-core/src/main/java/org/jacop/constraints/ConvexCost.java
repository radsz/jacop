/*
 * ConvexCost.java
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
import java.util.List;

/**
 * An integer cost function of one integer variable, for {@link ConvexAllocation}. It is a sum of
 * pieces, each one of
 *
 * <ul>
 *   <li>w &middot; max<sub>k</sub>(a<sub>k</sub> &middot; v + b<sub>k</sub>), a piecewise linear
 *       convex function (an affine function, |a &middot; v + b|, a dead zone, ...);
 *   <li>w &middot; max<sub>k</sub>(a<sub>k</sub> &middot; v + b<sub>k</sub>)<sup>2</sup>, the
 *       square of the same, convex where the maximum is not negative;
 *   <li>a table of values for v = first, first + 1, ..., extended linearly on both sides.
 * </ul>
 *
 * with w &ge; 0. {@link #isConvexOn} tells whether the sum is convex on an interval of integers,
 * which {@link ConvexAllocation} requires. Values are computed exactly in long arithmetic and throw
 * {@link ArithmeticException} on overflow.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public final class ConvexCost {

  /** One piece: weight times the (squared) maximum of affine functions, or a table. */
  private static final class Piece {
    final long weight;
    final long[] a;
    final long[] b;
    final boolean squared;
    final long first;
    final long[] table;

    Piece(long weight, long[] a, long[] b, boolean squared) {
      if (weight < 0) {
        throw new IllegalArgumentException("A convex cost piece needs a weight of at least 0.");
      }
      if (a.length == 0 || a.length != b.length) {
        throw new IllegalArgumentException(
            "A convex cost piece needs as many slopes as offsets, at least one.");
      }
      this.weight = weight;
      this.a = a.clone();
      this.b = b.clone();
      this.squared = squared;
      this.first = 0;
      this.table = null;
    }

    Piece(long first, long[] table) {
      if (table.length == 0) {
        throw new IllegalArgumentException("A convex cost table needs at least one value.");
      }
      this.weight = 1;
      this.a = null;
      this.b = null;
      this.squared = false;
      this.first = first;
      this.table = table.clone();
    }

    // the maximum of the affine functions at v
    long inner(long v) {
      long m = Math.addExact(Math.multiplyExact(a[0], v), b[0]);
      for (int k = 1; k < a.length; k++) {
        m = Math.max(m, Math.addExact(Math.multiplyExact(a[k], v), b[k]));
      }
      return m;
    }

    long value(long v) {
      if (table != null) {
        long last = first + table.length - 1;
        if (v < first) {
          long slope = table.length > 1 ? table[1] - table[0] : 0;
          return Math.subtractExact(table[0], Math.multiplyExact(first - v, slope));
        }
        if (v > last) {
          long slope = table.length > 1 ? table[table.length - 1] - table[table.length - 2] : 0;
          return Math.addExact(table[table.length - 1], Math.multiplyExact(v - last, slope));
        }
        return table[(int) (v - first)];
      }
      long m = inner(v);
      return Math.multiplyExact(weight, squared ? Math.multiplyExact(m, m) : m);
    }

    boolean convexOn(long lo, long hi) {
      if (table != null) {
        for (int k = 2; k < table.length; k++) {
          if (table[k] - table[k - 1] < table[k - 1] - table[k - 2]) {
            return false;
          }
        }
        return true;
      }
      if (!squared || a.length == 1 || weight == 0) {
        return true;
      }
      // the square of a convex function is convex where the function is not negative
      long l = lo;
      long h = hi;
      while (l < h) {
        long m = l + (h - l) / 2;
        if (inner(m + 1) >= inner(m)) {
          h = m;
        } else {
          l = m + 1;
        }
      }
      return inner(l) >= 0;
    }

    @Override
    public String toString() {
      if (table != null) {
        return "table(" + first + ", " + Arrays.toString(table) + ")";
      }
      StringBuilder s = new StringBuilder();
      if (weight != 1) {
        s.append(weight).append('*');
      }
      s.append(a.length > 1 ? "max(" : "(");
      for (int k = 0; k < a.length; k++) {
        if (k > 0) {
          s.append(", ");
        }
        s.append(a[k]).append("*v");
        if (b[k] != 0) {
          s.append(b[k] > 0 ? "+" : "").append(b[k]);
        }
      }
      s.append(')');
      if (squared) {
        s.append("^2");
      }
      return s.toString();
    }
  }

  private final Piece[] pieces;

  private ConvexCost(Piece... pieces) {
    this.pieces = pieces;
  }

  /**
   * The affine cost a &middot; v + b.
   *
   * @param a the slope
   * @param b the offset
   * @return the cost
   */
  public static ConvexCost linear(long a, long b) {
    return new ConvexCost(new Piece(1, new long[] {a}, new long[] {b}, false));
  }

  /**
   * The cost w &middot; |a &middot; v + b|.
   *
   * @param w the weight, at least 0
   * @param a the slope
   * @param b the offset
   * @return the cost
   */
  public static ConvexCost abs(long w, long a, long b) {
    return new ConvexCost(new Piece(w, new long[] {a, -a}, new long[] {b, -b}, false));
  }

  /**
   * The cost w &middot; (a &middot; v + b)<sup>2</sup>.
   *
   * @param w the weight, at least 0
   * @param a the slope
   * @param b the offset
   * @return the cost
   */
  public static ConvexCost square(long w, long a, long b) {
    return new ConvexCost(new Piece(w, new long[] {a}, new long[] {b}, true));
  }

  /**
   * The cost w &middot; max<sub>k</sub>(a[k] &middot; v + b[k]).
   *
   * @param w the weight, at least 0
   * @param a the slopes
   * @param b the offsets
   * @return the cost
   */
  public static ConvexCost max(long w, long[] a, long[] b) {
    return new ConvexCost(new Piece(w, a, b, false));
  }

  /**
   * The cost w &middot; max<sub>k</sub>(a[k] &middot; v + b[k])<sup>2</sup>, convex where the
   * maximum is not negative.
   *
   * @param w the weight, at least 0
   * @param a the slopes
   * @param b the offsets
   * @return the cost
   */
  public static ConvexCost squaredMax(long w, long[] a, long[] b) {
    return new ConvexCost(new Piece(w, a, b, true));
  }

  /**
   * The cost values[v - first] for v from first to first + values.length - 1, extended linearly
   * with the slope of the first two (last two) values below (above) them.
   *
   * @param first the value of v the first cost is for
   * @param values the costs
   * @return the cost
   */
  public static ConvexCost table(long first, long[] values) {
    return new ConvexCost(new Piece(first, values));
  }

  /**
   * The sum of this cost and another one.
   *
   * @param other the other cost
   * @return the sum of both
   */
  public ConvexCost plus(ConvexCost other) {
    List<Piece> all = new ArrayList<>(Arrays.asList(pieces));
    all.addAll(Arrays.asList(other.pieces));
    return new ConvexCost(all.toArray(new Piece[0]));
  }

  /**
   * The cost of a value.
   *
   * @param v the value
   * @return the cost
   * @throws ArithmeticException when the cost does not fit in a long
   */
  public long value(long v) {
    long s = 0;
    for (Piece p : pieces) {
      s = Math.addExact(s, p.value(v));
    }
    return s;
  }

  /**
   * It tells whether the cost is convex on the integers from lo to hi: each piece is.
   *
   * @param lo the least value
   * @param hi the greatest value
   * @return true if every piece is convex there
   */
  public boolean isConvexOn(long lo, long hi) {
    for (Piece p : pieces) {
      if (!p.convexOn(lo, hi)) {
        return false;
      }
    }
    return true;
  }

  /**
   * The least value v in [lo, hi] at which the cost is minimal, for a cost convex there.
   *
   * @param lo the least value
   * @param hi the greatest value, at least lo
   * @return the least minimizer
   */
  public long argMin(long lo, long hi) {
    long l = lo;
    long h = hi;
    while (l < h) {
      long m = l + (h - l) / 2;
      if (value(m + 1) >= value(m)) {
        h = m;
      } else {
        l = m + 1;
      }
    }
    return l;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    for (int k = 0; k < pieces.length; k++) {
      if (k > 0) {
        s.append(" + ");
      }
      s.append(pieces[k]);
    }
    return s.toString();
  }
}
