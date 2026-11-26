/*
 * PiecewiseLinear.java
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

package org.jacop.floats.constraints;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;

/**
 * PiecewiseLinear states that the point (x, y) lies on the polygonal line through the knots
 * (xKnot[0], yKnot[0]), ..., (xKnot[k-1], yKnot[k-1]): for some segment i, x = xKnot[i] + s
 * (xKnot[i+1] - xKnot[i]) and y = yKnot[i] + s (yKnot[i+1] - yKnot[i]) with s in [0, 1]. With
 * increasing knots this is y = f(x) for the piecewise-linear function f on [xKnot[0], xKnot[k-1]];
 * two equal consecutive x knots give a vertical segment, that is a jump of f. It is MiniZinc's
 * {@code piecewise_linear}, whose decomposition uses a 0/1 variable and a fraction per segment.
 *
 * <p>Propagation is bounds consistency on the union of the segments: each segment is cut to the
 * range of its parameter s that keeps x and y in their domains, and x and y are narrowed to the
 * hull of what remains, with outward rounding. It is the projection rule of the interval constraint
 * propagation of Benhamou and Older, "Applying interval arithmetic to real, integer and boolean
 * constraints" (J. Logic Programming 32, 1997), applied to each segment, and the disjunctive hull
 * of the segments as in the piecewise-linear constraints of CP solvers (Refalo, "Tight cooperation
 * and its application in piecewise linear optimization", CP 1999).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class PiecewiseLinear extends Constraint
    implements SatisfiedPresent, Copyable<PiecewiseLinear> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private final FloatVar x;
  private final FloatVar y;
  private final double[] xKnot;
  private final double[] yKnot;

  /**
   * It constructs a piecewise-linear constraint y = f(x).
   *
   * @param x the argument.
   * @param y the value.
   * @param xKnot the x coordinates of the knots.
   * @param yKnot the y coordinates of the knots, as many as xKnot.
   */
  public PiecewiseLinear(FloatVar x, FloatVar y, double[] xKnot, double[] yKnot) {
    checkInputForNullness(
        new String[] {"x", "y", "xKnot", "yKnot"}, new Object[] {x, y, xKnot, yKnot});
    if (xKnot.length != yKnot.length || xKnot.length == 0) {
      throw new IllegalArgumentException(
          "PiecewiseLinear needs as many x knots as y knots, and at least one, got "
              + xKnot.length
              + " and "
              + yKnot.length);
    }
    for (int i = 0; i < xKnot.length; i++) {
      if (!Double.isFinite(xKnot[i]) || !Double.isFinite(yKnot[i])) {
        throw new IllegalArgumentException("PiecewiseLinear needs finite knots.");
      }
    }
    numberId = idNumber.incrementAndGet();
    this.queueIndex = 0;
    this.x = x;
    this.y = y;
    this.xKnot = Arrays.copyOf(xKnot, xKnot.length);
    this.yKnot = Arrays.copyOf(yKnot, yKnot.length);
    setScope(x, y);
  }

  @Override
  public void consistency(Store store) {
    do {
      store.propagationHasOccurred = false;
      double xLo = Double.POSITIVE_INFINITY;
      double xHi = Double.NEGATIVE_INFINITY;
      double yLo = Double.POSITIVE_INFINITY;
      double yHi = Double.NEGATIVE_INFINITY;
      int segments = Math.max(1, xKnot.length - 1);
      double[] range = new double[2];
      for (int i = 0; i < segments; i++) {
        int j = Math.min(i + 1, xKnot.length - 1);
        double a = xKnot[i];
        double dx = xKnot[j] - a;
        double c = yKnot[i];
        double dy = yKnot[j] - c;
        range[0] = 0.0;
        range[1] = 1.0;
        if (!cut(range, a, dx, x.min(), x.max()) || !cut(range, c, dy, y.min(), y.max())) {
          continue;
        }
        xLo = Math.min(xLo, low(a, dx, range));
        xHi = Math.max(xHi, high(a, dx, range));
        yLo = Math.min(yLo, low(c, dy, range));
        yHi = Math.max(yHi, high(c, dy, range));
      }
      if (xLo > xHi) {
        throw Store.failException;
      }
      x.domain.in(store.level, x, Math.max(xLo, x.min()), Math.min(xHi, x.max()));
      y.domain.in(store.level, y, Math.max(yLo, y.min()), Math.min(yHi, y.max()));
    } while (store.propagationHasOccurred);
  }

  /**
   * Narrows the parameter range so that v + s d stays in [lo, hi]; false when nothing stays. The
   * bounds are widened by a precision step, so that rounding never cuts a solution.
   */
  private static boolean cut(double[] range, double v, double d, double lo, double hi) {
    double eps = Math.max(FloatDomain.epsilon(lo), FloatDomain.epsilon(hi));
    if (d == 0.0) {
      return v >= lo - eps && v <= hi + eps;
    }
    double s1 = (lo - eps - v) / d;
    double s2 = (hi + eps - v) / d;
    double sLo = FloatDomain.down(Math.min(s1, s2));
    double sHi = FloatDomain.up(Math.max(s1, s2));
    range[0] = Math.max(range[0], sLo);
    range[1] = Math.min(range[1], sHi);
    return range[0] <= range[1];
  }

  private static double low(double v, double d, double[] range) {
    double e = d >= 0 ? v + d * range[0] : v + d * range[1];
    return FloatDomain.down(FloatDomain.down(e));
  }

  private static double high(double v, double d, double[] range) {
    double e = d >= 0 ? v + d * range[1] : v + d * range[0];
    return FloatDomain.up(FloatDomain.up(e));
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    if (!x.singleton() || !y.singleton()) {
      return false;
    }
    double[] range = new double[2];
    int segments = Math.max(1, xKnot.length - 1);
    for (int i = 0; i < segments; i++) {
      int j = Math.min(i + 1, xKnot.length - 1);
      range[0] = 0.0;
      range[1] = 1.0;
      if (cut(range, xKnot[i], xKnot[j] - xKnot[i], x.min(), x.max())
          && cut(range, yKnot[i], yKnot[j] - yKnot[i], y.min(), y.max())) {
        return true;
      }
    }
    return false;
  }

  @Override
  public String toString() {
    return id()
        + " : PiecewiseLinear("
        + x
        + ", "
        + y
        + ", "
        + Arrays.toString(xKnot)
        + ", "
        + Arrays.toString(yKnot)
        + ")";
  }

  @Override
  public PiecewiseLinear copy(VarMap map) {
    return new PiecewiseLinear(map.get(x), map.get(y), xKnot, yKnot);
  }
}
