/*
 * FloatDomain.java
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

package org.jacop.floats.core;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import org.jacop.constraints.Constraint;
import org.jacop.core.Domain;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Defines an integer domain and related operations on it.
 *
 * <p>FloatDomain implementations can not assume that arguments to any function can not be empty
 * domains.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class FloatDomain extends Domain {

  /*
   * It specifies the minimum element in the domain.
   */
  public static final double MIN_FLOAT = -Double.MAX_VALUE; // -1e150;

  /*
   * It specifies the maximum element in the domain.
   */
  public static final double MAX_FLOAT = Double.MAX_VALUE; // 1e150;
  /*
   * It specifies the constant pi, as defined in java.lang.Math package.
   */
  public static final double PI = Math.PI;
  /*
   * It specifies the constant e, as defined in java.lang.Math package.
   */
  public static final double E = Math.E;

  /**
   * It specifies the constant for GROUND event. It has to be smaller than the constant for events
   * BOUND and ANY.
   */
  public static final int GROUND = 0;

  /**
   * It specifies the constant for BOUND event. It has to be smaller than the constant for event
   * ANY.
   */
  public static final int BOUND = 1;

  /** It specifies the constant for ANY event. */
  public static final int ANY = 2;

  /** Unique identifier for an interval domain type. */
  public static final int FLOAT_INTERVAL_DOMAIN_ID = 0;

  /** Unique identifier for an interval domain type. */
  public static final int INTERVAL_DOMAIN_ID = 0;

  /**
   * It specifies for each event what other events are subsumed by this event. Possibly implement
   * this by bit flags in int.
   */
  static final int[][] eventsInclusion = {
    {GROUND, BOUND, ANY}, // GROUND event
    {BOUND, ANY}, // BOUND event
    {ANY}
  }; // ANY event

  /*
   * Minimization step for floating-point cost function minimization.
   */
  public static double minimizationStep = 0;
  /*
   * It specifies the rounding method;
   * true - extend interval outward
   * false - does not extend interval and use calculation results.
   */
  static boolean outward = true;
  /*
   * It specifies the method for printing a domain.
   * If true, we print each domain as an interval regardles of
   * the current precision of calculations.
   * If true, the print-out prints singletons, defined by method
   * singleton() in FloatingInterval, as single values.
   */
  static boolean intervalPrint;

  /** The default precision format for floating point print-out: no rounding. */
  public static final double DEFAULT_FORMAT = Double.MAX_VALUE;

  /** The default precision for floating point operations. */
  public static final double DEFAULT_PRECISION = 1e-11;

  /*
   * It specifies the precision format for floating point print-out
   */
  static double format = DEFAULT_FORMAT;
  /*
   * It specifies the precision for floating point operations, among others
   * decide when two numbers are equal and when a interval is singleton.
   */
  static double precision = DEFAULT_PRECISION;

  /**
   * The smallest relative reduction of a float domain that is applied; smaller narrowings are
   * skipped. Zero (the default) applies every narrowing. Set by system property {@code
   * org.jacop.floats.minReduction}.
   */
  static double minReduction =
      Double.parseDouble(System.getProperty("org.jacop.floats.minReduction", "0"));

  /**
   * It returns the smallest relative reduction of a float domain that is applied.
   *
   * @return the ratio, zero when every narrowing is applied
   */
  public static double minReduction() {
    return minReduction;
  }

  /**
   * It sets the smallest relative reduction of a float domain that is applied.
   *
   * @param ratio the ratio in [0, 1), zero to apply every narrowing
   */
  public static void setMinReduction(double ratio) {
    minReduction = ratio;
  }

  /**
   * It specifies the previous domain which was used by this domain. The old domain is stored here
   * and can be easily restored if necessary.
   */
  public FloatDomain prevDomain;

  /*
   * It defines rounding method
   *
   * @param out defines rounding method true = outward, false = no rounding outward
   */
  public static void setOutward(boolean out) {
    outward = out;
  }

  /**
   * It sets the interval print mode for domain output.
   *
   * @param p true to print as intervals, false to print singletons as single values
   */
  public static void intervalPrint(boolean p) {
    intervalPrint = p;
  }

  /**
   * It returns the current precision format for floating point print-out.
   *
   * @return the format precision value
   */
  public static double format() {
    return format;
  }

  /**
   * It sets the precision format for floating point print-out.
   *
   * @param f the format precision value
   */
  public static void setFormat(double f) {
    format = f;
  }

  /**
   * It returns the current precision for floating point operations.
   *
   * @return the precision value
   */
  public static double precision() {
    return precision;
  }

  /**
   * It sets the precision for floating point operations.
   *
   * @param p the precision value
   */
  public static void setPrecision(double p) {
    precision = p;
  }

  /**
   * It returns the epsilon value for the given floating-point number.
   *
   * @param f the floating-point value
   * @return the maximum of precision and ULP of f
   */
  public static double epsilon(double f) {

    return Math.max(precision(), Math.ulp(f));
  }

  /**
   * It returns the unit in the last place (ULP) of the given floating-point value.
   *
   * @param f the floating-point value
   * @return the ULP of f
   */
  public static double ulp(double f) {

    return Math.ulp(f);
  }

  /**
   * It returns the unit in the last place (ULP) for the minimal value of the variable.
   *
   * @param f the floating-point variable
   * @return the ULP of the minimum value
   */
  public static double minUlp(FloatVar f) {

    return Math.ulp(f.min());
  }

  /**
   * It returns the unit in the last place (ULP) for the maximal value of the variable.
   *
   * @param f the floating-point variable
   * @return the ULP of the maximum value
   */
  public static double maxUlp(FloatVar f) {

    return Math.ulp(f.max());
  }

  /**
   * It returns the previous floating-point number toward negative infinity before d. This method is
   * supposed to be used by constraints.
   *
   * @param d the floating-point value
   * @return the previous floating-point number if outward rounding is enabled, otherwise d
   */
  public static double down(double d) {

    if (outward) {
      return Math.nextDown(d);
    } else {
      return d;
    }
  }

  /**
   * It returns the next floating-point number toward positive infinity after d. This method is
   * supposed to be used by constraints.
   *
   * @param d the floating-point value
   * @return the next floating-point number if outward rounding is enabled, otherwise d
   */
  public static double up(double d) {

    if (outward) {
      return Math.nextUp(d);
    } else {
      return d;
    }
  }

  // Directed rounding of one operation. Double arithmetic rounds to nearest, so the computed value
  // is within an ulp of the exact one; down(x op y) and up(x op y) step one ulp out even when the
  // operation is exact (2.0 + 3.0, 0.5 * 4.0, -2.0 + 2.0), which turned exact integer values into
  // two-ulp intervals: floor(x + y) of x = -2, y = 2 then admitted -1 as well as 0. These versions
  // compute the rounding error exactly (Knuth's TwoSum, the fused multiply-add for products,
  // quotients and square roots) and step out only on the side where the exact value lies. Results
  // that are infinite or near the underflow range (where the error itself rounds) keep the step.

  /** Below this magnitude the error of a product or quotient may itself be inexact. */
  private static final double EXACT_ERROR_MIN = 0x1.0p-960;

  /**
   * The largest double at most a + b.
   *
   * @param a the first summand
   * @param b the second summand
   * @return a lower bound of a + b
   */
  public static double addDown(double a, double b) {
    double s = a + b;
    if (!outward) {
      return s;
    }
    // TwoSum: the exact error of s, without branches; it is NaN when s overflows or an operand is
    // infinite, which also steps out
    double bb = s - a;
    double err = (a - (s - bb)) + (b - bb);
    return err >= 0 ? s : Math.nextDown(s);
  }

  /**
   * The smallest double at least a + b.
   *
   * @param a the first summand
   * @param b the second summand
   * @return an upper bound of a + b
   */
  public static double addUp(double a, double b) {
    double s = a + b;
    if (!outward) {
      return s;
    }
    // TwoSum: the exact error of s, without branches; it is NaN when s overflows or an operand is
    // infinite, which also steps out
    double bb = s - a;
    double err = (a - (s - bb)) + (b - bb);
    return err <= 0 ? s : Math.nextUp(s);
  }

  /**
   * The largest double at most a * b.
   *
   * @param a the first factor
   * @param b the second factor
   * @return a lower bound of a * b
   */
  public static double mulDown(double a, double b) {
    double p = a * b;
    if (!outward) {
      return p;
    }
    if (!exactErrorRange(p, a, b)) {
      return Math.nextDown(p);
    }
    return Math.fma(a, b, -p) >= 0 ? p : Math.nextDown(p);
  }

  /**
   * The smallest double at least a * b.
   *
   * @param a the first factor
   * @param b the second factor
   * @return an upper bound of a * b
   */
  public static double mulUp(double a, double b) {
    double p = a * b;
    if (!outward) {
      return p;
    }
    if (!exactErrorRange(p, a, b)) {
      return Math.nextUp(p);
    }
    return Math.fma(a, b, -p) <= 0 ? p : Math.nextUp(p);
  }

  /**
   * The largest double at most a / b.
   *
   * @param a the dividend
   * @param b the divisor
   * @return a lower bound of a / b
   */
  public static double divDown(double a, double b) {
    double q = a / b;
    if (!outward) {
      return q;
    }
    if (!exactErrorRange(q, a, b)) {
      return Math.nextDown(q);
    }
    // a - q * b, exact; the exact quotient is above q when it has the sign of b
    double rem = Math.fma(-q, b, a);
    return rem == 0 || (rem > 0) == (b > 0) ? q : Math.nextDown(q);
  }

  /**
   * The smallest double at least a / b.
   *
   * @param a the dividend
   * @param b the divisor
   * @return an upper bound of a / b
   */
  public static double divUp(double a, double b) {
    double q = a / b;
    if (!outward) {
      return q;
    }
    if (!exactErrorRange(q, a, b)) {
      return Math.nextUp(q);
    }
    double rem = Math.fma(-q, b, a);
    return rem == 0 || (rem > 0) != (b > 0) ? q : Math.nextUp(q);
  }

  /**
   * The largest double at most the square root of a (a &gt;= 0).
   *
   * @param a the argument
   * @return a lower bound of sqrt(a)
   */
  public static double sqrtDown(double a) {
    double r = Math.sqrt(a);
    if (!outward) {
      return r;
    }
    if (!exactErrorRange(r, a, r)) {
      return Math.nextDown(r);
    }
    return Math.fma(r, r, -a) <= 0 ? r : Math.nextDown(r);
  }

  /**
   * The smallest double at least the square root of a (a &gt;= 0).
   *
   * @param a the argument
   * @return an upper bound of sqrt(a)
   */
  public static double sqrtUp(double a) {
    double r = Math.sqrt(a);
    if (!outward) {
      return r;
    }
    if (!exactErrorRange(r, a, r)) {
      return Math.nextUp(r);
    }
    return Math.fma(r, r, -a) >= 0 ? r : Math.nextUp(r);
  }

  // the result and the operands are finite and the result is zero only for a zero operand, far
  // enough from the underflow range for the error term to be exact
  private static boolean exactErrorRange(double result, double a, double b) {
    if (Double.isInfinite(result) || Double.isNaN(result)) {
      return false;
    }
    if (result == 0) {
      return a == 0 || b == 0 && !Double.isInfinite(a);
    }
    return Math.abs(result) >= EXACT_ERROR_MIN
        && Math.abs(a) >= EXACT_ERROR_MIN
        && Math.abs(b) >= EXACT_ERROR_MIN;
  }

  /**
   * It returns the previous floating-point number toward negative infinity before d. This method is
   * supposed to be used by methods for domain computations.
   *
   * @param d the floating-point value
   * @return the previous floating-point number
   */
  public static double previous(double d) {
    return Math.nextDown(d); // downBit(d); //d - ulp(d);
  }

  /**
   * It sets the optimization step for floating point optimization.
   *
   * @param s the step size for minimization
   */
  public static void setStep(double s) {
    minimizationStep = s;
  }

  /**
   * It returns the previous floating-point number before d for minimization with FloatVar cost
   * function.
   *
   * @param d the floating-point value
   * @return the previous value for minimization purposes
   */
  public static double previousForMinimization(double d) {
    if (minimizationStep == 0) {
      return previous(d);
    } else {
      return d - minimizationStep;
    }
  }

  /**
   * It returns the next floating-point number toward positive infinity after d. This method is
   * supposed to be used by methods for domain computations.
   *
   * @param d the floating-point value
   * @return the next floating-point number
   */
  public static double next(double d) {
    return Math.nextUp(d); // upBit(d); // d + ulp(d);
  }

  /**
   * It finds the result interval for addition of {a..b} + {c..d}.
   *
   * @param a the minimum value of the first interval
   * @param b the maximum value of the first interval
   * @param c the minimum value of the second interval
   * @param d the maximum value of the second interval
   * @return the interval domain representing the result of the addition
   */
  public static FloatIntervalDomain addBounds(double a, double b, double c, double d) {

    // directed rounding keeps exact sums (such as x + 0.0) exact
    return new FloatIntervalDomain(addDown(a, c), addUp(b, d));
  }

  /**
   * It finds the result interval for subtraction of {a..b} - {c..d}.
   *
   * @param a the minimum value of the first interval
   * @param b the maximum value of the first interval
   * @param c the minimum value of the second interval
   * @param d the maximum value of the second interval
   * @return the interval domain representing the result of the subtraction
   */
  public static FloatIntervalDomain subBounds(double a, double b, double c, double d) {
    return new FloatIntervalDomain(addDown(a, -d), addUp(b, -c));
  }

  /**
   * It finds the result interval for multiplication of {a..b} * {c..d}.
   *
   * @param a the minimum value of the first interval
   * @param b the maximum value of the first interval
   * @param c the minimum value of the second interval
   * @param d the maximum value of the second interval
   * @return the interval domain representing the result of the multiplication
   */
  private static FloatIntervalDomain mulBoundsDispatch(
      double a,
      double b,
      double c,
      double d,
      boolean m1,
      boolean p01,
      boolean p11,
      boolean n01,
      boolean n11,
      boolean m2,
      boolean p02,
      boolean p12,
      boolean n02,
      boolean n12) {
    if (p11) {
      return mulBoundsP1(a, b, c, d, m2, p02, p12, n02, n12);
    }
    if (p01) {
      return mulBoundsP0(b, c, d, m2, p02, p12, n02, n12);
    }
    if (m1) {
      return mulBoundsM(a, b, c, d, m2, p02, p12, n02, n12);
    }
    if (n11) {
      return mulBoundsN1(a, b, c, d, m2, p02, p12, n02, n12);
    }
    if (n01) {
      return mulBoundsN0(a, c, d, m2, p02, p12, n02, n12);
    }
    return new FloatIntervalDomain(0.0, 0.0);
  }

  /**
   * Computes bounds for multiplication of two closed intervals.
   *
   * @param a the minimum value of the first interval
   * @param b the maximum value of the first interval
   * @param c the minimum value of the second interval
   * @param d the maximum value of the second interval
   * @return the interval enclosing products of values from both intervals
   */
  public static FloatIntervalDomain mulBounds(double a, double b, double c, double d) {

    if (c == 1.0 && d == 1.0) {
      return new FloatIntervalDomain(a, b);
    }
    if (c == -1.0 && d == -1.0) {
      return new FloatIntervalDomain(-b, -a);
    }

    return mulBoundsDispatch(
        a,
        b,
        c,
        d,
        a < 0 && b > 0,
        a == 0 && b > 0,
        a > 0 && b > 0,
        a < 0 && b == 0,
        a < 0 && b < 0,
        c < 0 && d > 0,
        c == 0 && d > 0,
        c > 0 && d > 0,
        c < 0 && d == 0,
        c < 0 && d < 0);
  }

  private static FloatIntervalDomain mulBoundsP1(
      double a,
      double b,
      double c,
      double d,
      boolean m2,
      boolean p02,
      boolean p12,
      boolean n02,
      boolean n12) {
    if (p12) {
      return new FloatIntervalDomain(mulDown(a, c), mulUp(b, d));
    }
    if (p02) {
      return new FloatIntervalDomain(0.0, mulUp(b, d));
    }
    if (m2) {
      return new FloatIntervalDomain(mulDown(b, c), mulUp(b, d));
    }
    if (n12) {
      return new FloatIntervalDomain(mulDown(b, c), mulUp(a, d));
    }
    if (n02) {
      return new FloatIntervalDomain(mulDown(b, c), 0.0);
    }
    return new FloatIntervalDomain(0.0, 0.0);
  }

  private static FloatIntervalDomain mulBoundsP0(
      double b,
      double c,
      double d,
      boolean m2,
      boolean p02,
      boolean p12,
      boolean n02,
      boolean n12) {
    if (p12 || p02) {
      return new FloatIntervalDomain(0.0, mulUp(b, d));
    }
    if (n12 || n02) {
      return new FloatIntervalDomain(mulDown(b, c), 0.0);
    }
    if (m2) {
      return new FloatIntervalDomain(mulDown(b, c), mulUp(b, d));
    }
    return new FloatIntervalDomain(0.0, 0.0);
  }

  private static FloatIntervalDomain mulBoundsM(
      double a,
      double b,
      double c,
      double d,
      boolean m2,
      boolean p02,
      boolean p12,
      boolean n02,
      boolean n12) {
    if (p02 || p12) {
      return new FloatIntervalDomain(mulDown(a, d), mulUp(b, d));
    }
    if (n02 || n12) {
      return new FloatIntervalDomain(mulDown(b, c), mulUp(a, c));
    }
    if (m2) {
      return new FloatIntervalDomain(
          Math.min(mulDown(a, d), mulDown(b, c)), Math.max(mulUp(a, c), mulUp(b, d)));
    }
    return new FloatIntervalDomain(0.0, 0.0);
  }

  private static FloatIntervalDomain mulBoundsN1(
      double a,
      double b,
      double c,
      double d,
      boolean m2,
      boolean p02,
      boolean p12,
      boolean n02,
      boolean n12) {
    if (p12) {
      return new FloatIntervalDomain(mulDown(a, d), mulUp(b, c));
    }
    if (p02) {
      return new FloatIntervalDomain(mulDown(a, d), 0.0);
    }
    if (m2) {
      return new FloatIntervalDomain(mulDown(a, d), mulUp(a, c));
    }
    if (n12) {
      return new FloatIntervalDomain(mulDown(b, d), mulUp(a, c));
    }
    if (n02) {
      return new FloatIntervalDomain(0.0, mulUp(a, c));
    }
    return new FloatIntervalDomain(0.0, 0.0);
  }

  private static FloatIntervalDomain mulBoundsN0(
      double a,
      double c,
      double d,
      boolean m2,
      boolean p02,
      boolean p12,
      boolean n02,
      boolean n12) {
    if (p02 || p12) {
      return new FloatIntervalDomain(mulDown(a, d), 0.0);
    }
    if (n02 || n12) {
      return new FloatIntervalDomain(0.0, mulUp(a, c));
    }
    if (m2) {
      return new FloatIntervalDomain(mulDown(a, d), mulUp(a, c));
    }
    return new FloatIntervalDomain(0.0, 0.0);
  }

  /**
   * It finds the result interval for division of {a..b} / {c..d} for div and mod constraints.
   *
   * @param a the minimum value of the first interval
   * @param b the maximum value of the first interval
   * @param c the minimum value of the second interval
   * @param d the maximum value of the second interval
   * @return the interval domain representing the result of the division
   */
  private static FloatIntervalDomain divBoundsDispatch(
      double a,
      double b,
      double c,
      double d,
      boolean m1,
      boolean z1,
      boolean p01,
      boolean p11,
      boolean n01,
      boolean n11,
      boolean m2,
      boolean p02,
      boolean p12,
      boolean n02,
      boolean n12) {
    if (p11) {
      return divBoundsP1(a, b, c, d, m2, p02, p12, n02, n12);
    }
    if (p01) {
      return divBoundsP0(b, c, d, p12, n12);
    }
    if (m1) {
      return divBoundsM(a, b, c, d, p12, n12);
    }
    if (n11) {
      return divBoundsN1(a, b, c, d, m2, p02, p12, n02, n12);
    }
    if (n01) {
      return divBoundsN0(a, c, d, p12, n12);
    }
    if (z1) {
      return divBoundsZ(p12, n12);
    }
    return null;
  }

  /**
   * Computes bounds for division of two closed intervals.
   *
   * @param a the minimum value of the dividend interval
   * @param b the maximum value of the dividend interval
   * @param c the minimum value of the divisor interval
   * @param d the maximum value of the divisor interval
   * @return the interval enclosing quotients of values from both intervals
   */
  public static FloatIntervalDomain divBounds(double a, double b, double c, double d) {

    if (c == 1.0 && d == 1.0) {
      return new FloatIntervalDomain(a, b);
    }
    if (c == -1.0 && d == -1.0) {
      return new FloatIntervalDomain(-b, -a);
    }

    return divBoundsDispatch(
        a,
        b,
        c,
        d,
        a < 0 && b > 0,
        a == 0 && b == 0,
        a == 0 && b > 0,
        a > 0 && b > 0,
        a < 0 && b == 0,
        a < 0 && b < 0,
        c < 0 && d > 0,
        c == 0 && d > 0,
        c > 0 && d > 0,
        c < 0 && d == 0,
        c < 0 && d < 0);
  }

  private static FloatIntervalDomain divBoundsP1(
      double a,
      double b,
      double c,
      double d,
      boolean m2,
      boolean p02,
      boolean p12,
      boolean n02,
      boolean n12) {
    if (p12) {
      return new FloatIntervalDomain(divDown(a, d), divUp(b, c));
    }
    if (p02) {
      return new FloatIntervalDomain(divDown(a, d), MAX_FLOAT);
    }
    if (m2) {
      double min = divDown(a, d);
      double max = divUp(a, c);
      return (FloatIntervalDomain)
          new FloatIntervalDomain(MIN_FLOAT, max).union(new FloatIntervalDomain(min, MAX_FLOAT));
    }
    if (n12) {
      return new FloatIntervalDomain(divDown(b, d), divUp(a, c));
    }
    if (n02) {
      return new FloatIntervalDomain(MIN_FLOAT, divUp(a, c));
    }
    throw Store.failException;
  }

  private static FloatIntervalDomain divBoundsP0(
      double b, double c, double d, boolean p12, boolean n12) {
    if (p12) {
      return new FloatIntervalDomain(0.0, divUp(b, c));
    }
    if (n12) {
      return new FloatIntervalDomain(divDown(b, d), 0.0);
    }
    return new FloatIntervalDomain(MIN_FLOAT, MAX_FLOAT);
  }

  private static FloatIntervalDomain divBoundsM(
      double a, double b, double c, double d, boolean p12, boolean n12) {
    if (p12) {
      return new FloatIntervalDomain(divDown(a, c), divUp(b, c));
    }
    if (n12) {
      return new FloatIntervalDomain(divDown(b, d), divUp(a, d));
    }
    return new FloatIntervalDomain(MIN_FLOAT, MAX_FLOAT);
  }

  private static FloatIntervalDomain divBoundsN1(
      double a,
      double b,
      double c,
      double d,
      boolean m2,
      boolean p02,
      boolean p12,
      boolean n02,
      boolean n12) {
    if (p12) {
      return new FloatIntervalDomain(divDown(a, c), divUp(b, d));
    }
    if (p02) {
      return new FloatIntervalDomain(MIN_FLOAT, divUp(b, d));
    }
    if (m2) {
      double min = divDown(b, c);
      double max = divUp(b, d);
      return (FloatIntervalDomain)
          new FloatIntervalDomain(MIN_FLOAT, max).union(new FloatIntervalDomain(min, MAX_FLOAT));
    }
    if (n12) {
      return new FloatIntervalDomain(divDown(b, c), divUp(a, d));
    }
    if (n02) {
      return new FloatIntervalDomain(divDown(b, c), MAX_FLOAT);
    }
    throw Store.failException;
  }

  private static FloatIntervalDomain divBoundsN0(
      double a, double c, double d, boolean p12, boolean n12) {
    if (p12) {
      return new FloatIntervalDomain(divDown(a, c), 0.0);
    }
    if (n12) {
      return new FloatIntervalDomain(0.0, divUp(a, d));
    }
    return new FloatIntervalDomain(MIN_FLOAT, MAX_FLOAT);
  }

  private static FloatIntervalDomain divBoundsZ(boolean p12, boolean n12) {
    if (p12 || n12) {
      return new FloatIntervalDomain(0.0, 0.0);
    }
    return new FloatIntervalDomain(MIN_FLOAT, MAX_FLOAT);
  }

  /**
   * It helps to specify what events should be executed if a given event occurs.
   *
   * @param pruningEvent the pruning event for which we want to know what events it encompasses.
   * @return an array specifying what events should be included given this event.
   */
  public int[] getEventsInclusion(int pruningEvent) {
    return eventsInclusion[pruningEvent];
  }

  /**
   * It adds interval of values to the domain.
   *
   * @param i Interval which needs to be added to the domain.
   */
  public void unionAdapt(FloatInterval i) {
    unionAdapt(i.min(), i.max());
  }

  /**
   * It adds all values between min and max to the domain.
   *
   * @param min the left bound of the interval being added.
   * @param max the right bound of the interval being added.
   */
  public abstract void unionAdapt(double min, double max);

  /**
   * It adds a values to the domain.
   *
   * @param value value being added to the domain.
   */
  public void unionAdapt(double value) {
    unionAdapt(value, value);
  }

  /**
   * It computes a union between this domain and the domain provided as a parameter. This domain is
   * changed to reflect the result.
   *
   * @param union the domain with is used for the union operation with this domain.
   * @return it returns information about the pruning event which has occurred due to this
   *     operation.
   */
  public int unionAdapt(FloatDomain union) {

    FloatDomain result = union(union);

    if (result.getSize() == getSize()) {
      return NONE;
    } else {
      setDomain(result);
      return ANY;
    }
  }

  /**
   * It adds values as specified by the parameter to the domain.
   *
   * @param domain Domain which needs to be added to the domain.
   */
  public void addDom(FloatDomain domain) {

    FloatIntervalEnumeration enumer = domain.floatIntervalEnumeration();
    while (enumer.hasMoreElements()) {
      unionAdapt(enumer.nextElement());
    }
    /*
    }
          else {
              ValueEnumeration enumer = domain.valueEnumeration();
              while (enumer.hasMoreElements())
                  unionAdapt(enumer.nextElement());
          }
              */

  }

  /**
   * Checks if two domains intersect.
   *
   * @param domain the domain for which intersection is checked.
   * @return true if domains are intersecting.
   */
  public boolean isIntersecting(FloatDomain domain) {

    FloatIntervalEnumeration enumer = domain.floatIntervalEnumeration();
    while (enumer.hasMoreElements()) {
      FloatInterval next = enumer.nextElement();
      if (isIntersecting(next.min(), next.max())) {
        return true;
      }
    }
    return false;
  }

  /**
   * It checks if interval min..max intersects with current domain.
   *
   * @param min the left bound of the interval.
   * @param max the right bound of the interval.
   * @return true if domain intersects with the specified interval.
   */
  public abstract boolean isIntersecting(double min, double max);

  /**
   * It specifies if the current domain contains the domain given as a parameter.
   *
   * @param domain for which we check if it is contained in the current domain.
   * @return true if the supplied domain is cover by this domain.
   */
  public boolean contains(FloatDomain domain) {

    FloatIntervalEnumeration enumer = domain.floatIntervalEnumeration();
    while (enumer.hasMoreElements()) {
      FloatInterval next = enumer.nextElement();
      if (!contains(next.min(), next.max())) {
        return false;
      }
    }
    /*
    }
    else {
        ValueEnumeration enumer = domain.valueEnumeration();
        while (enumer.hasMoreElements())
            if (!contains(enumer.nextElement()))
                return false;
    }
        */
    return true;
  }

  /**
   * It checks if an interval min..max belongs to the domain.
   *
   * @param min the minimum value of the interval being checked
   * @param max the maximum value of the interval being checked
   * @return true if value belongs to the domain.
   */
  public abstract boolean contains(double min, double max);

  /**
   * It checks if value belongs to the domain.
   *
   * @param value which is checked if it exists in the domain.
   * @return true if value belongs to the domain.
   */
  public boolean contains(int value) {
    return contains(value, value);
  }

  /**
   * Checks whether the given double value belongs to the domain.
   *
   * @param value the value to check.
   * @return true if value belongs to the domain.
   */
  public abstract boolean contains(double value);

  /**
   * It creates a complement of a domain.
   *
   * @return it returns the complement of this domain.
   */
  public abstract FloatDomain complement();

  /**
   * It returns value enumeration of the domain values.
   *
   * @return valueEnumeration which can be used to enumerate one by one value from this domain.
   */
  public abstract ValueEnumeration valueEnumeration();

  /**
   * It returns interval enumeration of the domain values.
   *
   * @return intervalEnumeration which can be used to enumerate intervals in this domain.
   */
  public abstract IntervalEnumeration intervalEnumeration();

  /**
   * It returns interval enumeration of the domain values.
   *
   * @return intervalEnumeration which can be used to enumerate intervals in this domain.
   */
  public abstract FloatIntervalEnumeration floatIntervalEnumeration();

  /**
   * It returns the size of the domain.
   *
   * @return number of elements in this domain.
   */
  public abstract int getSize();

  /**
   * It intersects current domain with the one given as a parameter.
   *
   * @param dom domain with which the intersection needs to be computed.
   * @return the intersection between supplied domain and this domain.
   */
  public abstract FloatDomain intersect(FloatDomain dom);

  /**
   * In intersects current domain with the interval min..max.
   *
   * @param min the left bound of the interval (inclusive)
   * @param max the right bound of the interval (inclusive)
   * @return the intersection between the specified interval and this domain.
   */
  public abstract FloatDomain intersect(double min, double max);

  /**
   * It intersects with the domain which is a complement of value.
   *
   * @param value the value for which the complement is computed
   * @return the domain which does not contain specified value.
   */
  public FloatDomain subtract(double value) {
    return subtract(value, value);
  }

  /**
   * It subtracts domain from current domain and returns the result.
   *
   * @param domain the domain which is subtracted from this domain.
   * @return the result of the subtraction.
   */
  public FloatDomain subtract(FloatDomain domain) {

    if (domain.isEmpty()) {
      return this.cloneLight();
    }

    FloatIntervalEnumeration enumer = domain.floatIntervalEnumeration();
    FloatInterval first = enumer.nextElement();
    FloatDomain result = this.subtract(first.min(), first.max());
    while (enumer.hasMoreElements()) {
      FloatInterval next = enumer.nextElement();
      result.subtractAdapt(next.min(), next.max());
    }
    return result;
    /*
    }
    else {
        ValueEnumeration enumer = domain.valueEnumeration();
        int first = enumer.nextElement();
        FloatDomain result = this.subtract(first);
        while (enumer.hasMoreElements()) {
            int next = enumer.nextElement();
            if (result.contains(next))
                result.subtractAdapt(next);
        }
        return result;
    }
        */
  }

  /**
   * It subtracts interval min..max.
   *
   * @param min the left bound of the interval (inclusive).
   * @param max the right bound of the interval (inclusive).
   * @return the result of the subtraction.
   */
  public abstract FloatDomain subtract(double min, double max);

  /**
   * It removes value from the domain. It adapts current (this) domain.
   *
   * @param value the value for which the complement is computed
   */
  public abstract void subtractAdapt(double value);

  /**
   * It removes all values between min and max to the domain.
   *
   * @param min the left bound of the interval being removed.
   * @param max the right bound of the interval being removed.
   */
  public abstract void subtractAdapt(double min, double max);

  /**
   * It returns the maximum value in a domain.
   *
   * @return the largest value present in the domain.
   */
  public abstract double max();

  /**
   * It returns the minimum value in a domain.
   *
   * @return the smallest value present in the domain.
   */
  public abstract double min();

  /**
   * It sets the domain to the specified domain.
   *
   * @param domain the domain from which this domain takes all elements.
   */
  public abstract void setDomain(FloatDomain domain);

  /**
   * It sets this domain to contain exactly all values between min and max.
   *
   * @param min the left bound of the interval (inclusive).
   * @param max the right bound of the interval (inclusive).
   */
  public abstract void setDomain(double min, double max);

  /**
   * It returns true if given domain has only one element equal c.
   *
   * @param c the value to which the only element should be equal to.
   * @return true if the domain contains only one element c.
   */
  public boolean singleton(double c) {
    return min() == c && getSize() == 1;
  }

  @Override
  public boolean singleton(Domain value) {

    if (getSize() > 1) {
      return false;
    }

    if (isEmpty()) {
      return false;
    }

    if (value.getSize() != 1) {
      throw new IllegalArgumentException("An argument should be a singleton domain");
    }

    if (ASSERTS_ENABLED && !(value instanceof FloatDomain)) {
      throw new IllegalStateException(
          String.valueOf("Can not compare int domains with other types of domains."));
    }

    FloatDomain domain = (FloatDomain) value;

    return eq(domain);
  }

  /**
   * It computes union of the supplied domain with this domain.
   *
   * @param domain the domain for which the union is computed.
   * @return the union of this domain with the supplied one.
   */
  public FloatDomain union(FloatDomain domain) {

    if (this.isEmpty()) {
      return domain.cloneLight();
    }

    FloatDomain result = this.cloneLight();

    if (domain.isEmpty()) {
      return result;
    }

    FloatIntervalEnumeration enumer = domain.floatIntervalEnumeration();
    while (enumer.hasMoreElements()) {
      FloatInterval next = enumer.nextElement();
      result.unionAdapt(next.min(), next.max());
    }
    return result;
    /*
    }
    else {
        ValueEnumeration enumer = domain.valueEnumeration();
        while (enumer.hasMoreElements()) {
            int next = enumer.nextElement();
            result.unionAdapt(next);
        }
        return result;
    }
        */
  }

  /**
   * It computes union of this domain and the interval.
   *
   * @param min the left bound of the interval (inclusive).
   * @param max the right bound of the interval (inclusive).
   * @return the union of this domain and the interval.
   */
  public FloatDomain union(double min, double max) {

    FloatDomain result = this.cloneLight();
    result.unionAdapt(min, max);
    return result;
  }

  /**
   * It computes union of this domain and value.
   *
   * @param value it specifies the value which is being added.
   * @return domain which is a union of this one and the value.
   */
  public FloatDomain union(double value) {
    return union(value, value);
  }

  /**
   * It updates the domain according to the minimum value and stamp value. It informs the variable
   * of a change if it occurred.
   *
   * @param storeLevel level of the store at which the update occurs.
   * @param v variable for which this domain is used.
   * @param min the minimum value to which the domain is updated.
   */
  public void inMin(int storeLevel, Var v, double min) {

    in(storeLevel, v, min, max());
  }

  /**
   * It updates the domain according to the maximum value and stamp value. It informs the variable
   * of a change if it occurred.
   *
   * @param storeLevel level of the store at which the update occurs.
   * @param v variable for which this domain is used.
   * @param max the maximum value to which the domain is updated.
   */
  public void inMax(int storeLevel, Var v, double max) {

    in(storeLevel, v, min(), max);
  }

  /**
   * It updates the domain to have values only within the interval min..max. The type of update is
   * decided by the value of stamp. It informs the variable of a change if it occurred.
   *
   * @param storeLevel level of the store at which the update occurs.
   * @param v variable for which this domain is used.
   * @param min the minimum value to which the domain is updated.
   * @param max the maximum value to which the domain is updated.
   */
  public abstract void in(int storeLevel, Var v, double min, double max);

  /**
   * It updates the domain to have values only within the domain. The type of update is decided by
   * the value of stamp. It informs the variable of a change if it occurred.
   *
   * @param storeLevel level of the store at which the update occurs.
   * @param v variable for which this domain is used.
   * @param domain the domain according to which the domain is updated.
   */
  public void in(int storeLevel, Var v, FloatDomain domain) {

    inShift(storeLevel, v, domain, 0);
  }

  @Override
  public void in(int level, Var v, Domain domain) {
    in(level, v, (FloatDomain) domain);
  }

  /**
   * It reduces domain to a single value.
   *
   * @param level level of the store at which the update occurs.
   * @param v variable for which this domain is used.
   * @param value the value according to which the domain is updated.
   */
  public void inValue(int level, Var v, double value) {
    in(level, v, value, value);
  }

  /**
   * It updates the domain to not contain the value complement. It informs the variable of a change
   * if it occurred.
   *
   * @param storeLevel level of the store at which the update occurs.
   * @param v variable for which this domain is used.
   * @param complement value which is removed from the domain if it belonged to the domain.
   */
  public void inComplement(int storeLevel, Var v, double complement) {

    inComplement(storeLevel, v, complement, complement);
  }

  /**
   * It updates the domain so it does not contain the supplied interval. It informs the variable of
   * a change if it occurred.
   *
   * @param storeLevel level of the store at which the update occurs.
   * @param v variable for which this domain is used.
   * @param min the left bound of the interval (inclusive).
   * @param max the right bound of the interval (inclusive).
   */
  public abstract void inComplement(int storeLevel, Var v, double min, double max);

  /**
   * It returns number of intervals required to represent this domain.
   *
   * @return the number of intervals in the domain.
   */
  public abstract int noIntervals();

  /**
   * It returns required interval.
   *
   * @param position the position of the interval.
   * @return the interval, or null if the required interval does not exist.
   */
  public abstract FloatInterval getInterval(int position);

  /**
   * It updates the domain to contain the elements as specifed by the domain, which is shifted. E.g.
   * {1..4} + 3 = 4..7
   *
   * @param storeLevel level of the store at which the update occurs.
   * @param v variable for which this domain is used.
   * @param domain the domain according to which the domain is updated.
   * @param shift the shift which is used to shift the domain supplied as argument.
   */
  public abstract void inShift(int storeLevel, Var v, FloatDomain domain, double shift);

  /**
   * It returns the left most element of the given interval.
   *
   * @param intervalNo the interval number.
   * @return the left bound of the specified interval.
   */
  public double leftElement(int intervalNo) {
    return getInterval(intervalNo).min();
  }

  /**
   * It returns the right most element of the given interval.
   *
   * @param intervalNo the interval number.
   * @return the right bound of the specified interval.
   */
  public double rightElement(int intervalNo) {
    return getInterval(intervalNo).max();
  }

  /**
   * It returns the values which have been removed at current store level.
   *
   * @param currentStoreLevel the current store level.
   * @return emptyDomain if domain did not change at current level, or the set of values which have
   *     been removed at current level.
   */
  public abstract FloatDomain recentDomainPruning(int currentStoreLevel);

  /*
   * It returns the number of constraints
   *
   * @return the number of constraints attached to this domain.
   */

  /**
   * It returns domain at earlier level at which the change has occurred.
   *
   * @return previous domain
   */
  public abstract FloatDomain previousDomain();

  /**
   * It specifies if the other int domain is equal to this one.
   *
   * @param domain the domain which is compared to this domain.
   * @return true if both domains contain the same elements, false otherwise.
   */
  public boolean eq(FloatDomain domain) {

    if (this.getSize() != domain.getSize()) {
      return false;
    }

    // the same size.
    FloatIntervalEnumeration enumer = domain.floatIntervalEnumeration();
    while (enumer.hasMoreElements()) {
      FloatInterval next = enumer.nextElement();
      if (!contains(next.min(), next.max())) {
        return false;
      }
    }
    return true;
    /*
    }
    else {
        ValueEnumeration enumer = domain.valueEnumeration();
        while (enumer.hasMoreElements()) {
            int next = enumer.nextElement();
            if (!contains(next))
                return false;
        }
        return true;
    }
        */
  }

  /**
   * Creates a deep copy of this float domain.
   *
   * @return a new FloatDomain that is a copy of this domain.
   */
  public abstract FloatDomain copy();

  /**
   * Creates a lightweight copy of this float domain without full history.
   *
   * @return a new FloatDomain that is a lightweight copy of this domain.
   */
  public abstract FloatDomain cloneLight();

  /**
   * Returns the lexical ordering between the sets.
   *
   * @param domain the set that should be lexically compared to this set.
   * @return -1 if s is greater than this set, 0 if s is equal to this set and else it returns 1.
   */
  public int lex(FloatDomain domain) {

    ValueEnumeration thisEnumer = this.valueEnumeration();
    ValueEnumeration paramEnumer = domain.valueEnumeration();

    int i;
    int j;

    while (thisEnumer.hasMoreElements()) {

      i = thisEnumer.nextElement();

      if (paramEnumer.hasMoreElements()) {

        j = paramEnumer.nextElement();

        if (i < j) {
          return -1;
        } else if (j < i) {
          return 1;
        }
      } else {
        return 1;
      }
    }

    if (paramEnumer.hasMoreElements()) {
      return -1;
    }

    return 0;
  }

  /**
   * It computes an intersection with a given domain and stores it in this domain.
   *
   * @param intersect domain with which the intersection is being computed.
   * @return type of event which has occurred due to the operation.
   */
  public abstract int intersectAdapt(FloatDomain intersect);

  /**
   * It computes an intersection of this domain with an interval [min..max]. It adapts this domain
   * to the result of the intersection.
   *
   * @param min the minimum value of the interval used in the intersection computation.
   * @param max the maximum value of the interval used in the intersection computation.
   * @return it returns information about the pruning event which has occurred due to this
   *     operation.
   */
  public abstract int intersectAdapt(int min, int max);

  /**
   * It computes the size of the intersection between this domain and the domain supplied as a
   * parameter.
   *
   * @param domain the domain with which the intersection is computed.
   * @return the size of the intersection.
   */
  public int sizeOfIntersection(FloatDomain domain) {
    return intersect(domain).getSize();
  }

  /**
   * Creates a copy of the modelConstraints array with the specified pruning event array replaced.
   *
   * @param pruningEvent the pruning event index
   * @param newPruningEventConstraints the new constraint array for this pruning event
   * @return a new modelConstraints array
   */
  private Constraint[][] copyModelConstraintsArray(
      int pruningEvent, Constraint[] newPruningEventConstraints) {
    Constraint[][] newModelConstraints = new Constraint[3][];
    newModelConstraints[0] = modelConstraints[0];
    newModelConstraints[1] = modelConstraints[1];
    newModelConstraints[2] = modelConstraints[2];
    newModelConstraints[pruningEvent] = newPruningEventConstraints;
    return newModelConstraints;
  }

  /**
   * Creates a copy of the modelConstraintsToEvaluate array with the specified pruning event count
   * updated.
   *
   * @param pruningEvent the pruning event index
   * @param delta the change to apply to the count (positive for add, negative for remove)
   * @return a new modelConstraintsToEvaluate array
   */
  private int[] copyModelConstraintsToEvaluateArray(int pruningEvent, int delta) {
    int[] newModelConstraintsToEvaluate = new int[3];
    newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
    newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
    newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];
    newModelConstraintsToEvaluate[pruningEvent] = modelConstraintsToEvaluate[pruningEvent] + delta;
    return newModelConstraintsToEvaluate;
  }

  /**
   * Adds a constraint to the specified pruning event array.
   *
   * @param constraint the constraint to add
   * @param pruningEvent the pruning event index
   */
  private void addConstraintToPruningEvent(Constraint constraint, int pruningEvent) {
    Constraint[] pruningEventConstraints = modelConstraints[pruningEvent];

    if (pruningEventConstraints != null) {
      boolean alreadyImposed = false;

      if (modelConstraintsToEvaluate[pruningEvent] > 0) {
        for (int i = pruningEventConstraints.length - 1; i >= 0; i--) {
          if (pruningEventConstraints[i] == constraint) {
            alreadyImposed = true;
            break;
          }
        }
      }

      if (!alreadyImposed) {
        int pruningConstraintsToEvaluate = modelConstraintsToEvaluate[pruningEvent];
        Constraint[] newPruningEventConstraints = new Constraint[pruningConstraintsToEvaluate + 1];

        System.arraycopy(
            pruningEventConstraints,
            0,
            newPruningEventConstraints,
            0,
            pruningConstraintsToEvaluate);
        newPruningEventConstraints[pruningConstraintsToEvaluate] = constraint;

        modelConstraints = copyModelConstraintsArray(pruningEvent, newPruningEventConstraints);
        modelConstraintsToEvaluate = copyModelConstraintsToEvaluateArray(pruningEvent, 1);
      }
    } else {
      Constraint[] newPruningEventConstraints = new Constraint[1];
      newPruningEventConstraints[0] = constraint;

      modelConstraints = copyModelConstraintsArray(pruningEvent, newPruningEventConstraints);
      int[] newModelConstraintsToEvaluate = new int[3];
      newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
      newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
      newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];
      newModelConstraintsToEvaluate[pruningEvent] = 1;
      modelConstraintsToEvaluate = newModelConstraintsToEvaluate;
    }
  }

  /**
   * Clones this domain and installs the clone on the given variable, preserving constraints and
   * metadata.
   *
   * @param storeLevel the current store level
   * @param v the variable to install the cloned domain on
   * @return the cloned domain
   */
  private FloatDomain cloneAndInstall(int storeLevel, Var v) {
    FloatDomain result = this.cloneLight();
    result.modelConstraints = modelConstraints;
    result.searchConstraints = searchConstraints;
    result.stamp = storeLevel;
    result.prevDomain = this;
    result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
    result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
    ((FloatVar) v).domain = result;
    return result;
  }

  /**
   * It adds a constraint to a domain, it should only be called by putConstraint function of
   * Variable object. putConstraint function from Variable must make a copy of a vector of
   * constraints if vector was not cloned.
   */
  @Override
  public void putModelConstraint(int storeLevel, Var v, Constraint constraint, int pruningEvent) {

    if (stamp < storeLevel) {
      FloatDomain result = cloneAndInstall(storeLevel, v);
      result.putModelConstraint(storeLevel, v, constraint, pruningEvent);
      return;
    }

    addConstraintToPruningEvent(constraint, pruningEvent);
  }

  /**
   * Removes a constraint from the specified pruning event array.
   *
   * @param constraint the constraint to remove
   * @param pruningEvent the pruning event index
   * @return true if the constraint was found and removed, false otherwise
   */
  private boolean removeConstraintFromPruningEvent(Constraint constraint, int pruningEvent) {
    Constraint[] pruningEventConstraints = modelConstraints[pruningEvent];

    if (pruningEventConstraints != null) {
      boolean isImposed = false;
      int i;

      for (i = modelConstraintsToEvaluate[pruningEvent] - 1; i >= 0; i--) {
        if (pruningEventConstraints[i] == constraint) {
          isImposed = true;
          break;
        }
      }

      if (isImposed) {
        if (i != modelConstraintsToEvaluate[pruningEvent] - 1) {
          modelConstraints[pruningEvent][i] =
              modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1];
          modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1] = constraint;
        }

        modelConstraintsToEvaluate = copyModelConstraintsToEvaluateArray(pruningEvent, -1);
        return true;
      }
    }
    return false;
  }

  @Override
  public void removeModelConstraint(int storeLevel, Var v, Constraint constraint) {

    if (stamp < storeLevel) {
      FloatDomain result = cloneAndInstall(storeLevel, v);
      result.removeModelConstraint(storeLevel, v, constraint);
      return;
    }

    if (removeConstraintFromPruningEvent(constraint, GROUND)) {
      return;
    }
    if (removeConstraintFromPruningEvent(constraint, BOUND)) {
      return;
    }
    removeConstraintFromPruningEvent(constraint, ANY);
  }

  /**
   * It constructs and int array containing all elements in the domain. The array will have size
   * equal to the number of elements in the domain.
   *
   * @return the int array containing all elements in a domain.
   */
  public int[] toIntArray() {

    int[] result = new int[getSize()];

    ValueEnumeration enumer = this.valueEnumeration();
    int i = 0;

    while (enumer.hasMoreElements()) {
      result[i++] = enumer.nextElement();
    }

    return result;
  }

  /**
   * It returns the value to which this domain is grounded. It assumes that a domain is a singleton
   * domain.
   *
   * @return the only value remaining in the domain.
   */
  public double value() {

    if (ASSERTS_ENABLED && !singleton()) {
      throw new IllegalStateException(
          String.valueOf("function value() called when domain is not a singleton domain."));
    }

    return min();
  }

  /**
   * It normalizes an angle interval to the range [0, 2*PI).
   *
   * @param min the minimum angle value
   * @param max the maximum angle value
   * @return the normalized angle interval
   */
  public static FloatInterval normalizeAngle(double min, double max) {
    double normMin = down(min % (2 * PI));
    double maxmin = max - min;
    double normMax = up(normMin + maxmin);

    if (normMax >= 2 * PI) {
      normMin = down(normMin - 2 * PI);
      normMax = up(normMax - 2 * PI);
    }

    return new FloatInterval(normMin, normMax);
  }
}
