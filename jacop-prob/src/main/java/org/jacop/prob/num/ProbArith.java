/*
 * ProbArith.java
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

package org.jacop.prob.num;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;

/**
 * Exact arithmetic on probabilities given as numerators over a common denominator. A probability p
 * is the fraction num / den with 0 &lt;= num &lt;= den; all the constraints of the module work on
 * such numerators, so they compare probabilities exactly and never prune on a rounded value.
 *
 * <p>The operations on longs throw {@link ArithmeticException} on overflow instead of wrapping.
 * Comparisons of fractions with different denominators use {@link BigInteger}, so they are exact
 * for all long values. {@link #numerator(double, long, boolean)} turns a decimal probability into a
 * numerator rounded in a chosen direction, which is how a model given with doubles is made safe: a
 * bound that is rounded towards the side that keeps every solution never removes one.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class ProbArith {

  private ProbArith() {}

  /**
   * Returns the sum of numerators, checked for overflow.
   *
   * @param numerators the numerators
   * @return their sum
   * @throws ArithmeticException on overflow
   */
  public static long sum(long... numerators) {
    long s = 0;
    for (long n : numerators) {
      s = Math.addExact(s, n);
    }
    return s;
  }

  /**
   * Checks that numerators are probabilities over a denominator: each one at least 0 and their sum
   * at most the denominator, or exactly it when {@code complete} is true.
   *
   * @param numerators the numerators
   * @param den the denominator, positive
   * @param complete whether the numerators must sum to the denominator (a distribution)
   * @throws IllegalArgumentException when they are not
   */
  public static void checkProbabilities(long[] numerators, long den, boolean complete) {
    if (den <= 0) {
      throw new IllegalArgumentException("The denominator must be positive, got " + den);
    }
    long s = 0;
    for (long n : numerators) {
      if (n < 0) {
        throw new IllegalArgumentException("A probability numerator is negative: " + n);
      }
      s = Math.addExact(s, n);
    }
    if (complete ? s != den : s > den) {
      throw new IllegalArgumentException(
          "The probability numerators sum to " + s + (complete ? ", not to " : ", above ") + den);
    }
  }

  /**
   * Compares two fractions a / b and c / d exactly, for positive denominators.
   *
   * @param a the first numerator
   * @param b the first denominator, positive
   * @param c the second numerator
   * @param d the second denominator, positive
   * @return a negative number, zero or a positive number as a / b is below, equal to or above c / d
   */
  public static int compare(long a, long b, long c, long d) {
    if (b <= 0 || d <= 0) {
      throw new IllegalArgumentException("Denominators must be positive");
    }
    if (b == d) {
      return Long.compare(a, c);
    }
    return BigInteger.valueOf(a)
        .multiply(BigInteger.valueOf(d))
        .compareTo(BigInteger.valueOf(c).multiply(BigInteger.valueOf(b)));
  }

  /**
   * Returns the numerator over {@code den} of a probability given as a double, rounded down or up
   * to the next integer. The rounding is exact: the double is converted to its exact binary value
   * before rounding, so {@code numerator(p, den, false) / den <= p <= numerator(p, den, true) /
   * den} always holds.
   *
   * @param p the probability, from 0 to 1
   * @param den the denominator, positive
   * @param up whether to round up, else down
   * @return the numerator, from 0 to den
   */
  @SuppressWarnings("PMD.AvoidDecimalLiteralsInBigDecimalConstructor")
  public static long numerator(double p, long den, boolean up) {
    if (!(p >= 0 && p <= 1) || den <= 0) {
      throw new IllegalArgumentException("Expected a probability and a positive denominator");
    }
    // new BigDecimal(double) on purpose: the exact binary value, not its shortest decimal form
    BigDecimal exact = new BigDecimal(p).multiply(BigDecimal.valueOf(den));
    return exact.setScale(0, up ? RoundingMode.CEILING : RoundingMode.FLOOR).longValueExact();
  }

  /**
   * Returns the numerator over {@code to} of a fraction num / from, rounded down or up. It is used
   * to move probabilities between denominators without losing safety.
   *
   * @param num the numerator
   * @param from its denominator, positive
   * @param to the new denominator, positive
   * @param up whether to round up, else down
   * @return the new numerator
   * @throws ArithmeticException when the result does not fit in a long
   */
  public static long rescale(long num, long from, long to, boolean up) {
    if (from <= 0 || to <= 0) {
      throw new IllegalArgumentException("Denominators must be positive");
    }
    return roundedQuotient(BigInteger.valueOf(num).multiply(BigInteger.valueOf(to)), from, up);
  }

  /**
   * Returns the product of two probabilities over the same denominator as a numerator over that
   * denominator, rounded down or up: (a / den) * (b / den) = (a * b / den) / den.
   *
   * @param a the first numerator
   * @param b the second numerator
   * @param den the denominator, positive
   * @param up whether to round up, else down
   * @return the numerator of the product
   */
  public static long multiply(long a, long b, long den, boolean up) {
    if (den <= 0) {
      throw new IllegalArgumentException("The denominator must be positive");
    }
    return roundedQuotient(BigInteger.valueOf(a).multiply(BigInteger.valueOf(b)), den, up);
  }

  private static long roundedQuotient(BigInteger n, long den, boolean up) {
    BigInteger[] qr = n.divideAndRemainder(BigInteger.valueOf(den));
    BigInteger q = qr[0];
    if (qr[1].signum() != 0 && (qr[1].signum() > 0) == up) {
      q = q.add(BigInteger.valueOf(up ? 1 : -1));
    }
    return q.longValueExact();
  }

  /**
   * Returns the greatest common divisor of two longs, at least 0.
   *
   * @param a the first value
   * @param b the second value
   * @return gcd(|a|, |b|)
   */
  public static long gcd(long a, long b) {
    a = Math.abs(a);
    b = Math.abs(b);
    while (b != 0) {
      long t = a % b;
      a = b;
      b = t;
    }
    return a;
  }

  /**
   * Returns a double enclosure [lo, hi] of num / den: the two doubles next to the exact value, so a
   * report never claims more than the exact value gives.
   *
   * @param num the numerator
   * @param den the denominator, positive
   * @return {lo, hi} with lo &lt;= num / den &lt;= hi
   */
  @SuppressWarnings("PMD.AvoidDecimalLiteralsInBigDecimalConstructor")
  public static double[] enclosure(long num, long den) {
    if (den <= 0) {
      throw new IllegalArgumentException("The denominator must be positive");
    }
    double d = (double) num / den;
    // compare the exact value of d with num / den: d * den against num
    int c = new BigDecimal(d).multiply(BigDecimal.valueOf(den)).compareTo(BigDecimal.valueOf(num));
    double lo = c <= 0 ? d : Math.nextDown(d);
    double hi = c >= 0 ? d : Math.nextUp(d);
    return new double[] {lo, hi};
  }
}
