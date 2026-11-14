/*
 * Dist.java
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

package org.jacop.prob.dist;

import java.util.Arrays;
import java.util.TreeMap;
import org.jacop.prob.num.ProbArith;

/**
 * A discrete probability distribution over integers with exact probabilities: value {@code
 * values[k]} has probability {@code weights[k] / den}. The values are distinct and increasing, the
 * weights positive and summing to the denominator. It is immutable.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class Dist {

  private final int[] values;
  private final long[] weights;
  private final long den;

  /**
   * It constructs a distribution. Equal values are merged and values of weight 0 dropped.
   *
   * @param values the values
   * @param weights the probability numerators of the values, at least 0
   * @param den the denominator; the weights must sum to it
   */
  public Dist(int[] values, long[] weights, long den) {
    if (values == null || weights == null || values.length != weights.length) {
      throw new IllegalArgumentException("Dist needs values and weights of the same length");
    }
    ProbArith.checkProbabilities(weights, den, true);
    TreeMap<Integer, Long> merged = new TreeMap<>();
    for (int k = 0; k < values.length; k++) {
      if (weights[k] > 0) {
        merged.merge(values[k], weights[k], Math::addExact);
      }
    }
    this.values = merged.keySet().stream().mapToInt(Integer::intValue).toArray();
    this.weights = merged.values().stream().mapToLong(Long::longValue).toArray();
    this.den = den;
  }

  /**
   * Returns the distribution that takes one value with probability 1.
   *
   * @param value the value
   * @return the point distribution
   */
  public static Dist point(int value) {
    return new Dist(new int[] {value}, new long[] {1}, 1);
  }

  /**
   * Returns the uniform distribution over values.
   *
   * @param values the values, distinct
   * @return each value with probability 1 / values.length
   */
  public static Dist uniform(int... values) {
    long[] w = new long[values.length];
    Arrays.fill(w, 1);
    return new Dist(values, w, values.length);
  }

  /**
   * Returns the Bernoulli distribution over {0, 1}.
   *
   * @param num the numerator of the probability of 1
   * @param den the denominator
   * @return 1 with probability num / den, 0 otherwise
   */
  public static Dist bernoulli(long num, long den) {
    return new Dist(new int[] {0, 1}, new long[] {den - num, num}, den);
  }

  /**
   * Returns the number of values with a positive probability.
   *
   * @return the support size
   */
  public int size() {
    return values.length;
  }

  /**
   * Returns a value of the support, in increasing order.
   *
   * @param k the index, below {@link #size()}
   * @return the k-th smallest value
   */
  public int value(int k) {
    return values[k];
  }

  /**
   * Returns the probability numerator of a value of the support.
   *
   * @param k the index, below {@link #size()}
   * @return the numerator of the k-th smallest value's probability
   */
  public long weight(int k) {
    return weights[k];
  }

  /**
   * Returns the denominator.
   *
   * @return the denominator
   */
  public long den() {
    return den;
  }

  /**
   * Returns the smallest value of the support.
   *
   * @return the minimum
   */
  public int min() {
    return values[0];
  }

  /**
   * Returns the largest value of the support.
   *
   * @return the maximum
   */
  public int max() {
    return values[values.length - 1];
  }

  /**
   * Returns the numerator over {@link #den()} of the mean: the sum of value times weight, exact.
   *
   * @return den times the mean
   * @throws ArithmeticException when it does not fit in a long
   */
  public long meanNumerator() {
    long s = 0;
    for (int k = 0; k < values.length; k++) {
      s = Math.addExact(s, Math.multiplyExact(values[k], weights[k]));
    }
    return s;
  }

  /**
   * Returns the numerator over {@link #den()} of the probability of a value at most t.
   *
   * @param t the threshold
   * @return den times Pr(X &lt;= t)
   */
  public long cdfNumerator(long t) {
    long s = 0;
    for (int k = 0; k < values.length && values[k] <= t; k++) {
      s += weights[k];
    }
    return s;
  }

  /**
   * Returns the same distribution over a multiple of its denominator.
   *
   * @param newDen the new denominator, a positive multiple of {@link #den()}
   * @return the distribution with weights scaled to newDen
   */
  public Dist withDenominator(long newDen) {
    if (newDen <= 0 || newDen % den != 0) {
      throw new IllegalArgumentException(newDen + " is not a multiple of " + den);
    }
    long f = newDen / den;
    long[] w = new long[weights.length];
    for (int k = 0; k < w.length; k++) {
      w[k] = Math.multiplyExact(weights[k], f);
    }
    return new Dist(values, w, newDen);
  }

  /**
   * Returns the distribution of the sum of two independent variables, over the product of the
   * denominators.
   *
   * @param other the other distribution
   * @return the distribution of X + Y
   */
  public Dist plus(Dist other) {
    TreeMap<Integer, Long> sum = new TreeMap<>();
    for (int k = 0; k < values.length; k++) {
      for (int l = 0; l < other.values.length; l++) {
        sum.merge(
            Math.addExact(values[k], other.values[l]),
            Math.multiplyExact(weights[k], other.weights[l]),
            Math::addExact);
      }
    }
    return new Dist(
        sum.keySet().stream().mapToInt(Integer::intValue).toArray(),
        sum.values().stream().mapToLong(Long::longValue).toArray(),
        Math.multiplyExact(den, other.den));
  }

  @Override
  public boolean equals(Object o) {
    if (!(o instanceof Dist d)) {
      return false;
    }
    // equal as distributions: the same values and the same exact probabilities
    if (!Arrays.equals(values, d.values)) {
      return false;
    }
    for (int k = 0; k < values.length; k++) {
      if (ProbArith.compare(weights[k], den, d.weights[k], d.den) != 0) {
        return false;
      }
    }
    return true;
  }

  @Override
  public int hashCode() {
    return Arrays.hashCode(values);
  }

  @Override
  public String toString() {
    StringBuilder b = new StringBuilder("{");
    for (int k = 0; k < values.length; k++) {
      if (k > 0) {
        b.append(", ");
      }
      b.append(values[k]).append(": ").append(weights[k]).append('/').append(den);
    }
    return b.append('}').toString();
  }
}
