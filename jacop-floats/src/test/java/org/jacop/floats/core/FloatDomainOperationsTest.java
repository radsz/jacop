/*
 * FloatDomainOperationsTest.java
 * <p>
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

package org.jacop.floats.core;

import static org.assertj.core.api.Assertions.assertThat;

import java.math.BigDecimal;
import java.math.MathContext;
import java.math.RoundingMode;
import java.util.Random;
import org.jacop.core.IntDomain;
import org.junit.jupiter.api.Test;

/**
 * Checks operations of FloatIntervalDomain that take another domain against the membership of
 * single values. Every value is a double, so a value belongs to a minus b exactly when it belongs
 * to a and not to b.
 */
class FloatDomainOperationsTest {

  private static final int TRIALS = 3000;

  private static final MathContext DIGITS = new MathContext(800, RoundingMode.HALF_EVEN);

  @Test
  void subtractDomainKeepsOnlyValuesOutsideTheSubtrahend() {
    FloatIntervalDomain a = new FloatIntervalDomain(-5.5, 9.5);
    FloatIntervalDomain b = new FloatIntervalDomain(-8.0, 5.5);
    FloatDomain result = a.subtract(b);
    assertThat(result.min()).isEqualTo(FloatDomain.next(5.5));
    assertThat(result.max()).isEqualTo(9.5);
    assertThat(result.noIntervals()).isEqualTo(1);

    assertThat(new FloatIntervalDomain(-4.0, 8.0).subtract(new FloatIntervalDomain(-7.5, 9.5)))
        .matches(FloatDomain::isEmpty, "empty");
  }

  @Test
  void intersectAdaptOfDisjointDomainsEmptiesTheDomain() {
    FloatIntervalDomain a = new FloatIntervalDomain(-10.0, -6.0);
    int event = a.intersectAdapt(new FloatIntervalDomain(-3.5, 9.0));
    assertThat(a.isEmpty()).isTrue();
    assertThat(event).isEqualTo(IntDomain.GROUND);
  }

  @Test
  void domainOperationsMatchValueMembership() {
    Random random = new Random(20261027);
    for (int trial = 0; trial < TRIALS; trial++) {
      FloatIntervalDomain a = randomDomain(random);
      FloatIntervalDomain b = randomDomain(random);
      String context = "a=" + a + " b=" + b;

      FloatDomain difference = a.subtract(b);
      FloatIntervalDomain intersection = (FloatIntervalDomain) a.cloneLight();
      intersection.intersectAdapt(b);
      FloatDomain intersect = a.intersect(b);
      FloatDomain union = a.union(b);

      assertThat(((FloatIntervalDomain) difference).checkInvariants())
          .as("subtract invariants " + context)
          .isNull();
      assertThat(intersection.checkInvariants())
          .as("intersectAdapt invariants " + context)
          .isNull();

      for (double value : probes()) {
        boolean inA = a.contains(value);
        boolean inB = b.contains(value);
        String at = context + " value=" + value;
        assertThat(difference.contains(value))
            .as("subtract(dom) " + at + " result=" + difference)
            .isEqualTo(inA && !inB);
        assertThat(intersection.contains(value))
            .as("intersectAdapt(dom) " + at + " result=" + intersection)
            .isEqualTo(inA && inB);
        assertThat(intersect.contains(value))
            .as("intersect(dom) " + at + " result=" + intersect)
            .isEqualTo(inA && inB);
        assertThat(union.contains(value))
            .as("union(dom) " + at + " result=" + union)
            .isEqualTo(inA || inB);
      }
    }
  }

  /**
   * addDown/addUp, mulDown/mulUp, divDown/divUp and sqrtDown/sqrtUp enclose the exact result
   * (BigDecimal) and are that result itself when it is a double: -2.0 + 2.0 was [-4.9e-324,
   * 4.9e-324] with plain outward rounding, so floor(x + y) of x = -2, y = 2 also admitted -1.
   */
  @Test
  void directedRoundingEnclosesTheExactResultAndKeepsExactOnes() {
    Random random = new Random(20261114);
    MathContext exact = MathContext.UNLIMITED;
    for (int trial = 0; trial < 20 * TRIALS; trial++) {
      double a = randomOperand(random);
      double b = randomOperand(random);
      String at = "a=" + a + " b=" + b;
      BigDecimal x = new BigDecimal(a);
      BigDecimal y = new BigDecimal(b);

      // the error of a product, quotient or root is exact away from the underflow range only
      boolean normal = normal(a) && normal(b);
      assertEncloses(x.add(y, exact), FloatDomain.addDown(a, b), FloatDomain.addUp(a, b), true, at);
      assertEncloses(
          x.multiply(y, exact), FloatDomain.mulDown(a, b), FloatDomain.mulUp(a, b), normal, at);
      if (b != 0) {
        // a double has at most 767 significant digits, so 800 keep a quotient that is a double
        // exact and put one that is not on the right side of every double
        BigDecimal q = x.divide(y, DIGITS);
        assertEncloses(q, FloatDomain.divDown(a, b), FloatDomain.divUp(a, b), normal, at);
      }
      double m = Math.abs(a);
      BigDecimal root = new BigDecimal(m).sqrt(DIGITS);
      assertEncloses(root, FloatDomain.sqrtDown(m), FloatDomain.sqrtUp(m), normal(m), "sqrt " + at);
    }
    assertThat(FloatDomain.addDown(-2.0, 2.0)).isZero();
    assertThat(FloatDomain.addUp(-2.0, 2.0)).isZero();
    assertThat(FloatDomain.mulDown(1.5, 4.0)).isEqualTo(6.0);
    assertThat(FloatDomain.divUp(1.0, 4.0)).isEqualTo(0.25);
    assertThat(FloatDomain.sqrtDown(9.0)).isEqualTo(3.0);
    assertThat(FloatDomain.mulUp(0.1, 3.0)).isEqualTo(Math.nextUp(FloatDomain.mulDown(0.1, 3.0)));
  }

  private static boolean normal(double v) {
    return v == 0 || Math.abs(v) > 1e-280;
  }

  private static void assertEncloses(
      BigDecimal value, double lo, double hi, boolean tight, String at) {
    if (Double.isInfinite(lo) || Double.isInfinite(hi)) {
      // an overflowing result: the infinite side encloses it, the finite side is MAX_VALUE
      assertThat(Double.isNaN(lo) || Double.isNaN(hi)).as("NaN bound " + at).isFalse();
      return;
    }
    assertThat(new BigDecimal(lo).compareTo(value))
        .as("lower bound " + lo + " " + at)
        .isLessThanOrEqualTo(0);
    assertThat(new BigDecimal(hi).compareTo(value))
        .as("upper bound " + hi + " " + at)
        .isGreaterThanOrEqualTo(0);
    if (!tight || Math.abs(lo) <= 1e-280 || Math.abs(hi) >= 1e300) {
      // near underflow and overflow the bounds may step out by one more ulp
      return;
    }
    boolean isDouble = new BigDecimal(value.doubleValue()).compareTo(value) == 0;
    if (isDouble) {
      assertThat(lo).as("exact lower bound " + at).isEqualTo(value.doubleValue());
      assertThat(hi).as("exact upper bound " + at).isEqualTo(value.doubleValue());
    } else {
      assertThat(Math.nextUp(lo)).as("tight bounds " + at).isEqualTo(hi);
    }
  }

  /** Small integers, quarters, random doubles over many magnitudes, and a few special values. */
  private static double randomOperand(Random random) {
    return switch (random.nextInt(5)) {
      case 0 -> random.nextInt(41) - 20;
      case 1 -> (random.nextInt(161) - 80) / 4.0;
      case 2 -> (random.nextDouble() - 0.5) * Math.pow(10, random.nextInt(41) - 20);
      case 3 -> new double[] {0.0, -0.0, 0.1, 1.0 / 3, Math.PI, 1e300, -1e-300}[random.nextInt(7)];
      default -> random.nextGaussian();
    };
  }

  /** Grid points with their neighbouring doubles, where interval ends of the domains lie. */
  private static double[] probes() {
    double[] probes = new double[3 * 41];
    int i = 0;
    for (int k = -20; k <= 20; k++) {
      double point = k * 0.5;
      probes[i++] = FloatDomain.previous(point);
      probes[i++] = point;
      probes[i++] = FloatDomain.next(point);
    }
    return probes;
  }

  private static double randomValue(Random random) {
    double point = (random.nextInt(33) - 16) * 0.5;
    return switch (random.nextInt(4)) {
      case 0 -> FloatDomain.next(point);
      case 1 -> FloatDomain.previous(point);
      default -> point;
    };
  }

  private static FloatIntervalDomain randomDomain(Random random) {
    FloatIntervalDomain domain = new FloatIntervalDomain();
    int intervals = 1 + random.nextInt(4);
    for (int i = 0; i < intervals; i++) {
      double first = randomValue(random);
      double second = random.nextInt(5) == 0 ? first : randomValue(random);
      domain.unionAdapt(Math.min(first, second), Math.max(first, second));
    }
    return domain;
  }

  @Test
  void intersectAdaptOfAnEmptyFloatDomainLeavesItEmpty() {
    // the first interval of an empty domain was read (ArrayIndexOutOfBoundsException)
    for (FloatIntervalDomain empty :
        new FloatIntervalDomain[] {new FloatIntervalDomain(), FloatIntervalDomain.emptyDomain}) {
      assertThat(empty.intersectAdapt(1, 2)).isEqualTo(FloatDomain.NONE);
      assertThat(empty.isEmpty()).isTrue();
    }
  }
}
