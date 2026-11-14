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
}
