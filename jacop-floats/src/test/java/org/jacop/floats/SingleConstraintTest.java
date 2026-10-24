/*
 * SingleConstraintTest.java
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

package org.jacop.floats;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;
import static org.assertj.core.api.Assertions.offset;

import org.jacop.constraints.Not;
import org.jacop.constraints.Reified;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.floats.constraints.ElementFloat;
import org.jacop.floats.constraints.ElementFloatVariable;
import org.jacop.floats.constraints.EquationSystem;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.PdivCeqR;
import org.jacop.floats.constraints.PdivQeqR;
import org.jacop.floats.constraints.PeqC;
import org.jacop.floats.constraints.PeqQ;
import org.jacop.floats.constraints.PgtC;
import org.jacop.floats.constraints.PltC;
import org.jacop.floats.constraints.PlteqQ;
import org.jacop.floats.constraints.PmulCeqR;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.constraints.PplusCeqR;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.RoundPeqX;
import org.jacop.floats.constraints.SqrtPeqR;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatVar;
import org.junit.jupiter.api.Test;

/** Tests of single float constraints. */
class SingleConstraintTest {

  @Test
  void testComparisonsRejectNaNConstant() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 0, 1);

    // p < NaN pruned nothing and p = NaN gave p the domain NaN..NaN
    assertThatThrownBy(() -> new PltC(p, Double.NaN)).isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new PgtC(p, Double.NaN)).isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new PeqC(p, Double.NaN)).isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testComparisonWithInfiniteConstantStillAccepted() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 0, 1);
    store.impose(new PltC(p, Double.POSITIVE_INFINITY));

    assertThat(store.consistency()).isTrue();
    assertThat(p.min()).isEqualTo(0.0);
    assertThat(p.max()).isEqualTo(1.0);
  }

  @Test
  void testArithmeticRejectsNonFiniteConstant() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 0, 1);
    FloatVar r = new FloatVar(store, "r", 0, 10);

    // p * NaN = r gave r = 0
    assertThatThrownBy(() -> new PmulCeqR(p, Double.NaN, r))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new PmulCeqR(p, Double.POSITIVE_INFINITY, r))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new PplusCeqR(p, Double.NaN, r))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testDivisionByConstantZeroRejected() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 0, 1);
    FloatVar r = new FloatVar(store, "r", 0, 10);

    // p / 0 = r was decomposed as r * 0 = p, which accepts p = 0 with any r
    assertThatThrownBy(() -> new PdivCeqR(p, 0, r)).isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testDivisionByVariableZeroFails() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 0, 0);
    FloatVar q = new FloatVar(store, "q", 0, 0);
    FloatVar r = new FloatVar(store, "r", 0, 10);
    store.impose(new PdivQeqR(p, q, r));

    // 0 / 0 = r was accepted for any r
    assertThat(store.consistency()).isFalse();
  }

  @Test
  void testDivisionByVariable() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 6, 6);
    FloatVar q = new FloatVar(store, "q", 2, 3);
    FloatVar r = new FloatVar(store, "r", 0, 10);
    store.impose(new PdivQeqR(p, q, r));

    assertThat(store.consistency()).isTrue();
    assertThat(r.min()).isCloseTo(2.0, offset(1e-9));
    assertThat(r.max()).isCloseTo(3.0, offset(1e-9));
  }

  @Test
  void testLinearFloatRejectsBadArguments() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 0, 1);

    assertThatThrownBy(() -> new LinearFloat(new FloatVar[] {}, new double[] {}, "==", 0))
        .isInstanceOf(IllegalArgumentException.class);
    // an unknown relation was taken to be ==
    assertThatThrownBy(() -> new LinearFloat(new FloatVar[] {p}, new double[] {1}, "<>", 0))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () -> new LinearFloat(new FloatVar[] {p}, new double[] {Double.NaN}, "==", 0))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () -> new LinearFloat(new FloatVar[] {p}, new double[] {1}, "==", Double.NaN))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testElementFloatRejectsNaN() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 0, 1);
    IntVar index = new IntVar(store, "index", 1, 2);

    assertThatThrownBy(() -> new ElementFloat(index, new double[] {Double.NaN, 0.5}, p))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testEquationSystemRejectsNullVariables() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 0, 1);

    assertThatThrownBy(() -> new EquationSystem(store, new FloatVar[] {null}, new FloatVar[] {p}))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testRemovingTheLastPointOfADomainWakesBoundConstraints() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", points(0, 1, 2));
    FloatVar q = new FloatVar(store, "q", 0, 2);
    store.impose(new PlteqQ(q, p));
    assertThat(store.consistency()).isTrue();

    // removing 2 lowered max(p) but was announced as ANY, so q <= p was not woken
    store.setLevel(1);
    p.domain.inComplement(store.level, p, 2);
    assertThat(store.consistency()).isTrue();
    assertThat(q.max()).isEqualTo(1.0);

    // the same at the level where p's domain was already copied
    p.domain.inComplement(store.level, p, 1);
    assertThat(store.consistency()).isTrue();
    assertThat(q.max()).isEqualTo(0.0);
  }

  @Test
  void testRemovingAPointThatLeavesASingletonIsAGroundEvent() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", points(0, 1));
    FloatVar q = new FloatVar(store, "q", points(0, 1));
    store.impose(new Not(new PeqQ(p, q)));
    assertThat(store.consistency()).isTrue();

    // q = 0 removed 0 from p, which left p = 1 and threw "Wrong event generated"
    store.setLevel(1);
    q.domain.in(store.level, q, 0, 0);
    assertThat(store.consistency()).isTrue();
    assertThat(p.singleton(1)).isTrue();
  }

  @Test
  void testRoundOfAHalfIsAwayFromZero() {
    for (double half : new double[] {-1.5, -0.5, 0.5, 1.5}) {
      Store store = new Store();
      FloatVar p = new FloatVar(store, "p", half, half);
      IntVar x = new IntVar(store, "x", -3, 3);
      RoundPeqX round = new RoundPeqX(p, x);
      store.impose(round);

      // p = 0.5 has round(p) = 1 but p was restricted to (x - 0.5, x + 0.5), which fails
      assertThat(store.consistency()).as("round(%s)", half).isTrue();
      assertThat(x.value()).isEqualTo((int) Math.round(Math.abs(half)) * (int) Math.signum(half));
      assertThat(round.satisfied()).isTrue();
    }

    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 0, 1);
    IntVar x = new IntVar(store, "x", 1, 1);
    store.impose(new RoundPeqX(p, x));
    assertThat(store.consistency()).isTrue();
    assertThat(p.min()).isEqualTo(0.5);
  }

  @Test
  void testElementSatisfiedWithIndexOutsideTheList() {
    Store store = new Store();
    IntVar index = new IntVar(store, "index", 3, 3);
    FloatVar value = new FloatVar(store, "value", 0.5, 0.5);
    FloatVar a = new FloatVar(store, "a", 0.5, 0.5);
    FloatVar b = new FloatVar(store, "b", 0.5, 0.5);
    ElementFloat element = new ElementFloat(index, new double[] {0.5, 0.5}, value);
    ElementFloatVariable elementVariable =
        new ElementFloatVariable(index, new FloatVar[] {a, b}, value);
    store.impose(element);
    store.impose(elementVariable);

    // satisfied() before the first consistency read list[2]
    assertThat(element.satisfied()).isFalse();
    assertThat(elementVariable.satisfied()).isFalse();
    assertThat(store.consistency()).isFalse();
  }

  private static FloatIntervalDomain points(double... values) {
    FloatIntervalDomain domain = new FloatIntervalDomain();
    for (double v : values) {
      domain.unionAdapt(v, v);
    }
    return domain;
  }

  @Test
  void testAdditionNotSatisfiedWhenSumIsTooSmall() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 1, 1);
    FloatVar q = new FloatVar(store, "q", 1, 1);
    FloatVar r = new FloatVar(store, "r", 0, 0);
    IntVar b = new IntVar(store, "b", 0, 1);

    // satisfied() tested r - p - q < epsilon without abs, so 1 + 1 = 0 counted as satisfied
    PplusQeqR sum = new PplusQeqR(p, q, r);
    assertThat(sum.satisfied()).isFalse();
    PplusCeqR sumC = new PplusCeqR(p, 1, r);
    assertThat(sumC.satisfied()).isFalse();

    store.impose(new Reified(new PplusQeqR(p, q, r), b));
    assertThat(store.consistency()).isTrue();
    assertThat(b.value()).isZero();
  }

  @Test
  void testAdditionWithConstantReifiedWhenGround() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 1, 1);
    FloatVar r = new FloatVar(store, "r", 0, 0);
    IntVar b = new IntVar(store, "b", 0, 1);

    store.impose(new Reified(new PplusCeqR(p, 1, r), b));
    assertThat(store.consistency()).isTrue();
    assertThat(b.value()).isZero();
  }

  @Test
  void testMultiplicationWithProductSameAsFactor() {
    // p * q = p was propagated as q = 1, which loses p = 0 with any q
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 0, 0);
    FloatVar q = new FloatVar(store, "q", 2, 3);
    store.impose(new PmulQeqR(p, q, p));
    assertThat(store.consistency()).isTrue();
    assertThat(q.min()).isEqualTo(2.0);
    assertThat(q.max()).isEqualTo(3.0);

    store = new Store();
    FloatVar p2 = new FloatVar(store, "p", 2, 3);
    FloatVar q2 = new FloatVar(store, "q", 0, 0);
    store.impose(new PmulQeqR(p2, q2, q2));
    assertThat(store.consistency()).isTrue();

    // p * q = p with p not containing 0 forces q = 1, with q not containing 1 forces p = 0
    store = new Store();
    FloatVar p3 = new FloatVar(store, "p", 1, 2);
    FloatVar q3 = new FloatVar(store, "q", 0, 4);
    store.impose(new PmulQeqR(p3, q3, p3));
    assertThat(store.consistency()).isTrue();
    assertThat(q3.singleton(1.0)).isTrue();

    store = new Store();
    FloatVar p4 = new FloatVar(store, "p", -1, 2);
    FloatVar q4 = new FloatVar(store, "q", 2, 4);
    store.impose(new PmulQeqR(p4, q4, p4));
    assertThat(store.consistency()).isTrue();
    assertThat(p4.singleton(0.0)).isTrue();
  }

  @Test
  void testSquareRootOfItself() {
    // sqrt(x) = x has the solutions 0 and 1, but x = 0 failed
    for (double v : new double[] {0, 1}) {
      Store store = new Store();
      FloatVar x = new FloatVar(store, "x", v, v);
      store.impose(new SqrtPeqR(x, x));
      assertThat(store.consistency()).isTrue();
    }
    Store store = new Store();
    FloatVar x = new FloatVar(store, "x", 2, 2);
    store.impose(new SqrtPeqR(x, x));
    assertThat(store.consistency()).isFalse();
  }

  @Test
  void testDivisionByVariableWithZeroBound() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 0, 0);
    FloatVar q = new FloatVar(store, "q", 0, 1.5);
    FloatVar r = new FloatVar(store, "r", 2, 2);
    store.impose(new PdivQeqR(p, q, r));

    // R * Q = P accepted Q = 0, so 0 / q = 2 was consistent and search reported q = 0
    assertThat(store.consistency()).isFalse();

    store = new Store();
    p = new FloatVar(store, "p", 0, 0);
    q = new FloatVar(store, "q", -1, 0);
    r = new FloatVar(store, "r", -1, 2);
    store.impose(new PdivQeqR(p, q, r));
    assertThat(store.consistency()).isTrue();
    assertThat(q.max()).isLessThan(0.0);
    assertThat(r.singleton(0.0)).isTrue();
  }
}
