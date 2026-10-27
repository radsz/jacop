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
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

import java.time.Duration;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.DoubleUnaryOperator;
import java.util.function.Function;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.Implies;
import org.jacop.constraints.Not;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.floats.constraints.AbsPeqR;
import org.jacop.floats.constraints.AcosPeqR;
import org.jacop.floats.constraints.AsinPeqR;
import org.jacop.floats.constraints.AtanPeqR;
import org.jacop.floats.constraints.CosPeqR;
import org.jacop.floats.constraints.ElementFloat;
import org.jacop.floats.constraints.ElementFloatVariable;
import org.jacop.floats.constraints.EquationSystem;
import org.jacop.floats.constraints.ExpPeqR;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.LnPeqR;
import org.jacop.floats.constraints.PdivCeqR;
import org.jacop.floats.constraints.PdivQeqR;
import org.jacop.floats.constraints.PeqC;
import org.jacop.floats.constraints.PeqQ;
import org.jacop.floats.constraints.PgtC;
import org.jacop.floats.constraints.PgtQ;
import org.jacop.floats.constraints.PgteqQ;
import org.jacop.floats.constraints.PltC;
import org.jacop.floats.constraints.PltQ;
import org.jacop.floats.constraints.PlteqQ;
import org.jacop.floats.constraints.PmulCeqR;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.constraints.PplusCeqR;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.RoundPeqX;
import org.jacop.floats.constraints.SinPeqR;
import org.jacop.floats.constraints.SqrtPeqR;
import org.jacop.floats.constraints.SumFloat;
import org.jacop.floats.constraints.TanPeqR;
import org.jacop.floats.core.FloatDomain;
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

  @Test
  void testLinearFloatDisequalityWhenGroundAfterImpose() {
    // variables ground after impose stay in the tree, whose outward rounded bounds never let
    // != fail on an exactly equal sum
    Store store = new Store();
    FloatVar x = new FloatVar(store, "x", -1.75, -0.5);
    FloatVar y = new FloatVar(store, "y", -1.5, -0.5);
    store.impose(new SumFloat(new FloatVar[] {x}, "!=", y));
    x.domain.in(store.level, x, -0.75, -0.75);
    y.domain.in(store.level, y, -0.75, -0.75);
    assertThat(store.consistency()).isFalse();

    store = new Store();
    FloatVar z = new FloatVar(store, "z", -1, 0.25);
    store.impose(new Not(new LinearFloat(new FloatVar[] {z}, new double[] {2}, "==", -0.5)));
    z.domain.in(store.level, z, -0.25, -0.25);
    assertThat(store.consistency()).isFalse();
  }

  @Test
  void testAbsAndSqrtNotSatisfiedByNegativeResult() {
    // |1| = -1 and sqrt(1) = -1 counted as satisfied: AbsPeqR compared -p with q, SqrtPeqR checked
    // only r * r = p
    Store store = new Store();
    FloatVar one = new FloatVar(store, "one", 1, 1);
    FloatVar minusOne = new FloatVar(store, "minusOne", -1, -1);
    assertThat(new AbsPeqR(one, minusOne).satisfied()).isFalse();
    assertThat(new AbsPeqR(minusOne, one).satisfied()).isTrue();
    assertThat(new SqrtPeqR(one, minusOne).satisfied()).isFalse();
    assertThat(new SqrtPeqR(one, one).satisfied()).isTrue();
  }

  @Test
  void testLinearFloatUnderImplies() {
    // Implies does not forward variable changes, so the tree of LinearFloat stayed at its initial
    // bounds and -x != 0.5 counted as satisfied with x = -0.5
    Store store = new Store();
    FloatVar x = new FloatVar(store, "x", -1, 1);
    IntVar b = new IntVar(store, "b", 0, 1);
    LinearFloat linear = new LinearFloat(new FloatVar[] {x}, new double[] {-1}, "!=", 0.5);
    store.impose(new Implies(b, linear));
    assertThat(store.consistency()).isTrue();

    store.setLevel(1);
    x.domain.in(store.level, x, -0.5, -0.5);
    assertThat(linear.satisfied()).isFalse();
    assertThat(linear.notSatisfied()).isTrue();
    assertThat(store.consistency()).isTrue();
    assertThat(b.max()).isZero();
  }

  @Test
  void testLinearFloatUnderIfThenAfterBacktracking() {
    // IfThen imposes its consequence at a search level, so LinearFloat must go back to its nested
    // mode, and resynchronise its tree, once that level is removed
    Store store = new Store();
    FloatVar x = new FloatVar(store, "x", -1, 0.75);
    IntVar b = new IntVar(store, "b", 0, 1);
    store.impose(
        new IfThen(
            new XeqC(b, 1), new LinearFloat(new FloatVar[] {x}, new double[] {1}, ">=", 0.25)));
    assertThat(store.consistency()).isTrue();

    int accepted = 0;
    for (double v : new double[] {-1, -0.75, -0.5, -0.25, 0, 0.5, 0.75}) {
      for (int bv = 0; bv <= 1; bv++) {
        store.setLevel(1);
        try {
          x.domain.in(store.level, x, v, v);
          if (store.consistency()) {
            store.setLevel(2);
            b.domain.in(store.level, b, bv, bv);
            if (store.consistency()) {
              accepted++;
            }
            store.removeLevel(2);
          }
        } catch (FailException e) {
          // not accepted
        }
        store.removeLevel(2);
        store.removeLevel(1);
        store.setLevel(0);
      }
    }
    // b = 0 for every x, and b = 1 for x = 0.5 and x = 0.75
    assertThat(accepted).isEqualTo(9);
  }

  @Test
  void testExpSatisfiedChecksBothSides() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 0, 0);
    FloatVar q = new FloatVar(store, "q", 5, 5);
    FloatVar r = new FloatVar(store, "r", 0.5, 0.5);
    FloatVar one = new FloatVar(store, "one", 1, 1);

    // exp(0) = 1, but satisfied() only checked exp(p) - q <= precision and accepted any q >= 1
    assertThat(new ExpPeqR(p, q).satisfied()).isFalse();
    assertThat(new ExpPeqR(p, r).satisfied()).isFalse();
    assertThat(new ExpPeqR(p, one).satisfied()).isTrue();
  }

  @Test
  void testInverseTrigonometricResultsStayOnPrincipalBranch() {
    checkInverse(AsinPeqR::new, Math::asin, new double[] {-1, -0.5, 0, 0.25, 0.5, 1});
    checkInverse(AcosPeqR::new, Math::acos, new double[] {-1, -0.5, 0, 0.25, 0.5, 1});
    checkInverse(AtanPeqR::new, Math::atan, new double[] {-1e6, -2, -0.5, 0, 0.25, 1, 3});

    // other branches of sin(r) = p, cos(r) = p and tan(r) = p were accepted
    assertThat(groundInverse(AsinPeqR::new, 0.5, 5 * FloatDomain.PI / 6)).isFalse();
    assertThat(groundInverse(AcosPeqR::new, 0.5, -FloatDomain.PI / 3)).isFalse();
    assertThat(groundInverse(AtanPeqR::new, 1, 5 * FloatDomain.PI / 4)).isFalse();
    assertThat(groundInverse(AsinPeqR::new, 0.5, FloatDomain.PI / 6)).isTrue();
    assertThat(groundInverse(AcosPeqR::new, 0.5, FloatDomain.PI / 3)).isTrue();
    assertThat(groundInverse(AtanPeqR::new, 1, FloatDomain.PI / 4)).isTrue();
    // ground pairs (x, f(x)) that the forward function maps back only approximately
    for (double x : new double[] {-0.9999, 0.3, 0.9999}) {
      assertThat(groundInverse(AsinPeqR::new, x, Math.asin(x))).as("asin %s", x).isTrue();
      assertThat(groundInverse(AcosPeqR::new, x, Math.acos(x))).as("acos %s", x).isTrue();
    }
    for (double x : new double[] {-61315.44894204959, 41.553635841197824, 9939.357064796095}) {
      assertThat(groundInverse(AtanPeqR::new, x, Math.atan(x))).as("atan %s", x).isTrue();
    }
  }

  @Test
  void testAtanToStringKeepsArgumentOrder() {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", 0, 1);
    FloatVar r = new FloatVar(store, "r", 0, 1);

    // printed AtanPeqR(r, p), unlike AsinPeqR and AcosPeqR
    assertThat(new AtanPeqR(p, r).toString()).contains("AtanPeqR(p");
    assertThat(new AsinPeqR(p, r).toString()).contains("AsinPeqR(p");
  }

  @Test
  void testTrigonometricFunctionsKeepTheirValueFarFromZero() {
    double[] points = {10, 100, 1e5, -1e5, 1e10, -1e10, 1e15, 1e20, 1e100};
    checkTrigonometric(SinPeqR::new, Math::sin, points);
    checkTrigonometric(CosPeqR::new, Math::cos, points);
    checkTrigonometric(TanPeqR::new, Math::tan, points);
  }

  /**
   * Ground p, or give it a small interval around a point, and check that r keeps f of the samples.
   * Reducing p by multiples of 2 * PI in doubles moved r off f(p): sin(100) was pruned to a value
   * 3e-15 away from Math.sin(100), sin(1e10) 3e-7 away and sin(1e100) to an unrelated value.
   */
  private static void checkTrigonometric(
      BiFunction<FloatVar, FloatVar, Constraint> build, DoubleUnaryOperator f, double[] points) {
    for (double x : points) {
      for (double width : new double[] {0, Math.ulp(x) * 8, 0.25}) {
        Store store = new Store();
        FloatVar p = new FloatVar(store, "p", x, x + width);
        FloatVar r = new FloatVar(store, "r", -1e150, 1e150);
        Constraint c = build.apply(p, r);
        store.impose(c);

        assertThat(store.consistency()).as("%s", c).isTrue();
        for (int i = 0; i <= 4; i++) {
          double value = f.applyAsDouble(width == 0 ? x : x + width * i / 4);
          assertThat(r.min()).as("%s, sample %s", c, i).isLessThanOrEqualTo(value);
          assertThat(r.max()).as("%s, sample %s", c, i).isGreaterThanOrEqualTo(value);
        }
        if (width == 0) {
          assertThat(r.max() - r.min()).as("%s", c).isLessThan(1e-12 * (1 + Math.abs(r.min())));
        }
      }
    }
  }

  @Test
  void testExpAndLnAcceptGroundPairs() {
    // exp(x) rounded to a double maps back to x only approximately: both directions pruned with
    // outward rounding and failed although the pair agrees within the float precision
    for (double x : new double[] {-3, 0.021939883301229743, 0.5, 11.197850576036105}) {
      assertThat(groundInverse(ExpPeqR::new, x, Math.exp(x))).as("exp %s", x).isTrue();
    }
    for (double x : new double[] {0.0069290397440928755, 2, 72973.42232045328}) {
      assertThat(groundInverse(LnPeqR::new, x, Math.log(x))).as("ln %s", x).isTrue();
    }
    assertThat(groundInverse(ExpPeqR::new, 0.5, Math.exp(0.5) + 1e-6)).isFalse();
    assertThat(groundInverse(LnPeqR::new, 2, Math.log(2) - 1e-6)).isFalse();
    // ln(0) = -infinity passed the precision test
    assertThat(groundInverse(ExpPeqR::new, 1, 0)).isFalse();
    assertThat(groundInverse(LnPeqR::new, 0, 0.25)).isFalse();
  }

  @Test
  void testTrigonometricWithTheSameVariableOnBothSides() {
    // sin(x) = x shrank the bounds of x towards 0 by about x^3 per pass and looped for hours
    for (BiFunction<FloatVar, FloatVar, Constraint> f :
        List.<BiFunction<FloatVar, FloatVar, Constraint>>of(
            SinPeqR::new, AsinPeqR::new, AtanPeqR::new)) {
      Store store = new Store();
      FloatVar x = new FloatVar(store, "x", -1, 1);
      Constraint c = f.apply(x, x);
      store.impose(c);
      assertTimeoutPreemptively(Duration.ofSeconds(10), () -> store.consistency(), c::toString);
      assertThat(x.min()).as("%s", c).isLessThanOrEqualTo(0);
      assertThat(x.max()).as("%s", c).isGreaterThanOrEqualTo(0);
    }
  }

  @Test
  void testRelationsOfAVariableWithItselfAcceptNoWrongPoint() {
    // one pass of x < x on {-0.5, 0, 0.5} left x = 0 and was not run again, so grounding x to 0
    // changed nothing and the point was accepted; sin(x) = x now stops after one pass, and must
    // still reject the point x = -0.5 that pass leaves
    double[] three = {-0.5, 0, 0.5};
    checkNoPointAccepted(x -> new PltQ(x, x), three);
    checkNoPointAccepted(x -> new PgtQ(x, x), three);
    checkNoPointAccepted(x -> new Not(new PlteqQ(x, x)), three);
    checkNoPointAccepted(x -> new Not(new PgteqQ(x, x)), three);
    checkNoPointAccepted(x -> new SinPeqR(x, x), new double[] {-1.25, -0.75, -0.5, 1.25, 1.5});
    checkNoPointAccepted(x -> new AsinPeqR(x, x), new double[] {-1.5, -1, -0.5, 0.25, 1.5});
    checkNoPointAccepted(x -> new AtanPeqR(x, x), new double[] {-1.75, -1.5, -1, -0.5, 1.75});
  }

  private static void checkNoPointAccepted(Function<FloatVar, Constraint> f, double[] points) {
    for (double v : points) {
      Store store = new Store();
      FloatIntervalDomain d = new FloatIntervalDomain();
      for (double w : points) {
        d.unionAdapt(w, w);
      }
      FloatVar x = new FloatVar(store, "x", d);
      Constraint c = f.apply(x);
      store.impose(c);
      boolean accepted = store.consistency();
      if (accepted) {
        store.setLevel(1);
        try {
          x.domain.in(1, x, v, v);
          accepted = store.consistency();
        } catch (FailException e) {
          accepted = false;
        }
      }
      assertThat(accepted).as("%s at %s", c, v).isFalse();
    }
  }

  @Test
  void testEquationSystemRejectsAFunctionDefinedTwice() {
    // f = x - y and f = x * y define f twice; Derivative ended the whole JVM with System.exit(0)
    Store store = new Store();
    FloatVar x = new FloatVar(store, "x", -1, 1);
    FloatVar y = new FloatVar(store, "y", -1, 1);
    FloatVar f = new FloatVar(store, "f", -1, 1);
    store.impose(new LinearFloat(new FloatVar[] {x, y, f}, new double[] {1, -1, -1}, "==", 0));
    store.impose(new PmulQeqR(x, y, f));
    assertThatThrownBy(
            () -> new EquationSystem(store, new FloatVar[] {f, f}, new FloatVar[] {x, y}))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testEquationSystemRejectsNonSquareSystem() {
    Store store = new Store();
    FloatVar x0 = new FloatVar(store, "x0", -1, 1);
    FloatVar x1 = new FloatVar(store, "x1", -1, 1);
    FloatVar f = new FloatVar(store, "f", 0, 0);
    store.impose(new PmulQeqR(x0, x1, f));

    // one equation in two variables threw ArrayIndexOutOfBoundsException in impose
    assertThatThrownBy(() -> new EquationSystem(store, new FloatVar[] {f}, new FloatVar[] {x0, x1}))
        .isInstanceOf(IllegalArgumentException.class);
  }

  /** Ground p and check that r = f(p) is pruned to f(p) within the float precision. */
  private static void checkInverse(
      BiFunction<FloatVar, FloatVar, Constraint> build, DoubleUnaryOperator f, double[] points) {
    for (double x : points) {
      Store store = new Store();
      FloatVar p = new FloatVar(store, "p", x, x);
      FloatVar r = new FloatVar(store, "r", -10, 10);
      store.impose(build.apply(p, r));

      assertThat(store.consistency()).as("%s at %s", build.apply(p, r), x).isTrue();
      assertThat(r.min()).as("r min at %s", x).isCloseTo(f.applyAsDouble(x), offset(1e-9));
      assertThat(r.max()).as("r max at %s", x).isCloseTo(f.applyAsDouble(x), offset(1e-9));
    }
  }

  private static boolean groundInverse(
      BiFunction<FloatVar, FloatVar, Constraint> build, double x, double y) {
    Store store = new Store();
    FloatVar p = new FloatVar(store, "p", x, x);
    FloatVar r = new FloatVar(store, "r", y, y);
    try {
      store.impose(build.apply(p, r));
      return store.consistency();
    } catch (FailException e) {
      return false;
    }
  }
}
