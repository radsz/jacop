/*
 * DomainInMethodsTest.java
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

package org.jacop;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;
import static org.mockito.Mockito.clearInvocations;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;

import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collection;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.SmallDenseDomain;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

/**
 * Comprehensive tests for IntDomain in* methods (in, inMin, inMax, inValue, inComplement, inShift)
 * covering both IntervalDomain and SmallDenseDomain implementations.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@ExtendWith(MockitoExtension.class)
class DomainInMethodsTest {

  private @Mock IntVar v;
  private Method prepareMethod;

  static Collection<String> parametricTest() {
    return Arrays.asList("prepareSmallDenseDomain", "prepareIntervalDomain");
  }

  private void setupPrepareMethod(String name) throws NoSuchMethodException {
    prepareMethod = this.getClass().getMethod(name, int[].class);
  }

  private IntDomain dom(int... intervals) throws Exception {
    return (IntDomain) prepareMethod.invoke(this, new Object[] {intervals});
  }

  private void verifyEvent(int event) {
    verify(v).domainHasChanged(event);
    clearInvocations(v);
  }

  private void verifyNoEvent() {
    verify(v, never()).domainHasChanged(IntDomain.ANY);
    verify(v, never()).domainHasChanged(IntDomain.BOUND);
    verify(v, never()).domainHasChanged(IntDomain.GROUND);
    clearInvocations(v);
  }

  /**
   * Prepares a SmallDenseDomain from pairs of min/max values.
   *
   * @param intervalList pairs of min/max for each interval.
   * @return prepared SmallDenseDomain.
   */
  public IntDomain prepareSmallDenseDomain(int[] intervalList) {
    if (intervalList.length % 2 != 0 || intervalList.length < 2) {
      throw new IllegalArgumentException("Need even number of elements >= 2");
    }
    IntDomain d = new SmallDenseDomain(intervalList[0], intervalList[1]);
    for (int i = 2; i < intervalList.length; i += 2) {
      d.addDom(new SmallDenseDomain(intervalList[i], intervalList[i + 1]));
    }
    return d;
  }

  /**
   * Prepares an IntervalDomain from pairs of min/max values.
   *
   * @param intervalList pairs of min/max for each interval.
   * @return prepared IntervalDomain.
   */
  public IntDomain prepareIntervalDomain(int[] intervalList) {
    if (intervalList.length % 2 != 0 || intervalList.length < 2) {
      throw new IllegalArgumentException("Need even number of elements >= 2");
    }
    IntDomain d = new IntervalDomain(intervalList[0], intervalList[1]);
    for (int i = 2; i < intervalList.length; i += 2) {
      d.addDom(new IntervalDomain(intervalList[i], intervalList[i + 1]));
    }
    return d;
  }

  private IntDomain intervalDom(int... intervals) {
    IntDomain d = new IntervalDomain(intervals[0], intervals[1]);
    for (int i = 2; i < intervals.length; i += 2) {
      d.addDom(new IntervalDomain(intervals[i], intervals[i + 1]));
    }
    return d;
  }

  private IntDomain sddDom(int... intervals) {
    IntDomain d = new SmallDenseDomain(intervals[0], intervals[1]);
    for (int i = 2; i < intervals.length; i += 2) {
      d.addDom(new SmallDenseDomain(intervals[i], intervals[i + 1]));
    }
    return d;
  }

  // =========================================================================
  // 1. in(storeLevel, Var, int min, int max)
  // =========================================================================

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testIn_oneInterval(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    // clip both sides
    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, 5, 15);
    assertThat(d).hasToString("{5..15}");
    verifyEvent(IntDomain.BOUND);

    // clip max only
    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, 1, 15);
    assertThat(d).hasToString("{1..15}");
    verifyEvent(IntDomain.BOUND);

    // clip min only
    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, 5, 20);
    assertThat(d).hasToString("{5..20}");
    verifyEvent(IntDomain.BOUND);

    // no change (exact match)
    d = dom(1, 20);
    d.in(100, v, 1, 20);
    verifyNoEvent();

    // no change (superset)
    d = dom(1, 20);
    d.in(100, v, -5, 25);
    verifyNoEvent();

    // reduce to singleton in middle
    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, 5, 5);
    assertThat(d).hasToString("5");
    verifyEvent(IntDomain.GROUND);

    // reduce to singleton at min
    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, 1, 1);
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    // reduce to singleton at max
    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, 20, 20);
    assertThat(d).hasToString("20");
    verifyEvent(IntDomain.GROUND);

    // singleton domain, no change
    d = dom(5, 5);
    d.in(100, v, 5, 5);
    verifyNoEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testIn_twoIntervals(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, 3, 12);
    assertThat(d).hasToString("{3..5, 10..12}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.in(100, v, 1, 15);
    verifyNoEvent();

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, 3, 15);
    assertThat(d).hasToString("{3..5, 10..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, 1, 12);
    assertThat(d).hasToString("{1..5, 10..12}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, 1, 7);
    assertThat(d).hasToString("{1..5}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, 8, 15);
    assertThat(d).hasToString("{10..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, 10, 10);
    assertThat(d).hasToString("10");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, 5, 10);
    assertThat(d).hasToString("{5, 10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 3, 5, 10);
    d.setStamp(100);
    d.in(100, v, 4, 8);
    assertThat(d).hasToString("{5..8}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 3, 5, 10);
    d.setStamp(100);
    d.in(100, v, 3, 5);
    assertThat(d).hasToString("{3, 5}");
    verifyEvent(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testIn_threeIntervals(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, 3, 17);
    assertThat(d).hasToString("{3..5, 8..12, 15..17}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, 8, 12);
    assertThat(d).hasToString("{8..12}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, 9, 11);
    assertThat(d).hasToString("{9..11}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, 10, 10);
    assertThat(d).hasToString("10");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.in(100, v, 1, 20);
    verifyNoEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testIn_fails(String name) throws Exception {
    setupPrepareMethod(name);

    assertThatThrownBy(() -> dom(1, 5).in(100, v, 10, 20)).isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(5, 10).in(100, v, 1, 3)).isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 5, 10, 15).in(100, v, 6, 9)).isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 5, 10, 15).in(100, v, 7, 7)).isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 3, 7, 9, 13, 15).in(100, v, 4, 6))
        .isInstanceOf(FailException.class);
  }

  // =========================================================================
  // 2. inMin(storeLevel, Var, int min)
  // =========================================================================

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInMin_oneInterval(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 10);
    d.setStamp(100);
    d.inMin(100, v, 5);
    assertThat(d).hasToString("{5..10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 10);
    d.inMin(100, v, 1);
    verifyNoEvent();

    d = dom(1, 10);
    d.inMin(100, v, -5);
    verifyNoEvent();

    d = dom(1, 10);
    d.setStamp(100);
    d.inMin(100, v, 10);
    assertThat(d).hasToString("10");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 2);
    d.setStamp(100);
    d.inMin(100, v, 2);
    assertThat(d).hasToString("2");
    verifyEvent(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInMin_twoIntervals(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inMin(100, v, 3);
    assertThat(d).hasToString("{3..5, 10..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inMin(100, v, 5);
    assertThat(d).hasToString("{5, 10..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.inMin(100, v, 1);
    verifyNoEvent();

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inMin(100, v, 7);
    assertThat(d).hasToString("{10..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inMin(100, v, 10);
    assertThat(d).hasToString("{10..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inMin(100, v, 12);
    assertThat(d).hasToString("{12..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inMin(100, v, 15);
    assertThat(d).hasToString("15");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 3, 5, 10);
    d.setStamp(100);
    d.inMin(100, v, 4);
    assertThat(d).hasToString("{5..10}");
    verifyEvent(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInMin_threeIntervals(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 3, 7, 9, 13, 15);
    d.setStamp(100);
    d.inMin(100, v, 5);
    assertThat(d).hasToString("{7..9, 13..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 3, 7, 9, 13, 15);
    d.setStamp(100);
    d.inMin(100, v, 8);
    assertThat(d).hasToString("{8..9, 13..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 3, 7, 9, 13, 15);
    d.setStamp(100);
    d.inMin(100, v, 10);
    assertThat(d).hasToString("{13..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 3, 7, 9, 15, 15);
    d.setStamp(100);
    d.inMin(100, v, 15);
    assertThat(d).hasToString("15");
    verifyEvent(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInMin_fails(String name) throws Exception {
    setupPrepareMethod(name);

    assertThatThrownBy(() -> dom(1, 5).inMin(100, v, 10)).isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 3, 5, 7).inMin(100, v, 20)).isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 5, 10, 15).inMin(100, v, 16)).isInstanceOf(FailException.class);
  }

  // =========================================================================
  // 3. inMax(storeLevel, Var, int max)
  // =========================================================================

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInMax_oneInterval(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 10);
    d.setStamp(100);
    d.inMax(100, v, 5);
    assertThat(d).hasToString("{1..5}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 10);
    d.inMax(100, v, 10);
    verifyNoEvent();

    d = dom(1, 10);
    d.inMax(100, v, 20);
    verifyNoEvent();

    d = dom(1, 10);
    d.setStamp(100);
    d.inMax(100, v, 1);
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 2);
    d.setStamp(100);
    d.inMax(100, v, 1);
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInMax_twoIntervals(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inMax(100, v, 12);
    assertThat(d).hasToString("{1..5, 10..12}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inMax(100, v, 10);
    assertThat(d).hasToString("{1..5, 10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.inMax(100, v, 15);
    verifyNoEvent();

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inMax(100, v, 7);
    assertThat(d).hasToString("{1..5}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inMax(100, v, 5);
    assertThat(d).hasToString("{1..5}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inMax(100, v, 3);
    assertThat(d).hasToString("{1..3}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inMax(100, v, 1);
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 5, 7, 10);
    d.setStamp(100);
    d.inMax(100, v, 6);
    assertThat(d).hasToString("{1..5}");
    verifyEvent(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInMax_threeIntervals(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 3, 7, 9, 13, 15);
    d.setStamp(100);
    d.inMax(100, v, 11);
    assertThat(d).hasToString("{1..3, 7..9}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 3, 7, 9, 13, 15);
    d.setStamp(100);
    d.inMax(100, v, 8);
    assertThat(d).hasToString("{1..3, 7..8}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 3, 7, 9, 13, 15);
    d.setStamp(100);
    d.inMax(100, v, 5);
    assertThat(d).hasToString("{1..3}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 1, 3, 5, 8, 10);
    d.setStamp(100);
    d.inMax(100, v, 1);
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInMax_fails(String name) throws Exception {
    setupPrepareMethod(name);

    assertThatThrownBy(() -> dom(5, 10).inMax(100, v, 2)).isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(5, 7, 10, 12).inMax(100, v, 3)).isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 5, 10, 15).inMax(100, v, -1)).isInstanceOf(FailException.class);
  }

  // =========================================================================
  // 4. inValue(storeLevel, IntVar, int value)
  // =========================================================================

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInValue(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 10);
    d.setStamp(100);
    d.inValue(100, v, 1);
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 10);
    d.setStamp(100);
    d.inValue(100, v, 10);
    assertThat(d).hasToString("10");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 10);
    d.setStamp(100);
    d.inValue(100, v, 5);
    assertThat(d).hasToString("5");
    verifyEvent(IntDomain.GROUND);

    d = dom(5, 5);
    d.inValue(100, v, 5);
    verifyNoEvent();

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inValue(100, v, 3);
    assertThat(d).hasToString("3");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inValue(100, v, 1);
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inValue(100, v, 5);
    assertThat(d).hasToString("5");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inValue(100, v, 10);
    assertThat(d).hasToString("10");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inValue(100, v, 15);
    assertThat(d).hasToString("15");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inValue(100, v, 12);
    assertThat(d).hasToString("12");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 3, 7, 9, 13, 15);
    d.setStamp(100);
    d.inValue(100, v, 8);
    assertThat(d).hasToString("8");
    verifyEvent(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInValue_fails(String name) throws Exception {
    setupPrepareMethod(name);

    assertThatThrownBy(() -> dom(1, 5).inValue(100, v, 10)).isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 5).inValue(100, v, -1)).isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 3, 7, 10).inValue(100, v, 5)).isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 5, 10, 15).inValue(100, v, 7))
        .isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(5, 5).inValue(100, v, 3)).isInstanceOf(FailException.class);
  }

  // =========================================================================
  // 5. inComplement(storeLevel, Var, int complement)
  // =========================================================================

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInComplement_oneInterval(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 10);
    d.setStamp(100);
    d.inComplement(100, v, 1);
    assertThat(d).hasToString("{2..10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 10);
    d.setStamp(100);
    d.inComplement(100, v, 10);
    assertThat(d).hasToString("{1..9}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 10);
    d.setStamp(100);
    d.inComplement(100, v, 5);
    assertThat(d).hasToString("{1..4, 6..10}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 10);
    d.setStamp(100);
    d.inComplement(100, v, 2);
    assertThat(d).hasToString("{1, 3..10}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 10);
    d.setStamp(100);
    d.inComplement(100, v, 9);
    assertThat(d).hasToString("{1..8, 10}");
    verifyEvent(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInComplement_singletonEdgeCases(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 2);
    d.setStamp(100);
    d.inComplement(100, v, 1);
    assertThat(d).hasToString("2");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 2);
    d.setStamp(100);
    d.inComplement(100, v, 2);
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    assertThatThrownBy(() -> dom(5, 5).inComplement(100, v, 5)).isInstanceOf(FailException.class);

    d = dom(1, 1, 3, 3);
    d.setStamp(100);
    d.inComplement(100, v, 3);
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 1, 3, 3);
    d.setStamp(100);
    d.inComplement(100, v, 1);
    assertThat(d).hasToString("3");
    verifyEvent(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInComplement_twoIntervals(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 8, 12);
    d.setStamp(100);
    d.inComplement(100, v, 1);
    assertThat(d).hasToString("{2..5, 8..12}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12);
    d.setStamp(100);
    d.inComplement(100, v, 5);
    assertThat(d).hasToString("{1..4, 8..12}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12);
    d.setStamp(100);
    d.inComplement(100, v, 3);
    assertThat(d).hasToString("{1..2, 4..5, 8..12}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12);
    d.setStamp(100);
    d.inComplement(100, v, 8);
    assertThat(d).hasToString("{1..5, 9..12}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12);
    d.setStamp(100);
    d.inComplement(100, v, 12);
    assertThat(d).hasToString("{1..5, 8..11}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12);
    d.setStamp(100);
    d.inComplement(100, v, 10);
    assertThat(d).hasToString("{1..5, 8..9, 11..12}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12);
    d.inComplement(100, v, 6);
    verifyNoEvent();

    d = dom(1, 1, 5, 10);
    d.setStamp(100);
    d.inComplement(100, v, 1);
    assertThat(d).hasToString("{5..10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 10);
    d.setStamp(100);
    d.inComplement(100, v, 10);
    assertThat(d).hasToString("{1..5}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 7, 7, 10, 15);
    d.setStamp(100);
    d.inComplement(100, v, 7);
    assertThat(d).hasToString("{1..5, 10..15}");
    verifyEvent(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInComplement_threeIntervals(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 10);
    assertThat(d).hasToString("{1..5, 8..9, 11..12, 15..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 8, 12, 15);
    d.setStamp(100);
    d.inComplement(100, v, 8);
    assertThat(d).hasToString("{1..5, 12..15}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 1);
    assertThat(d).hasToString("{2..5, 8..12, 15..20}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 20);
    assertThat(d).hasToString("{1..5, 8..12, 15..19}");
    verifyEvent(IntDomain.BOUND);
  }

  // =========================================================================
  // 6. inComplement(storeLevel, Var, int min, int max)
  // =========================================================================

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInComplementRange_oneInterval(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 20);
    d.setStamp(100);
    d.inComplement(100, v, 5, 10);
    assertThat(d).hasToString("{1..4, 11..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 20);
    d.setStamp(100);
    d.inComplement(100, v, 1, 5);
    assertThat(d).hasToString("{6..20}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 20);
    d.setStamp(100);
    d.inComplement(100, v, 15, 20);
    assertThat(d).hasToString("{1..14}");
    verifyEvent(IntDomain.BOUND);

    assertThatThrownBy(() -> dom(1, 20).inComplement(100, v, 1, 20))
        .isInstanceOf(FailException.class);

    assertThatThrownBy(() -> dom(1, 20).inComplement(100, v, -5, 25))
        .isInstanceOf(FailException.class);

    d = dom(1, 20);
    d.setStamp(100);
    d.inComplement(100, v, 2, 20);
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 20);
    d.setStamp(100);
    d.inComplement(100, v, 1, 19);
    assertThat(d).hasToString("20");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 20);
    d.setStamp(100);
    d.inComplement(100, v, 2, 19);
    assertThat(d).hasToString("{1, 20}");
    verifyEvent(IntDomain.ANY);

    d = dom(5, 10);
    d.inComplement(100, v, 1, 3);
    verifyNoEvent();

    d = dom(5, 10);
    d.inComplement(100, v, 12, 15);
    verifyNoEvent();

    d = dom(5, 10);
    d.setStamp(100);
    d.inComplement(100, v, 3, 7);
    assertThat(d).hasToString("{8..10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(5, 10);
    d.setStamp(100);
    d.inComplement(100, v, 8, 12);
    assertThat(d).hasToString("{5..7}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 20);
    d.setStamp(100);
    d.inComplement(100, v, 10, 10);
    assertThat(d).hasToString("{1..9, 11..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 20);
    d.setStamp(100);
    d.inComplement(100, v, 1, 1);
    assertThat(d).hasToString("{2..20}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 20);
    d.setStamp(100);
    d.inComplement(100, v, 20, 20);
    assertThat(d).hasToString("{1..19}");
    verifyEvent(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInComplementRange_twoIntervals(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 10, 15);
    d.inComplement(100, v, 6, 9);
    verifyNoEvent();

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inComplement(100, v, 1, 5);
    assertThat(d).hasToString("{10..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inComplement(100, v, 10, 15);
    assertThat(d).hasToString("{1..5}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inComplement(100, v, 3, 12);
    assertThat(d).hasToString("{1..2, 13..15}");
    verifyEvent(IntDomain.ANY);

    assertThatThrownBy(() -> dom(1, 5, 10, 15).inComplement(100, v, 1, 15))
        .isInstanceOf(FailException.class);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inComplement(100, v, 2, 15);
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inComplement(100, v, 1, 14);
    assertThat(d).hasToString("15");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 10, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 3, 5);
    assertThat(d).hasToString("{1..2, 6..10, 15..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inComplement(100, v, 3, 5);
    assertThat(d).hasToString("{1..2, 10..15}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inComplement(100, v, 10, 12);
    assertThat(d).hasToString("{1..5, 13..15}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inComplement(100, v, 5, 10);
    assertThat(d).hasToString("{1..4, 11..15}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 3, 5, 10);
    d.inComplement(100, v, 4, 4);
    verifyNoEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInComplementRange_threeIntervals(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 8, 12);
    assertThat(d).hasToString("{1..5, 15..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 3, 17);
    assertThat(d).hasToString("{1..2, 18..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 1, 12);
    assertThat(d).hasToString("{15..20}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 8, 20);
    assertThat(d).hasToString("{1..5}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 2, 20);
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 1, 19);
    assertThat(d).hasToString("20");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 6, 14);
    assertThat(d).hasToString("{1..5, 15..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 4, 5);
    assertThat(d).hasToString("{1..3, 8..12, 15..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 4, 12);
    assertThat(d).hasToString("{1..3, 15..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 8, 16);
    assertThat(d).hasToString("{1..5, 17..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 15, 20);
    assertThat(d).hasToString("{1..5, 8..12}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.inComplement(100, v, 9, 18);
    assertThat(d).hasToString("{1..5, 8, 19..20}");
    verifyEvent(IntDomain.ANY);
  }

  // =========================================================================
  // 7. in(storeLevel, Var, IntDomain)
  // =========================================================================

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInDomain_1x1(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 10);
    d.setStamp(100);
    d.in(100, v, dom(3, 7));
    assertThat(d).hasToString("{3..7}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 10);
    d.in(100, v, dom(1, 10));
    verifyNoEvent();

    d = dom(3, 7);
    d.in(100, v, dom(1, 10));
    verifyNoEvent();

    d = dom(1, 10);
    d.setStamp(100);
    d.in(100, v, dom(5, 15));
    assertThat(d).hasToString("{5..10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(5, 15);
    d.setStamp(100);
    d.in(100, v, dom(1, 10));
    assertThat(d).hasToString("{5..10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 10);
    d.setStamp(100);
    d.in(100, v, dom(5, 5));
    assertThat(d).hasToString("5");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 10);
    d.setStamp(100);
    d.in(100, v, dom(10, 10));
    assertThat(d).hasToString("10");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 10);
    d.setStamp(100);
    d.in(100, v, dom(1, 1));
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 5);
    d.setStamp(100);
    d.in(100, v, dom(5, 10));
    assertThat(d).hasToString("5");
    verifyEvent(IntDomain.GROUND);

    d = dom(5, 5);
    d.in(100, v, dom(5, 5));
    verifyNoEvent();

    d = dom(5, 5);
    d.in(100, v, dom(1, 10));
    verifyNoEvent();

    d = dom(5, 5);
    d.in(100, v, dom(3, 5));
    verifyNoEvent();

    d = dom(5, 5);
    d.in(100, v, dom(5, 8));
    verifyNoEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInDomain_1x2(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, dom(3, 5, 15, 18));
    assertThat(d).hasToString("{3..5, 15..18}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, dom(1, 5, 15, 20));
    assertThat(d).hasToString("{1..5, 15..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, dom(1, 3, 18, 20));
    assertThat(d).hasToString("{1..3, 18..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, dom(5, 5, 15, 15));
    assertThat(d).hasToString("{5, 15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, dom(1, 1, 20, 20));
    assertThat(d).hasToString("{1, 20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 10);
    d.setStamp(100);
    d.in(100, v, dom(1, 3, 8, 10));
    assertThat(d).hasToString("{1..3, 8..10}");
    verifyEvent(IntDomain.ANY);

    d = dom(5, 15);
    d.setStamp(100);
    d.in(100, v, dom(1, 7, 12, 20));
    assertThat(d).hasToString("{5..7, 12..15}");
    verifyEvent(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInDomain_1x3(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, dom(1, 3, 8, 12, 18, 20));
    assertThat(d).hasToString("{1..3, 8..12, 18..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, dom(3, 5, 10, 12, 17, 19));
    assertThat(d).hasToString("{3..5, 10..12, 17..19}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 20);
    d.setStamp(100);
    d.in(100, v, dom(1, 1, 10, 10, 20, 20));
    assertThat(d).hasToString("{1, 10, 20}");
    verifyEvent(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInDomain_2x1(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(3, 12));
    assertThat(d).hasToString("{3..5, 10..12}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(1, 7));
    assertThat(d).hasToString("{1..5}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(8, 15));
    assertThat(d).hasToString("{10..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.in(100, v, dom(1, 15));
    verifyNoEvent();

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(5, 10));
    assertThat(d).hasToString("{5, 10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(1, 5));
    assertThat(d).hasToString("{1..5}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(10, 15));
    assertThat(d).hasToString("{10..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(3, 5));
    assertThat(d).hasToString("{3..5}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(10, 12));
    assertThat(d).hasToString("{10..12}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(1, 3));
    assertThat(d).hasToString("{1..3}");
    verifyEvent(IntDomain.BOUND);

    // 1-wide gap tests
    d = dom(1, 3, 5, 10);
    d.setStamp(100);
    d.in(100, v, dom(3, 5));
    assertThat(d).hasToString("{3, 5}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 3, 5, 10);
    d.setStamp(100);
    d.in(100, v, dom(2, 8));
    assertThat(d).hasToString("{2..3, 5..8}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 3, 5, 10);
    d.setStamp(100);
    d.in(100, v, dom(1, 4));
    assertThat(d).hasToString("{1..3}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 3, 5, 10);
    d.setStamp(100);
    d.in(100, v, dom(4, 10));
    assertThat(d).hasToString("{5..10}");
    verifyEvent(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInDomain_2x1_singletonIntervals(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 1, 5, 10);
    d.setStamp(100);
    d.in(100, v, dom(1, 7));
    assertThat(d).hasToString("{1, 5..7}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 1, 5, 10);
    d.setStamp(100);
    d.in(100, v, dom(1, 1));
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 1, 5, 10);
    d.setStamp(100);
    d.in(100, v, dom(5, 10));
    assertThat(d).hasToString("{5..10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 1, 5, 10);
    d.in(100, v, dom(1, 10));
    verifyNoEvent();

    d = dom(1, 5, 10, 10);
    d.setStamp(100);
    d.in(100, v, dom(3, 10));
    assertThat(d).hasToString("{3..5, 10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 10);
    d.setStamp(100);
    d.in(100, v, dom(10, 10));
    assertThat(d).hasToString("10");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 1, 10, 10);
    d.in(100, v, dom(1, 10));
    verifyNoEvent();

    d = dom(1, 1, 10, 10);
    d.setStamp(100);
    d.in(100, v, dom(1, 1));
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 1, 10, 10);
    d.setStamp(100);
    d.in(100, v, dom(10, 10));
    assertThat(d).hasToString("10");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 1, 10, 10);
    d.setStamp(100);
    d.in(100, v, dom(1, 5));
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInDomain_2x2(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 10, 15);
    d.in(100, v, dom(1, 5, 10, 15));
    verifyNoEvent();

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(2, 4, 11, 14));
    assertThat(d).hasToString("{2..4, 11..14}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(3, 12, 14, 20));
    assertThat(d).hasToString("{3..5, 10..12, 14..15}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 10, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(5, 17, 19, 25));
    assertThat(d).hasToString("{5..10, 15..17, 19..20}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(1, 3, 12, 15));
    assertThat(d).hasToString("{1..3, 12..15}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(1, 1, 15, 15));
    assertThat(d).hasToString("{1, 15}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(5, 5, 10, 10));
    assertThat(d).hasToString("{5, 10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.in(100, v, dom(1, 5, 12, 12));
    assertThat(d).hasToString("{1..5, 12}");
    verifyEvent(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInDomain_2x2_singletons(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 1, 5, 5);
    d.in(100, v, dom(1, 1, 5, 5));
    verifyNoEvent();

    d = dom(1, 1, 5, 5);
    d.in(100, v, dom(1, 5));
    verifyNoEvent();

    d = dom(1, 1, 5, 5);
    d.setStamp(100);
    d.in(100, v, dom(1, 3));
    assertThat(d).hasToString("1");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 1, 5, 5);
    d.setStamp(100);
    d.in(100, v, dom(3, 5));
    assertThat(d).hasToString("5");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 1, 5, 10);
    d.setStamp(100);
    d.in(100, v, dom(1, 1, 7, 8));
    assertThat(d).hasToString("{1, 7..8}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 10, 10);
    d.setStamp(100);
    d.in(100, v, dom(3, 3, 10, 10));
    assertThat(d).hasToString("{3, 10}");
    verifyEvent(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInDomain_3x1(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(4, 17));
    assertThat(d).hasToString("{4..5, 8..12, 15..17}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(8, 12));
    assertThat(d).hasToString("{8..12}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.in(100, v, dom(1, 20));
    verifyNoEvent();

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(6, 14));
    assertThat(d).hasToString("{8..12}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(1, 5));
    assertThat(d).hasToString("{1..5}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(15, 20));
    assertThat(d).hasToString("{15..20}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(10, 10));
    assertThat(d).hasToString("10");
    verifyEvent(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInDomain_3x2(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(1, 5, 15, 20));
    assertThat(d).hasToString("{1..5, 15..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(3, 9, 18, 20));
    assertThat(d).hasToString("{3..5, 8..9, 18..20}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(1, 1, 20, 20));
    assertThat(d).hasToString("{1, 20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(5, 8, 12, 15));
    assertThat(d).hasToString("{5, 8, 12, 15}");
    verifyEvent(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInDomain_3x3(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(1, 3, 10, 16, 19, 25));
    assertThat(d).hasToString("{1..3, 10..12, 15..16, 19..20}");
    verifyEvent(IntDomain.ANY);

    d = dom(1, 5, 8, 12, 15, 20);
    d.in(100, v, dom(1, 5, 8, 12, 15, 20));
    verifyNoEvent();

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(2, 4, 9, 11, 16, 18));
    assertThat(d).hasToString("{2..4, 9..11, 16..18}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 5, 8, 12, 15, 20);
    d.setStamp(100);
    d.in(100, v, dom(3, 10, 12, 12, 17, 25));
    assertThat(d).hasToString("{3..5, 8..10, 12, 17..20}");
    verifyEvent(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInDomain_3_singletonReceivers(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 1, 5, 5, 10, 10);
    d.in(100, v, dom(1, 10));
    verifyNoEvent();

    d = dom(1, 1, 5, 5, 10, 10);
    d.setStamp(100);
    d.in(100, v, dom(1, 5));
    assertThat(d).hasToString("{1, 5}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 1, 5, 5, 10, 10);
    d.setStamp(100);
    d.in(100, v, dom(5, 10));
    assertThat(d).hasToString("{5, 10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 1, 5, 5, 10, 10);
    d.setStamp(100);
    d.in(100, v, dom(5, 5));
    assertThat(d).hasToString("5");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 1, 5, 10, 15, 15);
    d.setStamp(100);
    d.in(100, v, dom(3, 12));
    assertThat(d).hasToString("{5..10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 1, 5, 10, 15, 15);
    d.in(100, v, dom(1, 15));
    verifyNoEvent();

    d = dom(1, 1, 5, 10, 15, 15);
    d.setStamp(100);
    d.in(100, v, dom(1, 1, 15, 15));
    assertThat(d).hasToString("{1, 15}");
    verifyEvent(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInDomain_fails(String name) throws Exception {
    setupPrepareMethod(name);

    assertThatThrownBy(() -> dom(1, 5).in(100, v, dom(8, 12))).isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 3, 7, 10).in(100, v, dom(4, 6)))
        .isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 5, 10, 15).in(100, v, dom(6, 9)))
        .isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 1, 5, 5).in(100, v, dom(3, 3)))
        .isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 1, 5, 5, 10, 10).in(100, v, dom(3, 3)))
        .isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 5, 10, 15).in(100, v, dom(20, 25)))
        .isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 5, 10, 15).in(100, v, dom(6, 9, 16, 20)))
        .isInstanceOf(FailException.class);
  }

  // =========================================================================
  // 8. in(IntDomain) cross-type tests
  // =========================================================================

  @Test
  void testInDomain_crossType() {
    IntDomain d;

    // IntervalDomain receives SDD: creates new SDD result, original d not modified in-place
    d = intervalDom(1, 10);
    d.in(100, v, sddDom(3, 7));
    verifyEvent(IntDomain.BOUND);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.in(100, v, intervalDom(3, 7));
    assertThat(d).hasToString("{3..7}");
    verifyEvent(IntDomain.BOUND);

    // IntervalDomain receives SDD (bounds unchanged → ANY)
    d = intervalDom(1, 10);
    d.in(100, v, sddDom(1, 3, 8, 10));
    verifyEvent(IntDomain.ANY);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.in(100, v, intervalDom(1, 3, 8, 10));
    assertThat(d).hasToString("{1..3, 8..10}");
    verifyEvent(IntDomain.ANY);

    // Singleton SDD also goes through SDD path (no singleton dispatch in IntervalDomain.in)
    d = intervalDom(1, 10);
    d.in(100, v, sddDom(5, 5));
    verifyEvent(IntDomain.GROUND);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.in(100, v, intervalDom(5, 5));
    assertThat(d).hasToString("5");
    verifyEvent(IntDomain.GROUND);

    assertThatThrownBy(() -> intervalDom(1, 5).in(100, v, sddDom(8, 12)))
        .isInstanceOf(FailException.class);
    assertThatThrownBy(() -> sddDom(1, 5).in(100, v, intervalDom(8, 12)))
        .isInstanceOf(FailException.class);
  }

  // =========================================================================
  // 9. inShift(storeLevel, Var, IntDomain, int shift)
  // =========================================================================

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInShift_noShift(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(5, 15);
    d.setStamp(100);
    d.inShift(100, v, dom(1, 10), 0);
    assertThat(d).hasToString("{5..10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 10);
    d.inShift(100, v, dom(1, 10), 0);
    verifyNoEvent();

    d = dom(1, 10);
    d.setStamp(100);
    d.inShift(100, v, dom(1, 3, 8, 10), 0);
    assertThat(d).hasToString("{1..3, 8..10}");
    verifyEvent(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInShift_positiveShift(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 10);
    d.setStamp(100);
    d.inShift(100, v, dom(1, 4), 3);
    assertThat(d).hasToString("{4..7}");
    verifyEvent(IntDomain.BOUND);

    d = dom(5, 15);
    d.setStamp(100);
    d.inShift(100, v, dom(1, 5), 5);
    assertThat(d).hasToString("{6..10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 20);
    d.setStamp(100);
    d.inShift(100, v, dom(5, 5), -2);
    assertThat(d).hasToString("3");
    verifyEvent(IntDomain.GROUND);

    d = dom(1, 5, 8, 12);
    d.setStamp(100);
    d.inShift(100, v, dom(1, 10), 2);
    assertThat(d).hasToString("{3..5, 8..12}");
    verifyEvent(IntDomain.BOUND);

    d = dom(5, 10);
    d.setStamp(100);
    d.inShift(100, v, dom(1, 3), 5);
    assertThat(d).hasToString("{6..8}");
    verifyEvent(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInShift_negativeShift(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 10);
    d.setStamp(100);
    d.inShift(100, v, dom(5, 15), -3);
    assertThat(d).hasToString("{2..10}");
    verifyEvent(IntDomain.BOUND);

    d = dom(0, 10);
    d.setStamp(100);
    d.inShift(100, v, dom(0, 5), -3);
    assertThat(d).hasToString("{0..2}");
    verifyEvent(IntDomain.BOUND);

    d = dom(-5, 5);
    d.setStamp(100);
    d.inShift(100, v, dom(-3, 3), 0);
    assertThat(d).hasToString("{-3..3}");
    verifyEvent(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInShift_multiInterval(String name) throws Exception {
    setupPrepareMethod(name);
    IntDomain d;

    d = dom(1, 5, 10, 15);
    d.setStamp(100);
    d.inShift(100, v, dom(1, 3, 8, 10), 2);
    assertThat(d).hasToString("{3..5, 10..12}");
    verifyEvent(IntDomain.BOUND);

    d = dom(1, 10, 15, 20);
    d.setStamp(100);
    d.inShift(100, v, dom(2, 5, 12, 15), 3);
    assertThat(d).hasToString("{5..8, 15..18}");
    verifyEvent(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testInShift_fails(String name) throws Exception {
    setupPrepareMethod(name);

    assertThatThrownBy(() -> dom(1, 5).inShift(100, v, dom(1, 5), 10))
        .isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 5).inShift(100, v, dom(10, 15), 0))
        .isInstanceOf(FailException.class);
    assertThatThrownBy(() -> dom(1, 3).inShift(100, v, dom(10, 12), -20))
        .isInstanceOf(FailException.class);
  }

  // =========================================================================
  // 10. inShift cross-type tests
  // =========================================================================

  @Test
  void testInShift_crossType() {
    IntDomain d;

    // IntervalDomain receives SDD in inShift: creates new SDD result, original d not modified
    d = intervalDom(1, 10);
    d.inShift(100, v, sddDom(1, 4), 3);
    verifyEvent(IntDomain.BOUND);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.inShift(100, v, intervalDom(1, 4), 3);
    assertThat(d).hasToString("{4..7}");
    verifyEvent(IntDomain.BOUND);

    // inShift has no singleton dispatch before SDD path, so same issue
    d = intervalDom(1, 10);
    d.inShift(100, v, sddDom(5, 5), 0);
    verifyEvent(IntDomain.GROUND);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.inShift(100, v, intervalDom(5, 5), 0);
    assertThat(d).hasToString("5");
    verifyEvent(IntDomain.GROUND);

    assertThatThrownBy(() -> intervalDom(1, 5).inShift(100, v, sddDom(10, 15), 0))
        .isInstanceOf(FailException.class);
    assertThatThrownBy(() -> sddDom(1, 5).inShift(100, v, intervalDom(10, 15), 0))
        .isInstanceOf(FailException.class);
  }

  // =========================================================================
  // 11. SmallDenseDomain-specific branches
  // =========================================================================

  @Test
  void testSdd_computeInBitsResult() {
    IntDomain d;

    d = sddDom(1, 10);
    d.setStamp(100);
    d.in(100, v, 3, 8);
    assertThat(d).hasToString("{3..8}");
    verifyEvent(IntDomain.BOUND);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.in(100, v, 1, 8);
    assertThat(d).hasToString("{1..8}");
    verifyEvent(IntDomain.BOUND);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.in(100, v, 3, 10);
    assertThat(d).hasToString("{3..10}");
    verifyEvent(IntDomain.BOUND);

    d = sddDom(1, 10);
    d.in(100, v, 1, 10);
    verifyNoEvent();

    d = sddDom(5, 5);
    d.in(100, v, 3, 8);
    verifyNoEvent();

    // sparse bits, both sides clipped
    d = sddDom(1, 1);
    d.addDom(sddDom(3, 3));
    d.addDom(sddDom(5, 5));
    d.addDom(sddDom(7, 7));
    d.addDom(sddDom(9, 9));
    d.setStamp(100);
    d.in(100, v, 3, 7);
    assertThat(d).hasToString("{3, 5, 7}");
    verifyEvent(IntDomain.BOUND);

    // sparse bits → GROUND
    d = sddDom(1, 1);
    d.addDom(sddDom(3, 3));
    d.addDom(sddDom(5, 5));
    d.addDom(sddDom(7, 7));
    d.addDom(sddDom(9, 9));
    d.setStamp(100);
    d.in(100, v, 4, 6);
    assertThat(d).hasToString("5");
    verifyEvent(IntDomain.GROUND);
  }

  @Test
  void testSdd_inDomainDispatch() {
    IntDomain d;

    d = sddDom(1, 10);
    d.setStamp(100);
    d.in(100, v, sddDom(3, 7));
    assertThat(d).hasToString("{3..7}");
    verifyEvent(IntDomain.BOUND);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.in(100, v, intervalDom(3, 5, 8, 10));
    assertThat(d).hasToString("{3..5, 8..10}");
    verifyEvent(IntDomain.BOUND);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.in(100, v, intervalDom(5, 5));
    assertThat(d).hasToString("5");
    verifyEvent(IntDomain.GROUND);

    d = sddDom(1, 10);
    d.in(100, v, intervalDom(1, 10));
    verifyNoEvent();

    assertThatThrownBy(() -> sddDom(1, 5).in(100, v, intervalDom(8, 12)))
        .isInstanceOf(FailException.class);

    assertThatThrownBy(() -> sddDom(1, 5).in(100, v, intervalDom(6, 7, 10, 12)))
        .isInstanceOf(FailException.class);
  }

  @Test
  void testSdd_inShiftDirection() {
    IntDomain d;

    d = sddDom(5, 15);
    d.setStamp(100);
    d.inShift(100, v, sddDom(1, 5), 5);
    assertThat(d).hasToString("{6..10}");
    verifyEvent(IntDomain.BOUND);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.inShift(100, v, sddDom(5, 15), -5);
    assertThat(d).hasToString("{1..10}");
    verifyNoEvent();

    assertThatThrownBy(() -> sddDom(5, 10).inShift(100, v, sddDom(1, 3), 100))
        .isInstanceOf(FailException.class);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.inShift(100, v, intervalDom(1, 5), 3);
    assertThat(d).hasToString("{4..8}");
    verifyEvent(IntDomain.BOUND);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.inShift(100, v, intervalDom(1, 3, 8, 10), 2);
    assertThat(d).hasToString("{3..5, 10}");
    verifyEvent(IntDomain.BOUND);
  }

  @Test
  void testSdd_inComplement() {
    IntDomain d;

    d = sddDom(1, 10);
    d.inComplement(100, v, -5);
    verifyNoEvent();

    d = sddDom(1, 10);
    d.inComplement(100, v, 100);
    verifyNoEvent();

    d = sddDom(1, 1);
    d.addDom(sddDom(3, 3));
    d.addDom(sddDom(5, 5));
    d.setStamp(100);
    d.inComplement(100, v, 3);
    assertThat(d).hasToString("{1, 5}");
    verifyEvent(IntDomain.ANY);

    d = sddDom(1, 1);
    d.addDom(sddDom(3, 3));
    d.addDom(sddDom(5, 5));
    d.inComplement(100, v, 2);
    verifyNoEvent();
  }

  @Test
  void testSdd_inComplementRange() {
    IntDomain d;

    d = sddDom(1, 10);
    d.inComplement(100, v, -5, -1);
    verifyNoEvent();

    d = sddDom(1, 10);
    d.inComplement(100, v, 15, 20);
    verifyNoEvent();

    d = sddDom(1, 10);
    d.setStamp(100);
    d.inComplement(100, v, -2, 3);
    assertThat(d).hasToString("{4..10}");
    verifyEvent(IntDomain.BOUND);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.inComplement(100, v, 8, 15);
    assertThat(d).hasToString("{1..7}");
    verifyEvent(IntDomain.BOUND);

    d = sddDom(1, 1);
    d.addDom(sddDom(3, 3));
    d.addDom(sddDom(5, 5));
    d.addDom(sddDom(7, 7));
    d.addDom(sddDom(9, 9));
    d.setStamp(100);
    d.inComplement(100, v, 3, 7);
    assertThat(d).hasToString("{1, 9}");
    verifyEvent(IntDomain.ANY);
  }

  @Test
  void testSdd_inBitLevel() {
    IntDomain d;

    d = sddDom(1, 10);
    d.in(100, v, sddDom(1, 10));
    verifyNoEvent();

    d = sddDom(1, 10);
    d.setStamp(100);
    d.in(100, v, sddDom(3, 7));
    assertThat(d).hasToString("{3..7}");
    verifyEvent(IntDomain.BOUND);

    d = sddDom(1, 10);
    d.setStamp(100);
    d.in(100, v, sddDom(1, 1, 10, 10));
    assertThat(d).hasToString("{1, 10}");
    verifyEvent(IntDomain.ANY);

    assertThatThrownBy(() -> sddDom(1, 5).in(100, v, sddDom(8, 12)))
        .isInstanceOf(FailException.class);
  }
}
