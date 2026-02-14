/*
 * IntDomainTest.java
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
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collection;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.SmallDenseDomain;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

/**
 * Tests to test different domain operations for IntDomains in particular SmallDenseDomain and
 * IntervalDomain.
 *
 * @author Mariusz Świerkot and Radoslaw Szymanek
 * @version 5.0
 */
@ExtendWith(MockitoExtension.class)
public class IntDomainTest {

  private Method prepareMethod;
  private @Mock IntVar var;
  private IntDomain intDomain;

  static Collection<String> parametricTest() {
    return Arrays.asList("prepareSmallDenseDomain", "prepareIntervalDomain");
  }

  private void setupPrepareMethod(String prepareMethodName) throws NoSuchMethodException {
    prepareMethod = this.getClass().getMethod(prepareMethodName, int[].class);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testContains(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});

    assertThat(testedDomain.contains(createDomain(new Interval(0, 0)))).isFalse();
    assertThat(testedDomain.contains(createDomain(new Interval(1, 1)))).isTrue();

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {-3, 4, 5, 5, 9, 10}});

    assertThat(testedDomain.contains(createDomain(new Interval(1, 2), new Interval(6, 6))))
        .isFalse();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testComplement(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    IntDomain testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(testedDomain.complement().toString())
        .isEqualTo("{" + IntDomain.MIN_INT + "..0, 4, 8..11, 19.." + IntDomain.MAX_INT + "}");
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testGetElementAt(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    IntDomain testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    assertThat(testedDomain.getElementAt(0)).isEqualTo(1);
    assertThat(testedDomain.getElementAt(1)).isEqualTo(2);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testIntersect(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});

    IntDomain goldenResultDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {2, 2}});
    assertThat(testedDomain.intersect(2, 3).toString()).isEqualTo(goldenResultDomain.toString());

    goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    assertThat(testedDomain.intersect(0, 25).toString()).isEqualTo(goldenResultDomain.toString());

    goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    assertThat(testedDomain.intersect(1, 2).toString()).isEqualTo(goldenResultDomain.toString());

    testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(2, 4)))).isEqualTo(0);

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    goldenResultDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {2, 3, 5, 7, 12, 14}});
    assertThat(testedDomain.intersect(2, 14).toString()).isEqualTo(goldenResultDomain.toString());

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {15, 15}});
    assertThat(testedDomain.intersect(15, 15).toString()).isEqualTo(goldenResultDomain.toString());
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testIntersectAdapt(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(2, 4)))).isEqualTo(0);

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(14, 20)))).isEqualTo(1);

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(2, 6)))).isEqualTo(1);

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(2, 6), new Interval(8, 15))))
        .isEqualTo(1);

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(0, 0), new Interval(20, 28))))
        .isEqualTo(0);

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(
            testedDomain.intersectAdapt(
                createDomain(new Interval(2, 2), new Interval(5, 5), new Interval(20, 25))))
        .isEqualTo(1);

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(
            testedDomain.intersectAdapt(
                createDomain(new Interval(1, 3), new Interval(5, 5), new Interval(20, 25))))
        .isEqualTo(1);

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(
            testedDomain.intersectAdapt(
                createDomain(new Interval(1, 3), new Interval(5, 5), new Interval(13, 18))))
        .isEqualTo(2);

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(4, 9)))).isEqualTo(1);

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(0, 0)))).isEqualTo(0);

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(0, 0), new Interval(2, 2))))
        .isEqualTo(0);

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(2, 2)).isEqualTo(0);

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(0, 0)).isEqualTo(0);

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(1, 9)).isEqualTo(1);

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(0, 26)).isEqualTo(-1);

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(28, 45)).isEqualTo(0);

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(-4, 3), new Interval(9, 18))))
        .isEqualTo(1);

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(-4, 1)))).isEqualTo(1);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testIsIntersecting(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.isIntersecting(28, 45)).isFalse();
    assertThat(testedDomain.isIntersecting(0, 0)).isTrue();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testSubtract(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    IntDomain goldenResultDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 0, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.subtract(1, 3).toString()).isEqualTo(goldenResultDomain.toString());

    goldenResultDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {1, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.subtract(0, 0).toString()).isEqualTo(goldenResultDomain.toString());

    goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 0}});
    assertThat(testedDomain.subtract(1, 26).toString()).isEqualTo(goldenResultDomain.toString());

    goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 6}});
    assertThat(testedDomain.subtract(8, 26).toString()).isEqualTo(goldenResultDomain.toString());
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testNextValue(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain goldenResultDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(goldenResultDomain.nextValue(3)).isEqualTo(5);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testPreviousValue(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    IntDomain goldenResultDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(goldenResultDomain.previousValue(2)).isEqualTo(1);
  }

  @BeforeEach
  public void setUp() {
    intDomain = new IntervalDomain();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    intDomain.inComplement(100, var, 2);

    verify(var).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval2(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    intDomain.inComplement(100, var, 1);

    verify(var).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval3(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 1);

    verify(var).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval4(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);
    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 2);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval5(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 5);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval6(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);
    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intDomain.inComplement(100, var, 5);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval7(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 5, 7, 10}});
    intDomain.inComplement(100, var, 5);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval8(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 5, 7, 10}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 5);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval9(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {5, 5, 7, 7}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 5);

    verify(var).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval10(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 9, 20}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 5);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval11(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 9, 20}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 1);

    verify(var).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval12(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 9, 20}});
    intDomain.inComplement(100, var, 1);

    verify(var).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval13(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 9, 20}});
    intDomain.inComplement(100, var, 7);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval14(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 0, 2, 2}});
    intDomain.inComplement(100, var, 0);

    verify(var).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval15(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 5}});
    intDomain.inComplement(100, var, 5);

    verify(var).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval16(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 5, 7, 9, 11, 20}});
    intDomain.inComplement(100, var, 7);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval17(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);
    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 10);

    verify(var).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval18(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 5}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 5);

    verify(var).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval19(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7}});
    intDomain.inComplement(100, var, 7);

    verify(var).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval20(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);
    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 2);
    verify(var).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval21(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);
    intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10, 12, 12}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 5);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval22(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);
    intDomain =
        (IntDomain)
            prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10, 12, 12, 15, 22}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 5);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval23(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 1, 2);

    verify(var).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval24(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 15}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 5, 5);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval25a(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10, 12, 33}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 2, 11);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval25b(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 20}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 2, 11);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testintervalNoEventGenerated(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 1, 12, 20}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 2, 11);

    verify(var, never()).domainHasChanged(IntDomain.ANY);
    verify(var, never()).domainHasChanged(IntDomain.BOUND);
    verify(var, never()).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval27(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {3, 6}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 2, 4);

    verify(var).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval28(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {1, 20, 22, 24, 26, 28, 30, 32, 34, 36}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 2, 11);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval29(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {3, 6}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 2, 5);

    verify(var).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval30(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intDomain.inComplement(100, var, 1, 2);

    verify(var).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval31(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intDomain.inComplement(100, var, 2, 4);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval32(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intDomain.inComplement(100, var, 2, 11);

    verify(var).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval33(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 20}});
    intDomain.inComplement(100, var, 2, 11);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval34(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {3, 6}});
    intDomain.inComplement(100, var, 2, 4);

    verify(var).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval35(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {3, 5}});
    intDomain.inComplement(100, var, 2, 4);

    verify(var).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval36(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intDomain.inComplement(100, var, 1, 9);

    verify(var).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval37(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intDomain.inComplement(100, var, 25, 50);

    verify(var).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval38(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 5, 35);
    verify(var).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval39(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intDomain.inComplement(100, var, 5, 11);
    verify(var).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval40(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 11, 41);
    verify(var).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval41(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 0, 3, 6, 7, 18}});
    intDomain.inComplement(100, var, 2, 4);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval42(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {18, 20, 22, 23}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 18, 22);
    verify(var).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval43(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 0, 4, 4, 16, 26}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 5, 17);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  public void testinterval44(String prepareMethodName)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {
    setupPrepareMethod(prepareMethodName);

    intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intDomain.setStamp(100);
    intDomain.inComplement(100, var, 3, 6);

    verify(var).domainHasChanged(IntDomain.ANY);
  }

  private IntDomain createDomain(Interval... intervals) {
    IntDomain result = new IntervalDomain();

    for (Interval interval : intervals) {
      result.addDom(new IntervalDomain(interval.min(), interval.max()));
    }

    return result;
  }

  /**
   * It is used by the reflection used by the parametrization parameters. It has to stay public.
   *
   * @param intervalList list of intervals where each two consequtive numbers specify the minimum
   *     and maximum of an interval.
   * @return prepared domain using SmallDenseDomain.
   */
  public IntDomain prepareSmallDenseDomain(int[] intervalList) {
    IntDomain domain;

    if (intervalList.length % 2 != 0) {
      throw new IllegalArgumentException(
          "List must have an even number of elements"
              + " since the domain is a list of intervals and each interval is denoted by two elements");
    }
    if (intervalList.length < 2) {
      throw new IllegalArgumentException(
          "List must have at least two elements since the domain"
              + " must have at least one interval and each interval is denoted by two integers.");
    }

    domain = new SmallDenseDomain(intervalList[0], intervalList[1]);
    for (int i = 2; i < intervalList.length; i += 2) {
      domain.addDom(new SmallDenseDomain(intervalList[i], intervalList[i + 1]));
    }

    return domain;
  }

  /**
   * It is used by the reflection used by the parametrization parameters. It has to stay public.
   *
   * @param intervalList list of intervals where each two consequtive numbers specify the minimum
   *     and maximum of an interval.
   * @return prepared domain using IntevalDomain.
   */
  public IntDomain prepareIntervalDomain(int[] intervalList) {
    IntDomain domain;

    if (intervalList.length % 2 != 0) {
      throw new IllegalArgumentException(
          "List must have an even number of elements"
              + " since the domain is a list of intervals and each interval is denoted by two elements");
    }
    if (intervalList.length < 2) {
      throw new IllegalArgumentException(
          "List must have at least two elements since the domain"
              + " must have at least one interval and each interval is denoted by two integers.");
    }

    domain = new IntervalDomain(intervalList[0], intervalList[1]);
    for (int i = 2; i < intervalList.length; i += 2) {
      domain.addDom(new IntervalDomain(intervalList[i], intervalList[i + 1]));
    }

    return domain;
  }
}
