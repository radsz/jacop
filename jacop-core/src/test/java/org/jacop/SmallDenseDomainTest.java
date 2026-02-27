package org.jacop;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Mockito.anyInt;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collection;
import lombok.extern.slf4j.Slf4j;
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
import org.mockito.Mockito;
import org.mockito.junit.jupiter.MockitoExtension;

/**
 * @author Mariusz Świerkot
 */
@ExtendWith(MockitoExtension.class)
@Slf4j
class SmallDenseDomainTest {

  @Mock IntVar v;
  IntDomain intervalDomain;
  private Method prepareMethod;

  static Collection<String> parametricTest() {
    return Arrays.asList("prepareSmallDenseDomain", "prepareIntervalDomain");
  }

  private void setupPrepareMethod(String prepareMethodName) throws NoSuchMethodException {
    Class<SmallDenseDomainTest> cls = SmallDenseDomainTest.class;
    prepareMethod = cls.getMethod(prepareMethodName, int[].class);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testContains(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    log.info("Contains function test");
    IntDomain testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});

    assertThat(testedDomain.contains(createDomain(new Interval(0, 0)))).isFalse();
    assertThat(testedDomain.contains(createDomain(new Interval(1, 1)))).isTrue();

    testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {-3, 4, 5, 5, 9, 10}});

    log.info("Test Complement function");
    assertThat(testedDomain.contains(createDomain(new Interval(1, 2), new Interval(6, 6))))
        .isFalse();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testComplement(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    log.info("Complement function test");
    IntDomain testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(testedDomain.complement().toString())
        .isEqualTo("{" + IntDomain.MIN_INT + "..0, 4, 8..11, 19.." + IntDomain.MAX_INT + "}");
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testGetElementAt(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    log.info("GetElementAt function test");
    IntDomain testedDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    assertThat(testedDomain.getElementAt(0)).isEqualTo(1);
    assertThat(testedDomain.getElementAt(1)).isEqualTo(2);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testIntersect(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    log.info("Intersect function test");

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
  void testIntersectAdapt(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    log.info("IntersectAdapt function test");
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
  void testIsIntersecting() throws Exception {

    log.info("IsIntersecting function test");
    IntDomain testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.isIntersecting(28, 45)).isFalse();
    assertThat(testedDomain.isIntersecting(0, 0)).isTrue();
    assertThat(testedDomain.isIntersecting(0, 26)).isTrue();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testSubtract() throws Exception {

    log.info("Subtract function test");
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
  void testNextValue() throws Exception {

    log.info("NextValue function test");

    IntDomain goldenResultDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(goldenResultDomain.nextValue(3)).isEqualTo(5);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testPreviousValue() throws Exception {

    log.info("previousValue function test");

    IntDomain goldenResultDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    assertThat(goldenResultDomain.previousValue(2)).isEqualTo(1);
  }

  @BeforeEach
  void setUp() {
    intervalDomain = new IntervalDomain();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    intervalDomain.inComplement(100, v, 2);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval2() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    intervalDomain.inComplement(100, v, 1);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval3() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 1);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval4() throws InvocationTargetException, IllegalAccessException {
    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 2);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval5() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval6() throws InvocationTargetException, IllegalAccessException {
    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval7() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 5, 7, 10}});
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval8() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 5, 7, 10}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval9() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {5, 5, 7, 7}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval10() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 9, 20}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval11() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 9, 20}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 1);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval12() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 9, 20}});
    intervalDomain.inComplement(100, v, 1);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval13() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 9, 20}});
    intervalDomain.inComplement(100, v, 7);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval14() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 0, 2, 2}});
    intervalDomain.inComplement(100, v, 0);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval15() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 5}});
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval16() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 5, 7, 9, 11, 20}});
    intervalDomain.inComplement(100, v, 7);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval17() throws InvocationTargetException, IllegalAccessException {
    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 10);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval18() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 5}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval19() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7}});
    intervalDomain.inComplement(100, v, 7);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval20() throws InvocationTargetException, IllegalAccessException {
    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 2);
    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval21() throws InvocationTargetException, IllegalAccessException {
    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10, 12, 12}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval22() throws InvocationTargetException, IllegalAccessException {
    intervalDomain =
        (IntDomain)
            prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10, 12, 12, 15, 22}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval23() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 1, 2);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval24() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 15}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval25() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10, 12, 33}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 2, 11);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval26() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 20}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 2, 11);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval27() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {3, 6}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 2, 4);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval28() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {1, 20, 22, 24, 26, 28, 30, 32, 34, 36}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 2, 11);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval29() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {3, 6}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 2, 5);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval30() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intervalDomain.inComplement(100, v, 1, 2);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval31() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intervalDomain.inComplement(100, v, 2, 4);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval32() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intervalDomain.inComplement(100, v, 2, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval33() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 20}});
    intervalDomain.inComplement(100, v, 2, 11);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval34() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {3, 6}});
    intervalDomain.inComplement(100, v, 2, 4);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval35() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {3, 5}});
    intervalDomain.inComplement(100, v, 2, 4);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval36() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intervalDomain.inComplement(100, v, 1, 9);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval37() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.inComplement(100, v, 25, 50);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval38() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5, 35);
    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval39() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.inComplement(100, v, 5, 11);
    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval40() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 11, 41);
    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval41() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 0, 3, 6, 7, 18}});
    intervalDomain.inComplement(100, v, 2, 4);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval42() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {18, 20, 22, 23}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 18, 22);
    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval43() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 0, 4, 4, 16, 26}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5, 17);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval44() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 3, 6);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval37b() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.in(100, v, 11, 50);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval46() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.in(100, v, 35, 50);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval47() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.in(100, v, 9, 11);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval48() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.in(100, v, 9, 21);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval49() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.in(100, v, 9, 31);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval50() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.in(100, v, 11, 31);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval51() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.inMax(100, v, 11); // in(100, v, 29, 41);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval52() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.inMax(100, v, 21); // in(100, v, 29, 41);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval53() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.inMax(100, v, 32); // in(100, v, 29, 41);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval54() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.inMin(200, v, 19);
    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval55() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.inMin(200, v, 21);
    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval56() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.inShift(100, v, intervalDomain, 2);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval57() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.inShift(100, v, intervalDomain, 15);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval58() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.inValue(100, v, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval59() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 11, 13, 15}});
    intervalDomain.in(100, v, 14, 15);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval60() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 10, 12, 20, 22, 22}});
    intervalDomain.in(100, v, 10, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval61() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 10, 12, 20, 22, 22}});
    intervalDomain.in(100, v, 22, 23);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval62() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 10, 12, 12, 22, 22}});
    intervalDomain.in(100, v, 12, 20);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval63() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 10, 12, 12, 22, 22}});
    intervalDomain.in(100, v, 10, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval64() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
    intervalDomain.in(100, v, 10, 10);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval65() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 11, 13, 15}});
    intervalDomain.in(100, v, 10, 11);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval66() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 11, 13, 15}});
    intervalDomain.in(100, v, 14, 15);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval67() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 11, 13, 15}});
    intervalDomain.in(100, v, 9, 14);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval68() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 11}});
    intervalDomain.in(100, v, 11, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval69() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 11}});
    intervalDomain.in(100, v, 10, 10);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval70() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 12}});
    intervalDomain.in(100, v, 11, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval71() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 12, 14, 21}});
    intervalDomain.inShift(100, v, intervalDomain, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval72() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 1, 3, 3}});
    intervalDomain.in(100, v, -1, 1);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval73() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 1, 3, 3}});
    intervalDomain.in(100, v, -1, 2);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval74() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {-10, -10, 14, 21}});
    intervalDomain.inShift(100, v, intervalDomain, 6);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval75() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {-2, -2, -1, -1}});
    intervalDomain.inShift(100, v, intervalDomain, 1);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval76() throws InvocationTargetException, IllegalAccessException {

    intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {-10, 10}});
    intervalDomain.inShift(100, v, intervalDomain, 5);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval77() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {-10, -5, -3, 10}});
    intervalDomain.inShift(100, v, intervalDomain, 5);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval78() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {-10, -5, -3, 10}});
    intervalDomain.in(100, v, -10, -10);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval79() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {-10, -5, -3, 10}});
    intervalDomain.in(100, v, -9, 10);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval80() throws InvocationTargetException, IllegalAccessException {

    intervalDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {-10, -5, -3, 10}});
    intervalDomain.in(100, v, -9, 9);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval81() throws InvocationTargetException, IllegalAccessException {

    IntDomain intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
    intDomain.inShift(100, v, intDomain, 1);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval82() throws InvocationTargetException, IllegalAccessException {

    IntDomain intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    intDomain.inShift(100, v, intDomain, 1);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval83() throws InvocationTargetException, IllegalAccessException {

    IntDomain intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
    intDomain.inShift(100, v, intDomain, 1);

    verify(v).domainHasChanged(IntDomain.BOUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval84() throws InvocationTargetException, IllegalAccessException {

    IntDomain intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});

    IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);
    when(intDomain1.contains(anyInt(), anyInt())).thenReturn(true);

    boolean result = intDomain1.contains(intDomain);

    assertThat(result).isTrue();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval86() throws InvocationTargetException, IllegalAccessException {

    IntDomain intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});

    IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

    when(intDomain1.isIntersecting(anyInt(), anyInt())).thenReturn(true);
    when(intDomain1.contains(anyInt())).thenReturn(true);

    boolean result = intDomain1.isIntersecting(intDomain);

    assertThat(result).isTrue();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval87() throws InvocationTargetException, IllegalAccessException {

    IntDomain intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {5, 5}});
    IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

    when(intDomain1.eq(intDomain)).thenReturn(true);
    boolean result = intDomain1.singleton(intDomain);

    assertThat(result).isTrue();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval88() throws InvocationTargetException, IllegalAccessException {

    IntDomain intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {5, 5}});

    IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

    when(intDomain1.getSize()).thenReturn(10);
    boolean result = intDomain1.singleton(intDomain);

    assertThat(result).isFalse();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval89() throws InvocationTargetException, IllegalAccessException {

    IntDomain intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {5, 5}});

    IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

    when(intDomain1.isEmpty()).thenReturn(true);
    boolean result = intDomain1.singleton(intDomain);

    assertThat(result).isFalse();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval188() throws InvocationTargetException, IllegalAccessException {

    IntDomain intDomain =
        (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});

    IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

    when(intDomain1.contains(anyInt(), anyInt())).thenReturn(true, true, true, true, true, false);

    intDomain1.contains(intDomain);
    intDomain1.contains(intDomain);
    intDomain1.contains(intDomain);
    intDomain1.contains(intDomain);
    intDomain1.contains(intDomain);

    boolean result = intDomain1.contains(intDomain);

    assertThat(result).isFalse();
  }

  public IntDomain createDomain(Interval... intervals) {
    IntDomain result = new IntervalDomain();

    for (Interval interval : intervals) {
      result.addDom(new IntervalDomain(interval.min(), interval.max()));
    }

    return result;
  }

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
