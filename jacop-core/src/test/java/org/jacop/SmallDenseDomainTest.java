package org.jacop;

import static org.assertj.core.api.Assertions.assertThat;
import static org.mockito.Mockito.anyInt;
import static org.mockito.Mockito.lenient;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
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
import org.mockito.ArgumentCaptor;
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

  // the domains prepared by the test, with their bounds when they were prepared
  private final List<IntDomain> prepared = new ArrayList<>();
  private final List<int[]> preparedBounds = new ArrayList<>();

  private IntDomain prepared(int[] intervals) throws Exception {
    IntDomain d = (IntDomain) prepareMethod.invoke(this, new Object[] {intervals});
    prepared.add(d);
    preparedBounds.add(new int[] {d.min(), d.max()});
    return d;
  }

  /**
   * Verifies the one event of a change of the bounds. A change of the minimum only (or of the
   * maximum only) may be reported as MIN_EVENT (MAX_EVENT) instead of BOUND; a directional event is
   * accepted when a prepared domain changed that bound only.
   */
  private void verifyBoundEvent() {
    ArgumentCaptor<Integer> reported = ArgumentCaptor.forClass(Integer.class);
    verify(v).domainHasChanged(reported.capture());
    int actual = reported.getValue();
    if (actual == IntDomain.MIN_EVENT || actual == IntDomain.MAX_EVENT) {
      boolean minOnly = false;
      boolean maxOnly = false;
      // a domain changed at a later level than its stamp is replaced by a new one in the variable
      for (int i = 0; i < 2 * prepared.size(); i++) {
        IntDomain d = i < prepared.size() ? prepared.get(i) : v.domain;
        if (d == null || d.isEmpty()) {
          continue;
        }
        int[] before = preparedBounds.get(i % prepared.size());
        minOnly |= d.min() > before[0] && d.max() == before[1];
        maxOnly |= d.max() < before[1] && d.min() == before[0];
      }
      assertThat(actual == IntDomain.MIN_EVENT ? minOnly : maxOnly)
          .as("event " + actual + " for a change that is not of one bound only")
          .isTrue();
    } else {
      assertThat(actual).isEqualTo(IntDomain.BOUND);
    }
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testContains(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    log.info("Contains function test");
    IntDomain testedDomain = prepared(new int[] {1, 2});

    assertThat(testedDomain.contains(createDomain(new Interval(0, 0)))).isFalse();
    assertThat(testedDomain.contains(createDomain(new Interval(1, 1)))).isTrue();

    testedDomain = prepared(new int[] {-3, 4, 5, 5, 9, 10});

    log.info("Test Complement function");
    assertThat(testedDomain.contains(createDomain(new Interval(1, 2), new Interval(6, 6))))
        .isFalse();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testComplement(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    log.info("Complement function test");
    IntDomain testedDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    assertThat(testedDomain.complement())
        .hasToString("{" + IntDomain.MIN_INT + "..0, 4, 8..11, 19.." + IntDomain.MAX_INT + "}");
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testGetElementAt(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    log.info("GetElementAt function test");
    IntDomain testedDomain = prepared(new int[] {1, 2});
    assertThat(testedDomain.getElementAt(0)).isOne();
    assertThat(testedDomain.getElementAt(1)).isEqualTo(2);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testIntersect(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    log.info("Intersect function test");

    IntDomain testedDomain = prepared(new int[] {1, 2});

    IntDomain goldenResultDomain = prepared(new int[] {2, 2});
    assertThat(testedDomain.intersect(2, 3)).hasToString(goldenResultDomain.toString());

    goldenResultDomain = prepared(new int[] {1, 2});
    assertThat(testedDomain.intersect(0, 25)).hasToString(goldenResultDomain.toString());

    goldenResultDomain = prepared(new int[] {1, 2});
    assertThat(testedDomain.intersect(1, 2)).hasToString(goldenResultDomain.toString());

    testedDomain = prepared(new int[] {1, 2});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(2, 4)))).isZero();

    testedDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    goldenResultDomain = prepared(new int[] {2, 3, 5, 7, 12, 14});
    assertThat(testedDomain.intersect(2, 14)).hasToString(goldenResultDomain.toString());

    testedDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    goldenResultDomain = prepared(new int[] {15, 15});
    assertThat(testedDomain.intersect(15, 15)).hasToString(goldenResultDomain.toString());
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testIntersectAdapt(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    log.info("IntersectAdapt function test");
    IntDomain testedDomain = prepared(new int[] {1, 2});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(2, 4)))).isZero();

    testedDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(14, 20)))).isOne();

    testedDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(2, 6)))).isOne();

    testedDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(2, 6), new Interval(8, 15))))
        .isOne();

    testedDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(0, 0), new Interval(20, 28))))
        .isZero();

    testedDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    assertThat(
            testedDomain.intersectAdapt(
                createDomain(new Interval(2, 2), new Interval(5, 5), new Interval(20, 25))))
        .isOne();

    testedDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    assertThat(
            testedDomain.intersectAdapt(
                createDomain(new Interval(1, 3), new Interval(5, 5), new Interval(20, 25))))
        .isOne();

    testedDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    assertThat(
            testedDomain.intersectAdapt(
                createDomain(new Interval(1, 3), new Interval(5, 5), new Interval(13, 18))))
        .isEqualTo(2);

    testedDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(4, 9)))).isOne();

    testedDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(0, 0)))).isZero();

    testedDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(0, 0), new Interval(2, 2))))
        .isZero();

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(2, 2)).isZero();

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(0, 0)).isZero();

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(1, 9)).isOne();

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(0, 26)).isEqualTo(-1);

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(28, 45)).isZero();

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(-4, 3), new Interval(9, 18))))
        .isOne();

    testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.intersectAdapt(createDomain(new Interval(-4, 1)))).isOne();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testIsIntersecting(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

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
  void testSubtract(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    log.info("Subtract function test");
    IntDomain testedDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    IntDomain goldenResultDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {0, 0, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.subtract(1, 3)).hasToString(goldenResultDomain.toString());

    goldenResultDomain =
        (IntDomain)
            prepareMethod.invoke(
                this, new Object[] {new int[] {1, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
    assertThat(testedDomain.subtract(0, 0)).hasToString(goldenResultDomain.toString());

    goldenResultDomain = prepared(new int[] {0, 0});
    assertThat(testedDomain.subtract(1, 26)).hasToString(goldenResultDomain.toString());

    goldenResultDomain = prepared(new int[] {0, 6});
    assertThat(testedDomain.subtract(8, 26)).hasToString(goldenResultDomain.toString());
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testNextValue(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    log.info("NextValue function test");

    IntDomain goldenResultDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    assertThat(goldenResultDomain.nextValue(3)).isEqualTo(5);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testPreviousValue(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    log.info("previousValue function test");

    IntDomain goldenResultDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    assertThat(goldenResultDomain.previousValue(2)).isOne();
  }

  @BeforeEach
  void setUp() {
    intervalDomain = new IntervalDomain();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 2});
    intervalDomain.inComplement(100, v, 2);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval2(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 2});
    intervalDomain.inComplement(100, v, 1);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval3(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 2});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 1);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval4(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    intervalDomain = prepared(new int[] {1, 2, 4, 10});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 2);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval5(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 2, 4, 10});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval6(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    intervalDomain = prepared(new int[] {1, 2, 4, 10});
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval7(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 3, 5, 5, 7, 10});
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval8(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 3, 5, 5, 7, 10});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval9(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {5, 5, 7, 7});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval10(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 3, 5, 7, 9, 20});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval11(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 3, 5, 7, 9, 20});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 1);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval12(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 3, 5, 7, 9, 20});
    intervalDomain.inComplement(100, v, 1);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval13(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 3, 5, 7, 9, 20});
    intervalDomain.inComplement(100, v, 7);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval14(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {0, 0, 2, 2});
    intervalDomain.inComplement(100, v, 0);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval15(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 3, 5, 5});
    intervalDomain.inComplement(100, v, 5);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval16(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 5, 7, 9, 11, 20});
    intervalDomain.inComplement(100, v, 7);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval17(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    intervalDomain = prepared(new int[] {1, 2, 4, 10});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 10);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval18(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 3, 5, 5});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval19(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 3, 5, 7});
    intervalDomain.inComplement(100, v, 7);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval20(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    intervalDomain = prepared(new int[] {1, 2});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 2);
    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval21(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    intervalDomain = prepared(new int[] {1, 2, 4, 10, 12, 12});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval22(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);
    intervalDomain = prepared(new int[] {1, 2, 4, 10, 12, 12, 15, 22});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval23(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 2, 4, 10});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 1, 2);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval24(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 2, 4, 15});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5, 5);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval25(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 2, 4, 10, 12, 33});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 2, 11);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval26(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 20});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 2, 11);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval27(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {3, 6});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 2, 4);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval28(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

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
  void testinterval29(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {3, 6});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 2, 5);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval30(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 2, 4, 10});
    intervalDomain.inComplement(100, v, 1, 2);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval31(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 2, 4, 10});
    intervalDomain.inComplement(100, v, 2, 4);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval32(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 2, 4, 10});
    intervalDomain.inComplement(100, v, 2, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval33(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 20});
    intervalDomain.inComplement(100, v, 2, 11);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval34(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {3, 6});
    intervalDomain.inComplement(100, v, 2, 4);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval35(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {3, 5});
    intervalDomain.inComplement(100, v, 2, 4);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval36(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 2, 4, 10});
    intervalDomain.inComplement(100, v, 1, 9);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval37(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.inComplement(100, v, 25, 50);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval38(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5, 35);
    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval39(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.inComplement(100, v, 5, 11);
    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval40(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 11, 41);
    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval41(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {0, 0, 3, 6, 7, 18});
    intervalDomain.inComplement(100, v, 2, 4);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval42(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {18, 20, 22, 23});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 18, 22);
    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval43(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {0, 0, 4, 4, 16, 26});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 5, 17);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval44(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 2, 4, 10});
    intervalDomain.setStamp(100);
    intervalDomain.inComplement(100, v, 3, 6);

    verify(v).domainHasChanged(IntDomain.ANY);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval37b(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.in(100, v, 11, 50);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval46(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.in(100, v, 35, 50);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval47(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.in(100, v, 9, 11);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval48(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.in(100, v, 9, 21);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval49(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.in(100, v, 9, 31);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval50(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.in(100, v, 11, 31);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval51(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.inMax(100, v, 11); // in(100, v, 29, 41);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval52(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.inMax(100, v, 21); // in(100, v, 29, 41);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval53(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.inMax(100, v, 32); // in(100, v, 29, 41);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval54(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.inMin(200, v, 19);
    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval55(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.inMin(200, v, 21);
    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval56(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.inShift(100, v, intervalDomain, 2);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval57(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.inShift(100, v, intervalDomain, 15);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval58(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.inValue(100, v, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval59(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 11, 13, 15});
    intervalDomain.in(100, v, 14, 15);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval60(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 10, 12, 20, 22, 22});
    intervalDomain.in(100, v, 10, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval61(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 10, 12, 20, 22, 22});
    intervalDomain.in(100, v, 22, 23);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval62(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 10, 12, 12, 22, 22});
    intervalDomain.in(100, v, 12, 20);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval63(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 10, 12, 12, 22, 22});
    intervalDomain.in(100, v, 10, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval64(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 20, 30, 40});
    intervalDomain.in(100, v, 10, 10);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval65(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 11, 13, 15});
    intervalDomain.in(100, v, 10, 11);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval66(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 11, 13, 15});
    intervalDomain.in(100, v, 14, 15);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval67(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 11, 13, 15});
    intervalDomain.in(100, v, 9, 14);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval68(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 11});
    intervalDomain.in(100, v, 11, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval69(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 11});
    intervalDomain.in(100, v, 10, 10);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval70(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 12});
    intervalDomain.in(100, v, 11, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval71(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {10, 12, 14, 21});
    intervalDomain.inShift(100, v, intervalDomain, 11);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval72(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 1, 3, 3});
    intervalDomain.in(100, v, -1, 1);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval73(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {1, 1, 3, 3});
    intervalDomain.in(100, v, -1, 2);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval74(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {-10, -10, 14, 21});
    intervalDomain.inShift(100, v, intervalDomain, 6);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval75(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {-2, -2, -1, -1});
    intervalDomain.inShift(100, v, intervalDomain, 1);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval76(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {-10, 10});
    intervalDomain.inShift(100, v, intervalDomain, 5);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval77(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {-10, -5, -3, 10});
    intervalDomain.inShift(100, v, intervalDomain, 5);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval78(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {-10, -5, -3, 10});
    intervalDomain.in(100, v, -10, -10);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval79(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {-10, -5, -3, 10});
    intervalDomain.in(100, v, -9, 10);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval80(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    intervalDomain = prepared(new int[] {-10, -5, -3, 10});
    intervalDomain.in(100, v, -9, 9);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval81(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain intDomain = prepared(new int[] {1, 2});
    intDomain.inShift(100, v, intDomain, 1);

    verify(v).domainHasChanged(IntDomain.GROUND);
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval82(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain intDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    intDomain.inShift(100, v, intDomain, 1);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval83(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain intDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});
    intDomain.inShift(100, v, intDomain, 1);

    verifyBoundEvent();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval84(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain intDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});

    IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);
    // a SmallDenseDomain argument is enumerated value by value, an IntervalDomain by intervals
    lenient().when(intDomain1.contains(anyInt(), anyInt())).thenReturn(true);
    lenient().when(intDomain1.contains(anyInt())).thenReturn(true);

    boolean result = intDomain1.contains(intDomain);

    assertThat(result).isTrue();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval86(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain intDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});

    IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

    // a SmallDenseDomain argument is enumerated value by value, an IntervalDomain by intervals
    lenient().when(intDomain1.isIntersecting(anyInt(), anyInt())).thenReturn(true);
    lenient().when(intDomain1.contains(anyInt())).thenReturn(true);

    boolean result = intDomain1.isIntersecting(intDomain);

    assertThat(result).isTrue();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval87(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain intDomain = prepared(new int[] {5, 5});
    IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

    when(intDomain1.eq(intDomain)).thenReturn(true);
    boolean result = intDomain1.singleton(intDomain);

    assertThat(result).isTrue();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval88(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain intDomain = prepared(new int[] {5, 5});

    IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

    when(intDomain1.getSize()).thenReturn(10);
    boolean result = intDomain1.singleton(intDomain);

    assertThat(result).isFalse();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval89(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain intDomain = prepared(new int[] {5, 5});

    IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

    when(intDomain1.isEmpty()).thenReturn(true);
    boolean result = intDomain1.singleton(intDomain);

    assertThat(result).isFalse();
  }

  @ParameterizedTest
  @MethodSource("parametricTest")
  void testinterval188(String prepareMethodName) throws Exception {
    setupPrepareMethod(prepareMethodName);

    IntDomain intDomain = prepared(new int[] {1, 3, 5, 7, 12, 18});

    IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

    // a SmallDenseDomain argument is enumerated value by value, an IntervalDomain by intervals
    lenient()
        .when(intDomain1.contains(anyInt(), anyInt()))
        .thenReturn(true, true, true, true, true, false);
    lenient().when(intDomain1.contains(anyInt())).thenReturn(true, true, true, true, true, false);

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
