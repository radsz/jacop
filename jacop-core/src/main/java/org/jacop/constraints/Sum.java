/*
 * Sum.java
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

package org.jacop.constraints;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;

/**
 * Sum constraint implements the summation over several Variable's . It provides the sum from all
 * Variable's on the list.
 *
 * <p>Use when number of variables is large (for example, greater than 30), otherwise use SumInt.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class Sum extends Constraint implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies the variables to be summed. */
  private final IntVar[] list;

  /** It specifies variable sum to store the overall sum of the variables being summed up. */
  private final IntVar sum;

  int guideValue;

  /** The sum of grounded variables. */
  private TimeStamp<Integer> sumGrounded;

  /** The position for the next grounded variable. */
  private TimeStamp<Integer> nextGroundedPosition;

  /**
   * It constructs sum constraint which sums all variables and makes it equal to variable sum.
   *
   * @param list list of variables to be added
   * @param sum the resulting sum
   */
  public Sum(IntVar[] list, IntVar sum) {

    checkInputForNullness(new String[] {"list", "sum"}, new Object[][] {list, {sum}});

    queueIndex = 1;
    numberId = idNumber.incrementAndGet();

    this.sum = sum;
    this.list = Arrays.copyOf(list, list.length);

    setScope(Stream.concat(Arrays.stream(list), Stream.of(sum)));
  }

  /**
   * It creates a sum constraints which sums all variables and makes it equal to variable sum.
   *
   * @param list variables being summed up.
   * @param sum the sum variable.
   */
  public Sum(List<? extends IntVar> list, IntVar sum) {
    this(list.toArray(IntVar[]::new), sum);
  }

  @Override
  public void consistency(Store store) {

    int pointer = nextGroundedPosition.value();
    long sumGroundedLocal = sumGrounded.value();

    do {
      store.propagationHasOccurred = false;
      long[] result = collectGroundedAndBounds(pointer, sumGroundedLocal);
      pointer = (int) result[0];
      sumGroundedLocal = result[1];
      long lMin = result[2];
      long lMax = result[3];

      applySumDomainAndPropagateToVariables(store, pointer, lMin, lMax);
    } while (store.propagationHasOccurred);

    nextGroundedPosition.update(pointer);
    sumGrounded.update(long2int(sumGroundedLocal));
  }

  private long[] collectGroundedAndBounds(int pointer, long sumGroundedLocal) {
    long lMin = sumGroundedLocal;
    long lMax = lMin;
    long sumJustGrounded = 0;

    for (int i = pointer; i < list.length; i++) {
      IntDomain currentDomain = list[i].domain;
      if (currentDomain.singleton()) {
        if (pointer < i) {
          IntVar grounded = list[i];
          list[i] = list[pointer];
          list[pointer] = grounded;
        }
        pointer++;
        sumJustGrounded += currentDomain.min();
        continue;
      }
      lMin += currentDomain.min();
      lMax += currentDomain.max();
    }

    sumGroundedLocal += sumJustGrounded;
    lMin += sumJustGrounded;
    lMax += sumJustGrounded;

    return new long[] {pointer, sumGroundedLocal, lMin, lMax};
  }

  private void applySumDomainAndPropagateToVariables(
      Store store, int pointer, long lMin, long lMax) {
    boolean needAdaptMin = sum.min() > lMin;
    boolean needAdaptMax = sum.max() < lMax;

    sum.domain.in(store.level, sum, long2int(lMin), long2int(lMax));
    store.propagationHasOccurred = false;

    if (needAdaptMin && !needAdaptMax) {
      propagateMinToVariables(store, pointer, lMax);
    } else if (!needAdaptMin && needAdaptMax) {
      propagateMaxToVariables(store, pointer, lMin);
    } else if (needAdaptMin && needAdaptMax) {
      propagateMinMaxToVariables(store, pointer, lMin, lMax);
    }
  }

  private void propagateMinToVariables(Store store, int pointer, long lMax) {
    for (int i = pointer; i < list.length; i++) {
      IntVar v = list[i];
      v.domain.inMin(store.level, v, long2int(sum.min() - lMax + v.max()));
    }
  }

  private void propagateMaxToVariables(Store store, int pointer, long lMin) {
    for (int i = pointer; i < list.length; i++) {
      IntVar v = list[i];
      v.domain.inMax(store.level, v, long2int(sum.max() - lMin + v.min()));
    }
  }

  private void propagateMinMaxToVariables(Store store, int pointer, long lMin, long lMax) {
    for (int i = pointer; i < list.length; i++) {
      IntVar v = list[i];
      v.domain.in(
          store.level,
          v,
          long2int(sum.min() - lMax + v.max()),
          long2int(sum.max() - lMin + v.min()));
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  // registers the constraint in the constraint store
  @Override
  public void impose(Store store) {

    sumGrounded = new TimeStamp<>(store, 0);
    nextGroundedPosition = new TimeStamp<>(store, 0);

    super.impose(store);
  }

  @Override
  public boolean satisfied() {

    if (!grounded()) {
      return false;
    }

    int sumAll = 0;
    for (IntVar v : list) {
      sumAll += v.min();
    }

    return sumAll == sum.min();
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : sum( [");
    appendArrayToString(result, list);
    result.append("], ").append(sum).append(" )");

    return result.toString();
  }

  @Override
  public Constraint getGuideConstraint() {

    IntVar proposedVariable = (IntVar) getGuideVariable();
    return proposedVariable != null ? new XeqC(proposedVariable, guideValue) : null;
  }

  @Override
  public int getGuideValue() {
    return guideValue;
  }

  @Override
  public Var getGuideVariable() {
    int[] guideValueOut = new int[1];
    Var result = AbstractSum.computeGuideVariable(list, guideValueOut);
    guideValue = guideValueOut[0];
    return result;
  }
}
