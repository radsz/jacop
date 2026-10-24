/*
 * AndBoolVector.java
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

import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * If all x's are equal 1 then result variable is equal 1 too. Otherwise, result variable is equal
 * to zero. It restricts the domain of all x as well as result to be between 0 and 1.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class AndBoolVector extends AbstractBoolVector {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs AndBoolVector.
   *
   * @param list list of x's which must all be equal 1 to make result equal 1.
   * @param result variable which is equal 0 if any of x is equal to zero.
   */
  public AndBoolVector(IntVar[] list, IntVar result) {
    super(idNumber, list, result);
  }

  /**
   * It constructs AndBoolVector.
   *
   * @param list list of x's which must all be equal 1 to make result equal 1.
   * @param result variable which is equal 0 if any of x is equal to zero.
   */
  public AndBoolVector(List<? extends IntVar> list, IntVar result) {
    super(idNumber, list, result);
  }

  @Override
  protected PrimitiveConstraint createCombiner(PrimitiveConstraint[] boolConstraints) {
    return new And(boolConstraints);
  }

  /**
   * Enforces consistency for this constraint.
   *
   * @param store the constraint store in which the constraint is imposed.
   */
  public void consistency(Store store) {
    propagateAndVector(store, false);
  }

  @Override
  public void notConsistency(Store store) {
    propagateAndVector(store, true);
  }

  private void propagateAndVector(Store store, boolean negated) {
    int allTrueVal = negated ? 0 : 1;
    int foundFalseVal = negated ? 1 : 0;
    int lastRemainingVal = negated ? 1 : 0;

    int start = position.value();
    final int index01 = l - 1;

    boolean allForced = negated ? result.max() == 0 : result.min() == 1;
    if (allForced) {
      forceAllToListToTrue(store, start);
      return;
    }

    if (propagateLoopFindsFalse(store, foundFalseVal, negated, start)) {
      return;
    }
    start = position.value();
    if (start == l) {
      result.domain.inValue(store.level, result, allTrueVal);
      return;
    }

    if (result.max() == 0 && start == l - 1) {
      list[index01].domain.inValue(store.level, list[index01], lastRemainingVal);
    }

    if ((l - start) < 3) {
      queueIndex = 0;
    }
  }

  private void forceAllToListToTrue(Store store, int start) {

    for (int i = start; i < l; i++) {
      list[i].domain.inValue(store.level, list[i], 1);
    }
  }

  /**
   * Scans list from start for a false (max==0); if found, sets result and optionally removes
   * constraint and returns true. Otherwise updates position with new start and returns false.
   */
  private boolean propagateLoopFindsFalse(
      Store store, int foundFalseVal, boolean negated, int start) {

    for (int i = start; i < l; i++) {
      if (list[i].min() == 1) {
        swap(start, i);
        start++;
      } else if (list[i].max() == 0) {
        result.domain.inValue(store.level, result, foundFalseVal);
        if (!negated) {
          removeConstraint();
        }
        return true;
      }
    }
    position.update(start);
    return false;
  }

  @Override
  public boolean satisfied() {
    return checkSatisfaction(false);
  }

  @Override
  public boolean notSatisfied() {
    return checkSatisfaction(true);
  }

  private boolean checkSatisfaction(boolean negated) {

    int start = position.value();

    // For satisfied: result==1 means check all are 1; result==0 means check any is 0
    // For notSatisfied: result==0 means check all are 1; result==1 means check any is 0
    boolean checkAllOnes = negated ? result.max() == 0 : result.min() == 1;
    boolean checkAnyZero = negated ? result.min() == 1 : result.max() == 0;

    if (checkAllOnes) {
      return checkAllOnesSatisfied(start);
    }
    if (checkAnyZero) {
      return checkAnyZeroSatisfied(start);
    }

    return false;
  }

  private boolean checkAllOnesSatisfied(int start) {

    for (int i = start; i < l; i++) {
      if (list[i].min() != 1) {
        return false;
      }
      swap(start, i);
      start++;
      position.update(start);
    }
    return true;
  }

  private boolean checkAnyZeroSatisfied(int start) {

    for (int i = start; i < l; i++) {
      if (list[i].max() == 0) {
        return true;
      }
      if (list[i].min() == 1) {
        swap(start, i);
        start++;
        position.update(start);
      }
    }
    return false;
  }

  @Override
  public String toString() {

    StringBuilder resultString = new StringBuilder(id());

    resultString.append(" : andBool([ ");
    appendArrayToString(resultString, list);
    resultString.append("], ");
    resultString.append(result);
    resultString.append(")");
    return resultString.toString();
  }
}
