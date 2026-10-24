/*
 * EqBool.java
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

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * If all x's are equal to each other then result variable is equal 1. Otherwise, result variable is
 * equal to zero. It restricts the domains of all variables to be either 0 or 1.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class EqBool extends PrimitiveConstraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies x variables in the constraint. */
  private final IntVar[] list;

  /** It specifies variable result in the constraint. */
  private final IntVar result;

  List<Constraint> constraints;

  /**
   * It constructs eqBool.
   *
   * @param list list of x's which must all be equal to the same value to make result equal 1.
   * @param result variable which is equal 0 if x's contain different values.
   */
  public EqBool(IntVar[] list, IntVar result) {

    checkInputForNullness(new String[] {"list", "result"}, list, new Object[] {result});

    numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.result = result;
    setScope(Stream.concat(Arrays.stream(list), Stream.of(result)));

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  /**
   * It constructs eqBool.
   *
   * @param list list of variables which must all be equal to the same value to make result equal 1.
   * @param result variable which is equal 0 if variables from list contain different values.
   */
  public EqBool(List<? extends IntVar> list, IntVar result) {
    this(list.toArray(IntVar[]::new), result);
  }

  /**
   * It checks invariants required by the constraint. Namely that boolean variables have boolean
   * domain.
   *
   * @return the string describing the violation of the invariant, null otherwise.
   */
  public String checkInvariants() {
    return checkBooleanDomains(list);
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  /**
   * Enforces consistency for this constraint.
   *
   * @param store the constraint store in which the constraint is imposed.
   */
  public void consistency(Store store) {
    propagateEqBool(store, false);
  }

  /**
   * Unified propagation logic for consistency and notConsistency.
   *
   * @param store the constraint store in which the constraint is imposed.
   * @param negated if true, handles the negated constraint logic.
   */
  private void propagateEqBool(Store store, boolean negated) {

    int[] counts = countX0X1AndIndex01();
    int x1 = counts[0];
    int x0 = counts[1];
    int index01 = counts[2];

    boolean resultIsPositive = negated ? result.max() == 0 : result.min() == 1;

    if (resultIsPositive) {
      applyResultPositivePropagation(store, negated, x0, x1, index01);
    } else {
      boolean resultIsNegative = negated ? result.min() == 1 : result.max() == 0;
      if (resultIsNegative) {
        applyResultNegativePropagation(store, negated, x0, x1, index01);
      }
    }

    if (x0 > 0 && x1 > 0) {
      result.domain.inValue(store.level, result, negated ? 1 : 0);
    }
    if (x0 == list.length || x1 == list.length) {
      result.domain.inValue(store.level, result, negated ? 0 : 1);
    }
  }

  private int[] countX0X1AndIndex01() {
    int x1 = 0;
    int x0 = 0;
    int index01 = 0;
    for (int i = 0; i < list.length; i++) {
      if (list[i].min() == 1) {
        x1++;
      } else if (list[i].max() == 0) {
        x0++;
      } else {
        index01 = i;
      }
    }
    return new int[] {x1, x0, index01};
  }

  private void applyResultPositivePropagation(
      Store store, boolean negated, int x0, int x1, int index01) {
    if (negated) {
      applyResultPositivePropagationNegated(store, x0, x1, index01);
    } else {
      applyResultPositivePropagationNonNegated(store, x0, x1);
    }
  }

  private void applyResultPositivePropagationNegated(Store store, int x0, int x1, int index01) {
    if (x0 == 0 && x1 == list.length - 1) {
      list[index01].domain.inValue(store.level, list[index01], 0);
    }
    if (x1 == 0 && x0 == list.length - 1) {
      list[index01].domain.inValue(store.level, list[index01], 1);
    }
  }

  private void applyResultPositivePropagationNonNegated(Store store, int x0, int x1) {
    if (x0 > 0) {
      for (IntVar intVar : list) {
        intVar.domain.inValue(store.level, intVar, 0);
      }
    }
    if (x1 > 0) {
      for (IntVar intVar : list) {
        intVar.domain.inValue(store.level, intVar, 1);
      }
    }
  }

  private void applyResultNegativePropagation(
      Store store, boolean negated, int x0, int x1, int index01) {
    if (negated) {
      applyResultNegativePropagationNegated(store, x0, x1);
    } else {
      applyResultNegativePropagationNonNegated(store, x0, x1, index01);
    }
  }

  private void applyResultNegativePropagationNegated(Store store, int x0, int x1) {
    if (x0 > 0) {
      for (IntVar intVar : list) {
        intVar.domain.inValue(store.level, intVar, 0);
      }
    }
    if (x1 > 0) {
      for (IntVar intVar : list) {
        intVar.domain.inValue(store.level, intVar, 1);
      }
    }
  }

  private void applyResultNegativePropagationNonNegated(Store store, int x0, int x1, int index01) {
    if (x0 == 0 && x1 == list.length - 1) {
      list[index01].domain.inValue(store.level, list[index01], 0);
    }
    if (x1 == 0 && x0 == list.length - 1) {
      list[index01].domain.inValue(store.level, list[index01], 1);
    }
  }

  @Override
  public void notConsistency(Store store) {

    do {

      store.propagationHasOccurred = false;
      propagateEqBool(store, true);

    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean satisfied() {
    return checkEqBoolSatisfaction(false);
  }

  /**
   * Unified satisfaction check for satisfied and notSatisfied.
   *
   * @param negated if true, handles the negated constraint logic.
   * @return true if the constraint is satisfied (or not satisfied if negated).
   */
  private boolean checkEqBoolSatisfaction(boolean negated) {

    if (!result.singleton()) {
      return false;
    }

    if (result.max() == 0) {
      return checkEqBoolSatisfactionWhenResultMax0(negated);
    }

    if (result.min() == 1) {
      return negated ? checkNotSatisfiedResultMin1() : checkSatisfiedResultMin1();
    }
    return false;
  }

  private boolean checkEqBoolSatisfactionWhenResultMax0(boolean negated) {
    int x1 = 0;
    int x0 = 0;
    for (IntVar intVar : list) {
      if (intVar.min() == 1) {
        x1++;
      } else if (intVar.max() == 0) {
        x0++;
      }
      if (x0 > 0 && x1 > 0) {
        return !negated;
      }
    }
    return negated && (x0 == list.length || x1 == list.length);
  }

  private boolean checkNotSatisfiedResultMin1() {
    int x1 = 0;
    int x0 = 0;
    for (IntVar intVar : list) {
      if (intVar.min() == 1) {
        x1++;
      } else if (intVar.max() == 0) {
        x0++;
      }
      if (x0 > 0 && x1 > 0) {
        return true;
      }
    }
    return false;
  }

  private boolean checkSatisfiedResultMin1() {
    if (!grounded()) {
      return false;
    }
    for (int i = 0; i < list.length - 1; i++) {
      if (list[i].value() != list[i + 1].value()) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean notSatisfied() {
    return checkEqBoolSatisfaction(true);
  }

  @Override
  public String toString() {

    StringBuilder resultString = new StringBuilder(id());

    resultString.append(" : eqBool( ");
    for (int i = 0; i < list.length; i++) {
      resultString.append(list[i]);
      if (i < list.length - 1) {
        resultString.append(", ");
      }
    }
    resultString.append(", ");
    resultString.append(result);
    resultString.append(")");
    return resultString.toString();
  }

  @Override
  public List<Constraint> decompose(Store store) {

    constraints = new ArrayList<>();

    PrimitiveConstraint[] eqConstraints = new PrimitiveConstraint[list.length];

    IntervalDomain booleanDom = new IntervalDomain(0, 1);

    for (int i = 0; i < eqConstraints.length - 1; i++) {
      eqConstraints[0] = new XeqY(list[i], list[i + 1]);
      constraints.add(new In(list[i], booleanDom));
    }

    constraints.add(new In(result, booleanDom));

    constraints.add(new Eq(new And(eqConstraints), new XeqC(result, 1)));

    return constraints;
  }

  @Override
  public void imposeDecomposition(Store store) {

    if (constraints == null) {
      constraints = decompose(store);
    }

    for (Constraint c : constraints) {
      store.impose(c, queueIndex);
    }
  }
}
