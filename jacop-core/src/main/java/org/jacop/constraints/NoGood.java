/*
 * NoGood.java
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
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * NoGood constraints implements a constraint which disallows given combination of values for given
 * variables. NoGoods are special constraints as they can be only triggered only when all variables
 * except one are grounded and equal to disallow values. This allows efficient implementation based
 * on watched literals idea from SAT community.
 *
 * <p>Do not be fooled by watched literals, if you add thousands of no-goods then traversing even
 * 1/10 of them if they are watched by variable which has been grounded can slow down search
 * considerably.
 *
 * <p>NoGoods constraints are imposed at all levels once added. Do not use in subsearches, as it
 * will not take into account the assignments performed in master search.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class NoGood extends Constraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);
  private static final boolean DEBUG = false;

  /** It specifies a list of variables in no-good constraint. */
  protected IntVar[] listOfVars;

  /** It specifies a list of values in no-good constraint. */
  protected int[] listOfValues;

  private IntVar firstWatch;
  private int firstValue;
  private IntVar secondWatch;
  private int secondValue;

  /**
   * It creates a no-good constraint.
   *
   * @param listOfVars the scope of the constraint.
   * @param listOfValues no-good values which all-together assignment to variables within constraint
   *     scope is a no-good.
   */
  public NoGood(IntVar[] listOfVars, int[] listOfValues) {

    commonInitialization(listOfVars, listOfValues);
  }

  /**
   * It creates a no-good constraint.
   *
   * @param listOfVars the scope of the constraint.
   * @param listOfValues no-good values which all-together assignment to variables within constraint
   *     scope is a no-good.
   */
  public NoGood(List<? extends IntVar> listOfVars, List<Integer> listOfValues) {

    checkInputForNullness(
        new String[] {"listOfVars", "listOfValues"}, new Object[] {listOfVars, listOfValues});
    commonInitialization(
        listOfVars.toArray(IntVar[]::new), listOfValues.stream().mapToInt(i -> i).toArray());
  }

  private void commonInitialization(IntVar[] listOfVars, int[] listOfValues) {

    checkInputForNullness("listOfVars", listOfVars);
    checkInputForNullness("listOfValues", listOfValues);

    if (listOfVars.length != listOfValues.length) {
      throw new IllegalArgumentException("Length of listOfVars is different from listOfValues");
    }

    this.queueIndex = 0;
    this.numberId = idNumber.incrementAndGet();
    this.listOfVars = Arrays.copyOf(listOfVars, listOfVars.length);
    this.listOfValues = Arrays.copyOf(listOfValues, listOfValues.length);

    setScope(listOfVars);
  }

  @Override
  public void consistency(Store store) {

    if (DEBUG) {
      log.debug("Start {}", this);
    }

    if (firstWatch == secondWatch) {
      handleSameWatchSpecialCase(store);
      return;
    }

    if (isNoGoodSatisfiedByFirstOrSecondWatch()) {
      return;
    }

    if (oneWatchIsSingletonAndSomeVarDisagrees()) {
      return;
    }

    if (firstWatch.getSize() == 1) {
      tryReplaceFirstWatch(store);
      return;
    }

    if (secondWatch.getSize() == 1) {
      tryReplaceSecondWatch(store);
    }

    if (DEBUG) {
      log.debug("End{}", this);
    }
  }

  private void handleSameWatchSpecialCase(Store store) {
    if (DEBUG) {
      log.debug("Special cases of noGood constraints have occured");
    }
    if (listOfVars.length != 1) {
      for (int i = 0; i < listOfVars.length; i++) {
        if (listOfVars[i].getSize() == 1 && listOfVars[i].value() != listOfValues[i]) {
          return;
        }
      }
      for (IntVar listOfVar : listOfVars) {
        if (listOfVar.getSize() != 1 && listOfVar != firstWatch) {
          throw new IllegalStateException(
              "The NoGood learnt for one model is used in different model (model created across many store levels)");
        }
      }
    }
    firstWatch.dom().inComplement(store.level, firstWatch, firstValue);
  }

  private boolean isNoGoodSatisfiedByFirstOrSecondWatch() {
    if (firstWatch.getSize() == 1 && firstWatch.value() != firstValue) {
      return true;
    }
    if (secondWatch.getSize() == 1 && secondWatch.value() != secondValue) {
      return true;
    }
    return false;
  }

  private boolean oneWatchIsSingletonAndSomeVarDisagrees() {
    if (firstWatch.getSize() != 1 && secondWatch.getSize() != 1) {
      return false;
    }
    for (int i = 0; i < listOfVars.length; i++) {
      if (listOfVars[i].singleton() && !listOfVars[i].singleton(listOfValues[i])) {
        return true;
      }
    }
    return false;
  }

  private void tryReplaceFirstWatch(Store store) {
    for (int i = 0; i < listOfVars.length; i++) {
      if (listOfVars[i] != secondWatch && listOfVars[i].getSize() != 1) {
        store.deregisterWatchedLiteralConstraint(firstWatch, this);
        firstWatch = listOfVars[i];
        firstValue = listOfValues[i];
        store.registerWatchedLiteralConstraint(firstWatch, this);
        return;
      }
    }
    secondWatch.dom().inComplement(store.level, secondWatch, secondValue);
    if (DEBUG) {
      log.debug("{}", secondWatch);
    }
  }

  private void tryReplaceSecondWatch(Store store) {
    for (int i = 0; i < listOfVars.length; i++) {
      if (listOfVars[i] != firstWatch && listOfVars[i].getSize() != 1) {
        store.deregisterWatchedLiteralConstraint(secondWatch, this);
        secondWatch = listOfVars[i];
        secondValue = listOfValues[i];
        store.registerWatchedLiteralConstraint(secondWatch, this);
        return;
      }
    }
    firstWatch.dom().inComplement(store.level, firstWatch, firstValue);
    if (DEBUG) {
      log.debug("{}", firstWatch);
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  // registers the constraint in the constraint store
  // using watched literals functionality.
  @Override
  public void impose(Store store) {

    if (store.watchedConstraints == null) {
      store.watchedConstraints = Var.createEmptyPositioning();
    }

    if (listOfVars.length == 1) {
      imposeSingleVariableNoGood(store);
      return;
    }

    int watchCount = findFirstTwoNonSingletonWatches();
    if (watchCount < 2) {
      imposeAsOneVariableNoGoodWhenFewWatches(store, watchCount);
    } else {
      store.registerWatchedLiteralConstraint(firstWatch, this);
      store.registerWatchedLiteralConstraint(secondWatch, this);
    }
  }

  private void imposeSingleVariableNoGood(Store store) {
    firstWatch = secondWatch = listOfVars[0];
    firstValue = listOfValues[0];
    store.registerWatchedLiteralConstraint(firstWatch, this);
    store.addChanged(this);
  }

  private int findFirstTwoNonSingletonWatches() {
    int i = 0;
    for (int j = 0; j < listOfVars.length; j++) {
      IntVar v = listOfVars[j];
      if (v.getSize() != 1 && i < 2) {
        if (i == 0) {
          firstWatch = v;
          firstValue = listOfValues[j];
        } else {
          secondWatch = v;
          secondValue = listOfValues[j];
        }
        i++;
      }
    }
    return i;
  }

  private void imposeAsOneVariableNoGoodWhenFewWatches(Store store, int watchCount) {
    secondWatch = firstWatch;
    secondValue = firstValue;

    for (IntVar _ : listOfVars) {
      if (listOfVars[watchCount].getSize() == 1
          && listOfVars[watchCount].value() != listOfValues[watchCount]) {
        return;
      }
    }

    store.registerWatchedLiteralConstraint(firstWatch, this);
    store.addChanged(this);
  }

  /**
   * This function does nothing as constraints can not be removed for a given level. In addition,
   * watched literals mechanism makes sure that constraint is not put in the queue when it can not
   * propagate.
   */
  @Override
  public void removeConstraint() {

    // This function does not do anything on purpose.
    // if constraint is removed from variable then it is removed for all
    // levels.
    // This is not how this function is being used, as constraint is removed
    // only on level on which it is satisfied.

  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : noGood([");

    for (int i = 0; i < listOfVars.length; i++) {
      if (listOfVars[i] == firstWatch || listOfVars[i] == secondWatch) {
        result.append("@");
      }
      result.append(listOfVars[i]);
      if (i < listOfVars.length - 1) {
        result.append(", ");
      }
    }
    result.append("], [");

    for (int i = 0; i < listOfValues.length; i++) {
      result.append(listOfValues[i]);
      if (i < listOfValues.length - 1) {
        result.append(", ");
      }
    }
    result.append("] )");
    return result.toString();
  }
}
