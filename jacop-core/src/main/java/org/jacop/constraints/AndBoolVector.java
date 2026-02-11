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

    int start = position.value();
    final int index01 = l - 1;

    if (result.min() == 1) {
      for (int i = start; i < l; i++) {
        list[i].domain.inValue(store.level, list[i], 1);
      }
      return;
    }

    for (int i = start; i < l; i++) {
      if (list[i].min() == 1) {
        swap(start, i);
        start++;
      } else if (list[i].max() == 0) {
        result.domain.inValue(store.level, result, 0);
        removeConstraint();
        return;
      }
    }
    position.update(start);

    if (start == l) {
      result.domain.inValue(store.level, result, 1);
      return;
    }

    if (result.max() == 0 && start == l - 1) {
      list[index01].domain.inValue(store.level, list[index01], 0);
    }

    if ((l - start) < 3) {
      queueIndex = 0;
    }
  }

  @Override
  public void notConsistency(Store store) {

    int start = position.value();

    final int index01 = l - 1;

    if (result.max() == 0) {
      for (int i = start; i < l; i++) {
        list[i].domain.inValue(store.level, list[i], 1);
      }
      return;
    }

    for (int i = start; i < l; i++) {
      if (list[i].min() == 1) {
        swap(start, i);
        start++;
      } else if (list[i].max() == 0) {
        result.domain.inValue(store.level, result, 1);
        return;
      }
    }
    position.update(start);

    if (start == l) {
      result.domain.inValue(store.level, result, 0);
      return;
    }

    if (result.max() == 0 && start == l - 1) {
      list[index01].domain.inValue(store.level, list[index01], 1);
    }

    if ((l - start) < 3) {
      queueIndex = 0;
    }
  }

  @Override
  public boolean satisfied() {

    int start = position.value();

    if (result.min() == 1) {
      for (int i = start; i < l; i++) {
        if (list[i].min() != 1) {
          return false;
        } else {
          swap(start, i);
          start++;
          position.update(start);
        }
      }
      return true;
    } else if (result.max() == 0) {
      for (int i = start; i < l; i++) {
        if (list[i].max() == 0) {
          return true;
        } else if (list[i].min() == 1) {
          swap(start, i);
          start++;
          position.update(start);
        }
      }
      return false;
    }

    return false;
  }

  @Override
  public boolean notSatisfied() {

    int start = position.value();

    if (result.max() == 0) {

      for (int i = start; i < l; i++) {
        if (list[i].min() != 1) {
          return false;
        } else {
          swap(start, i);
          start++;
          position.update(start);
        }
      }

      return true;

    } else {

      if (result.min() == 1) {

        for (int i = start; i < l; i++) {
          if (list[i].max() == 0) {
            return true;
          } else if (list[i].min() == 1) {
            swap(start, i);
            start++;
            position.update(start);
          }
        }
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
