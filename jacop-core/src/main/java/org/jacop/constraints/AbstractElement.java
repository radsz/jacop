/*
 * AbstractElement.java
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

import org.jacop.api.Stateful;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * Abstract base class for Element constraints that define a relation list[index - indexOffset] =
 * value. Provides shared fields and methods common to all Element constraint variants.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractElement extends Constraint implements Stateful {

  /** It specifies variable index within an element constraint list[index - indexOffset] = value. */
  protected final IntVar index;

  /** It specifies indexOffset within an element constraint list[index - indexOffset] = value. */
  protected final int indexOffset;

  protected boolean firstConsistencyCheck = true;
  protected int firstConsistencyLevel;

  /**
   * Constructs the common part of an element constraint.
   *
   * @param index variable index
   * @param indexOffset shift applied to index variable.
   */
  protected AbstractElement(IntVar index, int indexOffset) {
    this.index = index;
    this.indexOffset = indexOffset;
  }

  /**
   * Returns the length of the list array.
   *
   * @return length of list array.
   */
  protected abstract int listLength();

  @Override
  public boolean isStateful() {
    return !(index.min() >= 1 + indexOffset && index.max() <= listLength() + indexOffset);
  }

  @Override
  public void removeLevel(int level) {
    if (level == firstConsistencyLevel) {
      firstConsistencyCheck = true;
    }
  }

  /**
   * Common impose logic: calls super.impose and disables firstConsistencyCheck if not stateful.
   *
   * @param store the constraint store.
   */
  protected void imposeInit(Store store) {
    super.impose(store);
    if (!isStateful()) {
      firstConsistencyCheck = false;
    }
  }

  /**
   * Performs the first consistency check initialization: narrows index domain to valid range.
   *
   * @param store the constraint store.
   */
  protected void initFirstConsistencyCheck(Store store) {
    index.domain.in(store.level, index, 1 + indexOffset, listLength() + indexOffset);
    firstConsistencyLevel = store.level;
    firstConsistencyCheck = false;
  }

  /**
   * Checks if two integer variable domains are disjoint.
   *
   * @param v1 the first variable
   * @param v2 the second variable
   * @return true if the domains are disjoint, false otherwise
   */
  protected static boolean disjoint(IntVar v1, IntVar v2) {
    return v1.min() > v2.max() || v2.min() > v1.max() || !v2.domain.isIntersecting(v1.domain);
  }

  /**
   * Checks if an integer variable domain and an integer value are disjoint.
   *
   * @param v1 the variable domain
   * @param v2 the integer value
   * @return true if the domain and value are disjoint, false otherwise
   */
  protected static boolean disjoint(IntDomain v1, int v2) {
    if (v1.min() > v2 || v2 > v1.max()) {
      return true;
    } else {
      return !v1.contains(v2);
    }
  }

  /**
   * Checks if an integer variable and an integer value are disjoint.
   *
   * @param v1 the variable
   * @param v2 the integer value
   * @return true if the variable domain and value are disjoint, false otherwise
   */
  protected static boolean disjoint(IntVar v1, int v2) {
    return disjoint(v1.domain, v2);
  }

  /**
   * Checks if the constraint is satisfied for element constraints with variable lists. The value
   * must be singleton, and for each index in the index domain, the corresponding list element must
   * be singleton and equal to the value.
   *
   * @param list the list of variables
   * @param value the value variable
   * @return true if the constraint is satisfied, false otherwise
   */
  protected boolean satisfiedForVariableList(IntVar[] list, IntVar value) {
    boolean sat = value.singleton();
    if (sat) {
      int v = value.min();
      ValueEnumeration e = index.domain.valueEnumeration();
      while (sat && e.hasMoreElements()) {
        IntVar fdv = list[e.nextElement() - 1 - indexOffset];
        sat = fdv.singleton() && fdv.min() == v;
      }
    }
    return sat;
  }

  /**
   * Checks if the constraint is satisfied for element constraints with integer lists. The value
   * must be singleton, and for each index in the index domain, the corresponding list element must
   * equal the value.
   *
   * @param list the list of integers
   * @param value the value variable
   * @return true if the constraint is satisfied, false otherwise
   */
  protected boolean satisfiedForIntegerList(int[] list, IntVar value) {
    boolean sat = value.singleton();
    if (sat) {
      int v = value.min();
      ValueEnumeration e = index.domain.valueEnumeration();
      while (sat && e.hasMoreElements()) {
        int fdv = list[e.nextElement() - 1 - indexOffset];
        sat = fdv == v;
      }
    }
    return sat;
  }

  /**
   * Builds the toString representation for this element constraint.
   *
   * @param constraintName the name of the specific element constraint variant.
   * @param listArray the list array (int[] or Object[]).
   * @param value the value variable.
   * @param includeOffset whether to include indexOffset in the output.
   * @return string representation of the constraint.
   */
  protected String buildToString(
      String constraintName, Object listArray, Object value, boolean includeOffset) {
    StringBuilder result = new StringBuilder(id());
    result.append(" : ").append(constraintName).append("( ").append(index).append(", [");
    appendList(result, listArray);
    result.append("], ").append(value);
    if (includeOffset) {
      result.append(", ").append(indexOffset);
    }
    result.append(" )");
    return result.toString();
  }

  private void appendList(StringBuilder sb, Object listArray) {
    if (listArray instanceof int[] intArr) {
      for (int i = 0; i < intArr.length; i++) {
        if (i > 0) {
          sb.append(", ");
        }
        sb.append(intArr[i]);
      }
    } else if (listArray instanceof double[] doubleArr) {
      for (int i = 0; i < doubleArr.length; i++) {
        if (i > 0) {
          sb.append(", ");
        }
        sb.append(doubleArr[i]);
      }
    } else if (listArray instanceof Object[] objArr) {
      for (int i = 0; i < objArr.length; i++) {
        if (i > 0) {
          sb.append(", ");
        }
        sb.append(objArr[i]);
      }
    }
  }
}
