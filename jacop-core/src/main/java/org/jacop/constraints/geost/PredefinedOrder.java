/*
 * PredefinedOrder.java
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

package org.jacop.constraints.geost;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.Arrays;

/**
 * It provides a very simple lexicographical order based on the dimension ordering, with the
 * possibility to choose the most significant dimension.
 *
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 * @version 5.0
 */
public class PredefinedOrder implements LexicographicalOrder {

  /**
   * It stores the ordering of dimensions without taking most significant dimension into account.
   */
  final int[] masterOrdering;

  /**
   * It stores the initial position of dimensions in the ordering array. It does not reflect shift
   * due to most significant dimension.
   */
  final int[] dimensionPosition;

  /**
   * It stores the position of dimensions in the ordering starting from most significant dimension
   * to the least significant one.
   */
  final int[] actualDimensionOrder;

  /** It stores currently the most significant dimension. */
  int mostSignificantDimension;

  /**
   * It specifies the comparison of k-dimensional point comparator based on the dimension ordering
   * and the most significant dimension.
   *
   * @param ordering how dimensions are stored within each compared point.
   * @param mostSignificantDimension the most significant dimension
   */
  public PredefinedOrder(int[] ordering, int mostSignificantDimension) {

    this.masterOrdering = ordering;
    this.mostSignificantDimension = mostSignificantDimension;

    dimensionPosition = new int[ordering.length];

    for (int i = 0; i < dimensionPosition.length; i++) {
      for (int j = 0; j < ordering.length; j++) {
        if (ordering[j] == i) {
          dimensionPosition[i] = j;
          break;
        }
      }
    }

    actualDimensionOrder = new int[ordering.length];
    recomputeActualDimensionOrder();

    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  /**
   * It checks the invariants for this order.
   *
   * @return it returns string describing the violated invariant, or null if everything is in order.
   */
  public String checkInvariants() {

    if (masterOrdering == null || masterOrdering.length == 0) {
      return "Invalid ordering " + Arrays.toString(masterOrdering);
    }

    if (mostSignificantDimension < 0) {
      return "The most significant dimension is negative";
    }

    if (mostSignificantDimension >= masterOrdering.length) {
      return "most significant dimension larger than or equal to total number of dimensions";
    }

    return null;
  }

  private void recomputeActualDimensionOrder() {

    int k = masterOrdering.length;
    int shift = dimensionPosition[mostSignificantDimension];

    for (int i = 0; i < k; i++) {
      actualDimensionOrder[i] = masterOrdering[(i + shift) % k];
    }

    if (ASSERTS_ENABLED && !(actualDimensionOrder[0] == mostSignificantDimension)) {
      throw new IllegalStateException(String.valueOf("wrong setup of precedence levels"));
    }
  }

  /**
   * Compares two k-dimensional points lexicographically based on the current dimension ordering.
   *
   * @param p1 the first point.
   * @param p2 the second point.
   * @return -1 if p1 is less than p2, 1 if greater, or 0 if equal.
   */
  public int compare(int[] p1, int[] p2) {

    if (ASSERTS_ENABLED && !(p1.length == p2.length)) {
      throw new IllegalStateException(String.valueOf("dimension mismatch"));
    }

    for (int i = 0; i < masterOrdering.length; i++) {
      int lexI = actualDimensionOrder[i];
      if (p1[lexI] < p2[lexI]) {
        return -1;
      } else if (p1[lexI] > p2[lexI]) {
        return 1;
      }
    }

    return 0;
  }

  /**
   * Returns the dimension at the given precedence level.
   *
   * @param precedenceLevel the precedence level (0 = most significant).
   * @return the dimension index at the given precedence level.
   */
  public int dimensionAt(int precedenceLevel) {
    return actualDimensionOrder[precedenceLevel];
  }

  /**
   * Returns the precedence level of the given dimension in the current ordering.
   *
   * @param dimension the dimension index to look up.
   * @return the precedence level (0 = most significant).
   */
  public int precedenceOf(int dimension) {
    // note: this can be optimized, there should be a relationship between the relations.
    // But since this function is never called, I will not lose time implementing it better

    for (int i = 0; i < masterOrdering.length; i++) {
      if (actualDimensionOrder[i] == dimension) {
        return i;
      }
    }

    if (ASSERTS_ENABLED && !(false)) {
      throw new IllegalStateException(String.valueOf("unreachable code"));
    }
    return 0;
  }

  /**
   * Returns the currently most significant dimension.
   *
   * @return the most significant dimension index.
   */
  public int getMostSignificantDimension() {
    return mostSignificantDimension;
  }

  /**
   * Sets the most significant dimension and recomputes the ordering.
   *
   * @param d the new most significant dimension index.
   */
  public void setMostSignificantDimension(int d) {
    this.mostSignificantDimension = d;
    recomputeActualDimensionOrder();
    if (ASSERTS_ENABLED && !(checkInvariants() == null)) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  /** {@inheritDoc} */
  public String toString() {
    return Arrays.toString(masterOrdering);
  }

  /**
   * Returns the master dimension ordering array.
   *
   * @return the master ordering of dimensions.
   */
  public int[] masterOrdering() {
    return masterOrdering;
  }
}
