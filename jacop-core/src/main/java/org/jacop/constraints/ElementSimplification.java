/*
 * ElementSimplification.java
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
import java.util.Optional;
import java.util.function.BiFunction;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;

/**
 * Global-specific presolve of the element constraints ({@link org.jacop.api.Simplifiable}), for
 * {@code list[index - indexOffset] = value} with the list indexed from 1, at a fixpoint of the
 * store.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class ElementSimplification {

  /** Builds an element constraint of the class being simplified over a shorter list. */
  @FunctionalInterface
  interface Factory<L> {
    Constraint element(IntVar index, L list, int indexOffset);
  }

  private ElementSimplification() {}

  /**
   * Simplifies an element constraint over a list of integers:
   *
   * <ul>
   *   <li>if every position the index can take holds the same value, the constraint holds;
   *   <li>if the positions the index can take hold {@code index + c}, or {@code c - index}, it
   *       becomes that equation, which is domain consistent;
   *   <li>otherwise the list is cut to the positions between the index bounds.
   * </ul>
   */
  static List<Constraint> integers(
      IntVar index, int[] list, IntVar value, int indexOffset, Factory<int[]> factory) {
    if (index == value || !indexWithinList(index, list.length, indexOffset)) {
      return null;
    }
    int lo = index.min();
    long first = list[lo - indexOffset - 1];
    boolean constant = true;
    boolean ascending = true;
    boolean descending = true;
    for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
      int i = e.nextElement();
      long v = list[i - indexOffset - 1];
      constant &= v == first;
      ascending &= v - i == first - lo;
      descending &= v + i == first + lo;
    }
    if (constant) {
      // at a fixpoint the value is the one the list holds there
      return value.singleton() && value.value() == first ? List.of() : null;
    }
    if (ascending && fitsInt(first - lo)) {
      int c = (int) (first - lo);
      return List.of(c == 0 ? new XeqY(index, value) : new XplusCeqZ(index, c, value));
    }
    if (descending && fitsInt(first + lo)) {
      return List.of(new XplusYeqC(index, value, (int) (first + lo)));
    }
    return cut(index, list.length, indexOffset, (from, to) -> Arrays.copyOfRange(list, from, to))
        .map(l -> List.of(factory.element(index, l, index.min() - 1)))
        .orElse(null);
  }

  /**
   * Simplifies an element constraint over a list of variables:
   *
   * <ul>
   *   <li>if the index is fixed, the constraint becomes {@code list[index] = value};
   *   <li>if every position the index can take holds a fixed variable, it becomes an element
   *       constraint over integers, built by {@code integers};
   *   <li>otherwise the list is cut to the positions between the index bounds.
   * </ul>
   */
  static List<Constraint> variables(
      IntVar index,
      IntVar[] list,
      IntVar value,
      int indexOffset,
      Factory<IntVar[]> factory,
      Factory<int[]> integers) {
    if (index == value || !indexWithinList(index, list.length, indexOffset)) {
      return null;
    }
    for (IntVar x : list) {
      if (x == index) {
        return null;
      }
    }
    if (index.singleton()) {
      IntVar x = list[index.value() - indexOffset - 1];
      return x == value ? List.of() : List.of(new XeqY(x, value));
    }
    int lo = index.min();
    int hi = index.max();
    boolean fixed = true;
    for (ValueEnumeration e = index.domain.valueEnumeration(); fixed && e.hasMoreElements(); ) {
      IntVar x = list[e.nextElement() - indexOffset - 1];
      fixed = x.singleton() && x != value;
    }
    if (fixed) {
      // positions the index cannot take get any value, the one of the nearest smaller position
      int[] values = new int[hi - lo + 1];
      for (int i = lo; i <= hi; i++) {
        IntVar x = list[i - indexOffset - 1];
        values[i - lo] = index.domain.contains(i) ? x.value() : values[i - lo - 1];
      }
      return List.of(integers.element(index, values, lo - 1));
    }
    return cut(index, list.length, indexOffset, (from, to) -> Arrays.copyOfRange(list, from, to))
        .map(l -> List.of(factory.element(index, l, index.min() - 1)))
        .orElse(null);
  }

  /** At a fixpoint the index is restricted to the positions of the list. */
  private static boolean indexWithinList(IntVar index, int length, int indexOffset) {
    return index.min() >= 1 + indexOffset && index.max() <= length + indexOffset;
  }

  private static <L> Optional<L> cut(
      IntVar index, int length, int indexOffset, BiFunction<Integer, Integer, L> range) {
    int from = index.min() - indexOffset - 1;
    int to = index.max() - indexOffset;
    if (from == 0 && to == length) {
      return Optional.empty();
    }
    return Optional.of(range.apply(from, to));
  }

  private static boolean fitsInt(long v) {
    return v >= Integer.MIN_VALUE && v <= Integer.MAX_VALUE;
  }
}
