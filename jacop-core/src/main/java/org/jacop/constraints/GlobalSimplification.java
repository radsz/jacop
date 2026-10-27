/*
 * GlobalSimplification.java
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

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import org.jacop.core.IntVar;

/**
 * Global-specific presolve shared by several constraint classes ({@link
 * org.jacop.api.Simplifiable}), at a fixpoint of the store. Each method returns the replacing
 * constraints, an empty list if the constraint holds, or null if there is nothing simpler.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class GlobalSimplification {

  private GlobalSimplification() {}

  /**
   * All different: a fixed variable whose value no other variable can take is left out; with at
   * most one variable left the constraint holds.
   */
  static List<Constraint> allDifferent(IntVar[] list, Function<IntVar[], Constraint> factory) {
    if (!distinct(list)) {
      return null;
    }
    List<IntVar> kept = new ArrayList<>(list.length);
    for (IntVar x : list) {
      if (!x.singleton() || takenByOther(list, x)) {
        kept.add(x);
      }
    }
    if (kept.size() == list.length) {
      return null;
    }
    return kept.size() <= 1 ? List.of() : List.of(factory.apply(kept.toArray(new IntVar[0])));
  }

  private static boolean takenByOther(IntVar[] list, IntVar x) {
    int v = x.value();
    for (IntVar y : list) {
      if (y != x && y.domain.contains(v)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Maximum (or minimum, with {@code maximum} false): a variable that can be no larger than the
   * smallest value of another one cannot be the maximum and is left out; with one variable left the
   * constraint is an equality.
   */
  static List<Constraint> extremum(
      IntVar[] list, IntVar result, boolean maximum, Function<IntVar[], Constraint> factory) {
    if (list.length == 0 || !distinct(list) || contains(list, result)) {
      return null;
    }
    // the variable with the largest guaranteed value
    IntVar best = list[0];
    for (IntVar x : list) {
      if (maximum ? x.min() > best.min() : x.max() < best.max()) {
        best = x;
      }
    }
    List<IntVar> kept = new ArrayList<>(list.length);
    for (IntVar x : list) {
      if (x == best || (maximum ? x.max() > best.min() : x.min() < best.max())) {
        kept.add(x);
      }
    }
    if (kept.size() == list.length) {
      return null;
    }
    if (kept.size() == 1) {
      return List.of(new XeqY(kept.get(0), result));
    }
    return List.of(factory.apply(kept.toArray(new IntVar[0])));
  }

  /**
   * Count of a value: a variable that cannot take the value never counts and is left out; with no
   * variable left the count is zero.
   */
  static List<Constraint> count(
      IntVar[] list, IntVar counter, int value, Function<IntVar[], Constraint> factory) {
    if (contains(list, counter)) {
      return null;
    }
    List<IntVar> kept = new ArrayList<>(list.length);
    for (IntVar x : list) {
      if (x.domain.contains(value)) {
        kept.add(x);
      }
    }
    if (kept.size() == list.length) {
      return null;
    }
    if (kept.isEmpty()) {
      return counter.singleton(0) ? List.of() : null;
    }
    return List.of(factory.apply(kept.toArray(new IntVar[0])));
  }

  static boolean distinct(IntVar[] list) {
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    for (IntVar x : list) {
      if (!seen.add(x)) {
        return false;
      }
    }
    return true;
  }

  static boolean contains(IntVar[] list, IntVar v) {
    for (IntVar x : list) {
      if (x == v) {
        return true;
      }
    }
    return false;
  }
}
