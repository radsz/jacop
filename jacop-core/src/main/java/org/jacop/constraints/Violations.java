/*
 * Violations.java
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
import java.util.function.ToIntFunction;
import org.jacop.core.IntVar;

/**
 * Measures shared by the {@link org.jacop.api.Violation} methods of several constraints.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class Violations {

  private Violations() {}

  /** The number of variables whose value another variable before them already has. */
  static long duplicates(IntVar[] list, ToIntFunction<IntVar> value) {
    int[] a = new int[list.length];
    for (int i = 0; i < list.length; i++) {
      a[i] = value.applyAsInt(list[i]);
    }
    Arrays.sort(a);
    long d = 0;
    for (int i = 1; i < a.length; i++) {
      if (a[i] == a[i - 1]) {
        d++;
      }
    }
    return d;
  }

  /** The number of variables that have value v. */
  static int count(IntVar[] list, int v, ToIntFunction<IntVar> value) {
    int c = 0;
    for (IntVar x : list) {
      if (value.applyAsInt(x) == v) {
        c++;
      }
    }
    return c;
  }
}
