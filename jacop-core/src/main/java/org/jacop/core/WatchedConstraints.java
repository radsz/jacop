/*
 * WatchedConstraints.java
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
package org.jacop.core;

import java.util.Arrays;
import org.jacop.constraints.Constraint;

/**
 * The constraints that watch a variable as a watched literal, see {@link
 * Store#registerWatchedLiteralConstraint(Var, Constraint)}, in the order they started to watch it
 * and without duplicates. They are kept in the variable, so waking them needs no map lookup.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
final class WatchedConstraints {

  /** The watching constraints; the first size entries are used. */
  Constraint[] constraints = new Constraint[2];

  /** The number of watching constraints. */
  int size;

  /** Adds a constraint at the end unless it already watches the variable. */
  void add(Constraint c) {
    for (int i = 0; i < size; i++) {
      if (constraints[i] == c) {
        return;
      }
    }
    if (size == constraints.length) {
      constraints = Arrays.copyOf(constraints, 2 * size);
    }
    constraints[size++] = c;
  }

  /** Removes a constraint, keeping the order of the others. */
  void remove(Constraint c) {
    for (int i = 0; i < size; i++) {
      if (constraints[i] == c) {
        System.arraycopy(constraints, i + 1, constraints, i, size - i - 1);
        constraints[--size] = null;
        return;
      }
    }
  }
}
