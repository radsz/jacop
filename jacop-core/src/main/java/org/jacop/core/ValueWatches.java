/*
 * ValueWatches.java
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
 * The constraints watching a variable for being fixed to 0 or to 1, with an int tag per watch that
 * is handed back to the constraint. They are kept in the variable, see {@link Store#watchValue(Var,
 * int, Constraint, int)}. Like the watched literals of a SAT solver, the watches are not restored
 * on backtracking.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
final class ValueWatches {

  /*
   * One field per watched value instead of arrays indexed by the value: a fired watch reads the
   * list straight from this object, without first reading an inner array object (a pointer hop
   * and a bounds check fewer per access).
   */

  /** The watching constraints of value 0. */
  Constraint[] constraints0 = new Constraint[2];

  /** The watching constraints of value 1. */
  Constraint[] constraints1 = new Constraint[2];

  /** The tags of the watches of value 0. */
  int[] tags0 = new int[2];

  /** The tags of the watches of value 1. */
  int[] tags1 = new int[2];

  /** The number of watches of value 0. */
  int size0;

  /** The number of watches of value 1. */
  int size1;

  void add(int value, Constraint c, int tag) {
    if (value == 0) {
      int n = size0;
      if (n == constraints0.length) {
        constraints0 = Arrays.copyOf(constraints0, 2 * n);
        tags0 = Arrays.copyOf(tags0, 2 * n);
      }
      constraints0[n] = c;
      tags0[n] = tag;
      size0 = n + 1;
    } else {
      int n = size1;
      if (n == constraints1.length) {
        constraints1 = Arrays.copyOf(constraints1, 2 * n);
        tags1 = Arrays.copyOf(tags1, 2 * n);
      }
      constraints1[n] = c;
      tags1[n] = tag;
      size1 = n + 1;
    }
  }

  /** Returns the watching constraints of a value, the first {@link #size(int)} entries are used. */
  Constraint[] constraints(int value) {
    return value == 0 ? constraints0 : constraints1;
  }

  /** Returns the tags of the watches of a value. */
  int[] tags(int value) {
    return value == 0 ? tags0 : tags1;
  }

  /** Returns the number of watches of a value. */
  int size(int value) {
    return value == 0 ? size0 : size1;
  }
}
