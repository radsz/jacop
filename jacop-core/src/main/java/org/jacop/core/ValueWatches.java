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

  /** The watching constraints, for value 0 and value 1. */
  final Constraint[][] constraints = {new Constraint[2], new Constraint[2]};

  /** The tags of the watches. */
  final int[][] tags = {new int[2], new int[2]};

  /** The number of watches for each value. */
  final int[] size = new int[2];

  void add(int value, Constraint c, int tag) {
    int n = size[value];
    if (n == constraints[value].length) {
      constraints[value] = Arrays.copyOf(constraints[value], 2 * n);
      tags[value] = Arrays.copyOf(tags[value], 2 * n);
    }
    constraints[value][n] = c;
    tags[value][n] = tag;
    size[value] = n + 1;
  }
}
