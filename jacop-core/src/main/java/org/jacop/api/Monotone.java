/*
 * Monotone.java
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

package org.jacop.api;

import org.jacop.core.Var;

/**
 * A constraint that can say in which direction a variable may move without breaking it. Presolve
 * uses it to find reifications whose Boolean is only ever wanted true (or only false) by the rest
 * of the model, and to weaken such a reification to an implication.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public interface Monotone {

  /** How the satisfaction of a constraint depends on one of its variables. */
  enum Direction {
    /** Raising the variable, the other variables unchanged, never breaks a satisfied constraint. */
    UP,
    /** Lowering the variable never breaks a satisfied constraint. */
    DOWN,
    /** Neither is known. */
    NONE;

    /**
     * Returns the opposite direction.
     *
     * @return UP for DOWN, DOWN for UP, NONE for NONE.
     */
    public Direction negate() {
      return this == UP ? DOWN : this == DOWN ? UP : NONE;
    }

    /**
     * Combines the directions of two occurrences of one variable.
     *
     * @param other the direction of the other occurrence.
     * @return the direction both occurrences agree on, or NONE.
     */
    public Direction and(Direction other) {
      return this == other ? this : NONE;
    }
  }

  /**
   * Returns the direction in which a variable may move without breaking this constraint, for the
   * domains of the moment: a direction that depends on a variable being fixed holds as long as it
   * stays fixed, so presolve asks only at its root.
   *
   * @param v a variable of the constraint.
   * @return the direction, NONE when unknown.
   */
  Direction monotonicity(Var v);

  /**
   * Tells whether a variable occurs in an array.
   *
   * @param vars the array.
   * @param v the variable.
   * @return true if some element is v.
   */
  static boolean contains(Var[] vars, Var v) {
    for (Var x : vars) {
      if (x == v) {
        return true;
      }
    }
    return false;
  }
}
