/*
 * VariableNode.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.floats.constraints.linear;

import org.jacop.core.Store;
import org.jacop.floats.core.FloatVar;

/** Variable node for linear constraint tree. */
public abstract class VariableNode extends BinaryNode {

  Store store;
  FloatVar v;
  byte rel;

  /** The linear constraint of this leaf, or null when it is not known. */
  Linear owner;

  /** The position of {@link #v} in the list of {@link #owner}. */
  int position = -1;

  /**
   * Narrows the variable of this leaf, telling the owner its position first, so that {@link
   * Linear#queueVariable} finds the changed variable without a lookup.
   *
   * @param min the new minimum.
   * @param max the new maximum.
   */
  final void narrow(double min, double max) {
    if (owner != null) {
      owner.narrowing = position;
    }
    v.domain.in(store.level, v, min, max);
  }
}
