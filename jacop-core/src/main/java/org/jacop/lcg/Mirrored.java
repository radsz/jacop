/*
 * Mirrored.java
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

package org.jacop.lcg;

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * A variable that is not an integer variable but whose domain lazy clause generation can follow
 * through integer variables that mirror it, such as a set variable mirrored by the membership of
 * its elements and its cardinality. Every change of its domain changes its mirror at once, with the
 * propagating constraint as reason, so the atoms of the mirror describe its domain and stand for it
 * in generic reasons.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface Mirrored {

  /**
   * Returns the integer variables that mirror this variable's domain.
   *
   * @return the mirror, or null when the variable has none
   */
  IntVar[] mirror();

  /**
   * Creates in another store a copy of this variable, with its domain when the mirror was made,
   * kept equal to copies of its mirror. {@link ExplanationChecker} checks the explanations of
   * constraints on this variable with it.
   *
   * @param target the store of the copy
   * @param mirror the copies of the mirror's variables, in the order of {@link #mirror()}
   * @return the copy
   */
  Var copyMirrored(Store target, IntVar[] mirror);
}
