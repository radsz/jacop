/*
 * PbModel.java
 * <p>
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

package org.jacop.lcg;

import org.jacop.core.IntVar;

/**
 * The pseudo-Boolean model that {@link PbEncodable} constraints write to. Each integer variable
 * stands for its order literals {@code [x >= v]} and value literals {@code [x = v]}, so a
 * constraint is stated over the variables themselves.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface PbModel {

  /**
   * Adds a linear relation.
   *
   * @param form the relation
   */
  void linear(LinearForm form);

  /**
   * Adds a linear relation that holds when a 0/1 variable is 1 and, for an equivalence, whose
   * negation holds when it is 0.
   *
   * @param b the 0/1 variable
   * @param form the relation
   * @param equivalence true for b = 1 if and only if the relation holds, false for an implication
   */
  void reified(IntVar b, LinearForm form, boolean equivalence);

  /**
   * Adds a clause over 0/1 variables: one of the positive ones is 1 or one of the negative ones is
   * 0.
   *
   * @param positive the variables of which one may be 1
   * @param negative the variables of which one may be 0
   */
  void clause(IntVar[] positive, IntVar[] negative);
}
