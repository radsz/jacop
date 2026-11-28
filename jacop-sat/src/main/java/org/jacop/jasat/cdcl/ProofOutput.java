/*
 * ProofOutput.java
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

package org.jacop.jasat.cdcl;

/**
 * Where {@link CdclSolver} writes its proof: every clause it derives or adds, before it uses it,
 * and every clause it deletes. Literals are the solver's internal ones; {@link CdclSolver#toDimacs}
 * turns one into its DIMACS literal.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface ProofOutput {

  /**
   * Records a clause the solver derived or added.
   *
   * @param lits the array holding the clause
   * @param from the position of its first literal
   * @param n its number of literals; 0 is the empty clause
   */
  void add(int[] lits, int from, int n);

  /**
   * Records a clause the solver deleted.
   *
   * @param lits the array holding the clause
   * @param from the position of its first literal
   * @param n its number of literals
   */
  void delete(int[] lits, int from, int n);
}
