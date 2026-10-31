/*
 * PbEncodable.java
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

/**
 * A constraint that can state itself as pseudo-Boolean constraints, for the OPB model a VeriPB
 * proof of an LCG search is checked against. Unit propagation over the encoding must derive every
 * explanation the constraint gives, since the proof states each one as a {@code rup} step. Linear
 * constraints with a {@link LinearForm} need not implement it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface PbEncodable {

  /**
   * Writes the constraint to a pseudo-Boolean model.
   *
   * @param model where the constraint goes
   * @return false when this constraint (for example a subclass) has no encoding
   */
  boolean encode(PbModel model);
}
