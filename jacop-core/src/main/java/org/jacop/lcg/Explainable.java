/*
 * Explainable.java
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

/**
 * A constraint that explains its own propagation for lazy clause generation, with a reason smaller
 * than the generic one of {@link AtomicTrail#genericReason}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface Explainable {

  /**
   * Adds to {@code out} the reason of an atom this constraint propagated: entries before it whose
   * atoms, with the domains at the start of recording, imply it under the constraint.
   *
   * @param trail the trail
   * @param entry the entry of the atom
   * @param out where the reason entries are added
   * @return false when this constraint has no reason of its own for the atom, so the generic reason
   *     is used (anything added is then dropped)
   */
  boolean explain(AtomicTrail trail, int entry, EntryList out);
}
