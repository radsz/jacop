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

  /**
   * Adds to {@code out} the reason of a failure of this constraint: entries whose atoms, with the
   * domains at the start of recording, cannot all hold under the constraint.
   *
   * @param trail the trail
   * @param out where the reason entries are added
   * @return false when this constraint has no reason of its own, so the generic one is used
   *     (anything added is then dropped)
   */
  default boolean explainFailure(AtomicTrail trail, EntryList out) {
    return false;
  }

  /**
   * Adds to {@code out} the reason why this constraint was entailed, or disentailed, just before a
   * trail position: entries whose atoms make every assignment of its variables satisfy it (or
   * violate it). A reification uses it to explain the value of its Boolean variable.
   *
   * @param trail the trail
   * @param position the trail position (an entry index, or {@link AtomicTrail#size()} for now)
   * @param entailed true for entailment, false for disentailment
   * @param out where the reason entries are added
   * @return false when this constraint has no such reason
   */
  default boolean explainEntailment(
      AtomicTrail trail, int position, boolean entailed, EntryList out) {
    return false;
  }

  /**
   * Adds to {@code out} the reason of an atom that the negation of this constraint propagated, as a
   * reification does when its Boolean variable is false.
   *
   * @param trail the trail
   * @param entry the entry of the atom
   * @param out where the reason entries are added
   * @return false when this constraint has no such reason
   */
  default boolean explainNegated(AtomicTrail trail, int entry, EntryList out) {
    return false;
  }

  /**
   * Adds to {@code out} the reason of a failure of the negation of this constraint.
   *
   * @param trail the trail
   * @param out where the reason entries are added
   * @return false when this constraint has no such reason
   */
  default boolean explainNegatedFailure(AtomicTrail trail, EntryList out) {
    return false;
  }

  /**
   * Tells whether {@link #explain}, {@link #explainNegated}, {@link #explainEntailment} and the
   * failure explanations check that their reasons imply what they explain, so that they may be
   * asked about an atom this constraint may not have propagated, as a disjunction of constraints
   * does.
   *
   * @return true when the reasons are checked
   */
  default boolean checksReasons() {
    return false;
  }
}
