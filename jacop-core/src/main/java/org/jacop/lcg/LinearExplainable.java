/*
 * LinearExplainable.java
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
 * A constraint explained through its {@link LinearForm}: its propagation, failures, entailment and
 * negation.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface LinearExplainable extends Explainable {

  /**
   * Returns the constraint as a linear relation.
   *
   * @return the linear form, or null when the constraint is not explained through one (a subclass,
   *     or variables shared in a way the propagator handles differently)
   */
  LinearForm linearForm();

  @Override
  default boolean explain(AtomicTrail trail, int entry, EntryList out) {
    LinearForm f = linearForm();
    return f != null && f.explain(trail, entry, out);
  }

  @Override
  default boolean explainFailure(AtomicTrail trail, EntryList out) {
    LinearForm f = linearForm();
    return f != null && f.explainFailure(trail, out);
  }

  @Override
  default boolean explainEntailment(
      AtomicTrail trail, int position, boolean entailed, EntryList out) {
    LinearForm f = linearForm();
    return f != null && (entailed ? f : f.negated()).explainEntailed(trail, position, out);
  }

  @Override
  default boolean explainNegated(AtomicTrail trail, int entry, EntryList out) {
    LinearForm f = linearForm();
    return f != null && f.negated().explain(trail, entry, out);
  }

  @Override
  default boolean explainNegatedFailure(AtomicTrail trail, EntryList out) {
    LinearForm f = linearForm();
    return f != null && f.negated().explainFailure(trail, out);
  }

  @Override
  default boolean checksReasons() {
    return true;
  }
}
