/*
 * SetExplanation.java
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

package org.jacop.set.constraints;

import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.set.core.SetVar;

/**
 * A set constraint explained for lazy clause generation element by element, by {@link
 * SetExplanation}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
interface ElementwiseExplainable extends Explainable {

  /**
   * Returns the relation of the constraint on the memberships of an element in its sets.
   *
   * @return the relation, or null when the explanations are generic
   */
  SetExplanation.Relation relation();

  /**
   * Returns the sets of the constraint, in the order of the relation's memberships.
   *
   * @return the sets
   */
  SetVar[] explainedSets();

  @Override
  default boolean explain(AtomicTrail trail, int entry, EntryList out) {
    SetExplanation.Relation r = relation();
    return r != null && SetExplanation.explain(trail, entry, explainedSets(), r, out);
  }

  @Override
  default boolean explainFailure(AtomicTrail trail, EntryList out) {
    SetExplanation.Relation r = relation();
    return r != null && SetExplanation.explainFailure(trail, explainedSets(), r, out);
  }
}
