/*
 * ReifiedExplanation.java
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

/**
 * Explanations of a reification {@code b <=> c}, or an implication {@code b => c}, from the
 * explanations of c: b is explained by the entailment or disentailment of c, an atom of c's
 * variables by c's own explanation (or that of its negation) and the value of b.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class ReifiedExplanation {

  private ReifiedExplanation() {}

  /**
   * Adds to {@code out} the reason of an entry made by the reification.
   *
   * @param trail the trail
   * @param entry the entry
   * @param b the 0/1 variable, not among c's variables
   * @param c the explanations of the reified constraint
   * @param equivalence true for {@code b <=> c}, false for {@code b => c}
   * @param out where the reason entries are added
   * @return false when there is no such reason
   */
  public static boolean explain(
      AtomicTrail trail, int entry, IntVar b, Explainable c, boolean equivalence, EntryList out) {
    if (trail.variable(entry) == b) {
      int kind = trail.kind(entry);
      boolean one = kind == AtomicTrail.GE || kind == AtomicTrail.NE && trail.value(entry) == 0;
      return c.explainEntailment(trail, entry, one, out);
    }
    if (trail.minBefore(b, entry) >= 1) {
      trail.addLowerBound(b, entry, out);
      return c.explain(trail, entry, out);
    }
    if (equivalence && trail.maxBefore(b, entry) <= 0) {
      trail.addUpperBound(b, entry, out);
      return c.explainNegated(trail, entry, out);
    }
    return false;
  }

  /**
   * Adds to {@code out} the reason of a failure of the reification now.
   *
   * @param trail the trail
   * @param b the 0/1 variable, not among c's variables
   * @param c the explanations of the reified constraint
   * @param equivalence true for {@code b <=> c}, false for {@code b => c}
   * @param out where the reason entries are added
   * @return false when there is no such reason
   */
  public static boolean explainFailure(
      AtomicTrail trail, IntVar b, Explainable c, boolean equivalence, EntryList out) {
    int now = trail.size();
    int mark = out.size();
    if (trail.minBefore(b, now) >= 1) {
      trail.addLowerBound(b, now, out);
      if (c.explainFailure(trail, out) || c.explainEntailment(trail, now, false, out)) {
        return true;
      }
    } else if (equivalence && trail.maxBefore(b, now) <= 0) {
      trail.addUpperBound(b, now, out);
      if (c.explainNegatedFailure(trail, out) || c.explainEntailment(trail, now, true, out)) {
        return true;
      }
    }
    out.truncate(mark);
    return false;
  }
}
