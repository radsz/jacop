/*
 * ImpliesNot.java
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

package org.jacop.constraints;

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.ReifiedExplanation;

/**
 * Constraint {@code b = 0 => c}: the implication {@link Implies} with a negated control literal.
 *
 * <p>The FlatZinc front end posts it when it eliminates the control {@code b2} of a half-reified
 * constraint {@code b2 => c} whose only other occurrence is a binary clause {@code b1 \/ b2}:
 * {@code b2} can then take the value of {@code c}, so the two constraints and {@code b2} become
 * {@code not b1 => c}. This is bounded variable elimination of the control (Een and Biere,
 * "Effective preprocessing in SAT through variable and clause elimination", SAT 2005), the
 * enforcement-literal reduction of CP-SAT's presolve.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ImpliesNot extends AbstractImplication implements Copyable<ImpliesNot>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs the implication {@code b = 0 => c}.
   *
   * @param b the 0/1 variable whose value 0 enforces c.
   * @param c the constraint which must hold if the variable is 0.
   */
  public ImpliesNot(IntVar b, PrimitiveConstraint c) {

    super(b, c, 0);
    numberId = idNumber.incrementAndGet();
  }

  @Override
  public String toString() {

    return id() + " : ImpliesNot(" + b + ", " + c + " )";
  }

  @Override
  public ImpliesNot copy(VarMap map) {
    return new ImpliesNot(map.get(b), Copyable.copyOf(c, map));
  }

  // the nested constraint's explanations, when c does not share b
  private Explainable nestedNot() {
    if (!nestedKnown) {
      nestedKnown = true;
      if (c instanceof Explainable e) {
        nested = e;
        for (Var v : c.arguments()) {
          if (v == b) {
            nested = null;
            break;
          }
        }
      }
    }
    return nested;
  }

  private boolean nestedKnown;
  private Explainable nested;

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    Explainable e = nestedNot();
    return e != null && ReifiedExplanation.explainNegatedControl(trail, entry, b, e, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    Explainable e = nestedNot();
    return e != null && ReifiedExplanation.explainNegatedControlFailure(trail, b, e, out);
  }
}
