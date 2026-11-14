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
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.ReifiedExplanation;
import org.jacop.util.QueueForward;

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
public class ImpliesNot extends AbstractReifiedConstraint implements Copyable<ImpliesNot> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private final QueueForward<PrimitiveConstraint> queueForward;

  /**
   * It constructs the implication {@code b = 0 => c}.
   *
   * @param b the 0/1 variable whose value 0 enforces c.
   * @param c the constraint which must hold if the variable is 0.
   */
  public ImpliesNot(IntVar b, PrimitiveConstraint c) {

    super(b, c);
    numberId = idNumber.incrementAndGet();
    setScope(Stream.concat(c.arguments().stream(), Stream.of(b)));
    setConstraintScope(c);
    queueForward = new QueueForward<>(c, arguments());
    this.queueIndex = c.queueIndex;
  }

  @Override
  public void consistency(Store store) {

    if (c.satisfied()) {
      removeConstraint();
    } else if (c.notSatisfied()) {
      b.domain.inValue(store.level, b, 1);
      removeConstraint();
    } else if (b.min() == 1) {
      removeConstraint();
    } else if (b.max() == 0) {
      c.consistency(store);
    }
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    if (v != b
        && (consistencyPruningEvents == null || !consistencyPruningEvents.containsKey(v))
        && isSimpleNestedConstraintOver(v)) {
      // as in Implies: c.notSatisfied() is decided before b is fixed, c.consistency() after
      return Math.max(
          IntDomain.GROUND,
          Math.max(c.getConsistencyPruningEvent(v), c.getNestedPruningEvent(v, false)));
    }
    return super.getConsistencyPruningEvent(v);
  }

  @Override
  public int getNestedPruningEvent(Var v, boolean mode) {
    return super.getConsistencyPruningEvent(v);
  }

  @Override
  protected int getNestedPropagationEvent(Var v) {
    return isSimpleNestedConstraintOver(v) ? c.getConsistencyPruningEvent(v) : Domain.NONE;
  }

  @Override
  public boolean notSatisfied() {
    return b.max() == 0 && c.notSatisfied();
  }

  @Override
  public void notConsistency(Store store) {

    // b first: c may share b, and c.notConsistency() must see it fixed
    b.domain.inValue(store.level, b, 0);
    c.notConsistency(store);
  }

  @Override
  public boolean satisfied() {

    return (b.max() == 0 && c.satisfied()) || b.min() == 1;
  }

  @Override
  public String toString() {

    return id() + " : ImpliesNot(" + b + ", " + c + " )";
  }

  @Override
  public void queueVariable(int level, Var variable) {
    queueForward.queueForward(level, variable);
  }

  @Override
  public ImpliesNot copy(VarMap map) {
    return new ImpliesNot(map.get(b), Copyable.copyOf(c, map));
  }

  @Override
  public boolean canCopy() {
    return Copyable.canCopy(c);
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
