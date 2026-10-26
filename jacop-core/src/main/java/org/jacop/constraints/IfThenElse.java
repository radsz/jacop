/*
 * IfThenElse.java
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
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.util.QueueForward;

/**
 * Constraint if constraint1 then constraint2 else constraint3 *.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class IfThenElse extends PrimitiveConstraint
    implements UsesQueueVariable, Copyable<IfThenElse>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);
  public final QueueForward<PrimitiveConstraint> queueForward;

  /** It specifies constraint condC in the IfThenElse constraint. */
  private final PrimitiveConstraint condC;

  /** It specifies constraint condC in the IfThenElse constraint. */
  private final PrimitiveConstraint thenC;

  /** It specifies constraint elseC in the IfThenElse constraint. */
  private final PrimitiveConstraint elseC;

  // imposed variable to manifest that constraint has been imposed (top-level)
  // constraint
  boolean imposed;
  Store store;

  /** Set when a variable changes, so consistency() repeats until no part prunes more. */
  private boolean propagation;

  /**
   * It creates ifthenelse constraint.
   *
   * @param condC the condition of the constraint.
   * @param thenC the condition which must be true if the constraint condition is true.
   * @param elseC the condition which must be true if the constraint condition is not true.
   */
  // Constructors
  public IfThenElse(
      PrimitiveConstraint condC, PrimitiveConstraint thenC, PrimitiveConstraint elseC) {

    PrimitiveConstraint[] scope = new PrimitiveConstraint[] {condC, thenC, elseC};
    checkInputForNullness(new String[] {"condC", "thenC", "elseC"}, scope);

    numberId = idNumber.incrementAndGet();

    this.condC = condC;
    this.thenC = thenC;
    this.elseC = elseC;

    setScope(scope);
    setConstraintScope(scope);
    queueForward = new QueueForward<>(new PrimitiveConstraint[] {condC, thenC, elseC}, arguments());
    this.queueIndex =
        Integer.max(Integer.max(condC.queueIndex, thenC.queueIndex), elseC.queueIndex);
  }

  @Override
  public void consistency(Store store) {

    do {
      propagation = false;

      if (condC.satisfied()) {
        thenC.consistency(store);
      } else if (condC.notSatisfied()) {
        elseC.consistency(store);
      }

      if (imposed) {

        if (thenC.notSatisfied()) {
          condC.notConsistency(store);
          elseC.consistency(store);
        }

        if (elseC.notSatisfied()) {
          condC.consistency(store);
          thenC.consistency(store);
        }
      }
    } while (propagation);
  }

  @Override
  public boolean notSatisfied() {
    return (condC.satisfied() && thenC.notSatisfied())
        || (condC.notSatisfied() && elseC.notSatisfied());
  }

  @Override
  public void notConsistency(Store store) {

    if (condC.notSatisfied()) {
      elseC.notConsistency(store);
    }

    if (condC.satisfied()) {
      thenC.notConsistency(store);
    }
  }

  @Override
  public int getNestedPruningEvent(Var v, boolean mode) {

    if (mode) {
      if (consistencyPruningEvents != null) {
        Integer possibleEvent = consistencyPruningEvents.get(v);
        if (possibleEvent != null) {
          return possibleEvent;
        }
      }
    } else {
      if (notConsistencyPruningEvents != null) {
        Integer possibleEvent = notConsistencyPruningEvents.get(v);
        if (possibleEvent != null) {
          return possibleEvent;
        }
      }
    }
    return computeMaxPruningEvent(v, condC, thenC, elseC);
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    throw new IllegalStateException("Not implemented as more precise method exists.");
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {

    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }
    return computeMaxPruningEvent(v, condC, thenC, elseC);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    throw new IllegalStateException("Not implemented as more precise method exists.");
  }

  @Override
  public int getNotConsistencyPruningEvent(Var v) {

    if (notConsistencyPruningEvents != null) {
      Integer possibleEvent = notConsistencyPruningEvents.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }
    return computeMaxPruningEvent(v, condC, thenC, elseC);
  }

  @Override
  public void impose(Store store) {

    super.impose(store);

    this.store = store;
    imposed = true;
  }

  @Override
  public void include(Store store) {
    this.store = store;
    super.include(store);
  }

  @Override
  public boolean satisfied() {
    return (condC.satisfied() && thenC.satisfied()) || (condC.notSatisfied() && elseC.satisfied());
  }

  @Override
  public String toString() {

    return id() + " : IfThenElse(" + condC + ", " + thenC + ", " + elseC + " )";
  }

  @Override
  public void queueVariable(int level, Var variable) {

    propagation = true;
    queueForward.queueForward(level, variable);
  }

  @Override
  public IfThenElse copy(VarMap map) {
    return new IfThenElse(
        Copyable.copyOf(condC, map), Copyable.copyOf(thenC, map), Copyable.copyOf(elseC, map));
  }

  @Override
  public boolean canCopy() {
    return Copyable.canCopyAll(condC, thenC, elseC);
  }

  // the explanations of the three constraints, when all check their reasons
  private Explainable[] lcgParts() {
    if (getClass() != IfThenElse.class
        || !(condC instanceof Explainable c && c.checksReasons())
        || !(thenC instanceof Explainable t && t.checksReasons())
        || !(elseC instanceof Explainable e && e.checksReasons())) {
      return null;
    }
    return new Explainable[] {c, t, e};
  }

  // a part explains the entry only when the entry's variable is one of its own
  private static boolean explains(
      PrimitiveConstraint part, Explainable e, AtomicTrail trail, int entry, EntryList out) {
    return part.arguments().contains(trail.variable(entry)) && e.explain(trail, entry, out);
  }

  /**
   * Explains an atom by the way it can follow: the condition entailed and the then part, the
   * condition disentailed and the else part, or a part disentailed and the others. The parts check
   * their reasons, so a way that does not imply the atom is not taken.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    Explainable[] p = lcgParts();
    if (p == null) {
      return false;
    }
    int mark = out.size();
    if (p[0].explainEntailment(trail, entry, true, out)
        && explains(thenC, p[1], trail, entry, out)) {
      return true;
    }
    out.truncate(mark);
    if (p[0].explainEntailment(trail, entry, false, out)
        && explains(elseC, p[2], trail, entry, out)) {
      return true;
    }
    out.truncate(mark);
    if (p[1].explainEntailment(trail, entry, false, out)) {
      int then = out.size();
      if (condC.arguments().contains(trail.variable(entry))
          && p[0].explainNegated(trail, entry, out)) {
        return true;
      }
      out.truncate(then);
      if (explains(elseC, p[2], trail, entry, out)) {
        return true;
      }
    }
    out.truncate(mark);
    if (p[2].explainEntailment(trail, entry, false, out)) {
      int then = out.size();
      if (explains(condC, p[0], trail, entry, out)) {
        return true;
      }
      out.truncate(then);
      if (explains(thenC, p[1], trail, entry, out)) {
        return true;
      }
    }
    out.truncate(mark);
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    Explainable[] p = lcgParts();
    if (p == null) {
      return false;
    }
    int now = trail.size();
    int mark = out.size();
    // the condition decided and its part failing or disentailed
    for (int side = 0; side < 2; side++) {
      Explainable part = p[1 + side];
      if (p[0].explainEntailment(trail, now, side == 0, out)) {
        int then = out.size();
        if (part.explainFailure(trail, out) || part.explainEntailment(trail, now, false, out)) {
          return true;
        }
        out.truncate(then);
      }
      out.truncate(mark);
    }
    // both parts disentailed
    if (p[1].explainEntailment(trail, now, false, out)
        && p[2].explainEntailment(trail, now, false, out)) {
      return true;
    }
    out.truncate(mark);
    return false;
  }
}
