/*
 * RewrittenNested.java
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

import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * The primitive constraint of a reification or an implication whose Boolean variable is fixed
 * during search ({@link Constraint#rewriteTo}): it propagates the nested constraint, or its
 * negation, on the nested constraint's own events, without the outer constraint's checks of
 * entailment and disentailment at every call and without waking on events only those checks need.
 * Gecode rewrites its reified propagators the same way once the control variable is assigned
 * ({@code GECODE_REWRITE}; C. Schulte, G. Tack and M. Z. Lagerkvist, Modeling and Programming with
 * Gecode, part "Programming propagators", propagator rewriting).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class RewrittenNested extends Constraint implements SatisfiedPresent {

  /**
   * Whether a fixed Boolean variable rewrites a reification or implication to its nested constraint
   * (org.jacop.rewrite.reified).
   */
  static final boolean ENABLED =
      Boolean.parseBoolean(System.getProperty("org.jacop.rewrite.reified", "true"));

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private final PrimitiveConstraint c;

  private final boolean positive;

  /**
   * Creates the constraint.
   *
   * @param c the nested constraint.
   * @param positive true to propagate c, false to propagate its negation.
   */
  RewrittenNested(PrimitiveConstraint c, boolean positive) {
    this.c = c;
    this.positive = positive;
    this.queueIndex = c.queueIndex;
    numberId = idNumber.incrementAndGet();
  }

  @Override
  public Set<Var> arguments() {
    return c.arguments();
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    return positive ? c.getConsistencyPruningEvent(v) : c.getNotConsistencyPruningEvent(v);
  }

  @Override
  protected int getSubscriptionPruningEvent(Var v) {
    return positive ? c.getSubscriptionPruningEvent(v) : c.getNotConsistencyPruningEvent(v);
  }

  @Override
  public void queueVariable(int level, Var var) {
    c.queueVariable(level, var);
  }

  @Override
  public void consistency(Store store) {
    if (positive) {
      c.consistency(store);
    } else {
      c.notConsistency(store);
    }
    if (c.isEntailed()) {
      removeConstraint();
    }
  }

  @Override
  public boolean satisfied() {
    return positive ? c.satisfied() : c.notSatisfied();
  }

  @Override
  public String toString() {
    return id() + " : RewrittenNested(" + (positive ? "" : "not ") + c + " )";
  }
}
