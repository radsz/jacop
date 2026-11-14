/*
 * Rule.java
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

package org.jacop.presolve;

import java.util.List;
import org.jacop.constraints.Constraint;
import org.jacop.core.Store;

/**
 * A presolve rule. A derivation runs its rules in rounds on the parent store at the level of the
 * derivation, and propagates the parent to a fixpoint after every round, so a rule always sees the
 * domains narrowed by root propagation. When a round changes something (a domain, a constraint
 * imposed or removed, a new variable) the rules run again, because the narrowed domains can make a
 * rule apply that did not before. The rounds stop at a fixpoint or after a budget of rounds.
 *
 * <p>A rule changes the problem only through the parent store and its context:
 *
 * <ul>
 *   <li>it narrows a domain at {@link Context#level()}, which is sound when every solution of the
 *       parent at that level keeps the values left; a {@link org.jacop.core.FailException} thrown
 *       there makes the derivation infeasible;
 *   <li>it imposes a constraint implied by the parent's problem with {@link
 *       Context#impose(Constraint)}; the constraint propagates in the parent from then on and is
 *       copied into the child, so it must be {@link org.jacop.api.Copyable};
 *   <li>it leaves a constraint out of the child with {@link Context#remove(Constraint)}, which is
 *       sound when the constraints left, with the domains, imply it. The parent keeps propagating
 *       it during presolve, and in checking mode it still checks every solution against it.
 * </ul>
 *
 * <p>A rule should be idempotent: run again on a problem it did not change, it changes nothing. A
 * rule that is not makes every round change something, and the rounds then stop at the budget.
 *
 * <p>Each rule has a {@link Timing timing class}, as SCIP's presolvers do. A round runs the fast
 * rules; the medium ones join only when a round of the fast ones found little, and the exhaustive
 * ones only when the medium ones found little too. A round that finds much goes back to the fast
 * rules alone.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@FunctionalInterface
public interface Rule {

  /**
   * Applies the rule once.
   *
   * @param context the parent store and the constraints the child would receive now.
   */
  void apply(Context context);

  /**
   * Returns the timing class of the rule; {@link Timing#FAST} unless a rule says otherwise.
   *
   * @return the timing class.
   */
  default Timing timing() {
    return Timing.FAST;
  }

  /** How costly a rule is, which decides how often the rounds run it. */
  enum Timing {
    /** About linear in the size of the problem: runs in every round. */
    FAST,
    /** Pairwise or graph work, run when the fast rules find little. */
    MEDIUM,
    /** Search-like work under a time budget, such as probing, run when the others find little. */
    EXHAUSTIVE
  }

  /** What a rule sees of a derivation in progress. */
  interface Context {

    /**
     * Returns the parent store, at its fixpoint when the rule starts.
     *
     * @return the parent store.
     */
    Store store();

    /**
     * Returns the level at which the rule narrows domains, the level of the derivation.
     *
     * @return the level.
     */
    int level();

    /**
     * Returns the round, from 1.
     *
     * @return the round.
     */
    int round();

    /**
     * Returns the constraints that the child would receive now: those attached in the parent, not
     * entailed and not removed, in a deterministic order. The list is a snapshot; it does not
     * change when the rule imposes or removes a constraint.
     *
     * @return the constraints.
     */
    List<Constraint> constraints();

    /**
     * Imposes a constraint implied by the parent's problem in the parent, so that it propagates and
     * is copied into the child.
     *
     * @param c the constraint, which must be {@link org.jacop.api.Copyable}.
     */
    void impose(Constraint c);

    /**
     * Leaves a constraint out of the child, because the other constraints and the domains imply it.
     *
     * @param c a constraint of {@link #constraints()}.
     */
    void remove(Constraint c);

    /**
     * Tells whether a constraint was removed by a rule.
     *
     * @param c a constraint.
     * @return true if it was removed.
     */
    boolean removed(Constraint c);
  }
}
