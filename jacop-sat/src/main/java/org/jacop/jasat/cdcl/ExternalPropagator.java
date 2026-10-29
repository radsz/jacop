/*
 * ExternalPropagator.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.cdcl;

/**
 * A propagator that takes part in the search of {@link CdclSolver#solve}, in the style of IPASIR-UP
 * (Fazekas et al. 2023). It sees the assignments of the variables it observes, can propagate
 * literals with a reason clause, add clauses, suggest decisions and reject complete assignments.
 * Literals are DIMACS literals.
 *
 * <p>Calls follow the solver's search: {@link #notifyNewDecisionLevel} when a level opens, {@link
 * #notifyAssignment} for every observed variable that gets a value (once per assignment), {@link
 * #notifyBacktrack} when levels are undone. After unit propagation reaches a fixpoint, the solver
 * asks for {@link #externalClause} until it returns null and for {@link #propagate} until it
 * returns 0. A literal returned by {@link #propagate} must be implied: the solver asks for its
 * {@link #reason} at once, a clause made of the literal and literals that are false now. When the
 * assignment is complete, {@link #checkModel} accepts it or adds a clause that it falsifies.
 *
 * <p>Clauses from {@link #externalClause} are kept; reason clauses are learnt clauses and may be
 * deleted. Every clause must be implied by the formula and the propagator's theory. DRAT proofs do
 * not cover the theory, so they cannot be checked when a propagator is connected.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface ExternalPropagator {

  /**
   * An observed variable got a value.
   *
   * @param lit the literal that became true
   * @param fixed whether it is fixed at level 0
   */
  default void notifyAssignment(int lit, boolean fixed) {}

  /** A new decision level opened. */
  default void notifyNewDecisionLevel() {}

  /**
   * The levels above {@code level} were undone, with all their assignments.
   *
   * @param level the decision level the search is now at
   */
  default void notifyBacktrack(int level) {}

  /** The solver restarted; {@link #notifyBacktrack} to level 0 came just before. */
  default void notifyRestart() {}

  /**
   * A literal of a clause just learnt by conflict analysis, for statistics. Called once per literal
   * of each learnt clause.
   *
   * @param lit the literal
   */
  default void notifyLearntLiteral(int lit) {}

  /**
   * A literal of a reason the solver keeps as a learnt clause. Called once per literal of each kept
   * reason, so the propagator knows the literal now occurs in a clause.
   *
   * @param lit the literal
   */
  default void notifyKeptLiteral(int lit) {}

  /**
   * Shortens a clause just learnt by conflict analysis by removing literals that imply another
   * literal of the clause, an implication only the propagator knows (semantic minimisation). The
   * first literal, the one the clause asserts, stays first and is never removed.
   *
   * @param clause the literals, in DIMACS form; the kept ones are moved to the front in order
   * @param size the number of literals
   * @return the number of literals kept
   */
  default int minimizeLearnt(int[] clause, int size) {
    return size;
  }

  /**
   * The integer variable whose atom a solver variable is, for semantic UIPs.
   *
   * @param var the solver variable, from 1
   * @return a non-negative index shared by the atoms of one integer variable, or -1 for none
   */
  default int integerVariable(int var) {
    return -1;
  }

  /**
   * Names a literal equivalent to the conjunction of true atoms of one integer variable, all set at
   * the conflict level, so that conflict analysis can stop there: a learnt clause with that
   * literal's negation in place of theirs is still implied, and asserting.
   *
   * @param lits the true literals, in DIMACS form, all of one {@link #integerVariable}
   * @param size the number of literals
   * @return a literal equivalent to their conjunction, or 0 for none
   */
  default int semanticUip(int[] lits, int size) {
    return 0;
  }

  /**
   * Checks a complete assignment.
   *
   * @param model the value of every variable, as {@code model[v-1] = v} or {@code -v}
   * @return true to accept it; false after preparing a clause, returned by {@link #externalClause},
   *     that the assignment falsifies
   */
  default boolean checkModel(int[] model) {
    return true;
  }

  /**
   * Suggests the next decision.
   *
   * @return an unassigned literal, or 0 to leave the decision to the solver
   */
  default int decide() {
    return 0;
  }

  /**
   * Suggests a decision once the solver has assigned all its variables, before the assignment is
   * offered as a model, for example on a variable that has no literal yet.
   *
   * @return an unassigned literal, or 0 to offer the assignment as a model
   */
  default int decideLast() {
    return 0;
  }

  /**
   * Returns a literal implied by the current assignment.
   *
   * @return the literal, or 0 when there is none
   */
  default int propagate() {
    return 0;
  }

  /**
   * Returns the reason of a literal returned by {@link #propagate}. The solver asks for it right
   * away when the literal is false (a conflict), and otherwise only when conflict analysis needs
   * it, at any time while the literal stays assigned.
   *
   * @param lit the propagated literal
   * @return a clause containing lit whose other literals were false before lit was assigned
   */
  default int[] reason(int lit) {
    throw new IllegalStateException("no reason for " + lit);
  }

  /**
   * Returns a clause to add.
   *
   * @return the clause, or null when there is none
   */
  default int[] externalClause() {
    return null;
  }
}
