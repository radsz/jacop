/*
 * Presolver.java
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
import java.util.function.Supplier;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Presolve for the common case: derive a simplified child store from a store at its current level,
 * search the child, and write its solutions back into the original variables.
 *
 * <pre>{@code
 * Derivation p = Presolver.of(store).keep(outputVars).presolve();
 * if (p.outcome() != Derivation.Outcome.INFEASIBLE) {
 *   Store search = p.child();
 *   IntVar[] decisions = p.counterparts(vars);
 *   // search the child; in its solution listener call p.returnSolution(), after which
 *   // the original variables hold the solution
 * }
 * }</pre>
 *
 * <p>In normal operation the original store's constraints are released once the child exists. In
 * checking mode they are kept, and every returned solution is propagated in the original store,
 * which checks it against the whole model.
 *
 * <p>The presolver applies the {@link #STANDARD standard rules} and any added with {@link
 * #rule(Rule)}, in rounds alternated with propagation until a fixpoint; see {@link Rule}.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class Presolver {

  /**
   * The rules every presolve applies, in this order, before those added with {@link #rule(Rule)}. A
   * new presolve rule is added here. The system property jacop.presolve.orderLiterals=false leaves
   * out {@link OrderLiterals}, for example to measure it.
   */
  static final List<Supplier<Rule>> STANDARD =
      Boolean.parseBoolean(System.getProperty("jacop.presolve.orderLiterals", "true"))
          ? List.of(
              GlobalPresolveRule::new,
              AtMostOneRule::new,
              BooleanProducts::new,
              () -> RedundantConstraints.RULE,
              () -> OrderLiterals.RULE)
          : List.of(
              GlobalPresolveRule::new,
              AtMostOneRule::new,
              BooleanProducts::new,
              () -> RedundantConstraints.RULE);

  private final Derivation.Builder builder;
  private boolean checking;

  private Presolver(Store store) {
    this.builder = Derivation.of(store);
    STANDARD.forEach(rule -> builder.rule(rule.get()));
  }

  /**
   * Starts presolving a store at its current level.
   *
   * @param store the store.
   * @return the presolver.
   */
  public static Presolver of(Store store) {
    return new Presolver(store);
  }

  /**
   * Sets the variables that must keep a counterpart in the child; see {@link
   * Derivation.Builder#keep(Var...)}.
   *
   * @param vars the variables, for example the output variables.
   * @return this presolver.
   */
  public Presolver keep(Var... vars) {
    builder.keep(vars);
    return this;
  }

  /**
   * Gives clauses kept outside the store to preprocess with the store's clauses; see {@link
   * Derivation.Builder#clauses(java.util.List)}.
   *
   * @param clauses the clauses, a list changed in place to the child's clauses.
   * @return this presolver.
   */
  public Presolver clauses(java.util.List<org.jacop.core.IntVar[][]> clauses) {
    builder.clauses(clauses);
    return this;
  }

  /**
   * Sets whether the child keeps every solution; see {@link
   * Derivation.Builder#solutionPreserving(boolean)}. True by default; false lets half-reification
   * and the clause rules that merge solutions run, which need the frozen variables given with
   * {@link #keep(Var...)}.
   *
   * @param on true to keep every solution, as all-solution search and counting need.
   * @return this presolver.
   */
  public Presolver solutionPreserving(boolean on) {
    builder.solutionPreserving(on);
    return this;
  }

  /**
   * Switches checking mode on: the original constraints are kept and every returned solution is
   * checked against them.
   *
   * @param on true for checking mode.
   * @return this presolver.
   */
  public Presolver checking(boolean on) {
    this.checking = on;
    return this;
  }

  /**
   * Adds a rule after the standard ones.
   *
   * @param rule the rule.
   * @return this presolver.
   */
  public Presolver rule(Rule rule) {
    builder.rule(rule);
    return this;
  }

  /**
   * Switches rule 2, affine equality substitution, on or off; see {@link
   * Derivation.Builder#affine(boolean)}.
   *
   * @param on true to substitute, the default.
   * @return this presolver.
   */
  public Presolver affine(boolean on) {
    builder.affine(on);
    return this;
  }

  /**
   * Probes the store in the rounds of rules, after the standard rules; see {@link ProbingRule}. Off
   * by default.
   *
   * @param mode what probing tries; {@link Probing.Mode#OFF} adds nothing.
   * @param budgetMillis the time probing may take over all rounds, in milliseconds.
   * @return this presolver.
   */
  public Presolver probing(Probing.Mode mode, long budgetMillis) {
    if (mode != Probing.Mode.OFF) {
      builder.rule(new ProbingRule(mode, budgetMillis));
    }
    return this;
  }

  /**
   * Switches the dual reductions on; see {@link Derivation.Builder#dualReductions(boolean)}. They
   * keep one solution and every optimum but not every solution, so they are only for a search that
   * wants one solution or an optimum.
   *
   * @param objective the objective variable, or null for a satisfaction problem.
   * @param minimize true if the objective is minimised.
   * @return this presolver.
   */
  public Presolver dualReductions(IntVar objective, boolean minimize) {
    builder.dualReductions(true).objective(objective, minimize);
    return this;
  }

  /**
   * Switches the dominated columns of the dual reductions on or off; see {@link
   * Derivation.Builder#dominatedColumns(boolean)}.
   *
   * @param on true to look for dominated columns when the dual reductions are on.
   * @return this presolver.
   */
  public Presolver dominatedColumns(boolean on) {
    builder.dominatedColumns(on);
    return this;
  }

  /**
   * Sets the most rounds of rules; see {@link Derivation.Builder#rounds(int)}.
   *
   * @param max the most rounds, at least 1.
   * @return this presolver.
   */
  public Presolver rounds(int max) {
    builder.rounds(max);
    return this;
  }

  /**
   * Sets the costliest timing class of rules to run; see {@link Derivation.Builder#timing}.
   *
   * @param max the costliest class; {@link Rule.Timing#EXHAUSTIVE}, the default, runs every rule.
   * @return this presolver.
   */
  public Presolver timing(Rule.Timing max) {
    builder.timing(max);
    return this;
  }

  /**
   * Sets the share of the variables a round must change to count as finding much; see {@link
   * Derivation.Builder#abortFactor(double)}.
   *
   * @param factor the share, at least 0.
   * @return this presolver.
   */
  public Presolver abortFactor(double factor) {
    builder.abortFactor(factor);
    return this;
  }

  /**
   * Sets the time the rounds of rules may take; see {@link Derivation.Builder#budget(long)}.
   *
   * @param millis the time in milliseconds.
   * @return this presolver.
   */
  public Presolver budget(long millis) {
    builder.budget(millis);
    return this;
  }

  /**
   * Sets variables the dual reductions leave alone; see {@link Derivation.Builder#exempt(Var...)}.
   *
   * @param vars the variables.
   * @return this presolver.
   */
  public Presolver exempt(Var... vars) {
    builder.exempt(vars);
    return this;
  }

  /**
   * Sets whether presolve leaves the store in place when its rules simplified nothing; see {@link
   * Derivation.Builder#inPlace(boolean)}.
   *
   * @param on true to skip a copy that would not simplify the problem.
   * @return this presolver.
   */
  public Presolver inPlace(boolean on) {
    builder.inPlace(on);
    return this;
  }

  /**
   * Switches the doubleton substitutions of rule 8 on or off; see {@link
   * Derivation.Builder#doubletons(boolean)}.
   *
   * @param on true to substitute, the default.
   * @return this presolver.
   */
  public Presolver doubletons(boolean on) {
    builder.doubletons(on);
    return this;
  }

  /**
   * Switches affine views on or off; see {@link Derivation.Builder#views(boolean)}.
   *
   * @param on true to use views, the default.
   * @return this presolver.
   */
  public Presolver views(boolean on) {
    builder.views(on);
    return this;
  }

  /**
   * Presolves.
   *
   * @return the derivation, whose child is the store to search.
   */
  public Derivation presolve() {
    return builder
        .retention(checking ? Derivation.Retention.KEPT : Derivation.Retention.RELEASED)
        .derive();
  }
}
