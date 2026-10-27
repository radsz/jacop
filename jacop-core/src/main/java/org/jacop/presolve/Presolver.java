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
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class Presolver {

  private final Derivation.Builder builder;
  private boolean checking;

  private Presolver(Store store) {
    this.builder = Derivation.of(store);
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
   * Switches the rule that posts implied constraints on or off; see {@link
   * Derivation.Builder#implied(boolean)}.
   *
   * @param on true to post implied constraints.
   * @return this presolver.
   */
  public Presolver implied(boolean on) {
    builder.implied(on);
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
