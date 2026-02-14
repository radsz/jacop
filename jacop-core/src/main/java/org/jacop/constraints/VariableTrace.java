/*
 * VariableTrace.java
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

import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.RemoveLevelLate;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * VariableTrace is a daemon that prints information on variables whenever they are changed.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class VariableTrace extends Constraint implements UsesQueueVariable, RemoveLevelLate {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final Var[] vars;
  Store store;

  /**
   * It constructs trace daemon for variable v.
   *
   * @param v variable to be traced
   */
  public VariableTrace(Var v) {
    this(new Var[] {v});
  }

  /**
   * It constructs trace daemon for variables vs.
   *
   * @param vs variables to be traced
   */
  public VariableTrace(Var[] vs) {

    numberId = idNumber.incrementAndGet();

    vars = new Var[vs.length];
    System.arraycopy(vs, 0, vars, 0, vs.length);

    setScope(vars);
  }

  /**
   * It constructs trace daemon for variables vs.
   *
   * @param vs variables to be traced
   */
  public VariableTrace(List<Var> vs) {
    this(vs.toArray(new Var[0]));
  }

  /**
   * Imposes this trace constraint on the given store, registering listeners for all traced
   * variables.
   *
   * @param store the constraint store.
   */
  public void impose(Store store) {

    this.store = store;

    store.registerRemoveLevelLateListener(this);

    for (Var v : vars) {
      v.putModelConstraint(this, getConsistencyPruningEvent(v));
      // we do not want to print initial values
    }

    store.countConstraint();
  }

  /** {@inheritDoc} */
  public void consistency(Store store) {}

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  /** {@inheritDoc} */
  public void queueVariable(int level, Var v) {
    log.debug("Var: {}, level: {}, constraint: {}", v, level, store.currentConstraint);
  }

  @Override
  public void removeLevelLate(int level) {
    log.debug("Restore level: {}, vars: {}", level, java.util.Arrays.toString(vars));
  }

  /** {@inheritDoc} */
  public void removeConstraint() {}

  /**
   * Checks whether this tracing constraint is definitely satisfied.
   *
   * @return {@code false}; this daemon-style constraint is not used as a satisfiability predicate.
   */
  public boolean satisfied() {
    return false;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : variableTrace([");
    appendArrayToString(result, vars);
    result.append("])");

    return result.toString();
  }

  /** {@inheritDoc} */
  public void increaseWeight() {}
}
