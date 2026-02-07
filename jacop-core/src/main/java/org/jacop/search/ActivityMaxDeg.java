/*
 * ActivityMaxDeg.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.search;

import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Defines a pruning activity comparatorfor variables. Every time a constraint prunes a variable
 * activity weight is increased by one. All other variables of constraint's activity weight value is
 * recalculated as activity weight * decay. The comparator will choose the variable with the highest
 * activity weight divided by its domain size.
 *
 * @param <T> type of variable being compared.
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */
public class ActivityMaxDeg<T extends Var> implements ComparatorVariable<T> {

  private ActivityMaxDeg() {}

  /**
   * Creates an ActivityMaxDeg comparator using the store's default decay.
   *
   * @param store the constraint store.
   */
  public ActivityMaxDeg(Store store) {
    this(store, store.getDecay());
  }

  /**
   * Creates an ActivityMaxDeg comparator with a specified decay factor.
   *
   * @param store the constraint store.
   * @param decay the decay factor for activity weight recalculation.
   */
  public ActivityMaxDeg(Store store, double decay) {
    store.activityManagement(true);
    store.setDecay(decay);
  }

  /** {@inheritDoc} */
  public int compare(double left, T var) {

    double right = var.activity() / var.getSizeFloat();

    return Double.compare(left, right);
  }

  /** {@inheritDoc} */
  public int compare(T leftVar, T rightVar) {

    double left = leftVar.activity() / leftVar.getSizeFloat();

    double right = rightVar.activity() / rightVar.getSizeFloat();

    return Double.compare(left, right);
  }

  /** {@inheritDoc} */
  public double metric(T var) {

    return var.activity() / var.getSizeFloat();
  }
}
