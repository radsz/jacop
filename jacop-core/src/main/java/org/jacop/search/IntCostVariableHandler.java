/*
 * IntCostVariableHandler.java
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

package org.jacop.search;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.XltC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Handler for IntVar cost variable operations in search algorithms. This is the default
 * implementation for integer cost variables.
 *
 * @author Generated for multi-module refactoring
 * @version 4.11
 */
public class IntCostVariableHandler implements CostVariableHandler {

  @Override
  public boolean isApplicable(Var v) {
    return v instanceof IntVar;
  }

  @Override
  public double getCostValue(Var v) {
    if (!(v instanceof IntVar intVar)) {
      throw new IllegalArgumentException("IntCostVariableHandler can only handle IntVar");
    }
    return intVar.dom().min();
  }

  @Override
  public Constraint createCostConstraint(Var v, double costValue) {
    if (!(v instanceof IntVar intVar)) {
      throw new IllegalArgumentException("IntCostVariableHandler can only handle IntVar");
    }
    int intCostValue = (int) costValue;
    return new XltC(intVar, intCostValue);
  }

  @Override
  public void updateCostDomain(Store store, Var v, double costValue) {
    if (!(v instanceof IntVar intVar)) {
      throw new IllegalArgumentException("IntCostVariableHandler can only handle IntVar");
    }
    int intCostValue = (int) costValue;
    intVar.domain.inMax(store.level, intVar, intCostValue - 1);
  }

  @Override
  public double getMinCostValue(Var v) {
    if (!(v instanceof IntVar intVar)) {
      throw new IllegalArgumentException("IntCostVariableHandler can only handle IntVar");
    }
    return intVar.dom().min();
  }

  @Override
  public double getMaxCostValue(Var v) {
    if (!(v instanceof IntVar intVar)) {
      throw new IllegalArgumentException("IntCostVariableHandler can only handle IntVar");
    }
    return intVar.dom().max();
  }

  @Override
  public boolean isBetterCost(double currentCost, double newCost, boolean minimize) {
    if (minimize) {
      return newCost < currentCost;
    } else {
      return newCost > currentCost;
    }
  }

  @Override
  public double getPreviousCostValue(double costValue) {
    // For IntVar, previous value is simply costValue - 1
    return costValue - 1.0;
  }
}
