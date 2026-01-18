/*
 * FloatCostVariableHandler.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.floats.search;

import org.jacop.constraints.Constraint;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.constraints.PlteqC;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.search.CostVariableHandler;

/**
 * Handler for FloatVar cost variable operations in search algorithms. This implementation handles
 * floating-point cost variables with proper precision handling.
 *
 * @author Generated for multi-module refactoring
 * @version 4.11
 */
public class FloatCostVariableHandler implements CostVariableHandler {

  @Override
  public boolean isApplicable(Var var) {
    return var instanceof FloatVar;
  }

  @Override
  public double getCostValue(Var var) {
    if (!(var instanceof FloatVar floatVar)) {
      throw new IllegalArgumentException("FloatCostVariableHandler can only handle FloatVar");
    }
    return floatVar.dom().max();
  }

  @Override
  public Constraint createCostConstraint(Var var, double costValue) {
    if (!(var instanceof FloatVar floatVar)) {
      throw new IllegalArgumentException("FloatCostVariableHandler can only handle FloatVar");
    }
    double previousCost = FloatDomain.previousForMinimization(costValue);
    return new PlteqC(floatVar, previousCost);
  }

  @Override
  public void updateCostDomain(Store store, Var var, double costValue) {
    if (!(var instanceof FloatVar floatVar)) {
      throw new IllegalArgumentException("FloatCostVariableHandler can only handle FloatVar");
    }
    double previousCost = FloatDomain.previous(costValue);
    floatVar.domain.inMax(store.level, floatVar, previousCost);
  }

  @Override
  public double getMinCostValue(Var var) {
    if (!(var instanceof FloatVar floatVar)) {
      throw new IllegalArgumentException("FloatCostVariableHandler can only handle FloatVar");
    }
    return floatVar.dom().min();
  }

  @Override
  public double getMaxCostValue(Var var) {
    if (!(var instanceof FloatVar floatVar)) {
      throw new IllegalArgumentException("FloatCostVariableHandler can only handle FloatVar");
    }
    return floatVar.dom().max();
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
    return FloatDomain.previousForMinimization(costValue);
  }
}
