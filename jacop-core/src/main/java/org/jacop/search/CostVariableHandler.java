/*
 * CostVariableHandler.java
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

package org.jacop.search;

import org.jacop.constraints.Constraint;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Handler interface for type-specific cost variable operations in search algorithms.
 * This interface allows search classes to work with different variable types (IntVar, FloatVar, SetVar)
 * without directly depending on their concrete implementations.
 * <p>
 * Implementations of this interface should be provided by the respective modules:
 * - IntCostVariableHandler in jacop-core
 * - FloatCostVariableHandler in jacop-floats
 * - SetCostVariableHandler in jacop-sets (if needed)
 *
 * @author Generated for multi-module refactoring
 * @version 4.11
 */
public interface CostVariableHandler {

    /**
     * Checks if this handler can process the given variable type.
     *
     * @param var the variable to check
     * @return true if this handler can process the variable, false otherwise
     */
    boolean isApplicable(Var var);

    /**
     * Gets the current cost value from the variable.
     * For IntVar, returns integer cost value.
     * For FloatVar, returns double cost value.
     *
     * @param var the cost variable
     * @return the current cost value
     */
    double getCostValue(Var var);

    /**
     * Creates a constraint that enforces the cost variable to be less than or equal to the given cost value.
     * This is used in optimization to ensure subsequent solutions are better.
     *
     * @param var the cost variable
     * @param costValue the cost value to enforce
     * @return a constraint enforcing cost <= costValue
     */
    Constraint createCostConstraint(Var var, double costValue);

    /**
     * Updates the cost variable's domain to exclude values greater than the given cost value.
     * This is used during optimization to prune the search space.
     *
     * @param store the store containing the variable
     * @param var the cost variable
     * @param costValue the maximum cost value to allow
     */
    void updateCostDomain(Store store, Var var, double costValue);

    /**
     * Gets the minimum cost value that can be achieved.
     * Used for checking if further optimization is possible.
     *
     * @param var the cost variable
     * @return the minimum possible cost value
     */
    double getMinCostValue(Var var);

    /**
     * Gets the maximum cost value that can be achieved.
     * Used for maximization problems.
     *
     * @param var the cost variable
     * @return the maximum possible cost value
     */
    double getMaxCostValue(Var var);

    /**
     * Checks if a given cost value is better than the current best cost.
     * For minimization: returns true if newCost < currentCost
     * For maximization: returns true if newCost > currentCost
     *
     * @param currentCost the current best cost
     * @param newCost the new cost to compare
     * @param minimize true for minimization, false for maximization
     * @return true if newCost is better than currentCost
     */
    boolean isBetterCost(double currentCost, double newCost, boolean minimize);

    /**
     * Gets the previous cost value for minimization.
     * For FloatVar, this accounts for floating-point precision.
     * For IntVar, this is simply costValue - 1.
     *
     * @param costValue the current cost value
     * @return the previous cost value (for minimization)
     */
    double getPreviousCostValue(double costValue);
}
