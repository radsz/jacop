/*
 * DecomposedConstraint.java
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

package org.jacop.constraints;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Standard unified interface/abstract class for constraints, which can only be decomposed. 
 * Defines how to construct a constraint out of other constraints.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */

public abstract class DecomposedConstraint<T extends Constraint> {

    /**
     * It specifies the queue (index), which is used to record that constraint
     * needs to be re-evaluated.
     *
     * Priorytet 0 - O(c), constant execution time, e.g. primitive constraints
     * Priorytet 1 - O(n), linear execution time, e.g. Sum, SumWeight
     * Priorytet 2 - O(n^2) quadratic execution time, e.g. Cumulative Diff2
     * Priorytet 3 - plynomial execution time
     * Priorytet 4 - execution time can be exponential in worst case, SumWeightDom
     */

    public int queueIndex = 0;

    /**
     * It imposes the constraint in a given store.
     * @param store the constraint store to which the constraint is imposed to.
     */
    public abstract void imposeDecomposition(Store store);

    /**
     * It imposes the constraint and adjusts the queue index.
     * @param store the constraint store to which the constraint is imposed to.
     * @param queueIndex the index of the queue in the store it is assigned to.
     */

    public void imposeDecomposition(Store store, int queueIndex) {

        assert (queueIndex < store.queueNo) : "Constraint queue number larger than permitted by store.";

        this.queueIndex = queueIndex;

        imposeDecomposition(store);

    }

    /**
     * It returns an array list of constraint which are used to decompose this
     * constraint. It actually creates a decomposition (possibly also creating
     * variables), but it does not impose the constraint.
     * @param store the constraint store in which context the decomposition takes place.
     *
     * @return an array list of constraints used to decompose this constraint.
     */
    public abstract List<T> decompose(Store store);

    /**
     * @return null if no auxiliary variables were created, otherwise a list with variables.
     */
    public List<Var> auxiliaryVariables() {
        return null;
    }

    public void checkInputForNullness(String[] a, Object[]... parameters) {

        // Case when parameters is just one array.
        if (parameters.length == 1) {
            if (a.length != parameters[0].length)
                throw new IllegalArgumentException("Constraint " + this.getClass().getSimpleName() +
                    " has parameters and descriptions that are not equal length as variables.");

            for (int i = 0; i < a.length; i++)
                if (parameters[0][i] == null)
                    throw new IllegalArgumentException(
                        "Constraint of type " + this.getClass().getSimpleName() + " has parameter " + a[i] + " that is null.");
            return;
        }

        // Case when parameters is more than one array then the length of a and parameters must match.
        if (a.length != parameters.length)
            throw new IllegalArgumentException("Constraint " + this.getClass().getSimpleName() +
                " has parameters and descriptions that are not equal length as variables.");

        for (int i = 0; i < a.length; i++) {
            if (parameters[i] == null)
                throw new IllegalArgumentException(
                    "Constraint of type " + this.getClass().getSimpleName() + " has parameter " + a[i] + " that is null.");
            for (int j = 0; j < parameters[i].length; j++) {
                if (parameters[i][j] == null)
                    if (parameters[i].length == 1) {
                        throw new IllegalArgumentException(
                            "Constraint of type " + this.getClass().getSimpleName() + " has parameter " + a[i] + " that is null.");
                    } else {
                        throw new IllegalArgumentException(
                            "Constrant of type " + this.getClass().getSimpleName() + " has parameter " + a[i] + "[" + j
                                + "] that is null.");
                    }
            }
        }
    }

    public void checkInputForNullness(String a, Object[] parameters) {

        if (parameters == null)
            throw new IllegalArgumentException(
                "Constraint of type " + this.getClass().getSimpleName() + " has parameter " + a + " that is null.");

        for (int i = 0; i < parameters.length; i++) {
            if (parameters[i] == null)
                throw new IllegalArgumentException(
                    "Constraint of type " + this.getClass().getSimpleName() + " has parameter " + a + "[" + i + "] that is null.");
        }

    }

    public void checkInputForDuplication(String a, Object[] parameters) {

        if ( Arrays.stream(parameters).collect(Collectors.toSet()).size() != parameters.length )
            throw new IllegalArgumentException(
                "Constraint of type " + this.getClass().getSimpleName() + " has parameter " + a + " that contains repeated values.");

    }

    public void checkInputForDuplicationSkipSingletons(String a, Var[] parameters) {

        Set<Var> dubletons = getDubletonsSkipSingletons(parameters);
        if ( ! dubletons.isEmpty() ) {
            throw new IllegalArgumentException(
                "Constraint of type " + this.getClass().getSimpleName() + " has parameter " + a + " that contains repeated variables " + dubletons);
        }

    }

    static public Set<Var> getDubletonsSkipSingletons(Var[] parameters) {
        List<Var> notGroundedParametersList = Arrays.stream(parameters).filter( i -> ! i.singleton()).collect(Collectors.toList());
        Set<Var> notGroundedParametersSet = new HashSet<Var>(notGroundedParametersList);
        if ( notGroundedParametersSet.size() != notGroundedParametersList.size() ) {
            notGroundedParametersSet.stream().forEach( i -> notGroundedParametersList.remove(i));
            return new HashSet<>(notGroundedParametersList);
        } else { return Collections.emptySet(); }
    }


    public void checkInputForNullness(String a, int[] parameters) {
        if (parameters == null)
            throw new IllegalArgumentException(
                "Constraint of type " + this.getClass().getSimpleName() + " has parameter " + a + " that is null.");
    }

    public <T> void checkInput(T[] list, Predicate<T> condition, String conditionDescription) {

        for (int i = 0; i < list.length; i++)
            if (! condition.test(list[i])) {
                throw new IllegalArgumentException(
                    "Constraint of type " + this.getClass().getSimpleName() + " has a condition " + conditionDescription + " violated for "
                        + i + "-th element");
            }

    }

    public void checkInput(int[] list, Predicate<Integer> condition, String conditionDescription) {

        for (int i = 0; i < list.length; i++)
            if (! condition.test(list[i])) {
                throw new IllegalArgumentException(
                    "Constraint of type " + this.getClass().getSimpleName() + " has a condition " + conditionDescription + " violated for "
                        + i + "-th element");
            }

    }


    public org.jacop.floats.core.FloatVar derivative(Store store, org.jacop.floats.core.FloatVar f,
        java.util.Set<org.jacop.floats.core.FloatVar> vars, org.jacop.floats.core.FloatVar x) {

        throw new RuntimeException("!!! Derivative not implemented for constraint " + this);
   }

}
