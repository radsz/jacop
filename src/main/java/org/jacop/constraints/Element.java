/*
 * Element.java
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

import java.util.List;
import java.util.Set;

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.Var;

/**
 * Element constraint implements the element/4 constraint (both with integer
 * list and variables list). It defines a following relation 
 * variables[index  + shift] = value. The default shift value is equal to zero.
 * The first index in the variables list is equal to 1.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Element extends Constraint implements UsesQueueVariable {

    Constraint c = null;

    /**
     * It constructs element constraint based on variables. The default shift value is equal 0.
     * @param index index variable.
     * @param variables list of variables.
     * @param value variable to which index variable is equal to.
     */
    @Deprecated
    public Element(IntVar index, List<? extends IntVar> variables, IntVar value) {
        queueIndex = 1;
        c = new ElementVariable(index, variables, value);
    }

    /**
     * It constructs element constraint based on variables.
     * @param index index variable.
     * @param variables variables list.
     * @param value value variable.
     * @param shift shift by which the index value is moved to the left.
     */
    @Deprecated
    public Element(IntVar index, List<? extends IntVar> variables, IntVar value, int shift) {
        queueIndex = 1;
        c = new ElementVariable(index, variables, value, shift);
    }

    /**
     * It constructs element constraint based on variables. The default shift value is equal 0.
     * @param index index variable.
     * @param values list of integers.
     * @param value variable to which index variable is equal to.
     */
    @Deprecated
    public Element(IntVar index, int[] values, IntVar value) {
        queueIndex = 0;
        c = new ElementInteger(index, values, value);
    }

    /**
     * It constructs element constraint based on variables.
     * @param index index variable.
     * @param values integer list.
     * @param value value variable.
     * @param shift shift by which the index value is moved to the left.
     */
    @Deprecated
    public Element(IntVar index, int[] values, IntVar value, int shift) {
        queueIndex = 0;
        c = new ElementInteger(index, values, value, shift);
    }

    /**
     * It constructs element constraint based on variables. The default shift value is equal 0.
     * @param index index variable.
     * @param variables list of integers.
     * @param value variable to which index variable is equal to.
     */
    @Deprecated
    public Element(IntVar index, IntVar[] variables, IntVar value) {
        queueIndex = 1;
        c = new ElementVariable(index, variables, value);
    }

    /**
     * It constructs element constraint based on variables.
     * @param index index variable.
     * @param variables variables list.
     * @param value value variable.
     * @param shift shift by which the index value is moved to the left.
     */
    @Deprecated
    public Element(IntVar index, IntVar[] variables, IntVar value, int shift) {
        queueIndex = 1;
        c = new ElementVariable(index, variables, value, shift);
    }

    @Override public Set<Var> arguments() {
        return c.arguments();
    }

    @Override public void consistency(Store store) {
        c.consistency(store);
    }

    @Override public int getConsistencyPruningEvent(Var var) {
        return c.getConsistencyPruningEvent(var);

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise method exists..");
    }

    @Override public String id() {
        return c.id();
    }

    @Override public void impose(Store store) {
        c.impose(store);
    }

    @Override public void queueVariable(int level, Var V) {
        c.queueVariable(level, V);
    }

    @Override public void removeConstraint() {
        c.removeConstraint();
    }

    @Override public String toString() {
        return c.toString();
    }

    @Override public void increaseWeight() {
        c.increaseWeight();
    }

    /**
     * It constructs element constraint based on variables. The default shift value is equal 0.
     * @param index index variable.
     * @param variables list of variables.
     * @param value variable to which index variable is equal to.
     * @return constraint that encodes the desired logic.
     */
    public static Constraint choose(IntVar index, List<? extends IntVar> variables, IntVar value) {
        return new ElementVariableFast(index, variables, value);
    }

    /**
     * It constructs element constraint based on variables.
     * @param index index variable.
     * @param variables variables list.
     * @param value value variable.
     * @param shift shift by which the index value is moved to the left.
     * @return constraint that encodes the desired logic.
     */
    public static Constraint choose(IntVar index, List<? extends IntVar> variables, IntVar value, int shift) {
        return new ElementVariableFast(index, variables, value, shift);
    }

    /**
     * It constructs element constraint based on variables. The default shift value is equal 0.
     * @param index index variable.
     * @param values list of integers.
     * @param value variable to which index variable is equal to.
     * @return constraint that encodes the desired logic.
     */
    public static Constraint choose(IntVar index, int[] values, IntVar value) {
        return new ElementInteger(index, values, value);
    }

    /**
     * It constructs element constraint based on variables.
     * @param index index variable.
     * @param values integer list.
     * @param value value variable.
     * @param shift shift by which the index value is moved to the left.
     * @return constraint that encodes the desired logic.
     */
    public static Constraint choose(IntVar index, int[] values, IntVar value, int shift) {
        return new ElementInteger(index, values, value, shift);
    }

    /**
     * It constructs element constraint based on variables. The default shift value is equal 0.
     * @param index index variable.
     * @param variables list of integers.
     * @param value variable to which index variable is equal to.
     * @return constraint that encodes the desired logic.
     */
    public static Constraint choose(IntVar index, IntVar[] variables, IntVar value) {
        return new ElementVariableFast(index, variables, value);
    }

    /**
     * It constructs element constraint based on variables.
     * @param index index variable.
     * @param variables variables list.
     * @param value value variable.
     * @param shift shift by which the index value is moved to the left.
     * @return constraint that encodes the desired logic.
     */
    public static Constraint choose(IntVar index, IntVar[] variables, IntVar value, int shift) {
        return new ElementVariableFast(index, variables, value, shift);
    }

}
