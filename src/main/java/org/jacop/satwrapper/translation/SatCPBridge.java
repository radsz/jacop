/*
 * SatCPBridge.java
 * <p>
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

package org.jacop.satwrapper.translation;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.satwrapper.SatWrapper;
import org.jacop.satwrapper.WrapperComponent;

/*
 * TODO: replace this by something embedded *inside* the CP variable itself
 */


/**
 * interface representing the domain of a CP variable as a range. It is used
 * to provide literals to represent assertions like 'X = v' or 'X{@literal <=} v' where X
 * is the CP variable and v a value from its domain
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */
public abstract class SatCPBridge implements WrapperComponent {

    // the wrapper
    protected SatWrapper wrapper;

    // the variable this object represents the range of
    public final IntVar variable;

    // the domain of the variable
    public final IntDomain initialDomain;

    // lower bound of the domain
    public int min;

    // upper bound of the domain
    public int max;

    protected boolean hasSetDomain = false;

    /**
     * the left limit of the range
     *
     * @return the *value* of the current left limit of the range
     */
    public final int getLeftLimit() {
        return initialDomain.min();
    }

    /**
     * the right limit of the range
     *
     * @return the *value* of the current right limit of the range
     */
    public final int getRightLimit() {
        return initialDomain.max();
    }

    /**
     * set the domain to be between minValue and maxValue. It only does
     * something on the first call.
     *
     * @param minValue minimum value of the range
     * @param maxValue maximum value of the range
     */
    public void setDomain(int minValue, int maxValue) {
        this.min = minValue;
        this.max = maxValue;
        hasSetDomain = true;
    }

    /**
     * return the literal that represents the assertion 'var = value'.
     * For the proposition 'var{@literal <=} value', set the isEquality flag to false
     *
     * @param value      the value for the variable this range represents
     * @param isEquality true if we want the literal for '{@code x=d}' kind of
     *                   propositions, false for '{@code x<=d}'
     * @return the literal corresponding to 'var = this value'. If the value
     * is out of the domain of the variable, returns 0.
     */
    public abstract int cpValueToBoolVar(int value, boolean isEquality);

    /**
     * return the value corresponding to given literal (variable)
     *
     * @param literal the literal standing for 'var = value'
     * @return the value such that 'var = value' (or 'var{@literal <=} value')
     */
    public abstract int boolVarToCpValue(int literal);


    /**
     * checks if the literal stands for a 'x=d' proposition, or a
     * 'x{@literal <=}d' proposition
     *
     * @param literal the literal (among literals from this range)
     * @return true if the literal stands for 'x=d', false otherwise
     */
    public abstract boolean isEqualityBoolVar(int literal);

    /**
     * checks if the literal represents a proposition about the variable
     * this object manages
     *
     * @param literal a literal
     * @return true if there is a 'd' such that literal stands for 'x=d'
     * or 'x{@literal <=}d'
     */
    public final boolean isInThisRange(int literal) {
        return wrapper.boolVarToCpVar(literal) == variable;
    }

    /**
     * does all propagation required, in a way specific to this range. This part
     * may not be used, if the variable is not bound to a DomainClausesDatabase.
     * This will be called only if <code>this.isTranslated()</code> is false.
     *
     * @param literal the literal that has been asserted
     */
    public abstract void propagate(int literal);

    /**
     * predicate for whether this variable should be handled by the
     * DomainClausesDatabase or not
     *
     * @return true if the variable should be handled by the
     * DomainClausesDatabase
     */
    public abstract boolean isTranslated();


    /**
     * simple constructor with a variable
     *
     * @param variable the variable of which this is the range
     */
    public SatCPBridge(IntVar variable) {
        this.variable = variable;
        this.initialDomain = variable.domain;
        variable.satBridge = this;
    }

    @Override public String toString() {
        return getClass().getSimpleName() + " for " + variable;
    }


    public abstract void initialize(SatWrapper wrapper);

}
