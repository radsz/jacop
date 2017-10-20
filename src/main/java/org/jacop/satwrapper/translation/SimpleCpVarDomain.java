/*
 * SimpleCpVarDomain.java
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

import java.util.Arrays;

import org.jacop.core.IntVar;
import org.jacop.satwrapper.SatWrapper;


/**
 * A simple representation for small domains, not lazy. It allocates boolean
 * variables to stand for propositions '[x=v]' and '[x{@literal <=}v]' for each value v of
 * the domain of x (even '[x{@literal <=}max]', which is a tautology, for simplicity)
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */
public class SimpleCpVarDomain extends SatCPBridge {

    // first boolean variable representing this
    private int firstVar;

    // width of the domain (number of different values)
    private int width;

    // the special clauses database of the wrapper
    private DomainClausesDatabase clauseDatabase;

    public boolean isTranslated = true;

    // basic constructor
    public SimpleCpVarDomain(SatWrapper wrapper, IntVar variable) {
        super(variable);
        initialize(wrapper);
        setDomain(variable.min(), variable.max());
        if (isTranslated)
            wrapper.domainTranslator.translate(variable);
    }

    // basic constructor
    public SimpleCpVarDomain(SatWrapper wrapper, IntVar variable, boolean translate) {
        super(variable);
        this.isTranslated = translate;
        initialize(wrapper);
        setDomain(variable.min(), variable.max());
        if (isTranslated)
            wrapper.domainTranslator.translate(variable);
    }

    @Override public final int cpValueToBoolVar(int value, boolean isEquality) {
        assert value >= min;
        assert value <= max;

        int offset = value - min;

        if (isEquality)
            return firstVar + 2 * offset;
        else
            return firstVar + 2 * offset + 1;
    }

    @Override public final int boolVarToCpValue(int literal) {
        int var = Math.abs(literal);
        assert var >= firstVar;
        assert var <= firstVar + (max - min + 1) * 2;

        return min + (var - firstVar) / 2;
    }

    @Override public final boolean isEqualityBoolVar(int literal) {
        assert wrapper.boolVarToCpVar(literal) == this.variable;
        int var = Math.abs(literal);

        return ((var - firstVar) & 0x1) == 0; // modulo 2
        // TODO : later, use parity (be sure the equality literal is even)
    }

    @Override public void setDomain(int minValue, int maxValue) {

        if (hasSetDomain)
            return;

        super.setDomain(minValue, maxValue);

        // get as many fresh variables as needed
        width = 2 * (maxValue - minValue + 1);
        firstVar = wrapper.core.getManyFreshVariables(width);

        // remember association literal -> range
        if (wrapper.boolVarToDomains.length <= firstVar + width) {
            int newLength = 2 * (firstVar + width);
            wrapper.boolVarToDomains = Arrays.copyOf(wrapper.boolVarToDomains, newLength);
        }
        for (int i = firstVar; i < firstVar + width; ++i)
            wrapper.boolVarToDomains[i] = this;
    }

    /**
     * given some literal has a value, what other literals should be asserted ?
     */
    @Override public void propagate(int literal) {

        assert isInThisRange(literal);

        int value = boolVarToCpValue(literal);
        boolean isEquality = isEqualityBoolVar(literal);

        assert max >= min;

        if (max == min) {
            // assert 'x=v' where v=min=max
            clauseDatabase.propagate(cpValueToBoolVar(min, true), literal);
            return;
        }

        if (isEquality) {
            // ok, this is an assertion of 'x=value' to true or false
            if (literal > 0) {
                // 'x=value' is true

                // set false all other equality literals
                for (int i = min; i <= max; ++i) {
                    if (i == value)
                        continue;
                    clauseDatabase.propagate(-cpValueToBoolVar(i, true), literal);
                }
                // set false all 'x<=d' for d < value (ie x>d)
                for (int i = min; i < value; ++i) {
                    clauseDatabase.propagate(-cpValueToBoolVar(i, false), literal);
                }
                // set true all 'x<=d' for d >= value
                for (int i = value; i <= max; ++i) {
                    clauseDatabase.propagate(cpValueToBoolVar(i, false), literal);
                }
            } else {
                // assertion 'x!=value'

                if (value == min)  // 'x!=min' => 'x>min'
                    clauseDatabase.propagate(-cpValueToBoolVar(value, false), literal);
                if (value == max)  // 'x!=max' => 'x<= max-1'
                    clauseDatabase.propagate(cpValueToBoolVar(value - 1, false), literal);

                // if there were 2 values, and one is falsified, assert the other
                if (max - min == 1 && value == max)
                    clauseDatabase.propagate(cpValueToBoolVar(min, true), literal);
                if (max - min == 1 && value == min)
                    clauseDatabase.propagate(cpValueToBoolVar(max, true), literal);
                if (value == min + 1)
                    clauseDatabase.propagate(cpValueToBoolVar(min, true), literal);
            }
        } else {
            // we just asserted 'x<=value' to true or false

            if (literal > 0) {
                // assertion 'x<=value'

                // set false all 'x=d' for d > value
                for (int i = value + 1; i <= max; ++i) {
                    clauseDatabase.propagate(-cpValueToBoolVar(i, true), literal);
                }
                // set true all 'x<=d' for d > value
                for (int i = value + 1; i <= max; ++i) {
                    clauseDatabase.propagate(cpValueToBoolVar(i, false), literal);
                }
            } else {
                // assertion 'x>value'

                // set false all 'x=d' for d <= value
                for (int i = min; i <= value; ++i) {
                    clauseDatabase.propagate(-cpValueToBoolVar(i, true), literal);
                }
                // set false all 'x<=d' for d <= value
                for (int i = min; i <= value; ++i) {
                    clauseDatabase.propagate(-cpValueToBoolVar(i, false), literal);
                }
            }
        }
    }



    @Override public boolean isTranslated() {
        return isTranslated;
    }

    @Override public void initialize(SatWrapper wrapper) {

        this.wrapper = wrapper;
        assert wrapper.domainDatabase != null : "DomainClausesDatabase is needed";
        this.clauseDatabase = wrapper.domainDatabase;

    }

}
