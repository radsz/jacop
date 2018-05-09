/**
 * XorBool.java
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

package org.jacop.constraints;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Constraint ( x_0 xor x_1 xor ... xor x_n ){@literal <=>} y
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class XorBool extends PrimitiveConstraint {

	/*
   * The logical XOR (exclusive OR) function gives True if an odd number of its arguments
	 * is True, and the rest are False. It gives False if an even number of its arguments is True, 
	 * and the rest are False.
	 *
	 * For two arguments the truth table is
	 *
	 * X | Y | Z
	 * 0   0   0
	 * 0   1   1
	 * 1   0   1
	 * 1   1   0
	 */

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variables x for the constraint.
     */
    final public IntVar[] x;

    final public IntVar y;

    /**
     * It constructs constraint (x_0 xor x_1 xor ... xor x_n ) {@literal <=>} y.
     *
     * @param x variables x.
     * @param y variable y.
     */
    public XorBool(IntVar[] x, IntVar y) {

        checkInputForNullness(new String[]{"x", "y"}, new Object[][]{x, {y}});

        queueIndex = 0;
        numberId = idNumber.incrementAndGet();

        this.x = Arrays.copyOf(x, x.length);
        this.y = y;

        assert (checkInvariants() == null) : checkInvariants();

        if (x.length > 2)
            queueIndex = 1;
        else
            queueIndex = 0;

        setScope(Stream.concat(Arrays.stream(x), Stream.of(y)));
    }

    /**
     * It checks invariants required by the constraint. Namely that
     * boolean variables have boolean domain.
     *
     * @return the string describing the violation of the invariant, null otherwise.
     */
    public String checkInvariants() {

        for (IntVar e : x)
            if (e.min() < 0 || e.max() > 1)
                return "Variable " + e + " does not have boolean domain";

        if (y.min() < 0 || y.max() > 1)
            return "Variable " + y + " does not have boolean domain";

        return null;
    }

    @Override public void consistency(final Store store) {

            IntVar nonGround = null;

            int numberOnes = 0;
            int numberZeros = 0;

            for (IntVar e : x) {
                if (e.min() == 1)
                    numberOnes++;
                else if (e.max() == 0)
                    numberZeros++;
                else nonGround = e;
            }
        
            if (numberOnes + numberZeros == x.length)
                if ((numberOnes & 1) == 1)
                    y.domain.in(store.level, y, 1, 1);
                else
                    y.domain.in(store.level, y, 0, 0);
            else if (nonGround != null && numberOnes + numberZeros == x.length - 1)
                if (y.min() == 1)
                    if ((numberOnes & 1) == 1)
                        nonGround.domain.in(store.level, nonGround, 0, 0);
                    else
                        nonGround.domain.in(store.level, nonGround, 1, 1);
                else if (y.max() == 0)
                    if ((numberOnes & 1) == 1)
                        nonGround.domain.in(store.level, nonGround, 1, 1);
                    else
                        nonGround.domain.in(store.level, nonGround, 0, 0);

    }

    @Override public void notConsistency(final Store store) {

            IntVar nonGround = null;

            int numberOnes = 0;
            int numberZeros = 0;

            for (IntVar e : x) {
                if (e.min() == 1)
                    numberOnes++;
                else if (e.max() == 0)
                    numberZeros++;
                else nonGround = e;
            }

            if (numberOnes + numberZeros == x.length)
                if ((numberOnes & 1) == 1)
                    y.domain.in(store.level, y, 0, 0);
                else
                    y.domain.in(store.level, y, 1, 1);
            else if (nonGround != null && numberOnes + numberZeros == x.length - 1)
                if (y.min() == 1)
                    if ((numberOnes & 1) == 1)
                        nonGround.domain.in(store.level, nonGround, 1, 1);
                    else
                        nonGround.domain.in(store.level, nonGround, 0, 0);
                else if (y.max() == 0)
                    if ((numberOnes & 1) == 1)
                        nonGround.domain.in(store.level, nonGround, 0, 0);
                    else
                        nonGround.domain.in(store.level, nonGround, 1, 1);

    }

    @Override public int getNestedPruningEvent(Var var, boolean mode) {

        // If consistency function mode
        if (mode) {
            if (consistencyPruningEvents != null) {
                Integer possibleEvent = consistencyPruningEvents.get(var);
                if (possibleEvent != null)
                    return possibleEvent;
            }
            return IntDomain.GROUND;
        }
        // If notConsistency function mode
        else {
            if (notConsistencyPruningEvents != null) {
                Integer possibleEvent = notConsistencyPruningEvents.get(var);
                if (possibleEvent != null)
                    return possibleEvent;
            }
            return IntDomain.BOUND;
        }
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public boolean satisfied() {

        if (! grounded() )
            return false;

        int sum = 0;
        for (IntVar e : x)
            sum += e.value();

        if ((sum & 1) == 1 && y.min() == 1)
            return true;
        else if ((sum & 1) == 0 && y.max() == 0)
            return true;

        return false;

    }

    @Override public boolean notSatisfied() {

        if (!y.singleton())
            return false;
        else
            for (IntVar e : x)
                if (!e.singleton())
                    return false;

        int sum = 0;
        for (IntVar e : x)
            sum += e.value();

        if ((sum & 1) == 1 && y.min() == 0)
            return true;
        else if ((sum & 1) == 0 && y.min() == 1)
            return true;

        return false;
    }

    @Override public String toString() {

        return id() + " : XorBool( (" + java.util.Arrays.asList(x) + ") <=>  " + y + ")";
    }

}
