/*
 * XeqA.java
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

package org.jacop.set.constraints;

import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It creates a constraint that makes sure that the value assigned to the integer variable x
 * is the only element of the set assigned to a set variable a. 
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */

public class XeqA extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable a.
     */
    public IntVar x;

    /**
     * It specifies variable b.
     */
    public SetVar a;

    /**
     * It constructs an XeqA constraint to restrict the domain of the integer variables x and set variable a.
     *
     * @param x variable x that is restricted to be the only element of a set assigned to set variable a.
     * @param a set variable that must be equal to a set containing only one element as specified by integer variable x.
     */
    public XeqA(IntVar x, SetVar a) {

        checkInputForNullness(new String[]{"x", "a"}, new Object[]{x, a});

        this.numberId = idNumber.incrementAndGet();

        this.x = x;
        this.a = a;

        setScope(x, a);

    }
    
    @Override public void consistency(Store store) {

        /**
         *
         * It specifies rule for X eq A.
         *
         * lubA = lubA /\ dom(X).
         *
         * dom(X) = dom(X) /\ lubA
         *
         * #A = 1.
         *
         */

        // if (aHasChanged)
        x.domain.in(store.level, x, a.domain.lub());
        // if (xHasChanged)
        a.domain.inLUB(store.level, a, x.domain);

        a.domain.inCardinality(store.level, a, 1, 1);

        // aHasChanged = false;
        // xHasChanged = false;

    }

    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }

        if (var == a)
            return SetDomain.ANY;
        else
            return IntDomain.ANY;

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise method exists.");
    }

    @Override public int getNotConsistencyPruningEvent(Var var) {

        // If notConsistency function mode
        if (notConsistencyPruningEvents != null) {
            Integer possibleEvent = notConsistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }

        if (var == a)
            return SetDomain.ANY;
        else
            return IntDomain.ANY;

    }

    @Override public void notConsistency(Store store) {

        if (a.domain.card().min() == 1 && a.domain.card().max() == 1) {

            if (x.singleton())
                a.domain.inLUBComplement(store.level, a, x.value());

            if (a.domain.singleton())
                x.domain.inComplement(store.level, x, a.domain.glb().min());

        }


    }

    @Override public boolean notSatisfied() {

        if (!a.domain.card().contains(1))
            return true;

        if (!a.domain.lub().isIntersecting(x.domain))
            return true;

        return false;

    }

    @Override public boolean satisfied() {
        return grounded() && a.domain.card().max() == 1 && a.domain.glb().min() == x.value();
    }

    @Override public int getNestedPruningEvent(Var var, boolean mode) {

        // If consistency function mode
        if (mode) {
            if (consistencyPruningEvents != null) {
                Integer possibleEvent = consistencyPruningEvents.get(var);
                if (possibleEvent != null)
                    return possibleEvent;
            }
            return getConsistencyPruningEvent(var);
        }
        // If notConsistency function mode
        else {
            if (notConsistencyPruningEvents != null) {
                Integer possibleEvent = notConsistencyPruningEvents.get(var);
                if (possibleEvent != null)
                    return possibleEvent;
            }
            return getNotConsistencyPruningEvent(var);
        }
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise method exists.");
    }

    @Override public String toString() {
        return id() + " : XeqA(" + x + ", " + a + " )";
    }

}
