/*
 * CardAeqX.java
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

import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * The set cardinality constraint.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 3.1
 */

public class CardAeqX extends Constraint implements SatisfiedPresent {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies set variable a which is being restricted.
     */
    public SetVar a;

    /**
     * It specifies integer variable c specifying the possible cardinality of set variable a.
     */
    public IntVar cardinality;

    /**
     * It constructs a cardinality constraint to restrict the number of elements
     * in the set assigned to set variable a.
     *
     * @param a variable that is restricted to have the cardinality c.
     * @param cardinality the variable specifying the possible values for cardinality of set variable a.
     */
    public CardAeqX(SetVar a, IntVar cardinality) {

        checkInputForNullness(new String[]{"a", "cardinality"}, new Object[]{a, cardinality});

        this.numberId = idNumber.incrementAndGet();
        this.a = a;
        this.cardinality = cardinality;

        setScope(a, cardinality);

    }

    @Override public void consistency(Store store) {

        /**
         * It computes the consistency of the constraint.
         *
         * #A = B
         *
         * Cardinality of set variable A is equal to int variable B.
         *
         * B.in(#glbA, #lubA).
         *
         * If #glbA is already equal to maximum allowed cardinality then set is specified by glbA.
         * if (#glbA == B.max()) then A = glbA
         * If #lubA is already equal to minimum allowed cardinality then set is specified by lubA.
         * if (#lubA == B.min()) then A = lubA
         *
         *
         */

        SetDomain aDom = a.domain;
        IntDomain card = cardinality.domain;

        //T12
        int min = Math.max(aDom.glb().getSize(), card.min());
        int max = Math.min(aDom.lub().getSize(), card.max());

        if (min > max)
            throw Store.failException;

        cardinality.domain.in(store.level, cardinality, min, max);

        //T13 else //T14
        if (aDom.glb().getSize() == card.max())
            a.domain.inLUB(store.level, a, aDom.glb());
        else if (aDom.lub().getSize() == card.min())
            a.domain.inGLB(store.level, a, aDom.lub());

    }

    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }

        if (var == cardinality)
            return IntDomain.ANY;
        else
            return SetDomain.ANY;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise variant exists.");
    }

    @Override public boolean satisfied() {
        return (grounded() && a.domain.card().eq(cardinality.dom()));
    }

    @Override public String toString() {
        return id() + " : card(" + a + ", " + cardinality + " )";
    }

}
