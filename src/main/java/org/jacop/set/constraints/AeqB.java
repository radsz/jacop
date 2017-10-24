/*
 * AeqB.java
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
import org.jacop.core.Store;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It creates an equality constraint to make sure that two set variables
 * have the same value. 
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */

public class AeqB extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies set variable a, which must be equal to set variable b.
     */
    public SetVar a;

    /**
     * It specifies set variable b, which must be equal to set variable a.
     */
    public SetVar b;

    // private boolean aHasChanged = true;
    // private boolean bHasChanged = true;

    /**
     * It constructs an AeqB constraint to restrict the domain of the variables.
     * @param a variable a restricted to be equal to b.
     * @param b variable b restricted to be equal to a.
     */
    public AeqB(SetVar a, SetVar b) {

        checkInputForNullness(new String[]{"a", "b"}, new Object[]{a, b});

        numberId = idNumber.incrementAndGet();

        this.a = a;
        this.b = b;
        setScope(a, b);

    }

    @Override public void consistency(Store store) {

        /**
         * It computes the consistency of the constraint.
         *
         * If two set variables are to be equal then they
         * are always reduced to the intersection of their domains.
         *
         * glbA = glbA \/ glbB
         * glbB = glbA \/ glbB
         *
         * lubA = lubA /\ lubB
         * lubB = lubA /\ lubB
         *
         *
         */

        // if (bHasChanged)
        a.domain.in(store.level, a, b.dom());

        // if (aHasChanged)
        b.domain.in(store.level, b, a.dom());

        a.domain.inCardinality(store.level, a, b.domain.card().min(), b.domain.card().max());
        b.domain.inCardinality(store.level, b, a.domain.card().min(), a.domain.card().max());

        // aHasChanged = false;
        // bHasChanged = false;

    }

    @Override public void notConsistency(Store store) {

        if (a.singleton() && b.singleton() && a.dom().glb().eq(b.dom().glb()))
            throw Store.failException;

    }

    @Override public boolean notSatisfied() {

        if (!a.domain.lub().contains(b.domain.glb()) || !b.domain.lub().contains(a.domain.glb()))
            return true;

        if (a.singleton() && b.singleton() && !a.domain.glb().eq(b.domain.glb()))
            return true;

        return false;
    }

    @Override public boolean satisfied() {

        if (grounded() && a.domain.glb().eq(b.domain.glb()))
            return true;

        return false;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return SetDomain.GROUND;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override public String toString() {
        return id() + " : AeqB(" + a + ", " + b + " )";
    }

}
