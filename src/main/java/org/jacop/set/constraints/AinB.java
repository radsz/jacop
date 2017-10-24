/*
 * AinB.java
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
 * It creates a constraint that makes sure that the set value of set variable A is included
 * in the set value of set variable B.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */

public class AinB extends PrimitiveConstraint {

    // FIXME, check consistency and other methods like satisfied, notConsistency, notSatisfied.

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable a.
     */
    public SetVar a;

    /**
     * It specifies variable b.
     */
    public SetVar b;

    /**
     * It specifies if the inclusion relation is strict.
     */
    public boolean strict = false;

    /**
     * It constructs an AinB constraint to restrict the domain of the variables A and B.
     * By default this inclusion relation does not have to be strict.
     *
     * @param a variable a that is restricted to be a subset of b.
     * @param b variable that is restricted to contain a.
     */
    public AinB(SetVar a, SetVar b) {

        checkInputForNullness(new String[]{"a", "b"}, new Object[]{a, b});

        this.numberId = idNumber.incrementAndGet();

        this.a = a;
        this.b = b;

        setScope(a, b);

    }

    /**
     * It constructs an AinB constraint to restrict the domain of the variables A and B.
     *
     * @param a variable a that is restricted to be a subset of variable b.
     * @param b variable that is restricted to contain variable a.
     * @param strict it specifies if the inclusion relation is strict.
     */
    public AinB(SetVar a, SetVar b, boolean strict) {

        this(a, b);
        this.strict = strict;

    }
    
    @Override public void consistency(Store store) {

        // FIXME, take into account strict relation.

        /**
         * Consistency of the constraint A in B.
         *
         * B can not be an empty set.
         *
         * T1.
         * glbA = glbA
         * lubA = lubA /\ lubB
         *
         * T2
         * glbB = glbB \/ glbA
         * lubB = lubB
         *
         */

        if (strict)
            if (b.domain.isEmpty())
                throw Store.failException;

        // if (bHasChanged)
        a.domain.inLUB(store.level, a, b.domain.lub());

        // if (aHasChanged)
        b.domain.inGLB(store.level, b, a.domain.glb());

        if (strict)
            a.domain.inCardinality(store.level, a, Integer.MIN_VALUE, b.domain.card().max() - 1);
        else
            a.domain.inCardinality(store.level, a, Integer.MIN_VALUE, b.domain.card().max());

        if (strict)
            b.domain.inCardinality(store.level, b, a.domain.card().min() + 1, Integer.MAX_VALUE);
        else
            b.domain.inCardinality(store.level, b, a.domain.card().min(), Integer.MAX_VALUE);

    }



    @Override public void notConsistency(Store store) {

        if (b.domain.glb().contains(a.domain.lub()))
            throw Store.failException;

    }

    @Override public boolean notSatisfied() {

        if (a.singleton() && b.singleton() && !a.domain.subtract(b.domain).isEmpty())
            return true;
        else
            return false;

    }

    @Override public boolean satisfied() {
        return grounded() && b.domain.contains(a.domain);
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override public String toString() {
        return id() + " : AinB(" + a + ", " + b + " )";
    }

}
