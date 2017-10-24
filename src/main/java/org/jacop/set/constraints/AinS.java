/*
 * AinS.java
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

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * It creates a constraint that makes sure that value of the variable A is included within 
 * a provided set. 
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */

public class AinS extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies set variable a.
     */
    public SetVar a;

    /**
     * It specifies set which must contain the value of set variable A.
     */
    public IntDomain set;

    /**
     * It specifies if the inclusion relation is strict.
     */
    public boolean strict;

    /**
     * It constructs a constraint that makes sure that value of set variable a is contained
     * within a provided set.
     *
     * @param a variable that is restricted to be included within a provided set.
     * @param set set that is restricted to contain the value of set variable a.
     */
    public AinS(SetVar a, IntDomain set) {
        this(a, set, false);
    }

    /**
     * It constructs a constraint that makes sure that value of set variable a is contained
     * within a provided set.
     *
     * @param a variable that is restricted to be included within a provided set.
     * @param set set that is restricted to contain the value of set variable a.
     * @param strict strict inclusion (true)
     */
    public AinS(SetVar a, IntDomain set, boolean strict) {

        checkInputForNullness(new String[]{"a", "set"}, new Object[]{a, set});

        numberId = idNumber.incrementAndGet();

        this.a = a;
        this.set = set;
        this.strict = strict;

        setScope(a);

    }

    @Override public void consistency(Store store) {

        /**
         * Consistency of the constraint A in B.
         *
         * B can not be an empty set.
         *
         * T1.
         * glbA = glbA
         * lubA = lubA /\ S
         *
         */

        a.domain.inLUB(store.level, a, set);

        if (strict && set.getSize() - 1 == a.domain.glb().getSize())
            a.domain.inLUBComplement(store.level, a, set.subtract(a.domain.glb()).value());

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override public boolean satisfied() {

        return grounded() && a.domain.lub().lex(set) < 0;

    }

    @Override public String toString() {
        return id() + " : AinS(" + a + " '< " + set + ")";
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return SetDomain.ANY;
    }
    
    @Override public void notConsistency(Store store) {

        // TODO, test it properly.

        if (a.domain.lub().getSize() > set.getSize() + 1)
            return;

        if (!set.contains(a.domain.glb()))
            return;

        IntDomain result = a.domain.lub().subtract(set);

        if (result.isEmpty())
            if (strict) {
                if (a.domain.lub().getSize() < set.getSize())
                    throw Store.failException;
                else {
                    a.domain.inGLB(store.level, a, a.domain.lub());
                }
            } else
                throw Store.failException;

        if (!strict && result.getSize() == 1) {
            // to remain inconsistency the last value which can make this constraint
            // inconsistent must be added to GLB so it becomes notSatisfied.
            a.domain.inGLB(store.level, a, result.value());
        }

        if (strict && result.getSize() == 1 && a.domain.lub().getSize() - 1 < set.getSize()) {
            a.domain.inGLB(store.level, a, result.value());
        }

    }

    @Override public boolean notSatisfied() {

        return !set.contains(a.domain.glb()) || (strict && a.domain.glb().eq(set));

    }

}
