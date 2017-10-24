/*
 * AeqS.java
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
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It creates an equality constraint to make sure that a set variable
 * is equal to a given set. 
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */

public class AeqS extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies set variable a, which must be equal to set variable b.
     */
    public SetVar a;

    /**
     * It specifies the set which must be equal to set variable a.
     */
    public IntDomain set;

    /**
     * It specifies the size of b.
     */
    int sizeOfB;

    /**
     * It constructs an AeqS constraint to restrict the domain of the variables.
     * @param a variable a that is forced to be equal to a specified set value.
     * @param set it specifies the set to which variable a must be equal to.
     */
    public AeqS(SetVar a, IntDomain set) {

        checkInputForNullness(new String[]{"a", "set"}, new Object[]{a, set});

        numberId = idNumber.incrementAndGet();

        this.a = a;
        this.set = set;
        this.sizeOfB = set.getSize();
        setScope(a);

    }

    @Override public void consistency(Store store) {

        /**
         * It computes the consistency of the constraint.
         *
         * If a set variables is to be equal to the set
         * then it is enough to perform the following once.
         *
         * glbA = s;
         * lubA = s;
         *
         */

        a.domain.inValue(store.level, a, set);

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override public int getNotConsistencyPruningEvent(Var var) {

        if (notConsistencyPruningEvents != null) {
            Integer possibleEvent = notConsistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        return SetDomain.GROUND;
    }

    @Override public void notConsistency(Store store) {

        if (a.singleton() && a.dom().glb().eq(set))
            throw Store.failException;

        if (sizeOfB == a.domain.glb().getSize() + 1 && sizeOfB == a.domain.lub().getSize() && set.contains(a.domain.glb())) {
            int value = a.domain.lub().subtract(a.domain.glb()).value();
            if (set.contains(value))
                a.domain.inLUBComplement(store.level, a, value);
            else
                a.domain.inValue(store.level, a, a.domain.lub());
        }

    }

    @Override public boolean notSatisfied() {

        if (!a.domain.lub().contains(set))
            return true;

        if (a.singleton() && !(a.domain.glb().eq(set)))
            return true;

        return false;
    }

    @Override public boolean satisfied() {
        return a.domain.singleton(set);
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


    @Override public String toString() {
        return id() + " : AeqS(" + a + ", " + set + " )";
    }

}
