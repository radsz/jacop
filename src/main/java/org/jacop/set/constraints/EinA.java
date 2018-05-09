/*
 * EinA.java
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
 *
 * It constructs a constraint which makes sure that a given element is 
 * in the domain of the set variable.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */

public class EinA extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies the element which must be present in the set variable.
     */
    public int element;

    /**
     * It specifies the set variable which must contain a specified element.
     */
    public SetVar a;

    /**
     * It specifies if the inclusion relation is strict.
     */
    public boolean strict = false;

    /**
     * It constructs an eInA constraint to restrict the domain of the variable.
     * @param a variable a for which the restriction is applied.
     * @param element the element that has to be a part of the variable domain.
     * @param strict it specifies if the inclusion relation is strict.
     */
    public EinA(int element, SetVar a, boolean strict) {
        this(element, a);
        this.strict = strict;

    }

    /**
     * It constructs an eInA constraint to restrict the domain of the variable.
     * @param a variable a for which the restriction is applied.
     * @param element the element that has to be a part of the variable domain.
     */
    public EinA(int element, SetVar a) {

        checkInputForNullness("a", new Object[]{a});

        numberId = idNumber.incrementAndGet();

        this.a = a;
        this.element = element;

        setScope(a);

    }

    @Override public void consistency(Store store) {

        a.domain.inGLB(store.level, a, element);

        if (strict)
            a.domain.inCardinality(store.level, a, 2, Integer.MAX_VALUE);

    }

    @Override public void notConsistency(Store store) {

        // FIXME, TODO, check notConsistency() functions in other set constraints.
        a.domain.inLUBComplement(store.level, a, element);

    }

    @Override public boolean notSatisfied() {
        return !a.domain.lub().contains(element);
    }

    @Override public boolean satisfied() {
        return a.domain.glb().contains(element);
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return SetDomain.GLB;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override public String toString() {
        return id() + " : EinA(" + element + ", " + a + " )";
    }

}
