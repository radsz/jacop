/*
 * PlteqC.java
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

package org.jacop.floats.constraints;

import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.Store;
import org.jacop.core.Var;

import org.jacop.constraints.PrimitiveConstraint;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;

/**
 * Constraint X {@literal <=} C for floats
 *
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class PlteqC extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x which must be smaller or equal to a given constant.
     */
    public FloatVar p;

    /**
     * It specifies constant c from which a given variable must be smaller or equal.
     */
    public double c;

    /**
     * It constructs constraint P {@literal <=} C.
     * @param p variable p.
     * @param c constant c.
     */
    public PlteqC(FloatVar p, double c) {

        checkInputForNullness(new String[]{"p"}, new Object[][]{{p}});

        numberId = idNumber.incrementAndGet();

        this.p = p;
        this.c = c;

        setScope(p);

    }

    @Override public void consistency(Store store) {

        p.domain.inMax(store.level, p, c);
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return FloatDomain.BOUND;
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return FloatDomain.BOUND;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return FloatDomain.NONE;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return FloatDomain.NONE;
    }

    @Override public void notConsistency(Store store) {
        p.domain.inMin(store.level, p, FloatDomain.next(c));
    }

    @Override public boolean notSatisfied() {
        return p.min() > c;
    }

    @Override public boolean satisfied() {
        return p.max() <= c;
    }

    @Override public String toString() {
        return id() + " : PlteqC(" + p + ", " + c + " )";
    }

}
