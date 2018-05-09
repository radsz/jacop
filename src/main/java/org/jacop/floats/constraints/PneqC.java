/*
 * PneqC.java
 * This file is part of org.jacop.
 * <p>
 * org.jacop is a Java Constraint Programming solver.
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

import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

import org.jacop.constraints.PrimitiveConstraint;

import org.jacop.floats.core.FloatVar;

/**
 * Constraints P != C
 *
 * Domain consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class PneqC extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies the constant to which a specified variable should be equal to.
     */
    public double c;

    /**
     * It specifies the variable which is constrained to be equal to the specified value.
     */
    public FloatVar p;

    /**
     * It constructs the constraint P = C.
     * @param p variable p.
     * @param c constant c.
     */
    public PneqC(FloatVar p, double c) {

        checkInputForNullness(new String[]{"p"}, new Object[][]{ {p} });
        if ( ! ( c >= IntDomain.MinInt && c <= IntDomain.MaxInt ) )
            throw new IllegalArgumentException("PneqC constraint has constant c " + c + " in the not allowed range.");

        numberId = idNumber.incrementAndGet();
        this.p = p;
        this.c = c;

        setScope(p);

    }

    @Override public void notConsistency(Store store) {

        p.domain.in(store.level, p, c, c);

    }

    @Override public void consistency(Store store) {

        p.domain.inComplement(store.level, p, c);

    }

    @Override public boolean notSatisfied() {
        return p.singleton(c);
    }

    @Override public boolean satisfied() {
        return !p.domain.contains(c);
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return Domain.NONE;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return Domain.NONE;
    }

    @Override public String toString() {
        return id() + " : PneqC(" + p + ", " + c + " )";
    }

    /**
     * It returns the constant to which a given variable should be equal to.
     * @return the constant to which the variable should be equal to.
     */
    public double getC() {
        return c;
    }

}
