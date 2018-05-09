/*
 * XeqY.java
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

import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Constraints X #= Y
 *
 * Domain consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class XeqY extends PrimitiveConstraint {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a left hand variable in equality constraint.
     */
    final public IntVar x;

    /**
     * It specifies a right hand variable in equality constraint.
     */
    final public IntVar y;

    /**
     * It constructs constraint X = Y.
     * @param x variable x.
     * @param y variable y.
     */
    public XeqY(IntVar x, IntVar y) {

        checkInputForNullness(new String[]{"x", "y"}, new Object[]{x, y});

        numberId = idNumber.incrementAndGet();

        this.x = x;
        this.y = y;

        setScope(x, y);
    }

    @Override public void consistency(final Store store) {

        do {

            // domain consistency
            x.domain.in(store.level, x, y.domain);

            store.propagationHasOccurred = false;

            y.domain.in(store.level, y, x.domain);

        } while (store.propagationHasOccurred);

    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public void notConsistency(final Store store) {

        if (y.singleton())
            x.domain.inComplement(store.level, x, y.value());

        if (x.singleton())
            y.domain.inComplement(store.level, y, x.value());

    }

    @Override public boolean notSatisfied() {
        return !x.domain.isIntersecting(y.domain);
    }

    @Override public boolean satisfied() {
        // return grounded() && x.min() == y.min();  // inefficient grounded() :(
	int xMin = x.min();
	return x.singleton(xMin) && y.singleton(xMin);
    }

    @Override public String toString() {
        return id() + " : XeqY(" + x + ", " + y + " )";
    }

}
