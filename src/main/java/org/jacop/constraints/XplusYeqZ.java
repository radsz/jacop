/*
 * XplusYeqZ.java
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
 * Constraint X + Y = Z
 *
 * Bound consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class XplusYeqZ extends PrimitiveConstraint {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x in constraint x+y=z.
     */
    final public IntVar x;

    /**
     * It specifies variable x in constraint x+y=z.
     */
    final public IntVar y;

    /**
     * It specifies variable x in constraint x+y=z.
     */
    final public IntVar z;

    /** It constructs constraint X+Y=Z.
     * @param x variable x.
     * @param y variable y.
     * @param z variable z.
     */
    public XplusYeqZ(IntVar x, IntVar y, IntVar z) {

        checkInputForNullness(new String[]{"x", "y", "z"}, new Object[]{x, y, z});

        numberId = idNumber.incrementAndGet();

        this.x = x;
        this.y = y;
        this.z = z;

        checkForOverflow();

        setScope(x, y, z);
    }

    @Override public void consistency(final Store store) {

        do {

            store.propagationHasOccurred = false;

            if (x.singleton()) {

                y.domain.inShift(store.level, y, z.domain, -x.value());
                z.domain.inShift(store.level, z, y.domain, x.value());

            } else if (y.singleton()) {

                x.domain.inShift(store.level, x, z.domain, -y.value());
                z.domain.inShift(store.level, z, x.dom(), y.value());

            } else {

                x.domain.in(store.level, x, z.min() - y.max(), z.max() - y.min());
                y.domain.in(store.level, y, z.min() - x.max(), z.max() - x.min());
                z.domain.in(store.level, z, x.min() + y.min(), x.max() + y.max());
            }

        } while (store.propagationHasOccurred);

    }

    void checkForOverflow() {

        int sumMin = 0, sumMax = 0;

        sumMin = Math.addExact(sumMin, x.min());
        sumMax = Math.addExact(sumMax, x.max());

        sumMin = Math.addExact(sumMin, y.min());
        sumMax = Math.addExact(sumMax, y.max());

        Math.subtractExact(sumMin, z.max());
        Math.subtractExact(sumMax, z.min());
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }


    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public void notConsistency(final Store store) {

        do {

            store.propagationHasOccurred = false;

            if (z.singleton() && y.singleton())
                x.domain.inComplement(store.level, x, z.min() - y.min());

            if (z.singleton() && x.singleton())
                y.domain.inComplement(store.level, y, z.min() - x.min());

            if (x.singleton() && y.singleton())
                z.domain.inComplement(store.level, z, x.min() + y.min());

        } while (store.propagationHasOccurred);

    }

    @Override public boolean notSatisfied() {
        IntDomain xDom = x.dom(), yDom = y.dom(), zDom = z.dom();
        return (xDom.max() + yDom.max() < zDom.min() || xDom.min() + yDom.min() > zDom.max());
    }

    @Override public boolean satisfied() {

        // return (grounded() && x.value() + y.value() == z.value());
	int xMin = x.min(), yMin = y.min(), zMin = z.min();
	return x.singleton(xMin) && y.singleton(yMin) && z.singleton(zMin) && xMin + yMin == zMin;
    }

    @Override public String toString() {

        return id() + " : XplusYeqZ(" + x + ", " + y + ", " + z + " )";
    }

}
