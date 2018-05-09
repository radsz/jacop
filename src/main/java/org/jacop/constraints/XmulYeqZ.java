/*
 * XmulYeqZ.java
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

import org.jacop.api.SatisfiedPresent;
import org.jacop.core.*;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * Constraint X * Y #= Z
 * <p>
 * Boundary consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class XmulYeqZ extends Constraint implements SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x in constraint x * y = z.
     */
    final public IntVar x;

    /**
     * It specifies variable y in constraint x * y = z.
     */
    final public IntVar y;

    /**
     * It specifies variable z in constraint x * y = z.
     */
    final public IntVar z;

    private final boolean xSquare;

    /**
     * It constructs a constraint X * Y = Z.
     *
     * @param x variable x.
     * @param y variable y.
     * @param z variable z.
     */
    public XmulYeqZ(IntVar x, IntVar y, IntVar z) {

        checkInputForNullness(new String[] {"x", "y", "z"}, new Object[] {x, y, z});

        numberId = idNumber.incrementAndGet();

        xSquare = (x == y);

        this.x = x;
        this.y = y;
        this.z = z;

        // checkForOverflow();

        setScope(x, y, z);
    }

    @Override public void consistency(Store store) {

        if (xSquare)  // X^2 = Z
            do {

                // Bounds for Z
                Interval zBounds = IntDomain.squareBounds(x.min(), x.max());
                z.domain.in(store.level, z, zBounds.min(), zBounds.max());

                store.propagationHasOccurred = false;

                // Bounds for X

                int xMin = toInt(Math.round(Math.ceil(Math.sqrt((double) z.min()))));
                int xMax = toInt(Math.round(Math.floor(Math.sqrt((double) z.max()))));

                if (xMin > xMax)
                    throw Store.failException;

                IntDomain dom = new IntervalDomain(-xMax, -xMin);
                dom.unionAdapt(xMin, xMax);

                x.domain.in(store.level, x, dom);

            } while (store.propagationHasOccurred);
        else    // X*Y=Z
            do {

                // Bounds for X
                Interval xBounds = IntDomain.divIntBounds(z.min(), z.max(), y.min(), y.max());

                x.domain.in(store.level, x, xBounds.min(), xBounds.max());

                store.propagationHasOccurred = false;

                // Bounds for Y
                Interval yBounds = IntDomain.divIntBounds(z.min(), z.max(), x.min(), x.max());

                y.domain.in(store.level, y, yBounds.min(), yBounds.max());

                // Bounds for Z
                Interval zBounds = IntDomain.mulBounds(x.min(), x.max(), y.min(), y.max());

                z.domain.in(store.level, z, zBounds.min(), zBounds.max());


            } while (store.propagationHasOccurred);

        if (x.singleton(0) || y.singleton(0))
            removeConstraint();
        else if (y.singleton(1)) {
            removeConstraint();
            if (!x.singleton() || !z.singleton())
                store.impose(new XeqY(x, z));
        } else if (x.singleton(1)) {
            removeConstraint();
            if (!y.singleton() || !z.singleton())
                store.impose(new XeqY(y, z));
        }
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public boolean satisfied() {
        return grounded() && x.min() * y.min() == z.min();
    }

    @Override public String toString() {

        return id() + " : XmulYeqZ(" + x + ", " + y + ", " + z + " )";
    }

}
