/*
 * XmulYeqC.java
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

import org.jacop.core.*;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * Constraint X * Y #= C
 * <p>
 * Boundary consistency is used.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */

public class XmulYeqC extends PrimitiveConstraint {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x in constraint x * y = c.
     */
    final public IntVar x;

    /**
     * It specifies variable y in constraint x * y = c.
     */
    final public IntVar y;

    /**
     * It specifies constant c in constraint x * y = c.
     */
    final public int c;

    /**
     * It specifies if the constraint is actually, x^2 = c.
     */
    private final boolean xSquare;

    /**
     * It constructs constraint X * Y = C.
     *
     * @param x variable x.
     * @param y variable y.
     * @param c constant c.
     */
    public XmulYeqC(IntVar x, IntVar y, int c) {

        checkInputForNullness(new String[] {"x", "y"}, new Object[] {x, y});

        numberId = idNumber.incrementAndGet();

        xSquare = x == y;

        this.x = x;
        this.y = y;
        this.c = c;

        setScope(x, y);

    }

    @Override public void consistency(final Store store) {

        if (xSquare)  // x^2 = c
            do {

                store.propagationHasOccurred = false;

                if (c < 0)
                    throw Store.failException;

                double sqrtOfC = Math.sqrt((double) c);

                if (Math.ceil(sqrtOfC) != Math.floor(sqrtOfC))
                    throw Store.failException;

                int value = (int) sqrtOfC;

                IntDomain dom = new IntervalDomain(-value, -value);
                dom.unionAdapt(value, value);

                x.domain.in(store.level, x, dom);

            } while (store.propagationHasOccurred);
        else    // X*Y=C
            do {

                store.propagationHasOccurred = false;

                // Bounds for X
                Interval xBounds = IntDomain.divIntBounds(c, c, y.min(), y.max());

                x.domain.in(store.level, x, xBounds.min(), xBounds.max());

                // Bounds for Y
                Interval yBounds = IntDomain.divIntBounds(c, c, x.min(), x.max());

                y.domain.in(store.level, y, yBounds.min(), yBounds.max());

                // check bounds, if C is covered.
                Interval cBounds = IntDomain.mulBounds(x.min(), x.max(), y.min(), y.max());

                if (c < cBounds.min() || c > cBounds.max())
                    throw Store.failException;

            } while (store.propagationHasOccurred);

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
        return IntDomain.ANY;
    }

    @Override public void notConsistency(final Store store) {

        do {

            store.propagationHasOccurred = false;

            if (x.singleton()) {
                if (c % x.value() == 0)
                    y.domain.inComplement(store.level, y, c / x.value());
            } else if (y.singleton()) {
                if (c % y.value() == 0)
                    x.domain.inComplement(store.level, x, c / y.value());
            }

        } while (store.propagationHasOccurred);

    }

    @Override public boolean notSatisfied() {
        IntDomain Xdom = x.dom(), Ydom = y.dom();
        return (Xdom.max() * Ydom.max() < c || Xdom.min() * Ydom.min() > c);
    }

    @Override public boolean satisfied() {
        return (grounded() && (x.min() * y.min() == c));
    }

    @Override public String toString() {

        return id() + " : XmulYeqC(" + x + ", " + y + ", " + c + " )";
    }

}
