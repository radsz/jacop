/**
 * XplusYeqC.java
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
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 *
 * Constraint X + Y #= C
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.4
 */

public class XplusYeqC extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x in constraint x+y=c.
     */
    public IntVar x;

    /**
     * It specifies variable y in constraint x+y=c.
     */
    public IntVar y;

    /**
     * It specifies constant c in constraint x+y=c.
     */
    int c;

    /**
     * It constructs the constraint X+Y=C.
     * @param x variable x.
     * @param y variable y.
     * @param c constant c.
     */
    public XplusYeqC(IntVar x, IntVar y, int c) {

        assert (x != null) : "Variable x is null";
        assert (y != null) : "Variable y is null";

        numberId = idNumber.incrementAndGet();
        numberArgs = 2;

        this.x = x;
        this.y = y;
        this.c = c;

        setScope(x, y);
    }

    @Override public void consistency(Store store) {

        do {

            store.propagationHasOccurred = false;

            // FIXME, make propagation without object creation, scan x ->, and y <-, at the same time.
            IntDomain xDom = x.dom();
            IntervalDomain yDomIn = new IntervalDomain(xDom.noIntervals() + 1);
            for (int i = xDom.noIntervals() - 1; i >= 0; i--)
                yDomIn.unionAdapt(new Interval(c - xDom.rightElement(i), c - xDom.leftElement(i)));

            y.domain.in(store.level, y, yDomIn);

            IntDomain yDom = y.domain;
            IntervalDomain xDomIn = new IntervalDomain(yDom.noIntervals() + 1);
            for (int i = yDom.noIntervals() - 1; i >= 0; i--)
                xDomIn.unionAdapt(new Interval(c - yDom.rightElement(i), c - yDom.leftElement(i)));

            x.domain.in(store.level, x, xDomIn);

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

    @Override public void notConsistency(Store store) {

        do {

            store.propagationHasOccurred = false;

            if (x.singleton())
                y.domain.inComplement(store.level, y, c - x.value());
            else if (y.singleton())
                x.domain.inComplement(store.level, x, c - y.value());


        } while (store.propagationHasOccurred);

    }

    @Override public boolean notSatisfied() {
        IntDomain Xdom = x.dom(), Ydom = y.dom();
        return (Xdom.max() + Ydom.max() < c || Xdom.min() + Ydom.min() > c);
    }

    @Override public boolean satisfied() {
        IntDomain Xdom = x.dom(), Ydom = y.dom();

        return (Xdom.singleton() && Ydom.singleton() && (Xdom.min() + Ydom.min() == c));

    }

    @Override public String toString() {

        return id() + " : XplusYeqC(" + x + ", " + y + ", " + c + " )";
    }

}
