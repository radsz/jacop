/*
 * XplusYgtC.java
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
 * Constraint X + Y{@literal >} C
 *
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class XplusYgtC extends PrimitiveConstraint {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x in constraint x + y{@literal >} c.
     */
    final public IntVar x;

    /**
     * It specifies variable y in constraint x + y{@literal >} c.
     */
    final public IntVar y;

    /**
     * It specifies constant c in constraint x + y{@literal >} c.
     */
    final public int c;

    /**
     * It constructs X+Y{@literal >} C constraint.
     * @param x variable x.
     * @param y variable y.
     * @param c variable c.
     */
    public XplusYgtC(IntVar x, IntVar y, int c) {

        checkInputForNullness(new String[]{"x", "y"}, new Object[]{x, y});

        numberId = idNumber.incrementAndGet();

        this.x = x;
        this.y = y;
        this.c = c;

        setScope(x, y);
    }

    @Override public void consistency(final Store store) {

            x.domain.inMin(store.level, x, c - y.max() + 1);
            y.domain.inMin(store.level, y, c - x.max() + 1);
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public void notConsistency(final Store store) {

            x.domain.inMax(store.level, x, c - y.min());
            y.domain.inMax(store.level, y, c - x.min());
    }

    @Override public boolean notSatisfied() {
        return x.max() + y.max() <= c;
    }

    @Override public boolean satisfied() {
        return x.min() + y.min() > c;
    }

    @Override public String toString() {

        return id() + " : XplusYgtC(" + x + ", " + y + ", " + c + " )";
    }

}
