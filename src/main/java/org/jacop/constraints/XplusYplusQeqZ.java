/*
 * XplusYplusQeqZ.java
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
 * Constraint X + Y + Q = Z
 *
 * Bound consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class XplusYplusQeqZ extends PrimitiveConstraint {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x in constraint x + y + q = z.
     */
    final public IntVar x;

    /**
     * It specifies variable y in constraint x + y + q = z.
     */
    final public IntVar y;

    /**
     * It specifies variable q in constraint x + y + q = z.
     */
    final public IntVar q;

    /**
     * It specifies variable z in constraint x + y + q = z.
     */
    final public IntVar z;

    /**
     * It constructs X+Y+Q=Z constraint.
     * @param x variable x.
     * @param y variable y.
     * @param q variable q.
     * @param z variable z.
     */
    public XplusYplusQeqZ(IntVar x, IntVar y, IntVar q, IntVar z) {

        checkInputForNullness(new String[]{"x", "y", "q", "z"}, new Object[]{x, y, q, z});

        numberId = idNumber.incrementAndGet();

        this.x = x;
        this.y = y;
        this.q = q;
        this.z = z;

        setScope(x, y, q, z);
    }

    @Override public void consistency(final Store store) {

        do {

            store.propagationHasOccurred = false;

            x.domain.in(store.level, x, z.min() - y.max() - q.max(), z.max() - y.min() - q.min());
            y.domain.in(store.level, y, z.min() - x.max() - q.max(), z.max() - x.min() - q.min());
            q.domain.in(store.level, q, z.min() - x.max() - y.max(), z.max() - x.min() - y.min());
            z.domain.in(store.level, z, x.min() + y.min() + q.min(), x.max() + y.max() + q.max());

        } while (store.propagationHasOccurred);

    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.BOUND;
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

            if (z.singleton() && y.singleton() && q.singleton())
                x.domain.inComplement(store.level, x, z.min() - y.min() - q.min());

            if (z.singleton() && x.singleton() && q.singleton())
                y.domain.inComplement(store.level, y, z.min() - x.min() - q.min());

            if (z.singleton() && x.singleton() && y.singleton())
                q.domain.inComplement(store.level, q, z.min() - x.min() - y.min());

            if (x.singleton() && y.singleton() && q.singleton())
                z.domain.inComplement(store.level, z, x.min() + y.min() + q.min());

        } while (store.propagationHasOccurred);

    }

    @Override public boolean notSatisfied() {
        return (x.max() + y.max() + q.max() < z.min() || x.min() + y.min() + q.min() > z.max());
    }

    @Override public boolean satisfied() {
        return grounded() && x.min() + y.min() + q.min() == z.min();
    }

    @Override public String toString() {

        return id() + " : XplusYplusQeqZ(" + x + ", " + y + ", " + ", " + q + ", " + z + " )";
    }

}
