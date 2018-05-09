/*
 * XplusYplusCeqZ.java
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
 * Constraints X + Y + C #= Z.
 *
 * Bound consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class XplusYplusCeqZ extends PrimitiveConstraint {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x in constraint x + y + c = z.
     */
    final IntVar x;

    /**
     * It specifies variable x in constraint x + y + c = z.
     */
    final IntVar y;

    /**
     * It specifies variable x in constraint x + y + c = z.
     */
    final int c;

    /**
     * It specifies variable x in constraint x + y + c = z.
     */
    final IntVar z;

    /**
     * It constructs constraint X+Y+C=Z.
     * @param x variable X.
     * @param y variable Y.
     * @param c constant C.
     * @param z variable Z.
     */
    public XplusYplusCeqZ(IntVar x, IntVar y, int c, IntVar z) {

        checkInputForNullness(new String[]{"x", "y", "z"}, new Object[]{x, y, z});

        numberId = idNumber.incrementAndGet();

        this.x = x;
        this.y = y;
        this.c = c;
        this.z = z;

        setScope(x, y, z);
    }

    @Override public void consistency(final Store store) {

        do {

            store.propagationHasOccurred = false;

            x.domain.in(store.level, x, z.min() - y.max() - c, z.max() - y.min() - c);

            y.domain.in(store.level, y, z.min() - x.max() - c, z.max() - x.min() - c);

            z.domain.in(store.level, z, x.min() + y.min() + c, x.max() + y.max() + c);

        } while (store.propagationHasOccurred);

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }
    
    @Override public void notConsistency(final Store store) {

        do {

            store.propagationHasOccurred = false;

            if (z.singleton() && y.singleton())
                x.domain.inComplement(store.level, x, z.min() - y.min() - c);

            if (z.singleton() && x.singleton())
                y.domain.inComplement(store.level, y, z.min() - x.min() - c);

            if (x.singleton() && y.singleton())
                z.domain.inComplement(store.level, z, x.min() + y.min() + c);

        } while (store.propagationHasOccurred);

    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }
    
    @Override public boolean notSatisfied() {
        return (x.max() + y.max() + c < z.min() || x.min() + y.min() + c > z.max());
    }

    @Override public boolean satisfied() {
        return grounded() && x.min() + y.min() + c == z.min();
    }

    @Override public String toString() {
        return id() + " : XplusYplusQeqZ(" + x + ", " + y + ", " + ", " + c + ", " + z + " )";
    }

}
