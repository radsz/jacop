/*
 * XplusCeqZ.java
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
 * Constraint X + C #= Z.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class XplusCeqZ extends PrimitiveConstraint {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x in constraint x+c=z.
     */
    final public IntVar x;

    /**
     * It specifies constant c in constraint x+c=z.
     */
    final public int c;

    /**
     * It specifies variable z in constraint x+c=z.
     */
    final public IntVar z;

    /**
     * It constructs a constraint x+c=z.
     * @param x variable x.
     * @param c constant c.
     * @param z variable z.
     */
    public XplusCeqZ(IntVar x, int c, IntVar z) {

        checkInputForNullness(new String[]{"x", "z"}, new Object[]{x, z});

        numberId = idNumber.incrementAndGet();

        this.x = x;
        this.c = c;
        this.z = z;

        setScope(x, z);

    }

    @Override public void consistency(final Store store) {

        do {

            x.domain.inShift(store.level, x, z.domain, -c);

            store.propagationHasOccurred = false;

            z.domain.inShift(store.level, z, x.domain, c);

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

            if (x.singleton())
                z.domain.inComplement(store.level, z, x.min() + c);

            if (z.singleton())
                x.domain.inComplement(store.level, x, z.min() - c);

        } while (store.propagationHasOccurred);

    }

    @Override public boolean notSatisfied() {
        return (x.max() + c < z.min() || x.min() + c > z.max());

    }

    @Override public boolean satisfied() {
        // return grounded() && x.min() + c == z.min();
	int xMin = x.min(), zMin = z.min();
	return x.singleton(xMin) && z.singleton(zMin) && xMin + c == zMin;
    }

    @Override public String toString() {

        return id() + " : XplusCeqZ(" + x + ", " + c + ", " + z + " )";
    }

}
