/**
 * XmulCeqZ.java
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
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.FailException;

/**
 * Constraint X * C #= Z
 *
 * Boundary consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 3.1
 */

public class XmulCeqZ extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x in constraint x * c = z.
     */
    public IntVar x;

    /**
     * It specifies constant c in constraint x * c = z.
     */
    public int c;

    /**
     * It specifies variable x in constraint x * c = z.
     */
    public IntVar z;

    /**
     * It constructs a constraint X * C = Z.
     * @param x variable x.
     * @param c constant c.
     * @param z variable z.
     */
    public XmulCeqZ(IntVar x, int c, IntVar z) {

        assert (x != null) : "Variable x is null";
        assert (z != null) : "Variable z is null";

        numberId = idNumber.incrementAndGet();
        numberArgs = 2;

        this.x = x;
        this.c = c;
        this.z = z;

        checkForOverflow();

        setScope(x, z);
    }

    @Override public void consistency(Store store) {

        if (c != 0)
            do {

                store.propagationHasOccurred = false;

                // Bounds for X
                Interval xBounds = IntDomain.divIntBounds(z.min(), z.max(), c, c);

                x.domain.in(store.level, x, xBounds.min(), xBounds.max());

                // Bounds for Z
                Interval zBounds = IntDomain.mulBounds(x.min(), x.max(), c, c);

                z.domain.in(store.level, z, zBounds.min(), zBounds.max());

            } while (store.propagationHasOccurred);
        else
            z.domain.in(store.level, z, 0, 0);
    }

    @Override public void notConsistency(Store store) {

        if (c != 0) {

            if (x.singleton())

                z.domain.inComplement(store.level, z, x.value() * c);

            if (z.singleton()) {
                Interval xBounds;

                try {
                    xBounds = IntDomain.divIntBounds(z.min(), z.max(), c, c);
                } catch (FailException e) {
                    // z/c does not produce integer value; nothing to do since inequality holds
                    return;
                }

                x.domain.inComplement(store.level, x, xBounds.min());
            }

        } else
            z.domain.inComplement(store.level, z, 0);
    }

    @Override public boolean satisfied() {
        IntDomain Xdom = x.dom(), Zdom = z.dom();
        return Xdom.singleton() && Zdom.singleton() && Xdom.min() * c == Zdom.min();
    }

    @Override public boolean notSatisfied() {

        Interval r = IntDomain.mulBounds(x.min(), x.max(), c, c);
        return !z.domain.isIntersecting(r.min(), r.max());

        // IntDomain Xdom = x.dom();
        // IntDomain Zdom = z.dom();
        // return Xdom.singleton() && Zdom.singleton() && Xdom.min() * c != Zdom.min();
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }


    @Override public String toString() {

        return id() + " : XmulCeqZ(" + x + ", " + c + ", " + z + " )";
    }

    private void checkForOverflow() {

        Math.multiplyExact(x.min(), c);
        Math.multiplyExact(x.max(), c);

    }

}
