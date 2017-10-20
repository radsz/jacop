/*
 * XexpYeqZ.java
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
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * Constraint X ^ Y #= Z
 * <p>
 * Boundary consistecny is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class XexpYeqZ extends Constraint implements SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies the variable x in equation x^y = z.
     */
    final public IntVar x;

    /**
     * It specifies the variable y in equation x^y = z.
     */
    final public IntVar y;

    /**
     * It specifies the variable z in equation x^y = z.
     */
    final public IntVar z;

    /**
     * It constructs constraint X^Y=Z.
     *
     * @param x variable x.
     * @param y variable y.
     * @param z variable z.
     */
    public XexpYeqZ(IntVar x, IntVar y, IntVar z) {

        checkInputForNullness(new String[] {"x", "y", "z"}, new Object[] {x, y, z});

        numberId = idNumber.incrementAndGet();

        this.x = x;
        this.y = y;
        this.z = z;

        setScope(x, y, z);

    }

    private double aLog(double a, double x) {
        return Math.log(x) / Math.log(a);
    }

    @Override public void consistency(Store store) {

        double xMin, xMax, yMin, yMax, zMin, zMax;

        do {

            store.propagationHasOccurred = false;

            if (x.min() >= 0 && y.min() > 0) {

                // compute bounds for z
                zMin = Math.max(Math.pow(x.min(), y.min()), z.min());
                zMax = Math.min(Math.pow(x.max(), y.max()), z.max());

                int zMinInt = toInt(Math.floor(zMin)), zMaxInt = toInt(Math.ceil(zMax));

                if (zMinInt > zMaxInt)
                    throw Store.failException;
                else
                    z.domain.in(store.level, z, zMinInt, zMaxInt);

                // compute bounds for x
                xMin = Math.max(Math.pow(z.min(), 1.0 / y.max()), x.min());
                xMax = Math.min(Math.pow(z.max(), 1.0 / y.min()), x.max());

                int xMinInt = toInt(Math.floor(xMin)), xMaxInt = toInt(Math.ceil(xMax));

                if (xMinInt > xMaxInt)
                    throw Store.failException;
                else
                    x.domain.in(store.level, x, xMinInt, xMaxInt);

                // compute bounds for y
                if (x.max() == 0 || z.min() == 0)
                    yMin = y.min();
                else if (x.max() != 1)
                    yMin = Math.max(aLog(x.max(), z.min()), y.min());
                else
                    yMin = y.min();
                if (x.min() == 0 || z.max() == 0)
                    yMax = y.max();
                else if (x.min() != 1)
                    yMax = Math.min(aLog(x.min(), z.max()), y.max());
                else
                    yMax = y.max();

                int yMinInt = toInt(Math.floor(yMin)), yMaxInt = toInt(Math.ceil(yMax));

                if (yMinInt > yMaxInt)
                    throw Store.failException;
                else
                    y.domain.in(store.level, y, yMinInt, yMaxInt);

            } else if (x.singleton() && y.singleton()) {  // x.min() < 0 || y.min() <= 0

                double zValue = Math.pow((double) x.value(), (double) y.value());

                if (zValue < (double) Integer.MIN_VALUE || zValue > (double) Integer.MAX_VALUE)
                    throw Store.failException;

                double z1 = Math.floor(zValue);
                double z2 = Math.ceil(zValue);

                if (z1 == z2)
                    z.domain.in(store.level, z, toInt(z1), toInt(z1));
                else
                    throw Store.failException;
            } else if (y.singleton(0))
                z.domain.in(store.level, z, 1, 1);
            else if (y.max() < -1) {
                x.domain.in(store.level, x, -1, 1);
                z.domain.in(store.level, z, -1, 1);
            }

        } while (store.propagationHasOccurred);

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public boolean satisfied() {

        return grounded() && Math.pow(x.min(), y.min()) == z.min();

    }

    @Override public String toString() {

        return id() + " : XexpYeqZ(" + x + ", " + y + ", " + z + " )";

    }

}
