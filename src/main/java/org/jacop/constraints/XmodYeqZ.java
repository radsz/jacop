/*
 * XmodYeqZ.java
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
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntDomain;
import org.jacop.core.IntervalDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Store;
import java.util.concurrent.atomic.AtomicInteger;

/*
 * Constraint X mod Y = Z
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */

public class XmodYeqZ extends Constraint implements SatisfiedPresent {

    static final AtomicInteger idNumber = new AtomicInteger(0);

    /*
     * It specifies variable x in constraint x mod y = z.
     */
    public final IntVar x;

    /*
     * It specifies variable y in constraint x mod y = z.
     */
    public final IntVar y;

    /*
     * It specifies variable z in constraint x mod y = z.
     */
    public final IntVar z;

    /**
     * It constructs a constraint X mod Y = Z.
     *
     * @param x variable x.
     * @param y variable y.
     * @param z variable z.
     */
    public XmodYeqZ(IntVar x, IntVar y, IntVar z) {

        checkInputForNullness(new String[] {"x", "y", "z"}, new Object[] {x, y, z});

        numberId = idNumber.incrementAndGet();

        this.x = x;
        this.y = y;
        this.z = z;

        setScope(x, y, z);
    }

    @Override public void consistency(final Store store) {

        int resultMin = IntDomain.MinInt;
        int resultMax = IntDomain.MaxInt;

        y.domain.inComplement(store.level, y, 0);

        do {

            store.propagationHasOccurred = false;

            // Compute bounds for reminder

            int reminderMin;
            int reminderMax;

            if (x.min() >= 0) {
                reminderMin = 0;
                reminderMax = Math.max(Math.abs(y.min()), Math.abs(y.max())) - 1;

                reminderMax = Math.min(reminderMax, x.max());

            } else if (x.max() < 0) {
                reminderMax = 0;
                reminderMin = -Math.max(Math.abs(y.min()), Math.abs(y.max())) + 1;

                reminderMin = Math.max(reminderMin, x.min());

            } else {
                reminderMin = Math.min(Math.min(y.min(), -y.min()), Math.min(y.max(), -y.max())) + 1;
                reminderMax = Math.max(Math.max(y.min(), -y.min()), Math.max(y.max(), -y.max())) - 1;

                reminderMin = Math.max(reminderMin, x.min());
                reminderMax = Math.min(reminderMax, x.max());

            }

            z.domain.in(store.level, z, reminderMin, reminderMax);

            if (y.singleton()) {
                if (x.domain.getSize() < 100) {
                    // domain consistency method for small domains of x
                    int absY = Math.abs(y.value());
                    IntDomain d = makeDomain(x, absY, z);
                    x.domain.in(store.level, x, d);
                } else {
                    // bound consistency
                    int absY = Math.abs(y.value());
                    IntDomain zDom = z.dom();

                    // compute LB
                    int xMin = x.min();
                    boolean found = false;
                    for (ValueEnumeration e = x.domain.valueEnumeration(); e.hasMoreElements(); ) {
                        xMin = e.nextElement();
                        if (zDom.contains(xMin % absY)) {
                            found = true;
                            break;
                        }
                    }
                    if (found)
                        x.domain.inMin(store.level, x, xMin);
                    else
                        throw Store.failException;

                    // compute UB
                    int xMax = x.max();
                    xMin = x.min();
                    while (!zDom.contains(xMax % absY) && xMax >= xMin) {
                        xMax--;
                    }
                    if (xMax >= xMin)
                        x.domain.inMax(store.level, x, xMax);
                    else
                        throw Store.failException;
                }
            }
            
            if (x.singleton())
                if (! z.domain.contains(x.value() % Math.abs(y.min())))
                    y.domain.inMin(store.level, y, y.min() + 1);
                else if (! z.domain.contains(x.value() % Math.abs(y.max())))
                    y.domain.inMax(store.level, y, y.max() - 1);
            
            reminderMin = z.min();
            reminderMax = z.max();

            if (!(y.min() <= 0 && y.max() >= 0)) {

                // Bounds for result
                int oldResultMin = resultMin;
                int oldResultMax = resultMax;

                Interval result = IntDomain.divBounds(x.min(), x.max(), y.min(), y.max());

                resultMin = result.min();
                resultMax = result.max();

                if (oldResultMin != resultMin || oldResultMax != resultMax)
                    store.propagationHasOccurred = true;

                // Bounds for Y
                Interval yBounds = IntDomain.divBounds(x.min() - reminderMax, x.max() - reminderMin, resultMin, resultMax);

                y.domain.in(store.level, y, yBounds.min(), yBounds.max());

                // Bounds for Z and reminder
                Interval reminder = IntDomain.mulBounds(resultMin, resultMax, y.min(), y.max());
                int zMin = reminder.min();
                int zMax = reminder.max();

                reminderMin = x.min() - zMax;
                reminderMax = x.max() - zMin;

                z.domain.in(store.level, z, reminderMin, reminderMax);

                x.domain.in(store.level, x, zMin + z.min(), zMax + z.max());
            }

        } while (store.propagationHasOccurred);

        assert checkSolution(resultMin, resultMax) == null : checkSolution(resultMin, resultMax);

    }

    IntDomain makeDomain(IntVar x, int y, IntVar z) {
        IntervalDomain d = new IntervalDomain();
        boolean empty = true;
        IntDomain zDom = z.dom();
        for (ValueEnumeration e = x.domain.valueEnumeration(); e.hasMoreElements(); ) {
            int val = e.nextElement();
            if (zDom.contains(val % y)) {
                empty = false;
                if (d.getSize() == 0)
                    d.unionAdapt(val);
                else
                    d.addLastElement(val);
            }
        }
        if (empty)
            throw Store.failException;
        return d;
    }
    
    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public boolean satisfied() {
        return grounded() && z.min() == mod(x.min(), y.min());
    }

    @Override public String toString() {

        return id() + " : XmodYeqZ(" + x + ", " + y + ", " + z + " )";
    }

    private String checkSolution(int resultMin, int resultMax) {
        String result = null;

        if (z.singleton() && y.singleton() && x.singleton()) {
            result = "Operation mod does not hold " + x + " mod " + y + " = " + z + "(result " + resultMin + ".." + resultMax;
            for (int i = resultMin; i <= resultMax; i++) {
                if (i * y.value() + z.value() == x.value())
                    result = null;
            }
        } else
            result = null;
        return result;
    }

    private int div(int a, int b) {
        return (int) Math.floor((float) a / (float) b);
    }

    private int mod(int a, int b) {
        return a - div(a, b) * b;
    }

}
