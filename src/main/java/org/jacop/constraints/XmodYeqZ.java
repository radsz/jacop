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
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.Store;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * Constraint X mod Y = Z
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class XmodYeqZ extends Constraint implements SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x in constraint x mod y = z.
     */
    final public IntVar x;

    /**
     * It specifies variable y in constraint x mod y = z.
     */
    final public IntVar y;

    /**
     * It specifies variable z in constraint x mod y = z.
     */
    final public IntVar z;

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

        do {

            store.propagationHasOccurred = false;

            y.domain.inComplement(store.level, y, 0);

            // Compute bounds for reminder

            int reminderMin, reminderMax;

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

            if (!(y.min() <= 0 && y.max() >= 0)) {

                // Bounds for result
                int oldResultMin = resultMin, oldResultMax = resultMax;

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
                int zMin = reminder.min(), zMax = reminder.max();

                reminderMin = x.min() - zMax;
                reminderMax = x.max() - zMin;

                z.domain.in(store.level, z, reminderMin, reminderMax);

                x.domain.in(store.level, x, zMin + z.min(), zMax + z.max());
            }

            assert checkSolution(resultMin, resultMax) == null : checkSolution(resultMin, resultMax);

        } while (store.propagationHasOccurred);

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
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
