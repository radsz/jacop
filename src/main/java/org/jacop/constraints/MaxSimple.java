/*
 * MaxSimple.java
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
 * MaxSimple constraint implements the Maximum/2 constraint. It provides the maximum
 * variable from all variables on the list.
 * <p>
 * max(x1, x2) = max.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class MaxSimple extends Constraint implements SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a variables between which a maximum value is being searched for.
     */
    final public IntVar x1, x2;

    /**
     * It specifies variable max which stores the maximum value present in the list.
     */
    final public IntVar max;

    /**
     * It constructs max constraint.
     *
     * @param max variable denoting the maximum value
     * @param x1  first variable for which a  maximum value is imposed.
     * @param x2  second variable for which a  maximum value is imposed.
     */
    public MaxSimple(IntVar x1, IntVar x2, IntVar max) {

        checkInputForNullness(new String[] {"x1", "x2", "max"}, new Object[] {x1, x2, max});

        this.numberId = idNumber.incrementAndGet();
        this.max = max;
        this.x1 = x1;
        this.x2 = x2;

        this.queueIndex = 1;

        setScope(x1, x2, max);
    }

    @Override public void consistency(Store store) {

        int maxMax = max.max();

        x1.domain.inMax(store.level, x1, maxMax);
        x2.domain.inMax(store.level, x2, maxMax);

        int minValue = (x1.min() > x2.min()) ? x1.min() : x2.min();
        int maxValue = (x1.max() > x2.max()) ? x1.max() : x2.max();

        max.domain.in(store.level, max, minValue, maxValue);

        if (x1.max() < max.min())
            x2.domain.in(store.level, x2, max.dom());
        if (x2.max() < max.min())
            x1.domain.in(store.level, x1, max.dom());

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public boolean satisfied() {

        int MAX = max.min();

        return x1.max() <= MAX && x2.max() <= MAX;
    }

    @Override public String toString() {

        return id() + " : maxSimple(" + x1 + ", " + x2 + ", " + max + ")";

    }

}
