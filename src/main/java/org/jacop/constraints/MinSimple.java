/*
 * MinSimple.java
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
 * MinSimple constraint implements the minimum/2 constraint. It provides the minimum
 * variable from all variables on the list.
 * <p>
 * min(x1, x2) = min.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class MinSimple extends Constraint implements SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a variables between which a minimum value is being searched for.
     */
    final public IntVar x1, x2;

    /**
     * It specifies variable min which stores the minimum value present in the list.
     */
    final public IntVar min;

    /**
     * It constructs min constraint.
     *
     * @param min variable denoting the minimum value
     * @param x1  first variable for which a  minimum value is imposed.
     * @param x2  second variable for which a  minimum value is imposed.
     */
    public MinSimple(IntVar x1, IntVar x2, IntVar min) {

        checkInputForNullness(new String[] {"x1", "x2", "min"}, new Object[] {x1, x2, min});

        this.numberId = idNumber.incrementAndGet();
        this.min = min;
        this.x1 = x1;
        this.x2 = x2;

        this.queueIndex = 1;

        setScope(x1, x2, min);

    }

    @Override public void consistency(final Store store) {

        int minMin = min.min();

        x1.domain.inMin(store.level, x1, minMin);
        x2.domain.inMin(store.level, x2, minMin);

        int minValue = (x1.min() > x2.min()) ? x2.min() : x1.min();
        int maxValue = (x1.max() > x2.max()) ? x2.max() : x1.max();

        min.domain.in(store.level, min, minValue, maxValue);

        if (x1.min() > min.max())
            x2.domain.in(store.level, x2, min.dom());
        if (x2.min() > min.max())
            x1.domain.in(store.level, x1, min.dom());

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    public boolean satisfied() {

        int MIN = min.max();
        return x1.min() >= MIN && x2.min() >= MIN;

    }

    @Override public String toString() {

        return id() + " : minSimple(" + x1 + ", " + x2 + ", " + min + ")";

    }

}
