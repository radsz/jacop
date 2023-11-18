/*
 * FloorPeqX.java
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

package org.jacop.floats.constraints;

import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * Constraints floor(P) #= X for integer variable X and float variable P.
 * <p>
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */

public class FloorPeqX extends Constraint implements SatisfiedPresent {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a left hand variable in equality constraint.
     */
    public IntVar x;

    /**
     * It specifies a right hand variable in equality constraint.
     */
    public FloatVar p;

    /**
     * It constructs constraint X = P.
     *
     * @param x variable x.
     * @param p variable p.
     */
    public FloorPeqX(FloatVar p, IntVar x) {

        checkInputForNullness(new String[] {"x", "q"}, new Object[] {x, p});

        double q = Double.max(p.min(), p.max());
        if (q >  (double)Integer.MAX_VALUE || q < (double)Integer.MIN_VALUE)
            throw new RuntimeException("Error: JaCoP cannor handle "+p+" in rounding to integer.");
        numberId = idNumber.incrementAndGet();

        this.x = x;
        this.p = p;

        setScope(x, p);
    }

    @Override public void consistency(Store store) {
        //floor(p) = x, x <= p < x+1

        do {
            p.domain.in(store.level, p, (double)x.min(), FloatDomain.previous((double)(x.max() + 1))); // p <= x+1, x <= p

            store.propagationHasOccurred = false;

            x.domain.in(store.level, x, (int)Math.floor(p.min()), (int)Math.floor(p.max()));

        } while (store.propagationHasOccurred);
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public boolean satisfied() {
        return x.singleton() &&
            p.min() >= (double)x.value() &&
            p.max() < (double)x.value() + 1.0;
    }

    @Override public String toString() {
        return id() + " : FloorPeqX(" + p + ", " + x + " )";
    }
}
