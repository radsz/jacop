/*
 * PneqQ.java
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

import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

import org.jacop.constraints.PrimitiveConstraint;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;

/**
 * Constraints P #= Q for P and Q floats
 *
 * Domain consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class PneqQ extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a left hand variable in equality constraint.
     */
    public FloatVar p;

    /**
     * It specifies a right hand variable in equality constraint.
     */
    public FloatVar q;

    /**
     * It constructs constraint P = Q.
     * @param p variable p.
     * @param q variable q.
     */
    public PneqQ(FloatVar p, FloatVar q) {

        checkInputForNullness(new String[]{"p", "q"}, new Object[]{p, q});

        numberId = idNumber.incrementAndGet();

        this.queueIndex = 0;

        this.p = p;
        this.q = q;

        setScope(p, q);
    }

    @Override public void consistency(Store store) {

        if (q.singleton())
            p.domain.inComplement(store.level, p, q.value());


        if (p.singleton())
            q.domain.inComplement(store.level, q, p.value());

    }

    @Override public void notConsistency(Store store) {

        do {

            // domain consistency
            p.domain.in(store.level, p, q.dom()); //min(), q.max());

            store.propagationHasOccurred = false;

            q.domain.in(store.level, q, p.dom()); //min(), p.max());

        } while (store.propagationHasOccurred);

    }

    @Override public boolean satisfied() {

        return !p.domain.isIntersecting(q.domain);

    }

    @Override public boolean notSatisfied() {
        return p.singleton() && q.singleton() && java.lang.Math.abs(p.min() - q.max()) <= FloatDomain.precision()
            && java.lang.Math.abs(p.max() - q.min()) <= FloatDomain.precision();
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public String toString() {
        return id() + " : PneqQ(" + p + ", " + q + " )";
    }

}
