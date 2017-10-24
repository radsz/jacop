/*
 * PmulCeqR.java
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

import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;

import org.jacop.constraints.Constraint;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;

/**
 * Constraint P * C = R for floats
 *
 * Boundary consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class PmulCeqR extends Constraint implements SatisfiedPresent {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable p in constraint p * c = r. 
     */
    public FloatVar p;

    /**
     * It specifies constants c in constraint p * c = r. 
     */
    public double c;

    /**
     * It specifies variable r in constraint p * c = r. 
     */
    public FloatVar r;

    /**
     * It constructs a constraint P * C = R.
     * @param p variable p.
     * @param c constnat c.
     * @param r variable r.
     */
    public PmulCeqR(FloatVar p, double c, FloatVar r) {

        checkInputForNullness(new String[]{"p", "r"}, new Object[]{p, r});

        numberId = idNumber.incrementAndGet();

        this.p = p;
        this.c = c;
        this.r = r;

        setScope(p, r);
    }

    @Override public void consistency(Store store) {


        do {

            store.propagationHasOccurred = false;

            // Bounds for P
            FloatIntervalDomain pBounds = FloatDomain.divBounds(r.min(), r.max(), c, c);

            p.domain.in(store.level, p, pBounds); //.min(), pBounds.max());

            // Bounds for R
            FloatIntervalDomain rBounds = FloatDomain.mulBounds(p.min(), p.max(), c, c);

            r.domain.in(store.level, r, rBounds); //.min(), rBounds.max());

        } while (store.propagationHasOccurred);

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public boolean satisfied() {
        FloatDomain pDom = p.dom(), rDom = r.dom();
        return grounded() &&
               rDom.eq(FloatDomain.mulBounds(pDom.min(), pDom.max(), c, c));
    }

    @Override public String toString() {
        return id() + " : PmulCeqR(" + p + ", " + c + ", " + r + " )";
    }

    public FloatVar derivative(Store store, FloatVar f, java.util.Set<FloatVar> vars, FloatVar x) {

        if (f.equals(r)) {
            // f = c * p
            // f' = c * d(p)
            FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
            Derivative.poseDerivativeConstraint(new PmulCeqR(Derivative.getDerivative(store, p, vars, x), c, v));
            return v;
        } else if (f.equals(p)) {
            // f = 1/c * r
            // f' = 1/c * d(r)
            FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
            Derivative.poseDerivativeConstraint(new PmulCeqR(Derivative.getDerivative(store, r, vars, x), 1 / c, v));
            return v;
        }

        return null;
    }
}
