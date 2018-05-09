/*
 * PplusQeqZ.java
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
import org.jacop.floats.core.FloatIntervalDomain;

/**
 * Constraint P + Q = R
 *
 * Bound consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */
public class PplusQeqR extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable p in constraint p+q=r. 
     */
    public FloatVar p;

    /**
     * It specifies variable q in constraint p+q=r. 
     */
    public FloatVar q;

    /**
     * It specifies variable r in constraint p+q=r. 
     */
    public FloatVar r;

    /** It constructs constraint P+Q=R.
     * @param p variable p.
     * @param q variable q.
     * @param r variable r.
     */
    public PplusQeqR(FloatVar p, FloatVar q, FloatVar r) {

        checkInputForNullness(new String[]{"p", "q", "r"}, new Object[]{p, q, r});

        numberId = idNumber.incrementAndGet();

        this.p = p;
        this.q = q;
        this.r = r;

        setScope(p, q, r);
    }

    @Override public void consistency(Store store) {

        // identity elements
        if (p.equals(r)) {
            q.domain.in(store.level, q, 0.0, 0.0);
            return;
        } else if (q.equals(r)) {
            p.domain.in(store.level, p, 0.0, 0.0);
            return;
        }

        do {
            store.propagationHasOccurred = false;

            FloatIntervalDomain pDom = FloatDomain.subBounds(r.min(), r.max(), q.min(), q.max());
            p.domain.in(store.level, p, pDom.min(), pDom.max());

            FloatIntervalDomain qDom = FloatDomain.subBounds(r.min(), r.max(), p.min(), p.max());
            q.domain.in(store.level, q, qDom.min(), qDom.max());

            FloatIntervalDomain rDom = FloatDomain.addBounds(p.min(), p.max(), q.min(), q.max());
            r.domain.in(store.level, r, rDom.min(), rDom.max());

        } while (store.propagationHasOccurred);

    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public void notConsistency(Store store) {

        do {

            store.propagationHasOccurred = false;

            if (r.singleton() && q.singleton())
                p.domain.inComplement(store.level, p, r.min() - q.min());

            if (r.singleton() && p.singleton())
                q.domain.inComplement(store.level, q, r.min() - p.min());

            if (p.singleton() && q.singleton())
                r.domain.inComplement(store.level, r, p.min() + q.min());

        } while (store.propagationHasOccurred);

    }

    @Override public boolean notSatisfied() {
        FloatDomain pDom = p.dom(), qDom = q.dom(), rDom = r.dom();
        return (pDom.max() + qDom.max() < rDom.min() || pDom.min() + qDom.min() > rDom.max());
    }

    @Override public boolean satisfied() {
        return (p.singleton() && q.singleton() && r.singleton() && r.value() - p.value() - q.value() < FloatDomain
            .epsilon(r.value() - p.value() - q.value()));

    }

    @Override public String toString() {

        return id() + " : PplusQeqR(" + p + ", " + q + ", " + r + " )";
    }

    public FloatVar derivative(Store store, FloatVar f, java.util.Set<FloatVar> vars, FloatVar x) {
        if (f.equals(r)) {
            // f = p + q
            // f' = d(p) + d(q)
            FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
            Derivative.poseDerivativeConstraint(
                new PplusQeqR(Derivative.getDerivative(store, p, vars, x), Derivative.getDerivative(store, q, vars, x), v));
            return v;

        } else if (f.equals(p)) {
            // f = r - q
            // f' = d(r) - d(q)
            FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
            Derivative.poseDerivativeConstraint(
                new PminusQeqR(Derivative.getDerivative(store, r, vars, x), Derivative.getDerivative(store, q, vars, x), v));
            return v;

        } else if (f.equals(q)) {
            // f = r - p
            // f' = d(r) - d(p)
            FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
            Derivative.poseDerivativeConstraint(
                new PminusQeqR(Derivative.getDerivative(store, r, vars, x), Derivative.getDerivative(store, p, vars, x), v));

            return v;
        }

        return null;

    }

}
