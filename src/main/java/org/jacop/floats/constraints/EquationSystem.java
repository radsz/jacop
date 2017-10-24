/*
 * EquationSystem.java
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

import java.util.Arrays;
import java.util.stream.Stream;

import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.constraints.Constraint;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatInterval;

/**
 * EquationSystem constraint implements the multivariate interval
 * Newton method for pruning domains of variables in a system of
 * non-linear equations.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class EquationSystem extends Constraint {

    final static boolean debug = false;

    // variables defining eqations
    FloatVar[] f;

    // variables of the eqation system
    FloatVar[] x;

    MultivariateIntervalNewton newton;

    /**
     * It constructs the constraint EquationSystem.
     *
     * @param store current store
     * @param f     a variable that defines an eqation
     * @param x     variables of eqation system
     */
    public EquationSystem(Store store, FloatVar[] f, FloatVar[] x) {

        checkInputForNullness(new String[]{"f", "x"}, new Object[]{f, x});

        this.f = Arrays.copyOf(f, f.length);
        this.x = Arrays.copyOf(x, x.length);

        queueIndex = 4;

        newton = new MultivariateIntervalNewton(store, f, x);

        setScope(Stream.concat(Arrays.stream(f), Arrays.stream(x)));

    }

    @Override public void consistency(Store store) {

        FloatInterval[] xs = newton.solve();

        if (xs != null)
            for (int i = 0; i < xs.length; i++) {
                if (debug)
                    if (x[i].min() < xs[i].min() || x[i].max() > xs[i].max())
                        System.out.println("*** " + x[i] + " in " + xs[i]);

                if (!xs[i].singleton())
                    x[i].domain.in(store.level, x[i], xs[i].min(), xs[i].max());
            }
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public void impose(Store store) {

        if (f == null)
            return;

        super.impose(store);

        // TODO, why do we call consistency of the whole store inside impose function of the constraint???
        if (!store.consistency())
            throw Store.failException;

        store.addChanged(this);
        store.countConstraint();
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : EquationSystem( [ ");

        for (int i = 0; i < f.length; i++) {
            result.append(f[i]);
            if (i < f.length - 1)
                result.append(", ");
        }
        result.append("], [");

        for (int i = 0; i < x.length; i++) {
            result.append(x[i]);
            if (i < x.length - 1)
                result.append(", ");
        }

        result.append("], ").append(" )");

        return result.toString();

    }

}
