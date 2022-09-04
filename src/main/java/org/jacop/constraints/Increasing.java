/*
 * Increasing.java
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

import org.jacop.core.*;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XlteqY;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.Arrays;
import java.util.ArrayList;

/**
 * Increasing constraint assures that all variables are in increasing order. 
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */

public class Increasing extends Constraint {


    static AtomicInteger idNumber = new AtomicInteger(0);

    IntVar[] x;
    int n;

    byte strict = 0;

    // List of decomposed constraints
    protected List<Constraint> constraints = null;

    /*
     * It constructs an increasing constraint.
     *
     * @param x variables which must be in increasing order.
     */
    public Increasing(IntVar[] x) {

        checkInputForNullness("x", x);

        this.numberId = idNumber.incrementAndGet();
        this.x = Arrays.copyOf(x, x.length);
        this.n = x.length;

        this.queueIndex = 1;

        setScope(x);
    }

    public Increasing(IntVar[] x, boolean strict) {
        this(x);

        if (strict)
            this.strict = 1;
    }

    /**
     * It constructs an increasing constraint.
     *
     * @param x variables which must be in increasing order.
     */
    public Increasing(List<IntVar> x) {
        this(x.toArray(new IntVar[x.size()]));
    }

    public Increasing(List<IntVar> x, boolean strict) {
        this(x.toArray(new IntVar[x.size()]), strict);
    }

    @Override public void consistency(Store store) {

        do {

            store.propagationHasOccurred = false;

            for (int i = 1; i < n; i++) {
                x[i - 1].domain.inMax(store.level, x[i - 1], x[i].max() - strict);
                x[i].domain.inMin(store.level, x[i], x[i - 1].min() + strict);
            }
            
        } while (store.propagationHasOccurred);

    }

    @Override public List<Constraint> decompose(Store store) {
        List<Constraint> cs = new ArrayList<>();

        for (int i = 1; i < n; i++) {
            if (strict == 1)
                cs.add(new XltY(x[i - 1], x[i]));
            else
                cs.add(new XlteqY(x[i - 1], x[i]));
        }
        
        return cs;
    }

    @Override public void imposeDecomposition(Store store) {

        if (constraints == null)
            constraints = decompose(store);

        for (Constraint c : constraints)
            store.impose(c);
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : Increasing([");

        for (int i = 0; i < n; i++) {
            result.append(x[i]);
            if (i < n - 1)
                result.append(", ");
        }
        result.append("], " + (strict == 1 ? "strict" : "non-strict") + ")");

        return result.toString();
    }
}
