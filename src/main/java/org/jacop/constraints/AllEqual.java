/*
 * AllEqual.java
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.api.SatisfiedPresent;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.Arrays;

/**
 * Constraints forall i != j: x[i] #= x[j]
 *
 * <p>Domain consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */

public class AllEqual extends PrimitiveConstraint {


    static final AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a left hand variable in equality constraint.
     */
    public final IntVar[] x;

    /**
     * It constructs constraint x[i] = x[j].
     *
     * @param x variables x.
     */
    public AllEqual(IntVar[] x) {

        checkInputForNullness(new String[] {"x"}, new Object[] {x});

        numberId = idNumber.incrementAndGet();

        this.x = x;

        setScope(x);
    }

    @Override public void consistency(final Store store) {

        // bottom up
        for (int i = 1; i < x.length; i++) {
    
            // domain consistency
            x[i - 1].domain.in(store.level, x[i - 1], x[i].domain);

            x[i].domain.in(store.level, x[i], x[i - 1].domain);
        }

        // top down
        for (int i = x.length - 2; i >= 0; i--) {
    
            // domain consistency
            x[i + 1].domain.in(store.level, x[i], x[i].domain);

            x[i].domain.in(store.level, x[i], x[i + 1].domain);
        }
    }
    
    @Override public void notConsistency(final Store store) {
        if (notSatisfied())
            removeConstraint();

        int n = 0;
        int idx = -1;
        int sIndex = -1;
        for (int i = 0; i < x.length; i++) {
            if (!x[i].singleton()) {
                idx = i;
                n++;
            } else
                sIndex = i;
        }
        if (n == 0)
            throw Store.failException;
        else if (n == 1)
            x[idx].domain.inComplement(store.level, x[idx], x[sIndex].value());
    }

    @Override public boolean satisfied() {

        for (int i = 0; i < x.length; i++) {
            for (int j = i + 1; j < x.length; j++) {
                if (! (x[i].singleton() && x[j].singleton() && x[i].value() == x[j].value()))
                    return false;
            }
        }
        return true;
    }

    @Override public boolean notSatisfied() {

        for (int i = 0; i < x.length; i++) {
            for (int j = i + 1; j < x.length; j++) {
                if (i != j && !x[i].domain.isIntersecting(x[j].domain))
                    return true;
            }
        }
        return false;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public String toString() {
        return id() + " : AllEqual(" + Arrays.asList(x) + " )";
    }

}
