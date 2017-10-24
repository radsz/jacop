/*
 * XneqC.java
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

import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Constraints X #\= C
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class XneqC extends PrimitiveConstraint {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x in constraint x != c.
     */
    final public IntVar x;

    /**
     * It specifies constant c in constraint x != c.
     */
    final public int c;

    /**
     * It constructs x != c constraint.
     * @param x variable x.
     * @param c constant c.
     */
    public XneqC(IntVar x, int c) {

        if (x == null)
            throw new IllegalArgumentException("Constraint XgtC has variable x that is null.");

        numberId = idNumber.incrementAndGet();

        this.x = x;
        this.c = c;

        setScope(x);
    }

    @Override public void consistency(final Store store) {

        x.domain.inComplement(store.level, x, c);

    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return Domain.NONE;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return Domain.NONE;
    }

    @Override public void notConsistency(final Store store) {
        x.domain.in(store.level, x, c, c);
    }

    @Override public boolean notSatisfied() {
        return x.singleton(c);
    }

    @Override public boolean satisfied() {
        return !x.domain.contains(c);
    }

    @Override public String toString() {
        return id() + " : XneqC(" + x + ", " + c + " )";
    }

}
