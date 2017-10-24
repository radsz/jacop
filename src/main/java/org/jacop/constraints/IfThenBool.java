/*
 * IfThenBool.java
 * <p>
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Constraint ( X {@literal =>} Y ) {@literal <=>} Z.
 *
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class IfThenBool extends PrimitiveConstraint {

	/*
   * X | Y | Z
	 * 0   0   1
	 * 0   1   1
	 * 1   0   0
	 * 1   1   1
	 */

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x in constraint ( X {@literal =>} Y ) {@literal <=>} Z.
     */
    public IntVar x;

    /**
     * It specifies variable y in constraint ( X {@literal =>} Y ) {@literal <=>} Z.
     */
    public IntVar y;

    /**
     * It specifies variable z in constraint ( X {@literal =>} Y ) {@literal <=>} Z.
     */
    public IntVar z;

    /** It constructs constraint ( X {@literal =>} Y ) {@literal <=>} Z.
     * @param x variable x.
     * @param y variable y.
     * @param z variable z.
     */
    public IfThenBool(IntVar x, IntVar y, IntVar z) {

        checkInputForNullness(new String[] {"x", "y", "z"}, new Object[] {x, y, z});

        numberId = idNumber.incrementAndGet();

        this.x = x;
        this.y = y;
        this.z = z;

        setScope(x, y, z);

        assert (checkInvariants() == null) : checkInvariants();

    }

    /**
     * It checks invariants required by the constraint. Namely that
     * boolean variables have boolean domain.
     *
     * @return the string describing the violation of the invariant, null otherwise.
     */
    public String checkInvariants() {

        if (x.min() < 0 || x.max() > 1)
            return "Variable " + x + " does not have boolean domain";

        if (y.min() < 0 || y.max() > 1)
            return "Variable " + y + " does not have boolean domain";

        if (z.min() < 0 || z.max() > 1)
            return "Variable " + z + " does not have boolean domain";

        return null;
    }

    @Override public void consistency(Store store) {

        if (z.max() == 0) {
            x.domain.in(store.level, x, 1, 1);
            y.domain.in(store.level, y, 0, 0);
        }

        if (x.max() == 0) {
            z.domain.in(store.level, z, 1, 1);
        } else if (x.min() == 1) {
            z.domain.in(store.level, z, y.domain);
            y.domain.in(store.level, y, z.domain);
        }

        if (y.max() == 0) {
            if (x.singleton())
                z.domain.inComplement(store.level, z, x.value());
            if (z.singleton())
                x.domain.inComplement(store.level, x, z.value());
        } else if (y.min() == 1) {
            z.domain.in(store.level, z, 1, 1);
        }

    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.BOUND;
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

            if (x.singleton()) {

                if (x.max() == 0) {
                    z.domain.in(store.level, z, 0, 0);
                }

                if (x.min() == 1) {
                    if (y.singleton())
                        z.domain.inComplement(store.level, z, y.value());
                    if (z.singleton())
                        y.domain.inComplement(store.level, y, z.value());
                }
            }

            if (y.singleton()) {

                if (y.max() == 0) {
                    z.domain.in(store.level, z, x.domain);
                    x.domain.in(store.level, x, z.domain);
                }

                if (y.min() == 1) {
                    z.domain.in(store.level, z, 0, 0);
                }
            }

            if (z.min() == 1) {
                x.domain.in(store.level, x, 1, 1);
                y.domain.in(store.level, y, 0, 0);
            }

        } while (store.propagationHasOccurred);

    }

    @Override public boolean notSatisfied() {

        if (!x.singleton())
            return false;
        if (!z.singleton())
            return false;

        if (x.singleton(0) && z.singleton(0))
            return true;

        if (!y.singleton())
            return false;

        if (x.singleton(1) && y.singleton(1) && z.singleton(0))
            return true;

        // 1 0 1
        return false;
    }

    @Override public boolean satisfied() {

        if (!x.singleton())
            return false;
        if (!z.singleton())
            return false;

        if (x.singleton(0) && z.singleton(1))
            return true;

        if (!y.singleton())
            return false;

        if (x.singleton(1) && y.singleton(1) && z.singleton(1))
            return true;

        // 1 0 0
        return false;

    }

    @Override public String toString() {

        return id() + " : IfThenBool( (" + x + "=> " + y + ") <=> " + z + " )";
    }
    
}
