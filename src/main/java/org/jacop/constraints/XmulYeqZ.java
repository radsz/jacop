/**
 * XmulYeqZ.java
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

import java.util.ArrayList;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Interval;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Constraint X * Y #= Z
 *
 * Boundary consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 3.1
 */

public class XmulYeqZ extends Constraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable x in constraint x * y = z.
     */
    public IntVar x;

    /**
     * It specifies variable y in constraint x * y = z.
     */
    public IntVar y;

    /**
     * It specifies variable z in constraint x * y = z.
     */
    public IntVar z;

    boolean xSquare = false;

    /**
     * It specifies the arguments required to be saved by an XML format as well as
     * the constructor being called to recreate an object from an XML format.
     */
    public static String[] xmlAttributes = {"x", "y", "z"};

    /**
     * It constructs a constraint X * Y = Z.
     * @param x variable x.
     * @param y variable y.
     * @param z variable z.
     */
    public XmulYeqZ(IntVar x, IntVar y, IntVar z) {

        assert (x != null) : "Variable x is null";
        assert (y != null) : "Variable y is null";
        assert (z != null) : "Variable z is null";

        numberId = idNumber.incrementAndGet();
        numberArgs = 3;

        xSquare = (x == y);

        this.x = x;
        this.y = y;
        this.z = z;

        checkForOverflow();
    }

    @Override public ArrayList<Var> arguments() {

        ArrayList<Var> variables = new ArrayList<Var>(3);

        variables.add(x);
        variables.add(y);
        variables.add(z);
        return variables;
    }

    @Override public void consistency(Store store) {

        if (xSquare)  // X^2 = Z
            do {

                // Bounds for Z
                Interval zBounds = IntDomain.mulBounds(x.min(), x.max(), x.min(), x.max());
                z.domain.in(store.level, z, zBounds.min(), zBounds.max());

                store.propagationHasOccurred = false;

                // Bounds for X

                int xMin = toInt(Math.round(Math.ceil(Math.sqrt((double) z.min()))));
                int xMax = toInt(Math.round(Math.floor(Math.sqrt((double) z.max()))));

                if (xMin > xMax)
                    throw Store.failException;

                IntDomain dom = new IntervalDomain(-xMax, -xMin);
                dom.unionAdapt(xMin, xMax);

                x.domain.in(store.level, x, dom);

            } while (store.propagationHasOccurred);
        else    // X*Y=Z
            do {

                // Bounds for X
                Interval xBounds = IntDomain.divIntBounds(z.min(), z.max(), y.min(), y.max());

                x.domain.in(store.level, x, xBounds.min(), xBounds.max());

                store.propagationHasOccurred = false;

                // Bounds for Y
                Interval yBounds = IntDomain.divIntBounds(z.min(), z.max(), x.min(), x.max());

                y.domain.in(store.level, y, yBounds.min(), yBounds.max());

                // Bounds for Z
                Interval zBounds = IntDomain.mulBounds(x.min(), x.max(), y.min(), y.max());

                z.domain.in(store.level, z, zBounds.min(), zBounds.max());


            } while (store.propagationHasOccurred);

        if (x.singleton(0) || y.singleton(0))
            removeConstraint();
    }

    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        return IntDomain.BOUND;
    }

    @Override public void impose(Store store) {
        x.putModelConstraint(this, getConsistencyPruningEvent(x));
        y.putModelConstraint(this, getConsistencyPruningEvent(y));
        z.putModelConstraint(this, getConsistencyPruningEvent(z));
        store.addChanged(this);
        store.countConstraint();
    }

    @Override public void removeConstraint() {
        x.removeConstraint(this);
        y.removeConstraint(this);
        z.removeConstraint(this);
    }

    @Override public boolean satisfied() {
        IntDomain xDom = x.dom(), yDom = y.dom(), zDom = z.dom();
        return xDom.singleton() && yDom.singleton() && zDom.singleton() && xDom.min() * yDom.min() == zDom.min();
    }

    @Override public String toString() {

        return id() + " : XmulYeqZ(" + x + ", " + y + ", " + z + " )";
    }

    private void checkForOverflow() {

        int n = IntDomain.multiply(x.min(), y.min());
        n = IntDomain.multiply(x.min(), y.max());
        n = IntDomain.multiply(x.max(), y.min());
        n = IntDomain.multiply(x.max(), y.max());

    }

    @Override public void increaseWeight() {
        if (increaseWeight) {
            x.weight++;
            y.weight++;
            z.weight++;
        }
    }

}
