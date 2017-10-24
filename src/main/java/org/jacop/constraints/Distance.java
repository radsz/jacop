/*
 * Distance.java
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

import org.jacop.api.Stateful;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * Constraint |X - Y| #= Z
 *
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */

public class Distance extends PrimitiveConstraint implements Stateful {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    boolean firstConsistencyCheck = false;

    int firstConsistencyLevel;

    /**
     * It specifes variable x in constraint |x-y|=z.
     */
    final public IntVar x;

    /**
     * It specifes variable y in constraint |x-y|=z.
     */
    final public IntVar y;

    /**
     * It specifes variable z in constraint |x-y|=z.
     */
    final public IntVar z;

    /**
     * Distance between x and y |x-y| = z
     * @param x first parameter
     * @param y second parameter
     * @param z result
     */
    public Distance(IntVar x, IntVar y, IntVar z) {

        checkInputForNullness(new String[] {"x", "y", "z"}, new Object[] {x, y, z});
        numberId = idNumber.incrementAndGet();

        this.x = x;
        this.y = y;
        this.z = z;

        setScope(x, y, z);

    }

    @Override public void removeLevel(int level) {
        if (level == firstConsistencyLevel)
            firstConsistencyCheck = true;
    }

    @Override public void consistency(final Store store) {

        if (firstConsistencyCheck) {
            z.domain.inMin(store.level, z, 0);
            firstConsistencyCheck = false;
            firstConsistencyLevel = store.level;
        }

        do {

            store.propagationHasOccurred = false;

            if (x.singleton()) {

                int xValue = x.value();
                // |X - Y| = Z

                IntDomain yDom = y.dom();
                int ySize = yDom.noIntervals();

                IntervalDomain tempPlus4Z = new IntervalDomain(ySize);

                for (int i = ySize - 1; i >= 0; i--)
                    if (xValue >= yDom.rightElement(i))
                        tempPlus4Z.unionAdapt(new Interval(xValue - yDom.rightElement(i), xValue - yDom.leftElement(i)));
                    else if (xValue >= yDom.leftElement(i))
                        tempPlus4Z.unionAdapt(new Interval(0, xValue - yDom.leftElement(i)));

                IntervalDomain tempMinus4Z = new IntervalDomain(ySize);

                for (int i = 0; i < ySize; i++)
                    if (xValue <= yDom.leftElement(i))
                        tempMinus4Z.unionAdapt(new Interval(-xValue + yDom.leftElement(i), -xValue + yDom.rightElement(i)));
                    else if (xValue <= yDom.rightElement(i))
                        tempMinus4Z.unionAdapt(new Interval(0, -xValue + yDom.rightElement(i)));

                tempPlus4Z.addDom(tempMinus4Z);
                z.domain.in(store.level, z, tempPlus4Z);

                // If Y changes Z then only if Z changes Y we execute
                // consistency again.
                store.propagationHasOccurred = false;

                // |X - Y| = Z

                IntDomain zDom = z.dom();
                int zSize = z.domain.noIntervals();

                IntervalDomain temp = new IntervalDomain(zSize);

                for (int i = zSize - 1; i >= 0; i--)
                    temp.unionAdapt(new Interval(-zDom.rightElement(i), -zDom.leftElement(i)));

                temp.addDom(zDom);

                y.domain.inShift(store.level, y, temp, xValue);

            } else {

                // X not singleton
                if (y.singleton()) {

                    int yValue = y.value();
                    // |X - Y| = Z

                    IntDomain xDom = x.dom();
                    int xSize = x.domain.noIntervals();

                    IntervalDomain temp4PlusZ = new IntervalDomain(xSize);
                    IntervalDomain temp4MinusZ = new IntervalDomain(xSize);

                    for (int i = 0; i < xSize; i++)
                        if (xDom.leftElement(i) - yValue >= 0)
                            temp4PlusZ.unionAdapt(new Interval(xDom.leftElement(i) - yValue, xDom.rightElement(i) - yValue));
                        else if (xDom.rightElement(i) - yValue >= 0)
                            temp4PlusZ.unionAdapt(0, xDom.rightElement(i) - yValue);

                    for (int i = xSize - 1; i >= 0; i--)
                        if (xDom.rightElement(i) - yValue <= 0)
                            temp4MinusZ.unionAdapt(new Interval(-xDom.rightElement(i) + yValue, -xDom.leftElement(i) + yValue));
                        else if (xDom.leftElement(i) - yValue <= 0)
                            temp4MinusZ.unionAdapt(0, -xDom.leftElement(i) + yValue);

                    temp4PlusZ.addDom(temp4MinusZ);
                    z.domain.in(store.level, z, temp4PlusZ);

                    // If X changes Z then only if Z changes X we execute
                    // consistency again.
                    store.propagationHasOccurred = false;

                    // Y.singleton()
                    // |X - Y| = Z

                    IntDomain zDom = z.dom();
                    int zSize = zDom.noIntervals();

                    IntervalDomain temp = new IntervalDomain(zSize);

                    for (int i = zSize - 1; i >= 0; i--)
                        temp.unionAdapt(new Interval(-zDom.rightElement(i), -zDom.leftElement(i)));

                    temp.addDom(zDom);

                    x.domain.inShift(store.level, x, temp, yValue);

                } else {

                    // X and Y not singleton

                    if (z.singleton()) {

                        // Z is singleton
                        int zValue = z.value();

                        IntDomain xDom = x.dom();
                        int xSize = xDom.noIntervals();

                        IntervalDomain tempPlusC = new IntervalDomain(xSize);
                        IntervalDomain tempMinusC = new IntervalDomain(xSize);

                        for (int i = 0; i < xSize; i++) {
                            tempPlusC.unionAdapt(new Interval(xDom.leftElement(i) + zValue, xDom.rightElement(i) + zValue));
                            tempMinusC.unionAdapt(new Interval(xDom.leftElement(i) - zValue, xDom.rightElement(i) - zValue));
                        }

                        tempPlusC.addDom(tempMinusC);

                        y.domain.in(store.level, y, tempPlusC);

                        // If X changes Y then only if Y changes X we execute
                        // consistency again.
                        store.propagationHasOccurred = false;

                        IntDomain yDom = y.dom();
                        int ySize = yDom.noIntervals();

                        tempPlusC = new IntervalDomain(ySize);
                        tempMinusC = new IntervalDomain(ySize);

                        for (int i = 0; i < ySize; i++) {
                            tempPlusC.unionAdapt(new Interval(yDom.leftElement(i) + zValue, yDom.rightElement(i) + zValue));
                            tempMinusC.unionAdapt(new Interval(yDom.leftElement(i) - zValue, yDom.rightElement(i) - zValue));
                        }

                        tempPlusC.addDom(tempMinusC);
                        x.domain.in(store.level, x, tempPlusC);

                    } else {
                        // None is singleton

                        // Y - X = Z
                        IntervalDomain Xdom1 = new IntervalDomain(y.min() - z.max(), y.max() - z.min());

                        // X - Y = Z
                        Xdom1.unionAdapt(y.min() + z.min(), y.max() + z.max());

                        x.domain.in(store.level, x, Xdom1);

                        store.propagationHasOccurred = false;

                        // Y - X = Z
                        IntervalDomain Ydom1 = new IntervalDomain(x.min() + z.min(), x.max() + z.max());
                        // X - Y = Z
                        Ydom1.unionAdapt(x.min() - z.max(), x.max() - z.min());

                        y.domain.in(store.level, y, Ydom1);

                        // Y - X = Z
                        IntervalDomain Zdom1 = new IntervalDomain(y.min() - x.max(), y.max() - x.min());
                        // X - Y = Z
                        Zdom1.unionAdapt(x.min() - y.max(), x.max() - y.min());

                        z.domain.in(store.level, z, Zdom1);

                    }

                }

            }

        } while (store.propagationHasOccurred);

    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override public boolean satisfied() {
        IntDomain Xdom = x.dom(), Ydom = y.dom(), Zdom = z.dom();
        return (Xdom.singleton() && Ydom.singleton() && Zdom.singleton() && java.lang.Math.abs(Xdom.min() - Ydom.min()) == Zdom.min());
    }

    @Override public String toString() {

        return id() + " : Distance(" + x + ", " + y + ", " + z + " )";
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public boolean notSatisfied() {

        IntDomain Xdom = x.dom(), Ydom = y.dom(), Zdom = z.dom();
        return (Xdom.singleton() && Ydom.singleton() && Zdom.singleton() && !(java.lang.Math.abs(Xdom.min() - Ydom.min()) == Zdom.min()));

    }

    @Override public void notConsistency(final Store store) {

        do {

            store.propagationHasOccurred = false;

            if (x.singleton()) {

                if (z.singleton()) {

                    // |X - Y| = Z
                    // X - Y = Z => Y = X - Z
                    // -X + Y = Z => Y = X + Z

                    // Domain first = Domain.domain.minus(X.dom(), Z.dom());

                    y.domain.inComplement(store.level, y, x.value() - z.value());
                    y.domain.inComplement(store.level, y, x.value() + z.value());

                } else if (y.singleton()) {

                    z.domain.inComplement(store.level, z, x.value() - y.value());
                    z.domain.inComplement(store.level, x, y.value() - x.value());

                }

            } else if (z.singleton() && y.singleton()) {

                // |X - Y| = Z
                // -X + Y = Z => X = Y - Z, Y = X + Z
                // X - Y = Z => X = Y + Z, Y = X - Z

                x.domain.inComplement(store.level, x, y.value() - z.value());
                x.domain.inComplement(store.level, x, y.value() + z.value());

            }

        } while (store.propagationHasOccurred);

    }

}
