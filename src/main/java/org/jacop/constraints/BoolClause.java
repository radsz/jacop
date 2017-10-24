/*
 * BoolClause.java
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
import org.jacop.core.TimeStamp;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * I defines a boolean clause for 0/1 variables x_i and y_i.
 * The clause is fulfilled if at least one varibale x_i = 1 or at least one varibale y_i = 0,
 * that is it defines (x_1 \/ x_2 \/ ... x_n) \/ (not y_1 \/ not y_2 \/ ... not y_n)
 * It restricts the domain of all x as well as result to be between 0 and 1.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class BoolClause extends PrimitiveConstraint {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies lists of variables for the constraint.
     */
    final public IntVar[] x;
    final public IntVar[] y;

    /**
     * It specifies length of lists x and y respectively.
     */
    private final int lx, ly;

    /**
     * Defines first position of the variable that is not ground to 0 (positionX) or 0 (positionY).
     */
    private TimeStamp<Integer> positionX;
    private TimeStamp<Integer> positionY;

    /**
     * It constructs BoolClause.
     *
     * @param x list of positive arguments x's.
     * @param y list of negative arguments y's.
     */
    public BoolClause(IntVar[] x, IntVar[] y) {

        checkInputForNullness(new String[] {"x", "y"}, x, y);

        this.numberId = idNumber.incrementAndGet();
        this.lx = x.length;
        this.ly = y.length;

        this.x = Arrays.copyOf(x, x.length);
        this.y = Arrays.copyOf(y, y.length);

        assert (checkInvariants() == null) : checkInvariants();

        if (lx + ly > 4)
            queueIndex = 1;
        else
            queueIndex = 0;

        setScope(Stream.concat(Arrays.stream(x), Arrays.stream(y)));
    }

    /**
     * It constructs BoolClause.
     *
     * @param x list of positive arguments x's.
     * @param y list of negative arguments y's.
     */
    public BoolClause(List<IntVar> x, List<IntVar> y) {
        this(x.toArray(new IntVar[x.size()]), y.toArray(new IntVar[y.size()]));
    }

    /**
     * It checks invariants required by the constraint. Namely that
     * boolean variables have boolean domain.
     *
     * @return the string describing the violation of the invariant, null otherwise.
     */
    public String checkInvariants() {

        for (IntVar var : x)
            if (var.min() < 0 || var.max() > 1)
                return "Variable " + var + " does not have boolean domain";

        for (IntVar var : y)
            if (var.min() < 0 || var.max() > 1)
                return "Variable " + var + " does not have boolean domain";

        return null;
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override public void include(Store store) {
        positionX = new TimeStamp<>(store, 0);
        positionY = new TimeStamp<>(store, 0);
    }

    /**
     * computes consistency for x_0 \/ ... \/ x_n \/ not y_0 \/ ... \/ not y_n
     */
    @Override public void consistency(Store store) {

        int startX = positionX.value();
        int startY = positionY.value();

        for (int i = startX; i < lx; i++) {
            if (x[i].max() == 0) {
                swap(x, startX, i);
                startX++;
                positionX.update(startX);
            } else if (x[i].min() == 1) {
                removeConstraint();
                return;
            }
        }

        for (int i = startY; i < ly; i++) {
            if (y[i].min() == 1) {
                swap(y, startY, i);
                startY++;
                positionY.update(startY);
            } else if (y[i].max() == 0) {
                removeConstraint();
                return;
            }
        }

        // all x are = 0 and all y = 1 => FAIL
        if (startX == lx && startY == ly)
            throw Store.failException;
            // last x must be 1
        else if (startX == lx - 1 && startY == ly)
            x[lx - 1].domain.in(store.level, x[lx - 1], 1, 1);
            // last y must be 0
        else if (startX == lx && startY == ly - 1)
            y[ly - 1].domain.in(store.level, y[ly - 1], 0, 0);

        if (lx - startX + ly + startY < 5)
            queueIndex = 0;
    }

    private void swap(IntVar[] p, int i, int j) {
        if (i != j) {
            IntVar tmp = p[i];
            p[i] = p[j];
            p[j] = tmp;
        }
    }


    /**
     * computes consistency for not (x_0 \/ ... \/ x_n \/ not y_0 \/ ... \/ not y_n)
     * implies
     * not x_0 /\ ... /\ not x_n /\ y_0 /\ ... /\ y_n
     * taht is all x_i = 0 /\ all y_i = 1
     */
    @Override public void notConsistency(Store store) {

        for (int i = 0; i < lx; i++)
            x[i].domain.in(store.level, x[i], 0, 0);
        for (int i = 0; i < ly; i++)
            y[i].domain.in(store.level, y[i], 1, 1);

        removeConstraint();

    }

    @Override public boolean satisfied() {

        int startX = positionX.value();
        int startY = positionY.value();

        for (int i = startX; i < lx; i++)
            if (x[i].min() == 1)
                return true;
            else if (x[i].max() == 0) {
                swap(x, startX, i);
                startX++;
                positionX.update(startX);
            }

        for (int i = startY; i < ly; i++)
            if (y[i].max() == 0)
                return true;
            else if (y[i].min() == 1) {
                swap(y, startY, i);
                startY++;
                positionY.update(startY);
            }

        return false;

    }

    @Override public boolean notSatisfied() {

        int startX = positionX.value();
        int startY = positionY.value();

        for (int i = startX; i < lx; i++)
            if (x[i].max() == 0) {
                swap(x, startX, i);
                startX++;
                positionX.update(startX);
            } else
                return false;

        for (int i = startY; i < ly; i++)
            if (y[i].min() == 1) {
                swap(y, startY, i);
                startY++;
                positionY.update(startY);
            } else
                return false;

        return startX == lx && startY == ly;
    }

    @Override public String toString() {

        StringBuilder resultString = new StringBuilder(id());

        resultString.append(" : BoolClause([ ");
        for (int i = 0; i < lx; i++) {
            resultString.append(x[i]);
            if (i < lx - 1)
                resultString.append(", ");
        }
        resultString.append("], [");

        for (int i = 0; i < ly; i++) {
            resultString.append(y[i]);
            if (i < ly - 1)
                resultString.append(", ");
        }
        resultString.append("])");
        return resultString.toString();
    }

}
