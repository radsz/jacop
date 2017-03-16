/**
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

import java.util.ArrayList;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.TimeStamp;

/**
 * I defines a boolean clause for 0/1 variables x_i and y_i.
 * The clause is fulfilled if at least one varibale x_i = 1 or at least one varibale y_i = 0,
 * that is it defines (x_1 \/ x_2 \/ ... x_n) \/ (not y_1 \/ not y_2 \/ ... not y_n)
 * It restricts the domain of all x as well as result to be between 0 and 1.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.4
 */

public class BoolClause extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies lists of variables for the constraint.
     */
    public IntVar[] x;
    public IntVar[] y;

    /**
     * It specifies length of lists x and y respectively.
     */
    final int lx, ly;

    /**
     * It specifies the arguments required to be saved by an XML format as well as 
     * the constructor being called to recreate an object from an XML format.
     */
    public static String[] xmlAttributes = {"x", "y"};

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

        assert (x != null) : "List variable is null";
        assert (y != null) : "Result variable is null";

        this.numberId = idNumber.incrementAndGet();
        this.lx = x.length;
        this.ly = y.length;
        this.numberArgs = (short) (lx + ly);

        this.x = new IntVar[lx];
        for (int i = 0; i < lx; i++) {
            assert (x[i] != null) : i + "-th element in the list is null";
            this.x[i] = x[i];
        }

        this.y = new IntVar[ly];
        for (int i = 0; i < ly; i++) {
            assert (y[i] != null) : i + "-th element in the list is null";
            this.y[i] = y[i];
        }

        assert (checkInvariants() == null) : checkInvariants();

        if (lx + ly > 4)
            queueIndex = 1;
        else
            queueIndex = 0;
    }

    /**
     * It constructs BoolClause. 
     *
     * @param x list of positive arguments x's.
     * @param y list of negative arguments y's. 
     */
    public BoolClause(ArrayList<IntVar> x, ArrayList<IntVar> y) {

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

    @Override public ArrayList<Var> arguments() {

        ArrayList<Var> variables = new ArrayList<Var>(lx + ly);

        for (int i = 0; i < lx; i++)
            variables.add(x[i]);

        for (int i = 0; i < ly; i++)
            variables.add(y[i]);

        return variables;
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

    @Override public int getNotConsistencyPruningEvent(Var var) {

        // If notConsistency function mode
        if (notConsistencyPruningEvents != null) {
            Integer possibleEvent = notConsistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        return IntDomain.GROUND;
    }

    @Override public int getNestedPruningEvent(Var var, boolean mode) {

        // If consistency function mode
        if (mode) {
            if (consistencyPruningEvents != null) {
                Integer possibleEvent = consistencyPruningEvents.get(var);
                if (possibleEvent != null)
                    return possibleEvent;
            }
            return IntDomain.ANY;
        }
        // If notConsistency function mode
        else {
            if (notConsistencyPruningEvents != null) {
                Integer possibleEvent = notConsistencyPruningEvents.get(var);
                if (possibleEvent != null)
                    return possibleEvent;
            }
            return IntDomain.GROUND;
        }
    }


    // registers the constraint in the constraint store
    @Override public void impose(Store store) {

        positionX = new TimeStamp<Integer>(store, 0);
        positionY = new TimeStamp<Integer>(store, 0);

        for (Var V : x)
            V.putModelConstraint(this, getConsistencyPruningEvent(V));
        for (Var V : y)
            V.putModelConstraint(this, getConsistencyPruningEvent(V));

        store.addChanged(this);
        store.countConstraint();

    }

    @Override public void include(Store store) {

        positionX = new TimeStamp<Integer>(store, 0);
        positionY = new TimeStamp<Integer>(store, 0);

    }

    @Override
    /**
     * computes consistency for x_0 \/ ... \/ x_n \/ not y_0 \/ ... \/ not y_n
     */ public void consistency(Store store) {

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

    @Override
    /**
     * computes consistency for not (x_0 \/ ... \/ x_n \/ not y_0 \/ ... \/ not y_n)
     * =>
     * not x_0 /\ ... /\ not x_n /\ y_0 /\ ... /\ y_n
     * taht is all x_i = 0 /\ all y_i = 1
     */ public void notConsistency(Store store) {

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

        if (startX == lx && startY == ly)
            return true;
        else
            return false;
    }

    @Override public void removeConstraint() {

        for (int i = 0; i < lx; i++)
            x[i].removeConstraint(this);
        for (int i = 0; i < ly; i++)
            y[i].removeConstraint(this);

    }

    @Override public String toString() {

        StringBuffer resultString = new StringBuffer(id());

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

    @Override public void increaseWeight() {
        if (increaseWeight) {
            for (Var v : x)
                v.weight++;
            for (Var v : y)
                v.weight++;
        }
    }

}
