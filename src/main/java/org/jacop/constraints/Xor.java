/**
 * Xor.java
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
import java.util.stream.Stream;

import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.util.QueueForward;

/**
 * Xor constraint - xor("constraint", B).
 *
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.4
 */

public class Xor extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies constraint c, which status must satisfy xor relationship with variable b.
     */
    public PrimitiveConstraint c;

    /**
     * It specifies variable b, which boolean status must satisfy xor relationship with status of constraint c.
     */
    public IntVar b;

    final public QueueForward<PrimitiveConstraint> queueForward;

    boolean needRemoveLevelLate = false;

    /**
     * It constructs a xor constraint.
     * @param c constraint c.
     * @param b boolean variable b.
     */
    public Xor(PrimitiveConstraint c, IntVar b) {

        checkInputForNullness(new String[]{"c", "b"}, new Object[]{c, b});

        if (! (b.min() >= 0 && b.max() <= 1) )
            throw new IllegalArgumentException( "Constraint Xor has a variable b = " + b + " that has a domain outside of 0..1.");

        numberId = idNumber.incrementAndGet();

        this.c = c;
        this.b = b;

        try {
            c.getClass().getDeclaredMethod("removeLevelLate", int.class);
            needRemoveLevelLate = true;
        } catch (NoSuchMethodException e) {
            needRemoveLevelLate = false;
        }

        setScope( Stream.concat(c.arguments().stream(), Stream.of(b)) );

        queueForward = new QueueForward<PrimitiveConstraint>(c, arguments());
    }

    @Override public void consistency(Store store) {

        // Does not need to loop on newPropagation since
        // the constraint C loops itself
        if (b.max() == 0)  // C must be true
            c.consistency(store);
        else if (b.min() == 1)  // C must be false
            c.notConsistency(store);
        else if (c.satisfied())
            b.domain.in(store.level, b, 0, 0);
        else if (c.notSatisfied())
            b.domain.in(store.level, b, 1, 1);
    }

    @Override public int getNestedPruningEvent(Var var, boolean mode) {

        return getConsistencyPruningEvent(var);

    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise variants exist.");
    }


    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }

        if (var == b)
            return IntDomain.GROUND;
        else {

            int eventAcross = -1;

            if (c.arguments().contains(var)) {
                int event = c.getNestedPruningEvent(var, true);
                if (event > eventAcross)
                    eventAcross = event;
            }

            if (c.arguments().contains(var)) {
                int event = c.getNestedPruningEvent(var, false);
                if (event > eventAcross)
                    eventAcross = event;
            }

            if (eventAcross == -1)
                return Domain.NONE;
            else
                return eventAcross;
        }
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise variants exist.");
    }


    @Override public int getNotConsistencyPruningEvent(Var var) {

        // If notConsistency function mode
        if (notConsistencyPruningEvents != null) {
            Integer possibleEvent = notConsistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        if (var == b)
            return IntDomain.GROUND;
        else {

            int eventAcross = -1;

            if (c.arguments().contains(var)) {
                int event = c.getNestedPruningEvent(var, true);
                if (event > eventAcross)
                    eventAcross = event;
            }

            if (c.arguments().contains(var)) {
                int event = c.getNestedPruningEvent(var, false);
                if (event > eventAcross)
                    eventAcross = event;
            }

            if (eventAcross == -1)
                return Domain.NONE;
            else
                return eventAcross;
        }
    }

    @Override public void impose(Store store) {

        super.impose(store);
        arguments().stream().forEach( i -> queueVariable(store.level, i));
        c.include(store);

    }

    @Override public void include(Store store) {
        c.include(store);
    }

    @Override public boolean satisfied() {
        IntDomain Bdom = b.dom();
        return (Bdom.max() == 0 && c.satisfied()) || (Bdom.min() == 1 && c.notSatisfied());
    }

    @Override public String toString() {
        return id() + " : Xor(" + c + ", " + b + " )";
    }

    @Override public void notConsistency(Store store) {

        // Does not need to loop on newPropagation since
        // the constraint C loops itself
        if (b.max() == 0)  // C must be false
            c.notConsistency(store);
        else if (b.min() == 1) // C must be true
            c.consistency(store);
        else if (c.satisfied())
            b.domain.in(store.level, b, 1, 1);
        else if (c.notSatisfied())
            b.domain.in(store.level, b, 0, 0);

    }

    @Override public boolean notSatisfied() {
        IntDomain bDom = b.dom();
        return (bDom.min() == 1 && c.satisfied()) || (bDom.max() == 0 && c.notSatisfied());
    }

    @Override public void queueVariable(int level, Var variable) {

        queueForward.queueForward(level, variable);

    }

    public void removeLevelLate(int level) {
        if (needRemoveLevelLate)
            c.removeLevelLate(level);
    }

}
