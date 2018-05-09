/*
 * Eq.java
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
import org.jacop.core.Store;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.Var;
import org.jacop.util.QueueForward;

/**
 * Constraint "constraint1"{@literal #<=>} "constraint2"
 *
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Eq extends PrimitiveConstraint implements UsesQueueVariable {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies the first constraint which status must be equivalent to the status of the second constraint.
     */
    public PrimitiveConstraint c1;

    /**
     * It specifies the second constraint which status must be equivalent to the status of the first constraint.
     */
    public PrimitiveConstraint c2;

    final public QueueForward<PrimitiveConstraint> queueForward;

    /**
     * It constructs equality constraint between two constraints.
     * @param c1 the first constraint
     * @param c2 the second constraint
     */
    public Eq(PrimitiveConstraint c1, PrimitiveConstraint c2) {

        PrimitiveConstraint[] scope = new PrimitiveConstraint[] {c1, c2};

        checkInputForNullness(new String[] {"c1", "c2"}, scope);
        numberId = idNumber.incrementAndGet();

        this.c1 = c1;
        this.c2 = c2;
        setScope(scope);
        setConstraintScope(scope);
        queueForward = new QueueForward<>(new PrimitiveConstraint[] {c1, c2}, arguments());
	this.queueIndex = Integer.max(c1.queueIndex, c2.queueIndex);
    }

    @Override public void consistency(Store store) {

        // Does not need to loop due to propagation occuring.
        if (c2.satisfied())
            c1.consistency(store);
        else if (c2.notSatisfied())
            c1.notConsistency(store);

        if (c1.satisfied())
            c2.consistency(store);
        else if (c1.notSatisfied())
            c2.notConsistency(store);

    }

    @Override public int getNestedPruningEvent(Var var, boolean mode) {

        return getConsistencyPruningEvent(var);

    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise version exists.");
    }


    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }

        int eventAcross = -1;

        if (c1.arguments().contains(var)) {
            int event = c1.getNestedPruningEvent(var, true);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (c1.arguments().contains(var)) {
            int event = c1.getNestedPruningEvent(var, false);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (c2.arguments().contains(var)) {
            int event = c2.getNestedPruningEvent(var, true);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (c2.arguments().contains(var)) {
            int event = c2.getNestedPruningEvent(var, false);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (eventAcross == -1)
            return Domain.NONE;
        else
            return eventAcross;

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise version exists.");
    }

    @Override public int getNotConsistencyPruningEvent(Var var) {

        // If notConsistency function mode
        if (notConsistencyPruningEvents != null) {
            Integer possibleEvent = notConsistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }

        int eventAcross = -1;

        if (c1.arguments().contains(var)) {
            int event = c1.getNestedPruningEvent(var, true);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (c1.arguments().contains(var)) {
            int event = c1.getNestedPruningEvent(var, false);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (c2.arguments().contains(var)) {
            int event = c2.getNestedPruningEvent(var, true);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (c2.arguments().contains(var)) {
            int event = c2.getNestedPruningEvent(var, false);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (eventAcross == -1)
            return Domain.NONE;
        else
            return eventAcross;

    }

    @Override public void notConsistency(Store store) {

        // No need for fixpoint loop in this context. Fixpoint always achieved after one execution.
        if (c2.satisfied())
            c1.notConsistency(store);
        else if (c2.notSatisfied())
            c1.consistency(store);

        if (c1.satisfied())
            c2.notConsistency(store);
        else if (c1.notSatisfied())
            c2.consistency(store);


    }

    @Override public boolean notSatisfied() {
        return (c1.satisfied() && c2.notSatisfied()) || (c1.notSatisfied() && c2.satisfied());
    }

    @Override public boolean satisfied() {
        return (c1.satisfied() && c2.satisfied()) || (c1.notSatisfied() && c2.notSatisfied());
    }

    @Override public String toString() {

        return id() + " : Eq(" + c1 + ", " + c2 + " )";
    }

    @Override public void queueVariable(int level, Var var) {
        queueForward.queueForward(level, var);
    }

}
