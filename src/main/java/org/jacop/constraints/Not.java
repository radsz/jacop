/*
 * Not.java
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

import org.jacop.api.UsesQueueVariable;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.util.QueueForward;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * Constraint "not costraint"
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Not extends PrimitiveConstraint implements UsesQueueVariable {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies the constraint which negation is being created.
     */
    final public PrimitiveConstraint c;

    private final QueueForward<PrimitiveConstraint> queueForward;

    /**
     * It constructs not constraint.
     *
     * @param c primitive constraint which is being negated.
     */
    public Not(PrimitiveConstraint c) {
        PrimitiveConstraint[] scope = new PrimitiveConstraint[] {c};
        checkInputForNullness("c", scope);
        numberId = idNumber.incrementAndGet();
        this.c = c;
        setScope(scope);
        setConstraintScope(scope);
        this.queueForward = new QueueForward<>(c, arguments());
        this.queueIndex = c.queueIndex;
    }

    @Override public void consistency(final Store store) {
        c.notConsistency(store);
    }

    @Override public int getNestedPruningEvent(Var var, boolean mode) {

        return getConsistencyPruningEvent(var);

    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as it delegates to internal constraint.");
    }

    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        return c.getNestedPruningEvent(var, false);
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as it delegates to internal constraint.");
    }


    @Override public int getNotConsistencyPruningEvent(Var var) {

        // If notConsistency function mode
        if (notConsistencyPruningEvents != null) {
            Integer possibleEvent = notConsistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        return c.getNestedPruningEvent(var, true);
    }

    @Override public void notConsistency(final Store store) {
        c.consistency(store);
    }

    @Override public boolean notSatisfied() {
        return c.satisfied();
    }

    @Override public boolean satisfied() {
        return c.notSatisfied();
    }

    @Override public String toString() {
        return id() + " : Not( " + c + ")";
    }

    @Override public void queueVariable(int level, Var variable) {
        queueForward.queueForward(level, variable);
    }

}
