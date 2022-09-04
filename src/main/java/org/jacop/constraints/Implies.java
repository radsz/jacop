/*
 * Implies.java
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
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.IntVar;
import org.jacop.util.QueueForward;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/*
 * Constraint b {@literal =>} c (implication or half-reification)
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */

public class Implies extends PrimitiveConstraint implements UsesQueueVariable {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable b in the Implies constraint.
     */
    public IntVar b;

    /**
     * It specifies constraint in the Implies constraint.
     */
    public PrimitiveConstraint c;

    boolean imposed = false;

    Store store;

    private final QueueForward<PrimitiveConstraint> queueForward;

    /**
     * It constructs ifthen constraint.
     *
     * @param b the varaible of the implied constraint.
     * @param c the constraint which must hold if the variable is 1.
     */
    public Implies(IntVar b, PrimitiveConstraint c) {

        checkInputForNullness(new String[] {"c", "b"}, new Object[] {c, b});
        if (b.min() > 1 || b.max() < 0)
            throw new IllegalArgumentException("Variable b in reified constraint must have domain at most 0..1");

        numberId = idNumber.incrementAndGet();
        this.b = b;
        this.c = c;
        setScope(Stream.concat(c.arguments().stream(), Stream.of(b)));
        setConstraintScope(c);
        queueForward = new QueueForward<>(c, arguments());
        this.queueIndex = c.queueIndex;

    }

    @Override public void consistency(Store store) {

        if (c.satisfied()) {
            removeConstraint();
        } else if (c.notSatisfied()) {
            b.domain.inValue(store.level, b, 0);
            removeConstraint();
        } else if (b.max() == 0) {
            removeConstraint();
        } else if (b.min() == 1) {
            c.consistency(store);
        }
    }

    @Override public boolean notSatisfied() {
        return b.min() == 1 && c.notSatisfied();
    }

    @Override public void notConsistency(Store store) {

        c.notConsistency(store);
        b.domain.inValue(store.level, b, 1);

    }

    @Override public int getNestedPruningEvent(Var var, boolean mode) {
        return getConsistencyPruningEvent(var);
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise method exists.");
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
        throw new IllegalStateException("Not implemented as more precise method exists.");
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

        this.store = store;
        super.impose(store);
        imposed = true;

    }

    @Override public void include(Store store) {
        this.store = store;
    }

    @Override public boolean satisfied() {

        return (b.min() == 1 && c.satisfied()) || (b.max() == 0);

    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());

        result.append(" : Implies(").append(b).append(", ").append(c).append(" )");

        return result.toString();

    }

    @Override public void queueVariable(int level, Var variable) {

        // queueForward.queueForward(level, variable);

    }
}
