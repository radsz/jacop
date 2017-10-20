/*
 * Reified.java
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
import org.jacop.core.*;
import org.jacop.util.QueueForward;

import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * Reified constraints "constraint" {@literal <=>} B
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Reified extends PrimitiveConstraint implements UsesQueueVariable {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies constraint c which status is being checked.
     */
    final public PrimitiveConstraint c;

    /**
     * It specifies variable b which stores status of the constraint (0 - for certain not satisfied, 1 - for certain satisfied).
     */
    final public IntVar b;

    final private QueueForward<PrimitiveConstraint> queueForward;

    private boolean needRemoveLevelLate = false;

    /**
     * It creates Reified constraint.
     *
     * @param c primitive constraint c.
     * @param b boolean variable b.
     */
    public Reified(PrimitiveConstraint c, IntVar b) {

        checkInputForNullness(new String[] {"c", "b"}, new Object[] {c, b});
        if (b.min() > 1 || b.max() < 0)
            throw new IllegalArgumentException("Variable b in reified constraint must have domain at most 0..1");

        numberId = idNumber.incrementAndGet();

        this.c = c;
        this.b = b;

        try {
            c.getClass().getDeclaredMethod("removeLevelLate", int.class);
            needRemoveLevelLate = true;
        } catch (NoSuchMethodException e) {
            needRemoveLevelLate = false;
        }

        setScope(Stream.concat(c.arguments().stream(), Stream.of(b)));
        setConstraintScope(c);
        queueForward = new QueueForward<>(c, arguments());
        this.queueIndex = c.queueIndex;
    }

    @Override public void consistency(final Store store) {

        if (c.satisfied()) {
            b.domain.in(store.level, b, 1, 1);
            removeConstraint();
        } else if (c.notSatisfied()) {
            b.domain.in(store.level, b, 0, 0);
            removeConstraint();
        } else if (b.max() == 0) // C must be false
            c.notConsistency(store);
        else if (b.min() == 1) // C must be true
            c.consistency(store);
    }

    @Override public void notConsistency(final Store store) {

        if (c.satisfied()) {
            b.domain.in(store.level, b, 0, 0);
            removeConstraint();
        } else if (c.notSatisfied()) {
            b.domain.in(store.level, b, 1, 1);
            removeConstraint();
        } else if (b.max() == 0) // C must be true
            c.consistency(store);
        else if (b.min() == 1) // C must be false
            c.notConsistency(store);
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

    // TODO, what about include function, should it have registerRemoveLevelLateListener?
    @Override public void impose(Store store) {

        super.impose(store);

        if (needRemoveLevelLate)
            store.registerRemoveLevelLateListener(this);

    }

    @Override public boolean satisfied() {
        IntDomain Bdom = b.dom();
        return (Bdom.min() == 1 && c.satisfied()) || (Bdom.max() == 0 && c.notSatisfied());
    }

    @Override public boolean notSatisfied() {
        IntDomain Bdom = b.dom();
        return (Bdom.max() == 0 && c.satisfied()) || (Bdom.min() == 1 && c.notSatisfied());
    }

    @Override public String toString() {

        return id() + " : Reified(" + c + ", " + b + " )";
    }

    @Override public void queueVariable(int level, Var variable) {

        queueForward.queueForward(level, variable);

    }

    public void removeLevelLate(int level) {
        if (needRemoveLevelLate)
            c.removeLevelLate(level);
    }

}
