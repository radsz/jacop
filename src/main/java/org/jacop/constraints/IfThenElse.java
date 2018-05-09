/*
 * IfThenElse.java
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
 * Constraint if constraint1 then constraint2 else constraint3
 *  * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class IfThenElse extends PrimitiveConstraint implements UsesQueueVariable {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies constraint condC in the IfThenElse constraint.
     */
    public PrimitiveConstraint condC;

    /**
     * It specifies constraint condC in the IfThenElse constraint.
     */
    public PrimitiveConstraint thenC;

    /**
     * It specifies constraint elseC in the IfThenElse constraint.
     */
    public PrimitiveConstraint elseC;

    // imposed variable to manifest that constraint has been imposed (top-level)
    // constraint
    boolean imposed = false;

    Store store;

    final public QueueForward<PrimitiveConstraint> queueForward;

    /**
     * It creates ifthenelse constraint.
     * @param condC the condition of the constraint.
     * @param thenC the condition which must be true if the constraint condition is true.
     * @param elseC the condition which must be true if the constraint condition is not true.
     */
    // Constructors
    public IfThenElse(PrimitiveConstraint condC, PrimitiveConstraint thenC, PrimitiveConstraint elseC) {

        PrimitiveConstraint[] scope = new PrimitiveConstraint[]{ condC, thenC, elseC};
        checkInputForNullness(new String[]{ "condC", "thenC", "elseC"}, scope);

        numberId = idNumber.incrementAndGet();

        this.condC = condC;
        this.thenC = thenC;
        this.elseC = elseC;

        setScope(scope);
        setConstraintScope(scope);
        queueForward = new QueueForward<PrimitiveConstraint>(new PrimitiveConstraint[] {condC, thenC, elseC}, arguments());
	this.queueIndex = Integer.max(Integer.max(condC.queueIndex, thenC.queueIndex), elseC.queueIndex);
    }

    @Override public void consistency(Store store) {

        if (condC.satisfied())
            thenC.consistency(store);
        else if (condC.notSatisfied())
            elseC.consistency(store);

        if (imposed) {

            if (thenC.notSatisfied()) {
                condC.notConsistency(store);
                elseC.consistency(store);
            }

            if (elseC.notSatisfied()) {
                condC.consistency(store);
                thenC.consistency(store);
            }
        }

    }

    @Override public boolean notSatisfied() {
        return (condC.satisfied() && thenC.notSatisfied()) || (condC.notSatisfied() && elseC.notSatisfied());
    }

    @Override public void notConsistency(Store store) {

        if (condC.notSatisfied())
            elseC.notConsistency(store);

        if (condC.satisfied())
            thenC.notConsistency(store);

    }

    @Override public int getNestedPruningEvent(Var var, boolean mode) {

        // If consistency function mode
        if (mode) {
            if (consistencyPruningEvents != null) {
                Integer possibleEvent = consistencyPruningEvents.get(var);
                if (possibleEvent != null)
                    return possibleEvent;
            }
        }
        // If notConsistency function mode
        else {
            if (notConsistencyPruningEvents != null) {
                Integer possibleEvent = notConsistencyPruningEvents.get(var);
                if (possibleEvent != null)
                    return possibleEvent;
            }
        }

        int eventAcross = -1;

        if (condC.arguments().contains(var)) {
            int event = condC.getNestedPruningEvent(var, true);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (condC.arguments().contains(var)) {
            int event = condC.getNestedPruningEvent(var, false);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (thenC.arguments().contains(var)) {
            int event = thenC.getNestedPruningEvent(var, true);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (thenC.arguments().contains(var)) {
            int event = thenC.getNestedPruningEvent(var, false);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (elseC.arguments().contains(var)) {
            int event = elseC.getNestedPruningEvent(var, true);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (elseC.arguments().contains(var)) {
            int event = elseC.getNestedPruningEvent(var, false);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (eventAcross == -1)
            return Domain.NONE;
        else
            return eventAcross;

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

        int eventAcross = -1;

        if (condC.arguments().contains(var)) {
            int event = condC.getNestedPruningEvent(var, true);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (condC.arguments().contains(var)) {
            int event = condC.getNestedPruningEvent(var, false);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (thenC.arguments().contains(var)) {
            int event = thenC.getNestedPruningEvent(var, true);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (thenC.arguments().contains(var)) {
            int event = thenC.getNestedPruningEvent(var, false);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (elseC.arguments().contains(var)) {
            int event = elseC.getNestedPruningEvent(var, true);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (elseC.arguments().contains(var)) {
            int event = elseC.getNestedPruningEvent(var, false);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (eventAcross == -1)
            return Domain.NONE;
        else
            return eventAcross;


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

        int eventAcross = -1;

        if (condC.arguments().contains(var)) {
            int event = condC.getNestedPruningEvent(var, true);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (condC.arguments().contains(var)) {
            int event = condC.getNestedPruningEvent(var, false);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (thenC.arguments().contains(var)) {
            int event = thenC.getNestedPruningEvent(var, true);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (thenC.arguments().contains(var)) {
            int event = thenC.getNestedPruningEvent(var, false);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (elseC.arguments().contains(var)) {
            int event = elseC.getNestedPruningEvent(var, true);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (elseC.arguments().contains(var)) {
            int event = elseC.getNestedPruningEvent(var, false);
            if (event > eventAcross)
                eventAcross = event;
        }

        if (eventAcross == -1)
            return Domain.NONE;
        else
            return eventAcross;

    }

    @Override public void impose(Store store) {

        super.impose(store);

        this.store = store;
        imposed = true;
    }

    @Override public void include(Store store) {
        this.store = store;
    }

    @Override public boolean satisfied() {

        if (imposed) {

            if (condC.satisfied()) {
                this.removeConstraint();
                store.impose(thenC);
                return false;
            }

            if (condC.notSatisfied()) {
                this.removeConstraint();
                store.impose(elseC);
                return false;
            }

        }

        return (condC.satisfied() && thenC.satisfied()) || (condC.notSatisfied() && elseC.satisfied());

    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : IfThenElse(").append(condC).append(", ");
        result.append(thenC).append(", ").append(elseC).append(" )");

        return result.toString();

    }

    @Override public void queueVariable(int level, Var variable) {

        queueForward.queueForward(level, variable);

    }

}
