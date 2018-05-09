/*
 * And.java
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

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * Constraint c1 /\ c2 ... /\ cn
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */
public class And extends PrimitiveConstraint implements UsesQueueVariable {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a list of constraints which must be satisfied to keep And constraint satisfied.
     */
    private final PrimitiveConstraint listOfC[];

    private final QueueForward<PrimitiveConstraint> queueForward;

    /**
     * It constructs an And constraint based on primitive constraints. The
     * constraint is satisfied if all constraints are satisfied.
     *
     * @param listOfC arraylist of constraints
     */
    public And(List<PrimitiveConstraint> listOfC) {
        this(listOfC.toArray(new PrimitiveConstraint[listOfC.size()]));
    }

    /**
     * It constructs a simple And constraint based on two primitive constraints.
     *
     * @param c1 the first primitive constraint
     * @param c2 the second primitive constraint
     */
    public And(PrimitiveConstraint c1, PrimitiveConstraint c2) {
        this(new PrimitiveConstraint[] {c1, c2});
    }

    /**
     * It constructs an And constraint over an array of primitive constraints.
     *
     * @param c an array of primitive constraints constituting the And constraint.
     */
    public And(PrimitiveConstraint[] c) {

        checkInputForNullness("c", c);
        this.queueIndex = 1;
        this.numberId = idNumber.incrementAndGet();
        this.listOfC = Arrays.copyOf(c, c.length);
        setScope(listOfC);
        setConstraintScope(listOfC);
        queueForward = new QueueForward<>(listOfC, arguments());
        this.queueIndex = Arrays.stream(c).max((a, b) -> Integer.max(a.queueIndex, b.queueIndex)).map( a -> a.queueIndex).orElse(0);

    }

    private boolean propagation;

    @Override public void consistency(Store store) {

        propagation = true;

        do {

            // Variable propagation can be set to true again if queueVariable function is being called.
            propagation = false;

            for (Constraint cc : listOfC)
                cc.consistency(store);

        } while (propagation);

    }

    @Override public int getNestedPruningEvent(Var var, boolean mode) {
        return getConsistencyPruningEvent(var);
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise version exists.");
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise version exists.");
    }

    @Override public void notConsistency(Store store) {

        int numberCertainNotSat = 0;
        int numberCertainSat = 0;
        int j = 0;
        int i = 0;

        while (numberCertainNotSat == 0 && i < listOfC.length) {
            if (listOfC[i].notSatisfied())
                numberCertainNotSat++;
            else {
                if (listOfC[i].satisfied())
                    numberCertainSat++;
                else
                    j = i;
            }
            i++;
        }

        if (numberCertainNotSat == 0) {
            if (numberCertainSat == listOfC.length - 1) {
                listOfC[j].notConsistency(store);
            } else if (numberCertainSat == listOfC.length)
                throw Store.failException;
        }
    }

    @Override public void queueVariable(int level, Var variable) {

        propagation = true;
        queueForward.queueForward(level, variable);

    }

    @Override public boolean notSatisfied() {
        boolean notSat = false;

        int i = 0;
        while (!notSat && i < listOfC.length) {
            notSat = listOfC[i].notSatisfied();
            i++;
        }
        return notSat;
    }

    @Override public boolean satisfied() {

        for (PrimitiveConstraint c : listOfC)
            if (! c.satisfied())
                return false;

        return true;

    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : And(");

        for (int i = 0; i < listOfC.length; i++) {
            result.append(listOfC[i]);
            if (i == listOfC.length - 1)
                result.append(",");
        }
        return result.toString();
    }

}
