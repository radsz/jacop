/*
 * Or.java
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
 * Constraint c1 \/ c2 \/ ... \/ cn.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Or extends PrimitiveConstraint implements UsesQueueVariable {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a list of constraints from which one constraint must be satisfied.
     */
    public PrimitiveConstraint listOfC[];

    /**
     * It specifies if during the consistency execution a propagation has occurred.
     */
    private boolean propagation;

    final public QueueForward<PrimitiveConstraint> queueForward;

    /**
     * It constructs Or constraint.
     *
     * @param listOfC list of primitive constraints which at least one of them has to be satisfied.
     */
    public Or(PrimitiveConstraint[] listOfC) {

        checkInputForNullness("listOfC", listOfC);

        this.queueIndex = 1;
        this.numberId = idNumber.incrementAndGet();
        this.listOfC = Arrays.copyOf(listOfC, listOfC.length);
        setScope(listOfC);
        setConstraintScope(listOfC);
        queueForward = new QueueForward<PrimitiveConstraint>(listOfC, arguments());
        this.queueIndex = Arrays.stream(listOfC).max((a, b) -> Integer.max(a.queueIndex, b.queueIndex)).map( a -> a.queueIndex ).orElse(0);
    }

    /**
     * It constructs Or constraint.
     *
     * @param listOfC list of primitive constraints which at least one of them has to be satisfied.
     */
    public Or(List<PrimitiveConstraint> listOfC) {
        this(listOfC.toArray(new PrimitiveConstraint[listOfC.size()]));
    }

    /**
     * It constructs an Or constraint, at least one constraint has to be satisfied.
     *
     * @param c1 the first constraint which can be satisfied.
     * @param c2 the second constraint which can be satisfied.
     */
    public Or(PrimitiveConstraint c1, PrimitiveConstraint c2) {
        this(new PrimitiveConstraint[] {c1, c2});
    }

    @Override public void consistency(Store store) {

        //@todo, why so much work?
        // search for the first one which returns false for notSatisfied() call
        // use circular buffer approach to remember the last notSatisfied()== false to start checking from this one.
        int numberSat = 0;
        int numberNotSat = 0;
        int j = 0;

        int i = 0;
        while (numberSat == 0 && i < listOfC.length) {
            if (listOfC[i].satisfied())
                numberSat++;
            else {
                if (listOfC[i].notSatisfied())
                    numberNotSat++;
                else
                    j = i;
            }
            i++;
        }

        if (numberSat == 0) {

            if (numberNotSat == listOfC.length - 1)
                listOfC[j].consistency(store);
            else if (numberNotSat == listOfC.length)
                throw Store.failException;

        } else if (numberSat > 0) {
            removeConstraint();
        }

    }

    @Override public int getNestedPruningEvent(Var var, boolean mode) {

        return getConsistencyPruningEvent(var);

    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise variant exists.");
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise variant exists.");
    }

    @Override public void queueVariable(int level, Var var) {

        propagation = true;
        queueForward.queueForward(level, var);

    }

    @Override public void notConsistency(Store store) {

        // From De'Morgan laws not(A or B) == not A and not B
        do {

            propagation = false;
            for (int i = 0; i < listOfC.length; i++)
                listOfC[i].notConsistency(store);

        } while (propagation);

    }

    @Override public boolean notSatisfied() {
        boolean notSat = true;

        int i = 0;
        while (notSat && i < listOfC.length) {
            notSat = notSat && listOfC[i].notSatisfied();
            i++;
        }
        return notSat;
    }

    @Override public boolean satisfied() {
        boolean sat = false;

        int i = 0;
        while (!sat && i < listOfC.length) {
            sat = sat || listOfC[i].satisfied();
            i++;
        }
        return sat;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : Or( ");
        for (int i = 0; i < listOfC.length; i++) {
            result.append(listOfC[i]);
            if (i == listOfC.length - 1)
                result.append("),");
            else
                result.append(", ");
        }
        return result.toString();
    }

}
