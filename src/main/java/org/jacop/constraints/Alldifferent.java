/*
 * Alldifferent.java
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

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.api.SatisfiedPresent;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.*;

/**
 * Alldifferent constraint assures that all FDVs has differnet values. It uses
 * partial consistency technique.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Alldifferent extends Constraint implements UsesQueueVariable, SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a list of variables which must take different values.
     */
    public IntVar[] list;

    LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<IntVar>();

    protected Map<IntVar, Integer> positionMapping;

    protected TimeStamp<Integer> grounded;

    protected Alldifferent() {
    }

    /**
     * It constructs the alldifferent constraint for the supplied variable.
     * @param list variables which are constrained to take different values.
     */
    public Alldifferent(IntVar[] list) {

        checkInputForNullness("list", list);
        checkInputForDuplication("list", list);

        this.numberId = idNumber.incrementAndGet();
        this.list = Arrays.copyOf(list, list.length);
        setScope(this.list);

    }

    /**
     * It constructs the alldifferent constraint for the supplied variable.
     * @param variables variables which are constrained to take different values.
     */

    public Alldifferent(List<? extends IntVar> variables) {
        this(variables.toArray(new IntVar[variables.size()]));
    }
    
    @Override public void consistency(Store store) {

        do {

            store.propagationHasOccurred = false;

            LinkedHashSet<IntVar> fdvs = variableQueue;
            variableQueue = new LinkedHashSet<IntVar>();

            for (IntVar Q : fdvs)
                if (Q.singleton()) {
                    int qPos = positionMapping.get(Q);
                    int groundPos = grounded.value();
                    if (qPos > groundPos) {
                        list[qPos] = list[groundPos];
                        list[groundPos] = Q;
                        positionMapping.put(Q, groundPos);
                        positionMapping.put(list[qPos], qPos);
                        grounded.update(++groundPos);
                        for (int i = groundPos; i < list.length; i++)
                            list[i].domain.inComplement(store.level, list[i], Q.min());
                    } else if (qPos == groundPos) {
                        grounded.update(++groundPos);
                        for (int i = groundPos; i < list.length; i++)
                            list[i].domain.inComplement(store.level, list[i], Q.min());
                    }

                }

        } while (store.propagationHasOccurred);


    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override public boolean satisfied() {

        for (int i = grounded.value(); i < list.length; i++)
            if (!list[i].singleton())
                return false;

        Set<Integer> values = new HashSet<>();

        for (IntVar aList : list)
            if (!values.add(aList.value()))
                return false;

        return true;

    }

    @SuppressWarnings("unused") private boolean satisfiedFullCheck(Store S) {

        int i = 0;

        IntervalDomain result = new IntervalDomain();

        while (i < list.length - 1) {

            if (list[i].domain.isIntersecting(result))
                return false;

            result.addDom(list[i].domain);

            i++;
        }

        return true;

    }

    @Override public void impose(Store store) {

        super.impose(store);
        positionMapping = Var.positionMapping(list, false, this.getClass());
        grounded = new TimeStamp<>(store, 0);
        
    }

    @Override public void queueVariable(int level, Var V) {
        variableQueue.add((IntVar) V);
    }

    @SuppressWarnings("unused") private boolean satisfiedBound() {
        boolean sat = true;
        int i = 0;
        while (sat && i < list.length) {
            IntDomain vDom = list[i].dom();
            int vMin = vDom.min(), vMax = vDom.max();
            int j = i + 1;
            while (sat && j < list.length) {
                IntDomain ljDom = list[j].dom();
                sat = (vMin > ljDom.max() || vMax < ljDom.min());
                j++;
            }
            i++;
        }
        return sat;
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : alldifferent([");

        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);
            if (i < list.length - 1)
                result.append(", ");
        }
        result.append("])");

        return result.toString();

    }
    
}
