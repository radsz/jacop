/*
 * PartitionSet.java
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

package org.jacop.set.constraints;

import org.jacop.constraints.Constraint;
import org.jacop.core.*;
import org.jacop.set.core.*;
import org.jacop.api.UsesQueueVariable;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.stream.Stream;
import java.util.LinkedHashSet;

/**
 * Channel constraint requires that array of int variables x and array
 * of set variables y are related such that (x[i] = j) {@literal <->}
 (i in s[j]).  Indexes start form 0, both for integer and set variables,
 * by default. To define other starting index use offset definitions.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */


public class PartitionSet extends Constraint implements UsesQueueVariable {

    static AtomicInteger idNumber = new AtomicInteger(0);

    SetVar[] s;
    int n;
    IntDomain u;

    boolean firstConsistencyCheck = true;

    LinkedHashSet<Integer> variableQueue = new LinkedHashSet<>();
    HashMap<SetVar, Integer> varMap = new HashMap<>();

    Store store;

    /**
     * It constructs a Channel constraint.
     *
     * @param s array of set variables.
     * @param universe set of all values.
     */
    public PartitionSet(SetVar[] s, IntDomain universe) {

        checkInputForNullness(new String[] {"s"}, new Object[] {s});

        numberId = idNumber.incrementAndGet();

        this.s = s;
        n = s.length;
        this.u = universe;

        for (int i = 0; i < n; i++) {
            varMap.put(s[i], i);
        }

        setScope(Arrays.stream(s));
    }

    @Override public void consistency(Store store) throws FailException {

        if (firstConsistencyCheck) {
            
            for (int i = 0; i < n; i++)
                s[i].domain.inLUB(store.level, s[i], u);

            firstConsistencyCheck = false;
        }

        do {

            store.propagationHasOccurred = false;

            LinkedHashSet<Integer> fdvs = variableQueue;
            variableQueue = new LinkedHashSet<Integer>();

            for (Integer i : fdvs)
                if (i != null) {
                    IntDomain glb = s[i].dom().glb();
                    for (ValueEnumeration e = glb.valueEnumeration(); e.hasMoreElements(); ) {
                        int si = e.nextElement();
                        for (int j = 0; j < n; j++) {
                            if (i != j)
                                s[j].dom().inLUBComplement(store.level, s[j], si);
                        }
                    }
                }
        } while (store.propagationHasOccurred);

        // check union constraint
        for (int i = 0; i < n; i++) {
            IntDomain t = u.cloneLight();
            for (int j = 0; j < n; j++) {
                if (i != j) {
                    t = t.subtract(s[j].dom().lub());
                }
            }
            s[i].dom().inGLB(store.level, s[i], t);
        }
    }

    @Override public void queueVariable(int level, Var var) {
        variableQueue.add(varMap.get((SetVar)var));
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return SetDomain.ANY;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer();
        result.append(id() + " : PartitionSet(");
        result.append(Arrays.asList(s)).append(", ").append(u);
        result.append(")");
        return result.toString();

    }
}
