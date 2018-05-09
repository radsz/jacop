/*
 * VariableTrace.java
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
import org.jacop.core.Var;
import org.jacop.core.Store;
import org.jacop.core.IntDomain;

import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * VariableTrace is a daemon that prints information on variables whenever they are changed.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class VariableTrace extends Constraint implements UsesQueueVariable {

    static AtomicInteger idNumber = new AtomicInteger(0);

    Var[] vars;
    Store store;

    /**
     * It constructs trace daemon for variable v
     * @param v variable to be traced
     */
    public VariableTrace(Var v) {
        this(new Var[] {v});
    }

    /**
     * It constructs trace daemon for variables vs
     * @param vs variables to be traced
     */
    public VariableTrace(Var[] vs) {

        numberId = idNumber.incrementAndGet();

        vars = new Var[vs.length];
        for (int i = 0; i < vs.length; i++) {
            vars[i] = vs[i];
        }

        setScope(vars);
    }

    /**
     * It constructs trace daemon for variables vs
     * @param vs variables to be traced
     */
    public VariableTrace(List<Var> vs) {
        this(vs.toArray(new Var[vs.size()]));
    }

    public void impose(Store store) {

        this.store = store;

        store.registerRemoveLevelLateListener(this);

        for (Var v : vars) {
            v.putModelConstraint(this, getConsistencyPruningEvent(v));
            // we do not want to print initial values
            // queueVariable(store.level, v);
        }

        store.countConstraint();
    }

    public void consistency(Store store) {
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    public void queueVariable(int level, Var var) {
        System.out.println("Var: " + var + ", level: " + level + ", constraint: " + store.currentConstraint);
    }

    @Override public void removeLevelLate(int level) {

        System.out.print("Restore level: " + level + ", vars: ");

        for (Var v : vars) {
            System.out.print(v + " ");
        }
        System.out.println();
    }

    public void removeConstraint() {
    }

    public boolean satisfied() {
        return false;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());

        result.append(" : variableTrace([");

        for (int i = 0; i < vars.length; i++) {
            result.append(vars[i]);
            if (i < vars.length - 1)
                result.append(", ");
        }
        result.append("])");

        return result.toString();

    }

    public void increaseWeight() {
    }

}
