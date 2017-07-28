/**
 * PrimitiveConstraint.java
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

import java.util.Hashtable;

import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Standard unified interface for all primitive constraints. In addition to
 * functions defined by interface Constraint it also defines function
 * notConsistency and notSatisfied. Only PrimitiveConstraints can be used as
 * arguments to constraints Not, And, Or, etc.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.4
 */

public abstract class PrimitiveConstraint extends Constraint {

    /**
     * It specifies the events which must occur for notConsistency()
     * method being executed.
     */
    public Hashtable<Var, Integer> notConsistencyPruningEvents;

    /**
     * It retrieves the pruning event which causes reevaluation of the
     * constraint notConsistency() function.
     *
     * @param var for which pruning event is retrieved
     * @return the int denoting the pruning event associated with given variable.
     */
    public int getNotConsistencyPruningEvent(Var var) {

        // If notConsistency function mode
        if (notConsistencyPruningEvents != null) {
            Integer possibleEvent = notConsistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        return getDefaultNotConsistencyPruningEvent();
    }

    /**
     * It retrieves the pruning event for which any composed constraint which
     * uses this constraint should be evaluated. This events are the ones which
     * can change satisfied status?
     *
     * @param var for which pruning event is retrieved
     * @param mode decides if pruning event for consistency or nonconsistency is required.
     * @return pruning event associated with the given variable for a given consistency mode.
     */
    public int getNestedPruningEvent(Var var, boolean mode) {

        // If consistency function mode
        if (mode) {
            if (consistencyPruningEvents != null) {
                Integer possibleEvent = consistencyPruningEvents.get(var);
                if (possibleEvent != null)
                    return possibleEvent;
            }
            return getDefaultNestedConsistencyPruningEvent();
        }
        // If notConsistency function mode
        else {
            if (notConsistencyPruningEvents != null) {
                Integer possibleEvent = notConsistencyPruningEvents.get(var);
                if (possibleEvent != null)
                    return possibleEvent;
            }
            return getDefaultNestedNotConsistencyPruningEvent();
        }
    }

    protected int getDefaultNestedNotConsistencyPruningEvent() {
        return getDefaultNotConsistencyPruningEvent();
    }

    protected int getDefaultNestedConsistencyPruningEvent() {
        return getDefaultConsistencyPruningEvent();
    }

    protected abstract int getDefaultNotConsistencyPruningEvent();
/*
    {
        throw new IllegalStateException("Not implemented as more precise variants exist.");
    }
*/

    /**
     * It makes pruning in such a way that constraint is notConsistent. It
     * removes values which always belong to a solution.
     * @param store the constraint store in which context the notConsistency technique is evaluated.
     */
    public abstract void notConsistency(Store store);

    /**
     * It checks if constraint would be always not satisfied.
     * @return true if constraint must be notSatisfied, false otherwise.
     */
    public abstract boolean notSatisfied();


    /**
     * It provide store for constraints that are not imposed but called from ather constraints.
     * @param store the constraint store in which context the constraint is executed.
     */
    public void include(Store store) {
    }

    /**
     * It allows to specify customized events required to trigger execution
     * of notConsitency() method.
     *
     * @param var variable for which customized event is setup.
     * @param pruningEvent the type of the event being setup.
     */
    public void setNotConsistencyPruningEvent(Var var, int pruningEvent) {

        if (notConsistencyPruningEvents == null)
            notConsistencyPruningEvents = new Hashtable<Var, Integer>();

        notConsistencyPruningEvents.put(var, pruningEvent);

    }

}
