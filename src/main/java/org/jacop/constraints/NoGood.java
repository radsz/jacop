/*
 * NoGood.java
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * NoGood constraints implements a constraint which disallows given combination
 * of values for given variables. NoGoods are special constraints as they can be
 * only triggered only when all variables except one are grounded and equal to
 * disallow values. This allows efficient implementation based on watched
 * literals idea from SAT community.
 *
 * Do not be fooled by watched literals, if you add thousands of no-goods then
 * traversing even 1/10 of them if they are watched by variable which has been 
 * grounded can slow down search considerably. 
 *
 * NoGoods constraints are imposed at all levels once added. Do not use in 
 * subsearches, as it will not take into account the assignments performed in
 * master search.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */

public class NoGood extends Constraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a list of variables in no-good constraint.
     */
    private IntVar listOfVars[];

    /**
     * It specifies a list of values in no-good constraint.
     */
    private int listOfValues[];

    private IntVar firstWatch;

    private int firstValue;

    private IntVar secondWatch;

    private int secondValue;

    private final static boolean debug = false;

    /**
     * It creates a no-good constraint.
     * @param listOfVars the scope of the constraint.
     * @param listOfValues no-good values which all-together assignment to variables within constraint scope is a no-good.
     */
    public NoGood(IntVar[] listOfVars, int[] listOfValues) {

        commonInitialization(listOfVars, listOfValues);

    }

    private void commonInitialization(IntVar[] listOfVars, int[] listOfValues) {

        checkInputForNullness("listOfVars", listOfVars);
        checkInputForNullness("listOfValues", listOfValues);

        if (listOfVars.length != listOfValues.length)
            throw new IllegalArgumentException("Length of listOfVars is different from listOfValues");

        this.queueIndex = 0;
        this.numberId = idNumber.incrementAndGet();
        this.listOfVars = Arrays.copyOf(listOfVars, listOfVars.length);
        this.listOfValues = Arrays.copyOf(listOfValues, listOfValues.length);

        setScope(listOfVars);

    }

    /**
     * It creates a no-good constraint.
     * @param listOfVars the scope of the constraint.
     * @param listOfValues no-good values which all-together assignment to variables within constraint scope is a no-good.
     */
    public NoGood(List<? extends IntVar> listOfVars, List<Integer> listOfValues) {

        checkInputForNullness(new String[]{"listOfVars", "listOfValues"}, new Object[]{ listOfVars, listOfValues});
        commonInitialization(listOfVars.toArray(new IntVar[listOfVars.size()]), listOfValues.stream().mapToInt(i -> i).toArray());

    }

    @Override public void consistency(Store store) {

        if (debug)
            System.out.println("Start " + this);

        if (firstWatch == secondWatch) {
            // Special case, when NoGood was one variable no-good
            // or there was no two not singleton variables to be
            // watched.

            if (debug)
                System.out.println("Special cases of noGood constraints have occured");

            if (listOfVars.length == 1) {

                firstWatch.dom().inComplement(store.level, firstWatch, firstValue);

                // store.in(firstWatch, Domain.domain.complement(firstValue));
                return;
            } else {
                // check if it still active no-good
                for (int i = 0; i < listOfVars.length; i++)
                    if (listOfVars[i].getSize() == 1 && listOfVars[i].value() != listOfValues[i])
                        return;

                // if variable is not singleton (even if it was at imposition
                // time)
                // sanity check, just in case, but if this code is executed than
                // mostly improper use of no-goods has been performed.
                for (IntVar listOfVar : listOfVars)
                    if (listOfVar.getSize() != 1 && listOfVar != firstWatch) {
                        throw new RuntimeException(
                            "The NoGood learnt for one model is used in different model (model created across many store levels)");
                    }

                firstWatch.dom().inComplement(store.level, firstWatch, firstValue);
                // store.in(firstWatch, Domain.domain.complement(firstValue));
                return;
            }

        }

        // no good satisfied
        if (firstWatch.getSize() == 1 && firstWatch.value() != firstValue)
            return;

        // no good satisfied
        if (secondWatch.getSize() == 1 && secondWatch.value() != secondValue)
            return;

        if (firstWatch.getSize() == 1 || secondWatch.getSize() == 1)
            for (int i = 0; i < listOfVars.length; i++)
                if (listOfVars[i].singleton() && !listOfVars[i].singleton(listOfValues[i]))
                    return;

        if (firstWatch.getSize() == 1) {

            boolean found = false;
            // new watched variable needs to be found
            for (int i = 0; i < listOfVars.length; i++)
                if (listOfVars[i] != secondWatch && listOfVars[i].getSize() != 1) {

                    store.deregisterWatchedLiteralConstraint(firstWatch, this);

                    firstWatch = listOfVars[i];
                    firstValue = listOfValues[i];

                    store.registerWatchedLiteralConstraint(firstWatch, this);

                    found = true;
                }

            if (!found) {
                // no new watch found, can propagate.

                secondWatch.dom().inComplement(store.level, secondWatch, secondValue);

                // store.in(secondWatch, Domain.domain.complement(secondValue));
                if (debug)
                    System.out.println(secondWatch);

                return;

            }
        }

        if (secondWatch.getSize() == 1) {
            // new watched variable needs to be found

            boolean found = false;

            for (int i = 0; i < listOfVars.length; i++)
                if (listOfVars[i] != firstWatch && listOfVars[i].getSize() != 1) {

                    store.deregisterWatchedLiteralConstraint(secondWatch, this);

                    secondWatch = listOfVars[i];
                    secondValue = listOfValues[i];

                    store.registerWatchedLiteralConstraint(secondWatch, this);

                    found = true;
                }

            if (!found) {
                // no new watch found, can propagate.

                firstWatch.dom().inComplement(store.level, firstWatch, firstValue);

                // store.in(firstWatch, Domain.domain.complement(firstValue));
                if (debug)
                    System.out.println(firstWatch);
            }

        }

        if (debug)
            System.out.println("End" + this);
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    // registers the constraint in the constraint store
    // using watched literals functionality.
    @Override public void impose(Store store) {

        if (store.watchedConstraints == null)
            store.watchedConstraints = Var.createEmptyPositioning();

        if (listOfVars.length == 1) {

            // No good is of form XneqC.
            firstWatch = secondWatch = listOfVars[0];
            firstValue = listOfValues[0];
            store.registerWatchedLiteralConstraint(firstWatch, this);

            // To obtain immediate pruning when consistency is called
            store.addChanged(this);
        } else {

            int i = 0;
            // Find any two variables and attach a no-good to it.
            for (int j = 0; j < listOfVars.length; j++) {
                IntVar v = listOfVars[j];
                if (v.getSize() != 1 && i < 2) {
                    if (i == 0) {
                        firstWatch = v;
                        firstValue = listOfValues[j];
                    } else {
                        secondWatch = v;
                        secondValue = listOfValues[j];
                    }
                    i++;
                }
            }

            if (i < 2) {
                // No good is of form XneqC, as there are no two variables which
                // are not singletons.

                secondWatch = firstWatch;
                secondValue = firstValue;

                // No good is already satisfied and it is ignored.
                for (IntVar listOfVar : listOfVars)
                    if (listOfVars[i].getSize() == 1 && listOfVars[i].value() != listOfValues[i])
                        return;

                // All values match, so no good is at the moment equivalent to
                // one-variable no-good.

                store.registerWatchedLiteralConstraint(firstWatch, this);

                // To obtain immediate pruning when consistency is called
                store.addChanged(this);
            } else {
                store.registerWatchedLiteralConstraint(firstWatch, this);
                store.registerWatchedLiteralConstraint(secondWatch, this);
            }
        }

    }

    /**
     * This function does nothing as constraints can not be removed for a given
     * level. In addition, watched literals mechanism makes sure that constraint
     * is not put in the queue when it can not propagate.
     */
    @Override public void removeConstraint() {

        // This function does not do anything on purpose.
        // if constraint is removed from variable then it is removed for all
        // levels.
        // This is not how this function is being used, as constraint is removed
        // only on level on which it is satisfied.

    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : noGood([");

        for (int i = 0; i < listOfVars.length; i++) {
            if (listOfVars[i] == firstWatch || listOfVars[i] == secondWatch)
                result.append("@");
            result.append(listOfVars[i]);
            if (i < listOfVars.length - 1)
                result.append(", ");
        }
        result.append("], [");

        for (int i = 0; i < listOfValues.length; i++) {
            result.append(listOfValues[i]);
            if (i < listOfValues.length - 1)
                result.append(", ");
        }
        result.append("] )");
        return result.toString();
    }

}
