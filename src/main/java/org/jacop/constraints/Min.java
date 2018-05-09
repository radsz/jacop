/*
 * Min.java
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

import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * Min constraint implements the minimum/2 constraint. It provides the minimum
 * varable from all FD varaibles on the list.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Min extends Constraint implements SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a list of variables among which the minimum value is being searched for.
     */
    final public IntVar list[];

    /**
     * It specifies variable min, which stores the minimum value within the whole list.
     */
    final public IntVar min;

    /**
     * It specifies the length of the list.
     */
    final int l;

    /**
     * Defines first position of the variable that needs to be considered
     */
    private TimeStamp<Integer> position;

    /**
     * It constructs min constraint.
     *
     * @param min  variable denoting the minimal value
     * @param list the array of variables for which the minimal value is imposed.
     */
    public Min(IntVar[] list, IntVar min) {

        checkInputForNullness(new String[] {"list", "min"}, list, new Object[] {min});

        this.l = list.length;
        this.min = min;
        this.list = Arrays.copyOf(list, list.length);

        if (list.length > 1000)  // rule of thumb
            this.queueIndex = 2;
        else
            this.queueIndex = 1;

        this.numberId = idNumber.incrementAndGet();

        setScope(Stream.concat(Arrays.stream(list), Stream.of(min)));
    }

    /**
     * It constructs min constraint.
     *
     * @param min  variable denoting the minimal value
     * @param list the array of variables for which the minimal value is imposed.
     */
    public Min(List<? extends IntVar> list, IntVar min) {

        this(list.toArray(new IntVar[list.size()]), min);

    }

    @Override public void consistency(Store store) {

        int start = position.value();
        IntVar var;
        IntDomain vDom;

        //@todo keep one variable with the smallest value as watched variable
        // only check for other support if that smallest value is no longer part
        // of the variable domain.

        int minValue = IntDomain.MaxInt;
        int maxValue = IntDomain.MaxInt;

        int minMin = min.min();
        int maxMin = min.max();
        for (int i = start; i < l; i++) {
            var = list[i];

            vDom = var.dom();
            int varMin = vDom.min(), varMax = vDom.max();

            if (varMin > maxMin) {
                swap(start, i);
                start++;
            } else if (varMin < minMin)
                var.domain.inMin(store.level, var, minMin);

            minValue = (minValue < varMin) ? minValue : varMin;
            maxValue = (maxValue < varMax) ? maxValue : varMax;
        }

        position.update(start);

        min.domain.in(store.level, min, minValue, maxValue);

        if (start == l) // all variables have their min value greater than max value of min variable
            throw Store.failException;

        if (start == list.length - 1) { // one variable on the list is minimal; its is max < min of all other variables
            list[start].domain.in(store.level, list[start], min.dom());

            if (min.singleton())
                removeConstraint();

        }

    }

    private void swap(int i, int j) {
        if (i != j) {
            IntVar tmp = list[i];
            list[i] = list[j];
            list[j] = tmp;
        }
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    // registers the constraint in the constraint store
    @Override public void impose(final Store store) {

        super.impose(store);
        position = new TimeStamp<>(store, 0);

    }

    @Override public boolean satisfied() {

        if (!min.singleton())
            return false;

        int minValue = min.max();
        int i = 0;
        boolean eq = false;

        while (i < list.length) {
            if (list[i].min() < minValue)
                return false;
            if (!eq && (list[i].singleton() && list[i].value() == minValue))
                eq = true;
            i++;
        }

        return eq;
    }

    @Override public String toString() {
        StringBuffer result = new StringBuffer(id());

        result.append(" : min( [ ");
        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);
            if (i < list.length - 1)
                result.append(", ");
        }

        result.append("], ").append(this.min);
        result.append(")");

        return result.toString();

    }

}
