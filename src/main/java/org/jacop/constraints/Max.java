/*
 * Max.java
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
 * Max constraint implements the Maximum/2 constraint. It provides the maximum
 * variable from all variables on the list.
 * <p>
 * max(list) = max.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Max extends Constraint implements SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a list of variables among which a maximum value is being searched for.
     */
    final public IntVar list[];

    /**
     * It specifies variable max which stores the maximum value present in the list.
     */
    final public IntVar max;

    /**
     * It specifies length of the list.
     */
    final int l;

    /**
     * Defines first position of the variable that needs to be considered
     */
    private TimeStamp<Integer> position;

    /**
     * It constructs max constraint.
     *
     * @param max  variable denoting the maximum value
     * @param list the array of variables for which the maximum value is imposed.
     */
    public Max(IntVar[] list, IntVar max) {

        checkInputForNullness(new String[] {"list", "max"}, new Object[][] {list, {max}});

        this.l = list.length;
        this.max = max;
        this.list = Arrays.copyOf(list, list.length);

        if (list.length > 1000)  // rule of thumb
            this.queueIndex = 2;
        else
            this.queueIndex = 1;

        this.numberId = idNumber.incrementAndGet();

        setScope(Stream.concat(Arrays.stream(list), Stream.of(max)));

    }

    /**
     * It constructs max constraint.
     *
     * @param max       variable denoting the maximum value
     * @param variables the array of variables for which the maximum value is imposed.
     */
    public Max(List<? extends IntVar> variables, IntVar max) {
        this(variables.toArray(new IntVar[variables.size()]), max);
    }

    @Override public void consistency(Store store) {

        int start = position.value();
        IntVar var;
        IntDomain vDom;

        int minValue = IntDomain.MinInt;
        int maxValue = IntDomain.MinInt;

        int maxMax = max.max();
        int minMax = max.min();
        for (int i = start; i < l; i++) {

            var = list[i];

            vDom = var.dom();
            int varMin = vDom.min(), varMax = vDom.max();

            if (varMax < minMax) {
                swap(start, i);
                start++;
            } else if (varMax > maxMax)
                var.domain.inMax(store.level, var, maxMax);

            minValue = (minValue > varMin) ? minValue : varMin;
            maxValue = (maxValue > varMax) ? maxValue : varMax;
        }

        position.update(start);

        max.domain.in(store.level, max, minValue, maxValue);

        if (start == l) // all variables have their max value lower than min value of max variable
            throw Store.failException;

        if (start == list.length - 1) { // one variable on the list is maximal; its is min > max of all other variables
            list[start].domain.in(store.level, list[start], max.dom());

            if (max.singleton())
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

    @Override public void impose(Store store) {

        position = new TimeStamp<>(store, 0);

        super.impose(store);

    }

    @Override public boolean satisfied() {

        boolean sat = max.singleton();
        int MAX = max.min();
        int i = 0, eq = 0;
        while (sat && i < list.length) {
            if (list[i].singleton() && list[i].value() == MAX)
                eq++;
            sat = list[i].max() <= MAX;
            i++;
        }
        return sat && eq > 0;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());

        result.append(" : max(  [ ");
        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);
            if (i < list.length - 1)
                result.append(", ");
        }

        result.append("], ").append(this.max);
        result.append(")");

        return result.toString();
    }

}
