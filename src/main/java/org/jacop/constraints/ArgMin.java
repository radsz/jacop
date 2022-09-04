/*
 * ArgMin.java
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
import org.jacop.core.*;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * ArgMin constraint provides the index of the maximum
 * variable from all variables on the list.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */

public class ArgMin extends Constraint implements SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    boolean firstConsistencyCheck = true;

    /**
     * It specifies a list of variables among which a maximum value is being searched for.
     */
    final public IntVar list[];

    /**
     * It specifies variable max which stores the maximum value present in the list.
     */
    final public IntVar minIndex;


    /**
     * It specifies indexOffset within an element constraint list[index-indexOffset] = value.
     */
    public int indexOffset;

    /**
     * It constructs max constraint.
     *
     * @param minIndex    variable denoting the index of the maximum value
     * @param list        the array of variables for which the index of the maximum value is imposed.
     * @param indexOffset the offset for the index that is computed from 1 by default (if needed from 0, use -1 for this parameter)
     */
    public ArgMin(IntVar[] list, IntVar minIndex, int indexOffset) {

        this(list, minIndex);
        this.indexOffset = indexOffset;
    }

    public ArgMin(IntVar[] list, IntVar minIndex) {

        checkInputForNullness(new String[] {"list", "minIndex"}, new Object[][] {list, {minIndex}});

        this.queueIndex = 1;
        this.numberId = idNumber.incrementAndGet();
        this.indexOffset = 0;
        this.minIndex = minIndex;
        this.list = Arrays.copyOf(list, list.length);

        setScope(Stream.concat(Stream.of(minIndex), Stream.of(list)));
    }

    /**
     * It constructs max constraint.
     *
     * @param minIndex    variable denoting the index of minimum value
     * @param variables   the array of variables for which the minimum value is imposed.
     * @param indexOffset the offset for the index that is computed from 1 by default (if needed from 0, use -1 for this parameter)
     */
    public ArgMin(List<? extends IntVar> variables, IntVar minIndex, int indexOffset) {
        this(variables, minIndex);
        this.indexOffset = indexOffset;
    }

    public ArgMin(List<? extends IntVar> variables, IntVar minIndex) {

        this(variables.toArray(new IntVar[variables.size()]), minIndex);

    }

    @Override public void consistency(Store store) {

        if (firstConsistencyCheck) {
            minIndex.domain.in(store.level, minIndex, 1 + indexOffset, list.length + indexOffset);
            firstConsistencyCheck = false;
        }

	int lb = IntDomain.MaxInt;
	int ub = IntDomain.MaxInt;
	int pos = -1;

	// find lower/upper bounds for elements on list
	for (int i = 0; i < list.length; i++) {

	    int vDomMin = list[i].dom().min();
	    if (lb > vDomMin) {
		lb = vDomMin;
	    }

	    int vDomMax = list[i].dom().max();
	    if (ub > vDomMax) {
		ub = vDomMax;
		pos = i;
	    }
	}

	if (lb == ub)
	    minIndex.domain.inMax(store.level, minIndex, pos + 1 + indexOffset);

	// find min/max values for index
	IntervalDomain idxDomain = new IntervalDomain();
	for (int i = 0; i < list.length; i++) {
	    int cp = i + 1 + indexOffset;

	    if (list[i].min() <= ub) {
		if (idxDomain.getSize() == 0)
		    idxDomain.unionAdapt(cp, cp);
		else
		    idxDomain.addLastElement(cp);
	    }
	}
	if (idxDomain.isEmpty())
	    throw Store.failException;
	else
	    minIndex.domain.in(store.level, minIndex, idxDomain);

	// find min value for variables indexed by index variable
	lb = IntDomain.MaxInt;
	pos = -1;
	for (ValueEnumeration e = minIndex.dom().valueEnumeration(); e.hasMoreElements(); ) {
	    int i = e.nextElement() - 1 - indexOffset;

	    int vDomMin = list[i].dom().min();
	    if (lb > vDomMin) {
		lb = vDomMin;
		pos = i;
	    }
	}
	if (list[pos].singleton())
	    minIndex.domain.in(store.level, minIndex, pos + 1 + indexOffset, pos + 1 + indexOffset);

	if (minIndex.singleton()) {

	    int idx = minIndex.value() - 1 - indexOffset;
	    IntVar y = list[idx];

	    for (int i = 0; i < list.length; i++) {

		// prune variables before and after index of max value
		IntVar x = list[i];
		if (i < idx) {
		    // x > y
		    x.domain.inMin(store.level, x, y.min() + 1);
		    y.domain.inMax(store.level, y, x.max() - 1);
		}
		else {
		    // x >= y
		    x.domain.inMin(store.level, x, y.min());
		    y.domain.inMax(store.level, y, x.max());
		}
	    }
	} else {
	    // prune values on the list
	    int im = minIndex.min();
	    for (int i = 0; i < list.length; i++) {
		int cp = i + 1 + indexOffset;

		if (cp < im)
		    list[i].domain.inMin(store.level, list[i], lb + 1);
		else if (cp > im)
		    list[i].domain.inMin(store.level, list[i], lb);
	    }
	}

	// if (maxIndex.singleton() && list[maxIndex.value() - 1 - indexOffset].singleton())
	//     removeConstraint();
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }

        if (var == minIndex)
            return IntDomain.ANY;
        else {
	    return IntDomain.BOUND;
	}
    }

    @Override public boolean satisfied() {

        boolean sat = minIndex.singleton();

        if (!sat)
            return false;

        int MIN = list[minIndex.value() - 1 - indexOffset].value();
        int i = 0, eq = 0;
        while (sat && i < list.length) {
            if (list[i].singleton() && list[i].value() >= MIN)
                eq++;
            sat = list[i].min() >= MIN;
            i++;
        }

        return sat && eq == list.length;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());

        result.append(" : ArgMin(  [ ");
        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);
            if (i < list.length - 1)
                result.append(", ");
        }

        result.append("], ").append(this.minIndex);
        result.append(", "+indexOffset+")");

        return result.toString();
    }

}
