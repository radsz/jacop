/*
 * ArgMax.java
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
 * ArgMax constraint provides the index of the maximum
 * variable from all variables on the list.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */

public class ArgMax extends Constraint implements SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    boolean firstConsistencyCheck = true;

    /**
     * It specifies a list of variables among which a maximum value is being searched for.
     */
    final public IntVar list[];

    /**
     * It specifies variable max which stores the maximum value present in the list.
     */
    final public IntVar maxIndex;


    /**
     * It specifies indexOffset within an element constraint list[index-indexOffset] = value.
     */
    public int indexOffset;

    /**
     * It constructs max constraint.
     *
     * @param maxIndex    variable denoting the index of the maximum value
     * @param list        the array of variables for which the index of the maximum value is imposed.
     * @param indexOffset the offset for the index that is computed from 1 by default (if needed from 0, use -1 for this parameter)
     */
    public ArgMax(IntVar[] list, IntVar maxIndex, int indexOffset) {
        this(list, maxIndex);
        this.indexOffset = indexOffset;
    }

    public ArgMax(IntVar[] list, IntVar maxIndex) {

        checkInputForNullness(new String[] {"list", "maxIndex"}, new Object[][] {list, {maxIndex}});

        this.queueIndex = 1;
        this.numberId = idNumber.incrementAndGet();
        this.indexOffset = 0;
        this.maxIndex = maxIndex;
        this.list = Arrays.copyOf(list, list.length);

        setScope(Stream.concat(Arrays.stream(list), Stream.of(maxIndex)));
    }

    /**
     * It constructs max constraint.
     *
     * @param maxIndex    variable denoting index of the maximum value
     * @param variables   the array of variables for which the maximum value is imposed.
     * @param indexOffset the offset for the index that is computed from 1 by default (if needed from 0, use -1 for this parameter)
     */
    public ArgMax(List<? extends IntVar> variables, IntVar maxIndex, int indexOffset) {
        this(variables, maxIndex);
        this.indexOffset = indexOffset;
    }

    public ArgMax(List<? extends IntVar> variables, IntVar maxIndex) {
        this(variables.toArray(new IntVar[variables.size()]), maxIndex);
    }

    @Override public void consistency(Store store) {

        if (firstConsistencyCheck) {
            maxIndex.domain.in(store.level, maxIndex, 1 + indexOffset, list.length + indexOffset);
            firstConsistencyCheck = false;
        }

	int lb = IntDomain.MinInt;
	int ub = IntDomain.MinInt;
	int pos = -1;

	// find lower/upper bounds for indexed elements on list
	for (ValueEnumeration e = maxIndex.dom().valueEnumeration(); e.hasMoreElements(); ) {
	    int cp = e.nextElement();
	    int i = cp - 1 - indexOffset;

	    int vDomMin = list[i].min();
	    if (lb < vDomMin) {
		lb = vDomMin;
		pos = i;
	    }

	    int vDomMax = list[i].max();
	    if (ub < vDomMax) {
		ub = vDomMax;
	    }
	}
	if (lb == ub)
	    maxIndex.domain.inMax(store.level, maxIndex, pos + 1 + indexOffset);

	// find min/max values for index
	IntervalDomain idxDomain = new IntervalDomain();
	for (ValueEnumeration e = maxIndex.dom().valueEnumeration(); e.hasMoreElements(); ) {
	    int cp = e.nextElement();
	    int i = cp - 1 - indexOffset;

	    if (list[i].max() >= lb) {
		if (idxDomain.getSize() == 0)
		    idxDomain.unionAdapt(cp, cp);
		else
		    idxDomain.addLastElement(cp);
	    }
	}
	if (idxDomain.isEmpty())
	    throw Store.failException;
	else
	    maxIndex.domain.in(store.level, maxIndex, idxDomain);

	ub = IntDomain.MinInt;
	pos = -1;
	for (ValueEnumeration e = maxIndex.dom().valueEnumeration(); e.hasMoreElements(); ) {
	    int i = e.nextElement() - 1 - indexOffset;

	    int vDomMax = list[i].max();
	    if (ub < vDomMax) {
		ub = vDomMax;
		pos = i;
	    }
	}
	if (list[pos].singleton())
	    maxIndex.domain.in(store.level, maxIndex, pos + 1 + indexOffset, pos + 1 + indexOffset);

	if (maxIndex.singleton()) {

	    int idx = maxIndex.value() - 1 - indexOffset;
	    IntVar y = list[idx];

	    for (int i = 0; i < list.length; i++) {

		// prune variables before and after index of max value
		IntVar x = list[i];
		if (i < idx) {
		    // x < y
		    x.domain.inMax(store.level, x, y.max() - 1);
		    y.domain.inMin(store.level, y, x.min() + 1);
		}
		else {
		    // x <= y
		    x.domain.inMax(store.level, x, y.max());
		    y.domain.inMin(store.level, y, x.min());
		}
	    }
	} else {
	    // prune values on the list
	    int im = maxIndex.min();
	    for (int i = 0; i < list.length; i++) {
		int cp = i + 1 + indexOffset;

		// prune variables before and after minimal index of max value
		IntVar v = list[i];
		if (cp < im)
		    v.domain.inMax(store.level, v, ub - 1);
		else
		    v.domain.inMax(store.level, v, ub);    
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

        if (var == maxIndex)
            return IntDomain.ANY;
        else {
    	    return IntDomain.BOUND;
    	}
    }

    @Override public boolean satisfied() {

        boolean sat = maxIndex.singleton();

        int MAX = list[maxIndex.value() - 1 - indexOffset].value();
        int i = 0, eq = 0;
        while (sat && i < list.length) {
            if (list[i].singleton() && list[i].value() <= MAX)
                eq++;
            sat = list[i].max() <= MAX;
            i++;
        }

        return sat && eq == list.length;
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : ArgMax(  [ ");
        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);
            if (i < list.length - 1)
                result.append(", ");
        }

        result.append("], ").append(this.maxIndex);
        result.append(", "+indexOffset+")");

        return result.toString();
    }

}
