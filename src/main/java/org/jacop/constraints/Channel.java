/*
 * Channel.java
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

import org.jacop.core.*;
import org.jacop.api.SatisfiedPresent;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * Channel constraints "constraint" {@literal <=>} B
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.7
 */

public class Channel extends Constraint implements SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * Variables that is checked for a value.
     */
    final public IntVar x;
    
    /**
     * It specifies variables b that store  which value is assigne to variable x.
     */
    final public IntVar[] bs;

    /**
     * length of vector bs
     */
    final int n;
    
    /**
     * It specifies indexOffset within bs vector.
     */
    final int[] value;

    boolean firstConsistencyCheck = true;
    
    /**
     * It creates Channel constraint.
     *
     * @param x variable to be checked.
     * @param bs array representing the status of equality x = i.
     * @param value array of values that are checked against x.
     */
    public Channel(IntVar x, IntVar[] bs, int[] value) {

	if (value.length > bs.length)
	    throw new IllegalArgumentException("Channel: Status array size ("+bs.length+"), lower than number of values "+value.length);
	
        checkInputForNullness(new String[] {"x", "bs"}, new Object[][] {{x}, bs});
	for (IntVar b : bs)
	    if (b.min() > 1 || b.max() < 0)
		throw new IllegalArgumentException("Channel: Variable b in reified constraint must have domain at most 0..1");

        numberId = idNumber.incrementAndGet();
        this.x = x;
        this.bs = bs;
	this.n = bs.length;

	this.value = value;

        setScope(Stream.concat(Stream.of(x), Arrays.stream(bs)));
        this.queueIndex = 0;
    }

    /**
     * It creates Channel constraint.
     *
     * @param x variable to be checked.
     * @param bs array representing the status of equality x = i.
     * @param value set of values that are checked against x.
     */
    public Channel(IntVar x, IntVar[] bs, IntDomain value) {
	this(x, bs, toArray(value));
    }

    public Channel(IntVar x, IntVar[] bs) {

	this(x, bs, toArray(x.domain));
    }

    static int[] toArray(IntDomain d) {

    	int[] vs = new int[d.getSize()];
    	int i = 0;
    	for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
    	    int v = e.nextElement();
    	    vs[i++] = v;
    	}
	return vs;
    }
    
    @Override public void consistency(final Store store) {

        if (firstConsistencyCheck) {
	    for (int i = 0; i < value.length; i++) {
		if (! x.domain.contains(value[i]))
		    bs[i].domain.in(store.level, bs[i], 0, 0);

		if (bs[i].max() == 0)
		    x.domain.inComplement(store.level, x, value[i]);
	    }

	    if (bs.length > value.length) {
	    	for (int i = value.length; i < n; i++) 
	    	    bs[i].domain.in(store.level, bs[i], 0, 0);
	    }
            firstConsistencyCheck = false;
        }
	
	for (int i = 0; i < value.length; i++) {
	    if (bs[i].max() == 0)
		x.domain.inComplement(store.level, x, value[i]);
	    else if (bs[i].min() == 1)
		x.domain.in(store.level, x, value[i], value[i]);
	}

	for (int i = 0; i < n; i++) {
	    if (i < value.length) {
		if (bs[i].max() != 0 && ! x.domain.contains(value[i]))
		    bs[i].domain.in(store.level, bs[i], 0, 0);
	    } else
		bs[i].domain.in(store.level, bs[i], 0, 0);
	}

	if (x.singleton()) {
	    int idx = indexOf(x.value());

	    bs[idx].domain.in(store.level, bs[idx], 1, 1);

	    for (int i = 0; i < n; i++) {
		if (i != idx)
		    bs[i].domain.in(store.level, bs[i], 0, 0);
	    }
	}
    }

    int indexOf(int v) {
	for (int i = 0; i < value.length; i++) {
	    if (v == value[i])
		return i;
	}
	throw Store.failException;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    public boolean satisfied() {

	int one = Integer.MIN_VALUE;
	if (x.singleton()) {
	    for (int i = 0; i < n; i++) {
		if (bs[i].singleton()) {
		    if (bs[i].value() == 1)
			if (one == -1)
			    one = i;
			else
			    return false;
		    else
			return false;
		} else
		    return false;
	    }
	}
	else
	    return false;

	return (one == Integer.MIN_VALUE) ? false : x.value() == value[one];
    }
	    

    @Override public String toString() {

        return id() + " : Channel(" + x + ", " + Arrays.asList(bs) + ", " + Arrays.toString(value) + " )";
    }

}
