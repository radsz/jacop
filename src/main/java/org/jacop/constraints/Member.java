/*
 * Member.java
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * Member constraint implements the membership of element e on list x.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.9
 */

public class Member extends PrimitiveConstraint {

    Store store;

    static AtomicInteger idNumber = new AtomicInteger(0);

    boolean reified = true;

    /**
     * It specifies a list of variables being summed.
     */
    IntVar[] x;

    /**
     * It specifies variable for the overall sum.
     */
    IntVar e;

    /**
     * It specifies the number of variables on the list.
     */
    int l;


    /*
     * Defines first position of the variable that might equal e
     */
    private TimeStamp<Integer> position;

    /**
     * @param list  list of variables.
     * @param e     variable to be checkd on the list.
     */
    public Member(IntVar[] list, IntVar e) {

        checkInputForNullness(new String[] {"list", "e"}, new Object[][] {list, {e}});

        this.e = e;

        x = Arrays.copyOf(list, list.length);
        numberId = idNumber.incrementAndGet();

        this.l = x.length;

	queueIndex = 1;

        setScope(Stream.concat(Arrays.stream(x), Stream.of(this.e)));

    }

    /**
     * It constructs the constraint Member.
     *
     * @param list  list of variables.
     * @param e     variable to be checkd on the list.
     */
    public Member(List<? extends IntVar> list, IntVar e) {
        this(list.toArray(new IntVar[list.size()]), e);
    }

    @Override public void consistency(Store store) {

	int start = position.value();

	IntDomain d = new IntervalDomain();
	boolean eGround = e.singleton();
	for (int i = start; i < l; i++) {

	    if (eGround && x[i].singleton() && x[i].value() == e.value()) {
		removeConstraint();
		return;
	    }
	    
	    if (!x[i].domain.isIntersecting(e.domain)) {
		swap(start, i);
		start++;
	    } else
		d.unionAdapt(x[i].domain);
	}

	if (start == l)
	    throw store.failException;

	e.domain.in(store.level, e, d);

	if (start == l-1) {
	    x[l-1].domain.in(store.level, x[l-1], e.domain);
	    e.domain.in(store.level, e, x[l-1].domain);
	}

	position.update(start);
    }

    @Override public void notConsistency(Store store) {

	int start = position.value();

	do {

            store.propagationHasOccurred = false;

	    boolean eGround = e.singleton();
	    for (int i = start; i < l; i++) {
		if (eGround)
		    x[i].domain.inComplement(store.level, x[i], e.value());

		if (x[i].singleton())
		    e.domain.inComplement(store.level, e, x[i].value());

		if (!x[i].domain.isIntersecting(e.domain)) {
		    swap(start, i);
		    start++;
		}
	    }

	    if (start == l)
		removeConstraint();

	    if (start == l - 1)
		if (e.singleton()) {
		    x[l-1].domain.inComplement(store.level, x[l-1], e.value());
		}
		else if (x[l-1].singleton()) {
		    e.domain.inComplement(store.level, e, x[l-1].value());
		}

	} while (store.propagationHasOccurred);

	position.update(start);
    }

    private void swap(int i, int j) {
        if (i != j) {
            IntVar tmp = x[i];
            x[i] = x[j];
            x[j] = tmp;
        }
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public void include(Store store) {
        position = new TimeStamp<Integer>(store, 0);
    }

    @Override public void impose(Store store) {

        if (x == null)
            return;

        reified = false;

        super.impose(store);

    }

    @Override public boolean satisfied() {

	if (e.singleton())
	    for (int i = 0; i < l; i++) {
		if (x[i].singleton() && x[i].value() == e.value())
		    return true;
	    }
        return false;
    }

    @Override public boolean notSatisfied() {
	for (int i = 0; i < l; i++) {
	    if (x[i].domain.isIntersecting(e.domain))
		return false;
	}
        return true;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : Member([");

        for (int i = 0; i < l; i++) {
            result.append(x[i]);
            if (i < l - 1)
                result.append(", ");
        }
        result.append("], ");

        result.append(e).append(" )");

        return result.toString();

    }
}
