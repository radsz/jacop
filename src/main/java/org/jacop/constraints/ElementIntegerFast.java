/*
 * ElementIntegerFast.java
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

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.TimeStamp;

/**
 * ElementIntegerFast constraint defines a relation 
 * list[index - indexOffset] = value. This version uses bounds consistency.
 *
 * The first element of the list corresponds to index - indexOffset = 1.
 * By default indexOffset is equal 0 so first value within a list corresponds to index equal 1.
 *
 * If index has a domain from 0 to list.length-1 then indexOffset has to be equal -1 to 
 * make addressing of list array starting from 1.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class ElementIntegerFast extends Constraint implements Stateful, SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    boolean firstConsistencyCheck = true;

    int firstConsistencyLevel;

    /**
     * It specifies variable index within an element constraint list[index - indexOffset] = value.
     */
    final public IntVar index;

    /**
     * It specifies variable value within an element constraint list[index - indexOffset] = value.
     */
    final public IntVar value;

    /**
     * It specifies indexOffset within an element constraint list[index - indexOffset] = value.
     */
    private final int indexOffset;

    /**
     * It specifies list of variables within an element constraint list[index - indexOffset] = value.
     * The list is addressed by positive integers ({@code >=1}) if indexOffset is equal to 0. 
     */
    final public int list[];

    /*
     * Defines if the current list is order (ascending, descending), needs detection (detect)
     * or is not checked (none).
     */
    private TimeStamp<Short> order;

    private short detect = 0, ascending = 1, descending = 2; //, none = 3;

    /**
     * It constructs an element constraint. 
     *
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     * @param indexOffset shift applied to index variable. 
     */
    public ElementIntegerFast(IntVar index, int[] list, IntVar value, int indexOffset) {

        checkInputForNullness(new String[] {"index", "value"}, new Object[] { index, value });
        checkInputForNullness("list", list);

        this.indexOffset = indexOffset;
        queueIndex = 1;
        this.numberId = idNumber.incrementAndGet();
        this.index = index;
        this.value = value;
        this.list = Arrays.copyOf(list, list.length);

        setScope( index, value );
    }

    /**
     * It constructs an element constraint. 
     *
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     */
    public ElementIntegerFast(IntVar index, List<? extends Integer> list, IntVar value) {
        this(index, list, value, 0);
    }

    /**
     * It constructs an element constraint. 
     *
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     * @param indexOffset shift applied to index variable. 
     */
    public ElementIntegerFast(IntVar index, List<? extends Integer> list, IntVar value, int indexOffset) {
        this(index, list.stream().mapToInt( i -> i).toArray(), value, indexOffset);
    }

    /**
     * It constructs an element constraint. 
     *
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     */
    public ElementIntegerFast(IntVar index, int[] list, IntVar value) {
        this(index, list, value, 0);
    }

    @Override public void consistency(Store store) {

        if (firstConsistencyCheck) {

            index.domain.in(store.level, index, 1 + this.indexOffset, list.length + this.indexOffset);
            firstConsistencyLevel = store.level;
            firstConsistencyCheck = false;
        }

        do {

            store.propagationHasOccurred = false;

            short sort = order.value();

            if (sort == ascending || sort == descending) {
                int minIndex = index.min();
                int maxIndex = index.max();

                if (sort == ascending)
                    value.domain.in(store.level, value, list[minIndex - 1 - indexOffset], list[maxIndex - 1 - indexOffset]);
                else
                    value.domain.in(store.level, value, list[maxIndex - 1 - indexOffset], list[minIndex - 1 - indexOffset]);

                IntervalDomain indexDom = new IntervalDomain(5); // create with size 5 ;)
                for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
                    int position = e.nextElement() - 1 - indexOffset;
                    int val = list[position];

                    if (disjoint(value, val))
                        if (indexDom.size == 0)
                            indexDom.unionAdapt(position + 1 + indexOffset);
                        else
                            // indexes are in ascending order and can be added at the end if the last element
                            // plus 1 is not equal a new value. In such case the max must be changed.
                            indexDom.addLastElement(position + 1 + indexOffset);
                    else if (val == list[maxIndex - 1 - indexOffset])
                        break;
                }

                index.domain.in(store.level, index, indexDom.complement());

            } else if (sort == detect) {

                int min = IntDomain.MaxInt;
                int max = IntDomain.MinInt;
                IntervalDomain indexDom = new IntervalDomain(5); // create with size 5 ;)
                boolean asc = true, desc = true;
                int previous = list[index.min() - 1 - indexOffset];

                for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
                    int position = e.nextElement() - 1 - indexOffset;
                    int val = list[position];

                    if (disjoint(value, val))
                        if (indexDom.size == 0)
                            indexDom.unionAdapt(position + 1 + indexOffset);
                        else
                            // indexes are in ascending order and can be added at the end if the last element
                            // plus 1 is not equal a new value. In such case the max must be changed.
                            indexDom.addLastElement(position + 1 + indexOffset);
                    else {
                        min = Math.min(min, val);
                        max = Math.max(max, val);
                    }

                    if (val > previous)
                        desc = false;
                    if (val < previous)
                        asc = false;

                    previous = val;
                }
                if (desc)
                    order.update(descending);
                if (asc)
                    order.update(ascending);

                index.domain.in(store.level, index, indexDom.complement());
                value.domain.in(store.level, value, min, max);

                if (index.singleton()) {
                    int position = index.value() - 1 - indexOffset;
                    value.domain.in(store.level, value, list[position], list[position]);
                    removeConstraint();
                }
            } else {// sort == none

                int min = IntDomain.MaxInt;
                int max = IntDomain.MinInt;
                IntervalDomain indexDom = new IntervalDomain(5); // create with size 5 ;)
                for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
                    int position = e.nextElement() - 1 - indexOffset;
                    int val = list[position];

                    if (disjoint(value, val))
                        if (indexDom.size == 0)
                            indexDom.unionAdapt(position + 1 + indexOffset);
                        else
                            // indexes are in ascending order and can be added at the end if the last element
                            // plus 1 is not equal a new value. In such case the max must be changed.
                            indexDom.addLastElement(position + 1 + indexOffset);
                    else {
                        min = Math.min(min, val);
                        max = Math.max(max, val);
                    }
                }
                
                index.domain.in(store.level, index, indexDom.complement());
                value.domain.in(store.level, value, min, max);

                if (index.singleton()) {
                    int position = index.value() - 1 - indexOffset;
                    value.domain.in(store.level, value, list[position], list[position]);
                    removeConstraint();
                }
            }
        } while (store.propagationHasOccurred);
    }

    private boolean disjoint(IntVar v1, int v2) {
        if (v1.min() > v2 || v2 > v1.max())
            return true;
        else
            return !v1.domain.contains(v2);
    }

    @Override public void removeLevel(int level) {
        if (level == firstConsistencyLevel)
            firstConsistencyCheck = true;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public boolean isStateful() {
        return  (!(index.min() >= 1 + indexOffset && index.max() <= list.length + indexOffset));
    }

    @Override public void impose(Store store) {

        super.impose(store);

        if (!isStateful()) {
            firstConsistencyCheck = false;
        }

        order = new TimeStamp<>(store, detect); // set to detect

    }

    @Override public boolean satisfied() {
        boolean sat = value.singleton();
        if (sat) {
            int v = value.min();
            ValueEnumeration e = index.domain.valueEnumeration();
            while (sat && e.hasMoreElements()) {
                int fdv = list[e.nextElement() - 1 - indexOffset];
                sat = (fdv == v);
            }
        }
        return sat;
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : elementIntegerFast").append("( ").append(index).append(", [");

        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);

            if (i < list.length - 1)
                result.append(", ");
        }

        result.append("], ").append(value).append(" )");

        return result.toString();

    }

}
