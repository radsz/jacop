/*
 * ElementVariable.java
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
import java.util.stream.Stream;

import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.*;

/**
 * ElementVariable constraint defines a relation 
 * list[index - indexOffset] = value.
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

public class ElementVariable extends Constraint implements UsesQueueVariable, Stateful, SatisfiedPresent {

    static AtomicInteger idNumber = new AtomicInteger(0);

    boolean firstConsistencyCheck = true;
    int firstConsistencyLevel;

    /**
     * It specifies variable index within an element constraint list[index - indexOffset] = value.
     */
    public IntVar index;

    /**
     * It specifies variable value within an element constraint list[index - indexOffset] = value.
     */
    public IntVar value;

    /**
     * It specifies indexOffset within an element constraint list[index - indexOffset] = value.
     */
    public final int indexOffset;

    /**
     * It specifies list of variables within an element constraint list[index - indexOffset] = value.
     * The list is addressed by positive integers ({@code >=1}) if indexOffset is equal to 0.
     */
    public IntVar list[];

    boolean indexHasChanged = false;

    IntDomain indexRange;

    LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<IntVar>();

    Map<IntVar, Integer> mapping = Var.createEmptyPositioning();

    Map<IntVar, List<Integer>> duplicates = Var.createEmptyPositioning();

    /**
     * It constructs an element constraint.
     *
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     * @param indexOffset shift applied to index variable.
     */
    public ElementVariable(IntVar index, IntVar[] list, IntVar value, int indexOffset) {

        checkInputForNullness(new String[] {"index", "value"}, new Object[] { index, value });
        checkInputForNullness("list", list);

        queueIndex = 2;

        this.indexOffset = indexOffset;
        this.numberId = idNumber.incrementAndGet();
        this.index = index;
        this.value = value;
        this.list = Arrays.copyOf(list, list.length);
        this.indexRange = new IntervalDomain(1 + this.indexOffset, list.length + this.indexOffset);

        setScope( Stream.concat( Stream.of(index), Stream.concat( Arrays.stream(list), Stream.of(value)) ) );

    }

    /**
     * It constructs an element constraint.
     *
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     */
    public ElementVariable(IntVar index, List<? extends IntVar> list, IntVar value) {
        this(index, list.toArray(new IntVar[list.size()]), value, 0);
    }

    /**
     * It constructs an element constraint.
     *
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     * @param indexOffset shift applied to index variable.
     */
    public ElementVariable(IntVar index, List<? extends IntVar> list, IntVar value, int indexOffset) {
        this(index, list.toArray(new IntVar[list.size()]), value, indexOffset);
    }

    /**
     * It constructs an element constraint.
     *
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     */
    public ElementVariable(IntVar index, IntVar[] list, IntVar value) {
        this(index, list, value, 0);
    }

    @Override public void removeLevel(int level) {
        if (level == firstConsistencyLevel)
            firstConsistencyCheck = true;
        indexHasChanged = false;
        valueHasChanged = false;
        variableQueue.clear();
    }

    // For each variable from the list it specifies the values it supports
    IntDomain[] supports;

    private boolean valueHasChanged;

    Random generator = new Random(2);

    @Override public void consistency(Store store) {

        if (index.singleton()) {
            // index is singleton.

            int position = index.value() - 1 - indexOffset;
            value.domain.in(store.level, value, list[position].domain);
            list[position].domain.in(store.level, list[position], value.domain);

        } else {
            // index is not singleton.


            if (firstConsistencyCheck) {

                index.domain.in(store.level, index, indexRange);

                IntDomain valDomain = new IntervalDomain();
                for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
                    int position = e.nextElement() - 1 - indexOffset;
                    valDomain.addDom(list[position].domain);
                }
                value.domain.in(store.level, value, valDomain);

                firstConsistencyCheck = false;
                firstConsistencyLevel = store.level;
                valueHasChanged = true;
                indexHasChanged = true;
                for (IntVar var : list)
                    variableQueue.add(var);

                supports = new IntDomain[list.length];
                IntDomain temp = value.domain.cloneLight();
                for (int i = list.length - 1; i >= 0; i--) {
                    if (!temp.isEmpty()) {
                        supports[i] = temp.intersect(list[i].domain);
                        if (!supports[i].isEmpty())
                            temp = temp.subtract(supports[i]);
                    } else
                        supports[i] = new IntervalDomain();
                }
            }

            // IntDomain valDomain = new IntervalDomain();
            int valMin = IntDomain.MaxInt, valMax = IntDomain.MinInt;
            for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
                int position = e.nextElement() - 1 - indexOffset;
                // valDomain.addDom(list[position].domain);
                int min = list[position].domain.min();
                int max = list[position].domain.max();
                valMin = (valMin > min) ? min : valMin;
                valMax = (valMax < max) ? max : valMax;
            }
            value.domain.in(store.level, value, valMin, valMax);
            // value.domain.in(store.level, value, valDomain);

            // Consequtive execution of the consistency function.

            if (valueHasChanged) {

                for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {

                    int position = e.nextElement() - 1 - indexOffset;

                    if (!list[position].domain.isIntersecting(value.domain)) {

                        index.domain.inComplement(store.level, index, position + 1 + indexOffset);

                        list[position].removeConstraint(this);

                    }
                }
            }

            if (indexHasChanged) {

                IntDomain nextValueDomain = new IntervalDomain();
                int checkTrigger = value.getSize() - 1;
                boolean propagation = true;
                for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
                    nextValueDomain.unionAdapt(list[e.nextElement() - 1 - indexOffset].dom());
                    if (nextValueDomain.getSize() > checkTrigger) {
                        if (nextValueDomain.contains(value.domain)) {
                            propagation = false;
                            break;
                        } else
                            checkTrigger = nextValueDomain.getSize();
                    }
                }

                if (propagation)
                    value.domain.in(store.level, value, nextValueDomain);

            }

            if (!variableQueue.isEmpty()) {

                Iterator<IntVar> itr = variableQueue.iterator();

                // TODO, what if one variable occurs multiple times in list? Only one
                // occurence in the list can be active, the other ones have to be ignored.

                while (itr.hasNext()) {

                    IntVar changedVar = itr.next();
                    int position = mapping.get(changedVar);

                    // reason about possible changes to value variable.
                    if (!supports[position].isEmpty()) {
                        // changed variable supports some values in Value variable.
                        IntDomain lostSupports = supports[position].subtract(changedVar.domain);
                        lostSupports.intersectAdapt(value.domain);
                        if (!lostSupports.isEmpty()) {
                            for (ValueEnumeration enumer = lostSupports.valueEnumeration(); enumer.hasMoreElements(); ) {
                                int lostSupport = enumer.nextElement();
                                int endingPosition = generator.nextInt(list.length - 1);
                                int nextSupportPosition = -1;
                                for (int i = endingPosition + 1; ; ) {
                                    if (i == list.length)
                                        i = 0;
                                    if (list[i].domain.contains(lostSupport)) {
                                        nextSupportPosition = i;
                                        break;
                                    }
                                    if (i == endingPosition)
                                        break;
                                    i++;
                                }
                                if (nextSupportPosition != -1) {
                                    supports[nextSupportPosition].unionAdapt(lostSupport);
                                    supports[position].subtractAdapt(lostSupport);
                                } else {
                                    value.domain.inComplement(store.level, value, lostSupport);
                                }

                            }
                        }
                    }

                    // reason about possible changes to index variable.
                    if (!changedVar.domain.isIntersecting(value.domain)) {

                        index.domain.inComplement(store.level, index, position + 1 + indexOffset);
                        list[position].removeConstraint(this);

                        List<Integer> array = duplicates.get(changedVar);
                        if (array != null)
                            for (int additionalPosition : array)
                                index.domain.inComplement(store.level, index, additionalPosition + 1 + indexOffset);

                    }
                }

            }

            if (indexHasChanged && index.singleton()) {
                    // index is singleton.

                    int position = index.value() - 1 - indexOffset;
                    value.domain.in(store.level, value, list[position].domain);
                    list[position].domain.in(store.level, list[position], value.domain);
                }

            indexHasChanged = false;
            valueHasChanged = false;
            variableQueue.clear();

        }
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public void impose(Store store) {

        super.impose(store);

        for (int i = 0; i < list.length; i++) {
            Integer oldInteger = mapping.put(list[i], i);
            if (oldInteger != null) {
                List<Integer> array = duplicates.get(list[i]);
                if (array != null)
                    array.add(i);
                else {
                    array = new ArrayList<Integer>();
                    array.add(i);
                    duplicates.put(list[i], array);
                }
            }
        }

    }

    @Override public void queueVariable(int level, Var var) {

        if (var == index) {
            indexHasChanged = true;
            return;
        }

        if (var == value) {
            valueHasChanged = true;
            return;
        }

        variableQueue.add((IntVar) var);

    }

    @Override public boolean satisfied() {
        boolean sat = value.singleton();
        if (sat) {
            int v = value.min();
            ValueEnumeration e = index.domain.valueEnumeration();
            while (sat && e.hasMoreElements()) {
                IntVar fdv = list[e.nextElement() - 1 - indexOffset];
                sat = fdv.singleton() && fdv.min() == v;
            }
        }
        return sat;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());

        result.append(" : elementVariable").append("( ").append(index).append(", [");

        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);

            if (i < list.length - 1)
                result.append(", ");
        }

        result.append("], ").append(value).append(" )");

        return result.toString();

    }

}
