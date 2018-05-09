/*
 * ElementSet.java
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

package org.jacop.set.constraints;

import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.*;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

import java.lang.reflect.Array;
import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * It is an element constraint that make sure that set variable value has a domain equal to 
 * the index-th element of the supplied list of sets.
 *
 * By default, indexing starts from 1, if it is required to be different for example starting from 0, 
 * then indexOffset must be specified to be equal to -1. 
 *
 * @author Radoslaw Szymanek, Krzysztof Kuchcinski and Robert Åkemalm
 * @version 4.5
 */

public class ElementSet extends Constraint implements SatisfiedPresent {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies what element from the list of sets is equal to set variable value.
     */
    public IntVar index;

    /**
     * It specifies a list of sets from which one element will be made equal to set variable
     * value.
     */
    public IntDomain[] list;

    /**
     * It specifies the set variable which is equal to one of the sets from the list as
     * indicated by int variable index.
     */
    public SetVar value;

    /**
     * It allows to offset the indexing. By default the indexing starts from 1, if index
     * variable starts from 0, and 0 denotes the first element then indexOffset should be
     * set to -1.
     */
    public int indexOffset = 0;

    /**
     * It constructs a constraint to restrict the domains of the variables index and value.
     *
     * @param value variable that is restricted to have the same elements as list[index].
     * @param list array of sets that contains possible values for variable value.
     * @param index variable that is restricted to be the index of sets for which list[index] == value.
     * @param indexOffset the shift applied to the index variable.
     */
    public ElementSet(IntVar index, IntDomain[] list, SetVar value, int indexOffset) {

        checkInputForNullness(new String[]{"index", "list", "value"}, new Object[][]{ {index}, list, {value}});

        numberId = idNumber.incrementAndGet();

        this.index = index;
        this.value = value;
        this.indexOffset = indexOffset;
        this.list = Arrays.copyOf(list, list.length);

        setScope(index, value);
    }

    /**
     * It constructs an elementSet constraint to restrict the domains of the variables index and value.
     *
     * @param value variable that is restricted to have the same elements as list[index].
     * @param list array of sets that contains possible values for variable value.
     * @param index variable that is restricted to be the index of sets for which list[index] == value.
     */
    public ElementSet(IntVar index, IntDomain[] list, SetVar value) {
        this(index, list, value, 0);
    }

    @Override public void consistency(Store store) {

        /**
         * It specifies the consistency rules of the
         * constraint
         *
         * L[I] = V, where I is intVar and L is a list of sets, and V is a setVar.
         *
         * glbV - elements which must be in V.
         *
         * glbV = glbV \/ ( for all i in I /\ L[i] )
         * lubV = lubV /\ ( for all i in I \/ L[i] )
         *
         * domI = all i in dom(I) such that L[i] in V and glbV in L[i]
         *
         */

        SetDomain valueDom = value.domain;
        IntDomain indexDom = index.domain;
        IntDomain newIndex = new IntervalDomain();

        IntDomain newValueGLB = valueDom.lub().cloneLight();
        IntDomain newValueLUB = new IntervalDomain();

        ValueEnumeration enumer = indexDom.valueEnumeration();
        int el = 0;

        while (enumer.hasMoreElements()) {
            el = enumer.nextElement() - 1 - indexOffset;
            if (el >= 0) {
                if (el >= list.length)
                    break;
                // TODO, implement some support functionality
                // e.g. values in valueLUB can be supported by element from the list
                // if index has some value being removed from it then new supports
                // for values from valueLUB may need to be found.
                // This is a cheaper way of restricting valueLUB.
                // Similarly for each value not present in valueGLB we keep support
                // that removes the need of having this value. As soon as no element
                // in the list supports removing it from glb then we put it in glb.
                newValueGLB = newValueGLB.intersect(list[el]);
                newValueLUB.addDom(list[el]);
                if (valueDom.lub().contains(list[el]) && list[el].contains(valueDom.glb()))
                    newIndex.unionAdapt(el + 1 + indexOffset, el + 1 + indexOffset);
            }
        }

        value.domain.in(store.level, value, newValueGLB, newValueLUB);
        index.domain.in(store.level, index, newIndex);
    }

    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        if (var == value)
            return SetDomain.ANY;
        else
            return IntDomain.ANY;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise variants exist.");
    }

    @Override public boolean satisfied() {
        return grounded() && list[index.domain.min() - 1 - indexOffset].eq(value.domain.glb());
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder();

        result.append(id()).append(" : ElementSet( ").append(index).append(", [ ");

        for (IntDomain s : list)
            result.append(s).append(" ");

        result.append(" ], ").append(value).append(" )");

        return result.toString();
    }

}
