/*
 * Match.java
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

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * This constraint matches the elements of the given set variable
 * onto a list of integer variables. 
 *
 * @author Radoslaw Szymanek, Krzysztof Kuchcinski, and Robert Åkemalm
 * @version 4.5
 */

public class Match extends Constraint implements SatisfiedPresent {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a set variable whose values are being matched against integer variables
     * from the list.
     */
    public SetVar a;

    /**
     * It specifies the list of integer variables which value is being matched against
     * elements from a set variable a.
     */
    public IntVar[] list;

    /**
     * It constructs a match constraint to connect the value of set variable a
     * to the values of integer variables provided in the list.
     *
     * @param a set variable that is restricted to be equal to a set created from values specified by integer variables form the list.
     * @param list of integer variables that is restricted to have the same elements as set variable a.
     */

    public Match(SetVar a, IntVar[] list) {

        checkInputForNullness(new String[]{"a", "list"}, new Object[][]{ {a}, list});

        this.numberId = idNumber.incrementAndGet();
        this.a = a;
        this.list = Arrays.copyOf(list, list.length);

        setScope(Stream.concat(Stream.of(a), Arrays.stream(list)));

    }

    @Override public void consistency(Store store) {

        /**
         * It specifies the consistency rules for constraint
         * match(list, a) where list is a list of intVar and a is a setVar.
         *
         * list is lexicographically ordered elements of a.
         *
         * [a, b, c, e, f] = {a, b, c, e, f}
         *
         * #A = list.length
         *
         * each element el in A.glb must occurr in one of the intvar in list.
         * elPos is lexicographical position of el in A.glb
         *
         * element el can only occur within an interval of intvars list[elPos]..list[list.length - (#A.glb-elPos)]
         *
         * every element elU in A.lub that is not in A.glb can if added to glb will end up at position posElU
         * and for this element we can also say that it can only occur in list[posElU]..list[list.length - (1+#A.glb-posElU)]
         *
         * for all l[i], D(l[i]) must be in A.lub
         *
         * A.lub = A.lub /\ ( \/ D(i) ).
         *
         */

        a.domain.inCardinality(store.level, a, list.length, list.length);

        if (a.domain.glb().getSize() == list.length) {

            ValueEnumeration ve = a.domain.glb().valueEnumeration();
            int el;
            for (int i = 0; i < list.length; i++) {
                el = ve.nextElement();
                list[i].domain.in(store.level, list[i], el, el);
            }
            a.domain.inLUB(store.level, a, a.domain.glb());

        } else if (a.domain.lub().getSize() == list.length) {

            ValueEnumeration ve = a.domain.lub().valueEnumeration();
            int el;
            for (int i = 0; i < list.length; i++) {
                el = ve.nextElement();
                list[i].domain.in(store.level, list[i], el, el);
            }
            a.domain.inGLB(store.level, a, a.domain.lub());

        } else {

            IntDomain glbA = a.domain.glb();
            IntDomain lubA = a.domain.lub();

            int sizeOfaGLB = glbA.getSize();
            int sizeOfaLUB = lubA.getSize();

            // glbA, lubA => list[i]
            for (int i = 0; i < list.length; i++) {

                list[i].domain.in(store.level, list[i], lubA);

                int minValue = lubA.getElementAt(i);

                if (i >= list.length - sizeOfaGLB) {
                    // -1 since indexing of arrays starts from 0.
                    int minValueFromGLB = glbA.getElementAt(sizeOfaGLB - list.length + i);
                    if (minValueFromGLB > minValue)
                        minValue = minValueFromGLB;
                }

                list[i].domain.inMin(store.level, list[i], minValue);

                int maxValue = lubA.getElementAt(sizeOfaLUB - list.length + i);

                if (i < sizeOfaGLB) {
                    int maxValueFromGLB = glbA.getElementAt(i);
                    if (maxValueFromGLB < maxValue)
                        maxValue = maxValueFromGLB;
                }

                list[i].domain.inMax(store.level, list[i], maxValue);

            }

            IntDomain lubFromList = list[0].domain.cloneLight();
            for (int i = 0; i < list.length; i++) {
                if (list[i].singleton())
                    a.domain.inGLB(store.level, a, list[i].value());
                if (i > 0)
                    lubFromList.unionAdapt(list[i].domain);
            }
            a.domain.inLUB(store.level, a, lubFromList);

        }

    }

    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }

        if (var == a)
            return SetDomain.ANY;
        else
            return IntDomain.ANY;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise version exist.");
    }

    @Override public boolean satisfied() {

        if (! grounded() )
            return false;

        if (a.domain.glb().getSize() == list.length ) {

            ValueEnumeration ve = a.domain.glb().valueEnumeration();

            for (int i = 0; i < list.length; i++) {
                if (ve.nextElement() != list[i].value())
                    return false;
            }

            return true;

        } else {
            return false;
        }

    }

    @Override public String toString() {

        StringBuffer ret = new StringBuffer(id());
        ret.append(" : Match(" + a + ", [ ");
        for (Var fdv : list)
	  ret.append(fdv + " ");
        ret.append("] )");
        return ret.toString();

    }

}
