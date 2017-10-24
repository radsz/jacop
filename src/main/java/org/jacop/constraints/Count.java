/*
 * Count.java
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

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * Count constraint implements the counting over number of occurrences of
 * a given value in a list of variables. The number of occurrences is
 * specified by variable idNumber.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Count extends Constraint implements SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies variable idNumber to count the number of occurences of the specified value in a list.
     */
    final public IntVar counter;

    /**
     * The list of variables which are checked and counted if equal to specified value.
     */
    final public IntVar list[];

    /**
     * The value to which is any variable is equal to makes the constraint count it.
     */
    final public int value;

    /**
     * It constructs a Count constraint.
     *
     * @param value   value which is counted
     * @param list    variables which equality to val is counted.
     * @param counter number of variables equal to val.
     */
    public Count(IntVar[] list, IntVar counter, int value) {

        checkInputForNullness(new String[] {"list", "counter"}, new Object[][] {list, {counter}});

        this.queueIndex = 1;
        this.numberId = idNumber.incrementAndGet();

        this.list = Arrays.copyOf(list, list.length);
        this.counter = counter;
        this.value = value;

        setScope(Stream.concat(Arrays.stream(list), Stream.of(counter)));

    }

    /**
     * It constructs a Count constraint.
     *
     * @param value   value which is counted
     * @param list    variables which equality to val is counted.
     * @param counter number of variables equal to val.
     */
    public Count(List<? extends IntVar> list, IntVar counter, int value) {
        this(list.toArray(new IntVar[list.size()]), counter, value);
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public void consistency(final Store store) {

        int numberEq = 0, numberMayBe = 0;
        for (IntVar v : list) {
            if (v.domain.contains(value))
                if (v.singleton())
                    numberEq++;
                else
                    numberMayBe++;
        }

        if (numberMayBe == counter.min() - numberEq) {
            for (IntVar v : list) {
                if (!v.singleton() && v.domain.contains(value))
                    v.domain.in(store.level, v, value, value);
            }

            numberEq += numberMayBe;
            numberMayBe = 0;

            counter.domain.in(store.level, counter, numberEq, numberEq);
            removeConstraint();
            return;

        } else if (numberEq == counter.max()) {
            for (IntVar v : list)
                if (!v.singleton() && v.domain.contains(value))
                    v.domain.inComplement(store.level, v, value);


            numberMayBe = 0;

            counter.domain.in(store.level, counter, numberEq, numberEq);
            removeConstraint();
            return;
        }

        counter.domain.in(store.level, counter, numberEq, numberEq + numberMayBe);

    }

    @Override public boolean satisfied() {

        if (!grounded())
            return false;

        int countAll = 0;

        for (IntVar v : list)
            if (v.singleton(value))
                countAll++;
        return (countAll == counter.min());
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : count(").append(value).append(",[");

        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);
            if (i < list.length - 1)
                result.append(", ");
        }

        result.append("], ").append(counter).append(" )");

        return result.toString();

    }

}
