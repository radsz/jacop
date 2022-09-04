/*
 * AtLeast.java
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
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

/*
 * AtLeast constraint implements the counting over number of occurrences of
 * a given value in a list of variables. The number of occurrences is
 * specified by variable value.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */

public class AtLeast extends PrimitiveConstraint {

    static final AtomicInteger idNumber = new AtomicInteger(0);

    /*
     * It specifies variable idNumber to count the number of occurences of the specified value in a list.
     */
    public final int counter;

    /*
     * The list of variables which are checked and counted if equal to specified value.
     */
    public final IntVar[] list;

    /*
     * The value to which is any variable is equal to makes the constraint count it.
     */
    public final int value;

    boolean reified = true;

    /*
     * Defines first position of the variable that are not considered;
     * either equal to value or missing the value in their domain.
     */
    private TimeStamp<Integer> position;

    /*
     * Defines number of variables equal to the value.
     */
    private TimeStamp<Integer> equal;

    /**
     * It constructs a AtLeast constraint.
     *
     * @param value   value which is counted
     * @param list    variables which equality to val is counted.
     * @param counter number of variables equal to val.
     */
    public AtLeast(IntVar[] list, int counter, int value) {

        checkInputForNullness("list", list);

        this.queueIndex = 1;
        this.numberId = idNumber.incrementAndGet();

        this.list = Arrays.copyOf(list, list.length);
        this.counter = counter;
        this.value = value;

        setScope(list);

    }

    /**
     * It constructs a AtLeast constraint.
     *
     * @param value   value which is counted
     * @param list    variables which equality to val is counted.
     * @param counter number of variables equal to val.
     */
    public AtLeast(List<? extends IntVar> list, int counter, int value) {
        this(list.toArray(new IntVar[list.size()]), counter, value);
    }

    @Override public void include(Store store) {
        position = new TimeStamp<>(store, 0);
        equal = new TimeStamp<>(store, 0);
    }

    @Override public void impose(Store store) {

        reified = false;

        super.impose(store);

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override public void consistency(final Store store) {

        int numberEq = equal.value();
        int numberMayBe = 0;
        int start = position.value();
        for (int i = start; i < list.length; i++) {
            IntVar v = list[i];
            if (v.domain.contains(value))
                if (v.singleton()) {
                    numberEq++;
                    swap(start, i);
                    start++;
                } else
                    numberMayBe++;
            else { // does not have the value in its domain
                swap(start, i);
                start++;
            }
        }

        if (numberMayBe + numberEq < counter)
            throw Store.failException;
        else if (numberEq >= counter) {
            if (!reified) removeConstraint();
        } else if (numberMayBe + numberEq == counter) {
            for (int i = start; i < list.length; i++) {
                IntVar v = list[i];
                if (!v.singleton() && v.domain.contains(value))
                    v.domain.inValue(store.level, v, value);
            }
            if (!reified)
                removeConstraint();
        }

        equal.update(numberEq);
        position.update(start);
    }

    @Override public void notConsistency(final Store store) {
        // at most counter - 1 values
        int numberEq = equal.value();
        int numberMayBe = 0;
        int start = position.value();
        for (int i = start; i < list.length; i++) {
            IntVar v = list[i];
            if (v.domain.contains(value))
                if (v.singleton()) {
                    numberEq++;
                    swap(start, i);
                    start++;
                } else
                    numberMayBe++;
            else { // does not have the value in its domain
                swap(start, i);
                start++;
            }
        }

        if (numberEq > counter - 1)
            throw Store.failException;
        else if (numberEq + numberMayBe <= counter - 1) {
            if (!reified)
                removeConstraint();
        } else if (numberEq == counter - 1) {
            for (int i = start; i < list.length; i++) {
                IntVar v = list[i];
                v.domain.inComplement(store.level, v, value, value);
            }
            if (!reified)
                removeConstraint();
        }

        equal.update(numberEq);
        position.update(start);
    }
    
    private void swap(int i, int j) {
        if (i != j) {
            IntVar tmp = list[i];
            list[i] = list[j];
            list[j] = tmp;
        }
    }

    @Override public boolean satisfied() {

        int numberEq = 0;
        for (IntVar v : list) 
            if (v.singleton(value))
                numberEq++;

        return numberEq >= counter;
    }

    @Override public boolean notSatisfied() {
        int numberEq = 0;
        int numberMayBe = 0;
        for (IntVar v : list) {
            if (v.domain.contains(value))
                if (v.singleton())
                    numberEq++;
                else
                    numberMayBe++;
        }

        return numberEq + numberMayBe <= counter - 1;
    }
    
    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : AtLeast(").append(value).append(",[");

        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);
            if (i < list.length - 1)
                result.append(", ");
        }

        result.append("], ").append(counter).append(" )");

        return result.toString();

    }

}
