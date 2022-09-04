/*
 * CountValues.java
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
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/*
 * CountValues constraint implements the counting over numbers of occurrences of a given
 * vector of values in a list of variables. The number of occurrences is specified by
 * variable counter.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */

public class CountValues extends Constraint implements SatisfiedPresent {

    static final AtomicInteger idNumber = new AtomicInteger(0);

    /*
     * It specifies variable idNumber to count the number of occurences of the specified value in a list.
     */
    public final IntVar[] counter;

    public final IntVar counterRest;
    public final IntVar[] extendedCounter;

    /*
     * The list of variables which are checked and counted if equal to specified value.
     */
    public final IntVar[] list;
    private final int n; // length of the list

    /*
     * The value to which is any variable is equal to makes the constraint count it.
     */
    public final int[] values;
    final IntDomain valuesDomain;
    final IntDomain valuesDomainComplement;

    /*
     * Defines first position of the variable that are not considered;
     * either equal to value or missing the value in their domain.
     */
    private TimeStamp<Integer> position;

    /*
     * Defines number of variables equal to the value.
     */
    private TimeStamp<Integer>[] equal;
    private TimeStamp<Integer> rest;

    /**
     * It constructs a CountValues constraint.
     *
     * @param values   values that are counted
     * @param list    variables which equality to values is counted.
     * @param counter number of variables equal to a value.
     */
    public CountValues(IntVar[] list, IntVar[] counter, int[] values) {

        checkInputForNullness(new String[] {"list", "counter"}, new Object[][] {list, {counter}});

        this.queueIndex = 1;
        this.numberId = idNumber.incrementAndGet();

        this.n = list.length;
        this.list = Arrays.copyOf(list, n);
        this.counter = counter;
        this.values = values;
        this.counterRest = new IntVar(counter[0].getStore(), 0, n);

        this.valuesDomain = new IntervalDomain();
        for (int v : values)
            valuesDomain.unionAdapt(v);
        this.valuesDomainComplement = valuesDomain.complement();

        extendedCounter = new IntVar[counter.length + 1];
        for (int i = 0; i < counter.length; i++) {
            extendedCounter[i] = counter[i];
        }
        extendedCounter[counter.length] = counterRest;

        setScope(Stream.concat(Arrays.stream(list), Arrays.stream(counter)));

    }

    /**
     * It constructs a CountValues constraint.
     *
     * @param values   value taht are counted
     * @param list    variables which equality to values is counted.
     * @param counter number of variables equal to values.
     */
    public CountValues(List<? extends IntVar> list, IntVar[] counter, int[] values) {
        this(list.toArray(new IntVar[list.size()]), counter, values);
    }

    // registers the constraint in the constraint store and
    // initialize stateful variables
    @SuppressWarnings("unchecked")
    @Override public void impose(Store store) {

        super.impose(store);

        position = new TimeStamp<>(store, 0);
        equal = new TimeStamp[values.length];
        for (int i = 0; i < values.length; i++) {
            equal[i] = new TimeStamp<>(store, 0);
        }
        rest = new TimeStamp<>(store, 0);
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public void consistency(final Store store) {

        int start = position.value();
        int[] numberMayBe = new int[values.length];
        int[] numberEq = new int[values.length];
        int restEq;
        int restMayBe;

        restEq = rest.value();
        for (int i = 0; i < values.length; i++)
            numberEq[i] = equal[i].value();

        do {

            restMayBe = 0;
            for (int i = 0; i < values.length; i++)
                numberMayBe[i] = 0;

            for (int i = start; i < n; i++) {
                IntVar v = list[i];
                int noValuesInDomain = 0;

                for (int j = 0; j < values.length; j++) {
                    if (v.domain.contains(values[j]))
                        if (v.singleton()) {
                            numberEq[j]++;
                            swap(start, i);
                            start++;
                        } else {
                            numberMayBe[j]++;
                        }
                    else { // does not have the values in its domain
                        noValuesInDomain++;
                    }
                }

                if (! v.domain.subtract(valuesDomain).isEmpty())
                    restMayBe++;

                if (noValuesInDomain == values.length) {
                    swap(start, i);
                    start++;
                    restEq++;
                }
            }

            store.propagationHasOccurred = false;

            counterRest.domain.in(store.level, counterRest, restEq, restEq + restMayBe);

            for (int i = 0; i < values.length; i++)         
                counter[i].domain.in(store.level, counter[i], numberEq[i], numberEq[i] + numberMayBe[i]);

            int min = 0;
            int max = 0;
            for (int i = 0; i < extendedCounter.length; i++) {
                min += extendedCounter[i].min();
                max += extendedCounter[i].max();
            }
            for (int i = 0; i < extendedCounter.length; i++) { // sum(extendedCounter) == n (list length)
                extendedCounter[i].domain.in(store.level, extendedCounter[i],
                                             n - max + extendedCounter[i].max(), n - min + extendedCounter[i].min());
            }

            for (int i = 0; i < values.length; i++) {

                if (numberMayBe[i] == counter[i].min() - numberEq[i]) {

                    for (int j = start; j < n; j++) {
                        IntVar v = list[j];
                        if (v.domain.contains(values[i]))
                            v.domain.in(store.level, v, values[i], values[i]);

                    }
                } else if (numberEq[i] == counter[i].max()) {

                    for (int j = start; j < n; j++) {
                        IntVar v = list[j];
                        v.domain.inComplement(store.level, v, values[i]);
                    }
                }
            }

            if (restMayBe == counterRest.min() - restEq) {

                for (int j = start; j < n; j++) {
                    IntVar v = list[j];
                    if (! v.domain.subtract(valuesDomain).isEmpty()) {
                        v.domain.in(store.level, v, valuesDomainComplement);
                    }
                }
            } else if (restEq == counterRest.max()) {

                for (int j = start; j < n; j++) {
                    IntVar v = list[j];
                    v.domain.in(store.level, v, valuesDomain);
                }
            }

        } while (store.propagationHasOccurred);

        for (int i = 0; i < values.length; i++) {
            equal[i].update(numberEq[i]);           
        }
        rest.update(restEq);        

        position.update(start);

    }

    private void swap(int i, int j) {
        if (i != j) {
            IntVar tmp = list[i];
            list[i] = list[j];
            list[j] = tmp;
        }
    }

    public boolean satisfied() {

        for (int i = 0; i < counter.length; i++) {
            int v = values[i];
            int c;
            if (counter[i].singleton())
                c = counter[i].value();
            else
                return false;

            int cc = 0;
            for (int j = 0; j < n; j++) {
                if (list[j].singleton(v))
                    cc++;
            }
            if (cc != counter[i].value())
                return false;
        }

        return true;
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : CountValues(").append(java.util.Arrays.asList(list)).append(", ")
            .append(java.util.Arrays.asList(counter)).append(", ").append(java.util.Arrays.toString(values));

        return result.toString();

    }

}
