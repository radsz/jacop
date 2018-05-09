/*
 * Values.java
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
import org.jacop.util.BipartiteGraphMatching;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Constraint Values counts number of different values on a list of Variables.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Values extends Constraint implements SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a list of variables which are counted.
     */
    final private IntVar[] list;

    /**
     * It specifies the idNumber of different values among variables on a given list.
     */
    final private IntVar count;
    
    Comparator<IntVar> minFDV = (o1, o2) -> (o1.min() - o2.min());

    final static private boolean debug = false;

    /**
     * It constructs Values constraint.
     *
     * @param list  list of variables for which different values are being counted.
     * @param count specifies the number of different values in the list.
     */
    public Values(IntVar[] list, IntVar count) {

        checkInputForNullness(new String[] {"list", "count"}, new Object[][] {list, {count}});

        this.queueIndex = 2;

        numberId = idNumber.incrementAndGet();

        this.count = count;
        this.list = Arrays.copyOf(list, list.length);

        setScope(Stream.concat(Arrays.stream(list), Stream.of(count)));

    }


    /**
     * It constructs Values constraint.
     *
     * @param list  list of variables for which different values are being counted.
     * @param count specifies the number of different values in the list.
     */
    public Values(List<? extends IntVar> list, IntVar count) {
        this(list.toArray(new IntVar[list.size()]), count);
    }

    @Override @SuppressWarnings("unchecked") public void consistency(Store store) {

        do {

            store.propagationHasOccurred = false;

            Arrays.sort(list, minFDV);

            if (debug)
                System.out.println("Sorted : \n" + this);

            int minNumberDifferent = 1, minimumMax = list[0].max();

            int[][] adj = new int[list.length + 1][];
            adj[0] = new int[0];
            Map<Integer, Integer> valueMap = new HashMap<>();
            int valueIndex = 0;

            int numberSingleton = 0;
            IntDomain singletonValues = new IntervalDomain();

            for (int i = 0; i < list.length; i++) {
                IntVar v = list[i];

                // compute information for pruning list of Variables
                if (v.singleton()) {
                    numberSingleton++;
                    singletonValues.unionAdapt(v.min(), v.min());
                }

                // compute minimal value for count
                if (v.min() > minimumMax) {
                    minNumberDifferent++;
                    minimumMax = v.max();
                }
                if (v.max() < minimumMax)
                    minimumMax = v.max();

                adj[i + 1] = new int[v.dom().getSize()];
                int j = 0;
                for (ValueEnumeration e = v.dom().valueEnumeration(); e.hasMoreElements(); ) {
                    int el = e.nextElement();
                    Integer elIndex = valueMap.get(el);
                    if (elIndex == null) {
                        valueMap.put(el, valueIndex);
                        adj[i + 1][j] = valueIndex + 1;
                        valueIndex++;
                    } else {
                        adj[i + 1][j] = elIndex + 1;
                    }
                    j++;
                }

            }
            // compute maximal value for count
            BipartiteGraphMatching matcher = new BipartiteGraphMatching(adj, list.length, valueMap.size());
            int maxNumberDifferent = matcher.hopcroftKarp();

            if (debug)
                System.out.println("Minimum number of different values = " + minNumberDifferent);
            if (debug)
                System.out.println("Maximum number of different values = " + maxNumberDifferent);

            count.domain.in(store.level, count, minNumberDifferent, maxNumberDifferent);

            if (debug)
                System.out.println("Number singleton values = " + numberSingleton + " Values = " + singletonValues);

            if (count.max() == singletonValues.getSize() && numberSingleton < list.length) {
                for (IntVar v : list)
                    if (!v.singleton())
                        v.domain.in(store.level, v, singletonValues);
            } else {

                int diffMin = count.min() - singletonValues.getSize();
                int diffSingleton = list.length - numberSingleton;

                if (diffMin == diffSingleton)
                    for (IntVar v : list)
                        if (!v.singleton())
                            v.domain.in(store.level, v, singletonValues.complement());
            }

        } while (store.propagationHasOccurred);

    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : Values([");
        for (int i = 0; i < list.length; i++) {
            if (i < list.length - 1)
                result.append(list[i]).append(", ");
            else
                result.append(list[i]);
        }
        result.append("], ").append(count).append(" )");
        return result.toString();
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public boolean satisfied() {

        return grounded() && Arrays.stream(list).map(IntVar::value).collect(Collectors.toSet()).size() == count.value();

    }


}

