/**
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

import org.jacop.util.BipartiteGraphMatching;

/**
 * Constraint Values counts number of different values on a list of Variables.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 * @version 4.4
 */

public class Values extends Constraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a list of variables which are counted.
     */
    IntVar[] list;

    /**
     * It specifies the idNumber of different values among variables on a given list.
     */
    IntVar count;

    Comparator<IntVar> minFDV = new FDVminimumComparator<IntVar>();

    static final boolean debug = false;

    /**
     * It specifies the arguments required to be saved by an XML format as well as
     * the constructor being called to recreate an object from an XML format.
     */
    public static String[] xmlAttributes = {"list", "count"};

    /**
     * It constructs Values constraint.
     *
     * @param list list of variables for which different values are being counted.
     * @param count specifies the number of different values in the list.
     */
    public Values(IntVar[] list, IntVar count) {

        assert (list != null) : "List argument is null";
        assert (count != null) : "count argument is null";

        this.queueIndex = 2;

        numberId = idNumber.incrementAndGet();
        numberArgs = (short) (list.length + 1);

        this.count = count;
        this.list = new IntVar[list.length];

        for (int i = 0; i < list.length; i++) {

            assert (list[i] != null) : i + "-th element of list is null";
            this.list[i] = list[i];

        }
    }


    /**
     * It constructs Values constraint.
     *
     * @param list list of variables for which different values are being counted.
     * @param count specifies the number of different values in the list.
     */
    public Values(ArrayList<? extends IntVar> list, IntVar count) {

        this(list.toArray(new IntVar[list.size()]), count);

    }

    @Override public void impose(Store store) {
        count.putConstraint(this);
        for (Var v : list)
            v.putConstraint(this);
        store.addChanged(this);
        store.countConstraint();
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
            HashMap<Integer, Integer> valueMap = new HashMap<Integer, Integer>();
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

    @Override public boolean satisfied() {
        boolean sat = true;
        int i = 0;
        if (count.singleton())
            while (sat && i < list.length) {
                sat = list[i].singleton();
                i++;
            }
        else
            return false;
        return sat;
    }

    @Override public ArrayList<Var> arguments() {

        ArrayList<Var> variables = new ArrayList<Var>(list.length + 1);

        variables.add(count);
        for (Var v : list)
            variables.add(v);
        return variables;
    }

    @Override public void removeConstraint() {
        count.removeConstraint(this);
        for (Var v : list)
            v.removeConstraint(this);
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

    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode

        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        //@todo, why so restrictive?
        return IntDomain.GROUND;
    }

    @Override public void increaseWeight() {
        if (increaseWeight) {
            count.weight++;
            for (Var v : list)
                v.weight++;
        }
    }

  private static class FDVminimumComparator<T extends IntVar> implements Comparator<T>, java.io.Serializable {

        FDVminimumComparator() {
        }

        public int compare(T o1, T o2) {
            return (o1.min() - o2.min());
        }

    }

}

