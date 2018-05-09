/*
 * Assignment.java
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
 * Assignment constraint implements facility to improve channeling constraints
 * between dual viewpoints of permutation models.
 * It enforces the relationship x[d[i]-shiftX]=i+shiftD and d[x[i]-shiftD]=i+shiftX. 
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 *
 * @version 4.5
 */

public class Assignment extends Constraint implements UsesQueueVariable, Stateful, SatisfiedPresent {

    final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a list of variables d.
     */
    final public IntVar d[];

    /**
     * It specifies a shift applied to variables d.
     */
    public int shiftD = 0;

    Map<IntVar, Integer> ds;

    /**
     * It specifies a list of variables x.
     */
    public IntVar x[];
    /**
     * It specifies a shift applied to variables x.
     */
    public int shiftX = 0;

    Map<IntVar, Integer> xs;


    LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<IntVar>();
    boolean firstConsistencyCheck = true;
    int firstConsistencyLevel;

    /**
     * It enforces the relationship x[d[i]-shiftX]=i+shiftD and
     * d[x[i]-shiftD]=i+shiftX.
     * @param xs array of variables x
     * @param ds array of variables d
     * @param shiftX a shift of indexes in X array.
     * @param shiftD a shift of indexes in D array.
     */
    public Assignment(IntVar[] xs, IntVar[] ds, int shiftX, int shiftD) {

        checkInputForNullness(new String[] {"xs", "ds"}, xs, ds);

        numberId = idNumber.incrementAndGet();

        this.shiftX = shiftX;
        this.shiftD = shiftD;
        this.x = Arrays.copyOf(xs, xs.length);
        this.d = Arrays.copyOf(ds, ds.length);
        this.queueIndex = 1;

        this.xs = Var.createEmptyPositioning();
        this.ds = Var.createEmptyPositioning();

        for (int i = 0; i < xs.length; i++) {
            this.xs.put(x[i], i + shiftX);
            this.ds.put(d[i], i + shiftD);
        }

        setScope( Stream.concat(Arrays.stream(xs), Arrays.stream(ds)) );

    }

    /**
     * It enforces the relationship x[d[i]-shiftX]=i+shiftD and
     * d[x[i]-shiftD]=i+shiftX.
     * @param xs arraylist of variables x
     * @param ds arraylist of variables d
     * @param shiftX shift for parameter xs
     * @param shiftD shift for parameter ds
     */
    public Assignment(List<? extends IntVar> xs, List<? extends IntVar> ds, int shiftX, int shiftD) {
        this(xs.toArray(new IntVar[xs.size()]), ds.toArray(new IntVar[ds.size()]), shiftX, shiftD);
    }


    /**
     * It constructs an Assignment constraint with shift equal 0. It
     * enforces relation - d[x[j]] = i and x[d[i]] = j.
     * @param xs arraylist of x variables
     * @param ds arraylist of d variables
     */
    public Assignment(List<? extends IntVar> xs, List<? extends IntVar> ds) {
        this(xs.toArray(new IntVar[xs.size()]), ds.toArray(new IntVar[ds.size()]), 0, 0);
    }

    /**
     * It enforces the relationship x[d[i]-min]=i+min and
     * d[x[i]-min]=i+min.
     * @param xs arraylist of variables x
     * @param ds arraylist of variables d
     * @param min shift
     */
    public Assignment(List<? extends Var> xs, List<? extends Var> ds, int min) {
        this(xs.toArray(new IntVar[xs.size()]), ds.toArray(new IntVar[ds.size()]), min, min);
    }


    /**
     * It constructs an Assignment constraint with shift equal 0. It
     * enforces relation - d[x[i]] = i and x[d[i]] = i.
     * @param xs array of x variables
     * @param ds array of d variables
     */
    public Assignment(IntVar[] xs, IntVar[] ds) {
        this(xs, ds, 0, 0);
    }

    /**
     * It enforces the relationship x[d[i]-min]=i+min and
     * d[x[i]-min]=i+min.
     * @param xs array of variables x
     * @param ds array of variables d
     * @param min shift
     */
    public Assignment(IntVar[] xs, IntVar[] ds, int min) {
        this(xs, ds, min, min);
    }

    @Override public void removeLevel(int level) {
        variableQueue.clear();
        if (level == firstConsistencyLevel)
            firstConsistencyCheck = true;
    }


    IntervalDomain rangeX;
    IntervalDomain rangeD;

    @Override public void consistency(Store store) {

        if (firstConsistencyCheck) {

            rangeX = new IntervalDomain(0 + shiftX, x.length - 1 + shiftX);

            rangeD = new IntervalDomain(0 + shiftD, x.length - 1 + shiftD);

            for (int i = 0; i < x.length; i++) {

                IntDomain alreadyRemoved = rangeD.subtract(x[i].domain);

                x[i].domain.in(store.level, x[i], shiftD, x.length - 1 + shiftD);

                if (!alreadyRemoved.isEmpty())
                    for (ValueEnumeration enumer = alreadyRemoved.valueEnumeration(); enumer.hasMoreElements(); ) {

                        int xValue = enumer.nextElement();

                        d[xValue - shiftD].domain.inComplement(store.level, d[xValue - shiftD], i + shiftX);

                    }

                if (x[i].singleton()) {
                    int position = x[i].value() - shiftD;
                    d[position].domain.in(store.level, d[position], i + shiftX, i + shiftX);
                }

            }

            for (int i = 0; i < d.length; i++) {

                IntDomain alreadyRemoved = rangeX.subtract(d[i].domain);

                d[i].domain.in(store.level, d[i], shiftX, x.length - 1 + shiftX);

                if (!alreadyRemoved.isEmpty())
                    for (ValueEnumeration enumer = alreadyRemoved.valueEnumeration(); enumer.hasMoreElements(); ) {

                        int dValue = enumer.nextElement();

                        x[dValue - shiftX].domain.inComplement(store.level, x[dValue - shiftX], i + shiftD);

                    }

                if (d[i].singleton()) {

                    x[d[i].value() - shiftX].domain.in(store.level, x[d[i].value() - shiftX], i + shiftD, i + shiftD);
                }

            }

            firstConsistencyCheck = false;
            firstConsistencyLevel = store.level;

        }

        while (!variableQueue.isEmpty()) {

            LinkedHashSet<IntVar> fdvs = variableQueue;

            variableQueue = new LinkedHashSet<IntVar>();

            for (IntVar V : fdvs) {

                IntDomain vPrunedDomain = V.recentDomainPruning();

                if (!vPrunedDomain.isEmpty()) {

                    Integer position = xs.get(V);
                    if (position == null) {
                        // d variable has been changed
                        position = ds.get(V);

                        vPrunedDomain = vPrunedDomain.intersect(rangeX);

                        if (vPrunedDomain.isEmpty())
                            continue;

                        for (ValueEnumeration enumer = vPrunedDomain.valueEnumeration(); enumer.hasMoreElements(); ) {

                            int dValue = enumer.nextElement() - shiftX;

                            if (dValue >= 0 && dValue < x.length)
                                x[dValue].domain.inComplement(store.level, x[dValue], position);
                        }

                        if (V.singleton())
                            x[V.value() - shiftX].domain.in(store.level, x[V.value() - shiftX], position, position);

                    } else {
                        // x variable has been changed

                        vPrunedDomain = vPrunedDomain.intersect(rangeD);

                        if (vPrunedDomain.isEmpty())
                            continue;

                        for (ValueEnumeration enumer = vPrunedDomain.valueEnumeration(); enumer.hasMoreElements(); ) {

                            int xValue = enumer.nextElement() - shiftD;

                            if (xValue >= 0 && xValue < d.length)
                                d[xValue].domain.inComplement(store.level, d[xValue], position);

                            if (V.singleton())
                                d[V.value() - shiftD].domain.in(store.level, d[V.value() - shiftD], position, position);

                        }

                    }

                }

            }

        }

    }

    @Override public boolean satisfied() {

        if (! grounded() )
            return false;

        for (int i = 0; i < x.length; i++) {
                int position = x[i].value() - shiftD;
                if ( d[position].value() != i + shiftX) {
                    return false;
                }
        }

        for (int i = 0; i < d.length; i++) {
                if (x[d[i].value() - shiftX].value() != i + shiftD) {
                    return false;
                }
        }

        return true;

    }


    public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    // registers the constraint in the constraint store
    @Override public void impose(Store store) {

        super.impose(store);

        store.raiseLevelBeforeConsistency = true;

    }

    @Override public void queueVariable(int level, Var var) {
        variableQueue.add((IntVar) var);
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());

        result.append(" : assignment([");

        for (int i = 0; i < x.length; i++) {
            result.append(x[i]);
            if (i < x.length - 1)
                result.append(", ");
        }
        result.append("], [");

        for (int i = 0; i < d.length; i++) {
            result.append(d[i]);
            if (i < d.length - 1)
                result.append(", ");
        }
        result.append("], ");
        result.append(shiftX + ", " + shiftD + ")");

        return result.toString();
    }

}
