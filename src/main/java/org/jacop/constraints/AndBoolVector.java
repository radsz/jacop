/*
 * AndBoolVector.java
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/**
 * If all x's are equal 1 then result variable is equal 1 too. Otherwise, result variable
 * is equal to zero. It restricts the domain of all x as well as result to be between 0 and 1.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class AndBoolVector extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a list of variables which all must be equal to 1 to set result variable to 1.
     */
    public IntVar[] list;

    /**
     * It specifies the length of the list.
     */
    final int l;

    /**
     * It specifies variable result, storing the result of and function performed a list of variables.
     */
    public IntVar result;

    /*
     * Defines first position of the variable that is not ground to 1
     */
    private TimeStamp<Integer> position;

    /**
     * It constructs AndBoolVector.
     *
     * @param list   list of x's which must all be equal 1 to make result equal 1.
     * @param result variable which is equal 0 if any of x is equal to zero.
     */
    public AndBoolVector(IntVar[] list, IntVar result) {

        checkInputForNullness(new String[] {"list", "result"}, list, new Object[] {result});

        this.numberId = idNumber.incrementAndGet();

        Set<IntVar> varSet = new HashSet<>();
        varSet.addAll(Arrays.asList(list));

        this.l = varSet.size();
        this.list = varSet.toArray(new IntVar[varSet.size()]);
        this.result = result;

        assert (checkInvariants() == null) : checkInvariants();

        if (l > 2)
            queueIndex = 1;
        else
            queueIndex = 0;

        setScope( Stream.concat(Arrays.stream(list), Stream.of(result)));

    }

    /**
     * It constructs AndBoolVector.
     *
     * @param list   list of x's which must all be equal 1 to make result equal 1.
     * @param result variable which is equal 0 if any of x is equal to zero.
     */
    public AndBoolVector(List<IntVar> list, IntVar result) {

        this(list.toArray(new IntVar[list.size()]), result);

    }

    /**
     * It checks invariants required by the constraint. Namely that
     * boolean variables have boolean domain.
     *
     * @return the string describing the violation of the invariant, null otherwise.
     */
    public String checkInvariants() {

        for (IntVar var : list)
            if (var.min() < 0 || var.max() > 1)
                return "Variable " + var + " does not have boolean domain";

        return null;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.GROUND;
    }

    @Override public void include(Store store) {
        position = new TimeStamp<>(store, 0);
    }

    public void consistency(Store store) {

        int start = position.value();
        int index_01 = l - 1;

        if (result.min() == 1) {
            for (int i = start; i < l; i++)
                list[i].domain.in(store.level, list[i], 1, 1);
            return;
        }

        for (int i = start; i < l; i++) {
            if (list[i].min() == 1) {
                swap(start, i);
                start++;
            } else if (list[i].max() == 0) {
                result.domain.in(store.level, result, 0, 0);
                removeConstraint();
                return;
            }
        }
        position.update(start);

        if (start == l) {
            result.domain.in(store.level, result, 1, 1);
            return;
        }

        if (result.max() == 0 && start == l - 1)
                list[index_01].domain.in(store.level, list[index_01], 0, 0);

        if ((l - start) < 3)
            queueIndex = 0;
    }

    private void swap(int i, int j) {
        if (i != j) {
            IntVar tmp = list[i];
            list[i] = list[j];
            list[j] = tmp;
        }
    }

    @Override public void notConsistency(Store store) {

        int start = position.value();

        int index_01 = l - 1;

        if (result.max() == 0) {
            for (int i = start; i < l; i++)
                list[i].domain.in(store.level, list[i], 1, 1);
            return;
        }

        for (int i = start; i < l; i++) {
            if (list[i].min() == 1) {
                swap(start, i);
                start++;
            } else if (list[i].max() == 0) {
                result.domain.in(store.level, result, 1, 1);
                return;
            }
        }
        position.update(start);

        if (start == l) {
            result.domain.in(store.level, result, 0, 0);
            return;
        }

        if (result.max() == 0 && start == l - 1)
                list[index_01].domain.in(store.level, list[index_01], 1, 1);

        if ((l - start) < 3)
            queueIndex = 0;
    }

    @Override public boolean satisfied() {

        int start = position.value();

        if (result.min() == 1) {
            for (int i = start; i < l; i++)
                if (list[i].min() != 1)
                    return false;
                else {
                    swap(start, i);
                    start++;
                    position.update(start);
                }
            return true;
        } else if (result.max() == 0) {
            for (int i = start; i < l; i++)
                if (list[i].max() == 0)
                    return true;
                else if (list[i].min() == 1) {
                    swap(start, i);
                    start++;
                    position.update(start);
                }
            return false;
        }

        return false;

    }

    @Override public boolean notSatisfied() {

        int start = position.value();

        if (result.max() == 0) {

            for (int i = start; i < l; i++)
                if (list[i].min() != 1)
                    return false;
                else {
                    swap(start, i);
                    start++;
                    position.update(start);
                }

            return true;

        } else {

            if (result.min() == 1) {

                for (int i = start; i < l; i++)
                    if (list[i].max() == 0)
                        return true;
                    else if (list[i].min() == 1) {
                        swap(start, i);
                        start++;
                        position.update(start);
                    }
            }
        }

        return false;
    }

    @Override public String toString() {

        StringBuilder resultString = new StringBuilder(id());

        resultString.append(" : andBool([ ");
        for (int i = 0; i < l; i++) {
            resultString.append(list[i]);
            if (i < l - 1)
                resultString.append(", ");
        }
        resultString.append("], ");
        resultString.append(result);
        resultString.append(")");
        return resultString.toString();
    }

    List<Constraint> constraints;

    @Override public List<Constraint> decompose(Store store) {

        constraints = new ArrayList<>();

        PrimitiveConstraint[] andConstraints = new PrimitiveConstraint[l];

        IntervalDomain booleanDom = new IntervalDomain(0, 1);

        for (int i = 0; i < andConstraints.length; i++) {
            andConstraints[0] = new XeqC(list[i], 1);
            constraints.add(new In(list[i], booleanDom));
        }

        constraints.add(new In(result, booleanDom));

        constraints.add(new Eq(new And(andConstraints), new XeqC(result, 1)));

        return constraints;
    }

    @Override public void imposeDecomposition(Store store) {

        if (constraints == null)
            constraints = decompose(store);

        for (Constraint c : constraints)
            store.impose(c, queueIndex);

    }

}
