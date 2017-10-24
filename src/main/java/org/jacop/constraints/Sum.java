/*
 * Sum.java
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

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;

/**
 * Sum constraint implements the summation over several Variable's . It provides
 * the sum from all Variable's on the list.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */


/**
 * @deprecated As of release 4.3.1 replaced by SumInt constraint.
 */
@Deprecated
public class Sum extends Constraint implements SatisfiedPresent {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies the variables to be summed.
     */
    public IntVar list[];

    /**
     * It specifies variable sum to store the overall sum of the variables being summed up.
     */
    public IntVar sum;

    /**
     * The sum of grounded variables.
     */
    private TimeStamp<Integer> sumGrounded;

    /**
     * The position for the next grounded variable.
     */
    private TimeStamp<Integer> nextGroundedPosition;

    /**
     * It constructs sum constraint which sums all variables and makes it equal to variable sum.
     * @param list list of variables to be added
     * @param sum the resulting sum
     */
    public Sum(IntVar[] list, IntVar sum) {

        checkInputForNullness(new String[]{"list", "sum"}, new Object[][]{list, {sum}});

        queueIndex = 1;
        numberId = idNumber.incrementAndGet();

        this.sum = sum;
        this.list = Arrays.copyOf(list, list.length);

        checkForOverflow();

        setScope( Stream.concat(Arrays.stream(list), Stream.of(sum)));
    }

    /**
     * It creates a sum constraints which sums all variables and makes it equal to variable sum.
     * @param list variables being summed up.
     * @param sum the sum variable.
     */

    public Sum(List<? extends IntVar> list, IntVar sum) {
        this(list.toArray(new IntVar[list.size()]), sum);
    }

    @Override public void consistency(Store store) {


        do {

            store.propagationHasOccurred = false;

            int pointer = nextGroundedPosition.value();

            int lMin = sumGrounded.value();
            int lMax = lMin;

            int sumJustGrounded = 0;

            for (int i = pointer; i < list.length; i++) {
                IntDomain currentDomain = list[i].domain;

                if (currentDomain.singleton()) {

                    if (pointer < i) {
                        IntVar grounded = list[i];
                        list[i] = list[pointer];
                        list[pointer] = grounded;
                    }

                    pointer++;
                    sumJustGrounded += currentDomain.min();
                    continue;
                }

                lMin += currentDomain.min();
                lMax += currentDomain.max();
            }

            nextGroundedPosition.update(pointer);
            sumGrounded.update(sumGrounded.value() + sumJustGrounded);

            lMin += sumJustGrounded;
            lMax += sumJustGrounded;

            boolean needAdaptMin = false;
            boolean needAdaptMax = false;

            if (sum.min() > lMin)
                needAdaptMin = true;

            if (sum.max() < lMax)
                needAdaptMax = true;

            sum.domain.in(store.level, sum, lMin, lMax);

            store.propagationHasOccurred = false;

            int min = sum.min() - lMax;
            int max = sum.max() - lMin;

            if (needAdaptMin && !needAdaptMax)
                for (int i = pointer; i < list.length; i++) {
                    IntVar v = list[i];
                    v.domain.inMin(store.level, v, min + v.max());
                }

            if (!needAdaptMin && needAdaptMax)
                for (int i = pointer; i < list.length; i++) {
                    IntVar v = list[i];
                    v.domain.inMax(store.level, v, max + v.min());
                }

            if (needAdaptMin && needAdaptMax)
                for (int i = pointer; i < list.length; i++) {
                    IntVar v = list[i];
                    v.domain.in(store.level, v, min + v.max(), max + v.min());
                }

        } while (store.propagationHasOccurred);

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    // registers the constraint in the constraint store
    @Override public void impose(Store store) {

        sumGrounded = new TimeStamp<Integer>(store, 0);
        nextGroundedPosition = new TimeStamp<Integer>(store, 0);

        super.impose(store);

    }

    @Override public boolean satisfied() {

        if (! grounded() )
            return false;

        int sumAll = 0;
        for (IntVar v : list)
                sumAll += v.min();

        return sumAll == sum.min();
    }

    void checkForOverflow() {

        int sumMin = 0, sumMax = 0;
        for (int i = 0; i < list.length; i++) {
            int n1 = list[i].min();
            int n2 = list[i].max();

            sumMin = Math.addExact(sumMin, n1);
            sumMax = Math.addExact(sumMax, n2);
        }

        Math.subtractExact(sumMin, sum.max());
        Math.subtractExact(sumMax, sum.min());
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : sum( [");

        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);
            if (i < list.length - 1)
                result.append(", ");
        }
        result.append("], ").append(sum).append(" )");

        return result.toString();
    }

    @Override public Constraint getGuideConstraint() {

        IntVar proposedVariable = (IntVar) getGuideVariable();
        if (proposedVariable != null)
            return new XeqC(proposedVariable, guideValue);
        else
            return null;
    }

    @Override public int getGuideValue() {
        return guideValue;
    }

    int guideValue = 0;


    @Override public Var getGuideVariable() {

        int regret = 1;
        Var proposedVariable = null;

        for (IntVar v : list) {

            IntDomain listDom = v.dom();

            if (v.singleton())
                continue;

            int currentRegret = listDom.nextValue(listDom.min()) - listDom.min();

            if (currentRegret > regret) {
                regret = currentRegret;
                proposedVariable = v;
                guideValue = listDom.min();
            }

            currentRegret = listDom.max() - listDom.previousValue(listDom.max());

            if (currentRegret > regret) {
                regret = currentRegret;
                proposedVariable = v;
                guideValue = listDom.max();
            }

        }

        return proposedVariable;

    }

    @Override public void supplyGuideFeedback(boolean feedback) {
    }

}
