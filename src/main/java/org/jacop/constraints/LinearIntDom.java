/*
 * LinearIntDom.java
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

import org.jacop.core.*;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.IntStream;
import java.util.stream.Stream;

/**
 * LinearIntDom constraint implements the weighted summation over several
 * variables.
 * <p>
 * sum(i in 1..N)(ai*xi) = b
 * <p>
 * It provides the weighted sum from all variables on the list.
 * The weights are integers. Domain consistency is used.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class LinearIntDom extends LinearInt {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * Defines support (valid values) for each variable
     */
    IntervalDomain[] support;

    /**
     * Collects support (valid assignments) for variables
     */
    int[] assignments;

    /**
     * Limit on the product of sizes of domains when domain consistency
     * is carried out.
     */
    double limitDomainPruning = 1e+7;

    /**
     * It constructs the constraint LinearIntDom.
     *
     * @param store   current store
     * @param list    variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param rel     the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum     the sum of weighted variables.
     * @deprecated LinearIntDom constraint does not use Store parameter any longer.
     */
    @Deprecated
    public LinearIntDom(Store store, IntVar[] list, int[] weights, String rel, int sum) {
        commonInitialization(store, list, weights, rel, sum);
        numberId = idNumber.incrementAndGet();
        queueIndex = 4;
    }

    /**
     * It constructs the constraint LinearIntDom.
     *
     * @param store   current store
     * @param list    variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param rel     the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum     variable containing the sum of weighted variables.
     * @deprecated LinearIntDom constraint does not use Store parameter any longer.
     */
    @Deprecated
    public LinearIntDom(Store store, IntVar[] list, int[] weights, String rel, IntVar sum) {
        commonInitialization(store, Stream.concat(Arrays.stream(list), Stream.of(sum)).toArray(IntVar[]::new),
            IntStream.concat(Arrays.stream(weights), IntStream.of(-1)).toArray(), rel, 0);
        numberId = idNumber.incrementAndGet();
        queueIndex = 4;

    }

    /**
     * It constructs the constraint LinearIntDom.
     *
     * @param store     current store
     * @param variables variables which are being multiplied by weights.
     * @param weights   weight for each variable.
     * @param rel       the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum       variable containing the sum of weighted variables.
     * @deprecated LinearIntDom constraint does not use Store parameter any longer.
     */
    @Deprecated
    public LinearIntDom(Store store, List<? extends IntVar> variables, List<Integer> weights, String rel, int sum) {
        commonInitialization(store, variables.toArray(new IntVar[variables.size()]), weights.stream().mapToInt(i -> i).toArray(), rel, sum);
        numberId = idNumber.incrementAndGet();
        queueIndex = 4;
    }


    // ================ new constructors ===================
    /**
     * It constructs the constraint LinearIntDom.
     *
     * @param list    variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param rel     the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum     the sum of weighted variables.
     */
    public LinearIntDom(IntVar[] list, int[] weights, String rel, int sum) {
        commonInitialization(list[0].getStore(), list, weights, rel, sum);
        numberId = idNumber.incrementAndGet();
        queueIndex = 4;
    }

    /**
     * It constructs the constraint LinearIntDom.
     *
     * @param list    variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param rel     the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum     variable containing the sum of weighted variables.
     */
    public LinearIntDom(IntVar[] list, int[] weights, String rel, IntVar sum) {
        commonInitialization(sum.getStore(), Stream.concat(Arrays.stream(list), Stream.of(sum)).toArray(IntVar[]::new),
            IntStream.concat(Arrays.stream(weights), IntStream.of(-1)).toArray(), rel, 0);
        numberId = idNumber.incrementAndGet();
        queueIndex = 4;

    }
    
    /**
     * It constructs the constraint LinearIntDom.
     *
     * @param variables variables which are being multiplied by weights.
     * @param weights   weight for each variable.
     * @param rel       the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum       variable containing the sum of weighted variables.
     */
    public LinearIntDom(List<? extends IntVar> variables, List<Integer> weights, String rel, int sum) {
        commonInitialization(variables.get(0).getStore(), variables.toArray(new IntVar[variables.size()]), weights.stream().mapToInt(i -> i).toArray(), rel, sum);
        numberId = idNumber.incrementAndGet();
        queueIndex = 4;
    }

    @Override public void consistency(Store store) {
        propagate(relationType);
    }

    @Override public void notConsistency(Store store) {
        propagate(negRel[relationType]);
    }

    public void propagate(int rel) {


	switch (rel) {
	case eq:
		    
	    if (domainSize() < limitDomainPruning) {
		computeInit();
		pruneEq(); // domain consistency
	    }
	    else  
		// bound consistency
		super.propagate(rel);

	    break;

	case ne:
	    if (domainSize() < limitDomainPruning) {
		computeInit();
		pruneNeq();
	    
		computeInit();

		if (!reified && (sumMin > b || sumMax < b))
		    removeConstraint();
	    }
	    else 
		super.propagate(rel);
		    
	    break;

	default:
	    System.out.println("Not implemented relation in LinearIntDom; implemented == and != only.");
	    break;
	}
    }

    double domainSize() {

        double s = 1;
        for (int i = 0; i < l; i++)
            s *= (double) x[i].domain.getSize();

        // System.out.println("s = " + s);

        return s;
    }

    void pruneEq() {

        assignments = new int[l];
        support = new IntervalDomain[l];

        findSupport(0, 0L);
	
        // System.out.println("Variables: "+java.util.Arrays.asList(x)+" have valid assignments: " + java.util.Arrays.asList(support));
        for (int i = 0; i < l; i++)
	    if (support[i] == null)
		throw store.failException;
	    else
		x[i].domain.in(store.level, x[i], support[i]);
    }

    void pruneNeq() {

        assignments = new int[l];
        support = new IntervalDomain[l];

        findSupport(0, 0L);

        // System.out.println("valid assignments: " + java.util.Arrays.asList(support));

        for (int i = 0; i < l; i++)
	    if (support[i] == null)
		removeConstraint();
	    else
		if (support[i].singleton())
		    x[i].domain.inComplement(store.level, x[i], support[i].value());

    }

    void findSupport(int index, long sum) {

        findSupportPositive(index, sum);

    }

    void findSupportPositive(int index, long partialSum) {

        int newIndex = index + 1;

        if (index == l - 1) {

            long element = b - partialSum;
            long val = element / a[index];
            long rest = element % a[index];
	    int valInt = (int)val;
            if (rest == 0 && valInt == val && x[index].domain.contains(valInt)) {
                assignments[index] = valInt;

                // store assignments
                for (int i = 0; i < l; i++) {
                    int a = assignments[i];
                    if (support[i] == null)
                        support[i] = new IntervalDomain(a, a);
                    else if (support[i].max() < a)
                        support[i].addLastElement(a);
                    else if (support[i].max() > a)
                        support[i].unionAdapt(a, a);
                }
            }
            return;
        }

        IntDomain currentDom = x[index].dom();
        long newPartialSum = partialSum;
        long w = a[index];

        long lb = b - sumMax + currentDom.max() * w;
        long ub = b - sumMin + currentDom.min() * w;

        if (currentDom.domainID() == IntDomain.IntervalDomainID) {
            int n = ((IntervalDomain) currentDom).size;

            outerloop:
            for (int k = 0; k < n; k++) {
                Interval e = ((IntervalDomain) currentDom).intervals[k];
                int eMin = e.min();
                int eMax = e.max();

                for (int element = eMin; element <= eMax; element++) {

                    long elementValue = (long)element * w;
                    if (elementValue < lb)
                        continue; // value too low
                    else if (elementValue > ub)
                        break outerloop; // value too large
                    else
                        newPartialSum = partialSum + elementValue;

                    assignments[index] = element;

                    if (newIndex < pos)
                        findSupportPositive(newIndex, newPartialSum);
                    else
                        findSupportNegative(newIndex, newPartialSum);
                }
            }
        } else

            for (ValueEnumeration val = currentDom.valueEnumeration(); val.hasMoreElements(); ) {
                int element = val.nextElement();

                long elementValue = (long)element * w;
                if (elementValue < lb)
                    continue; // value too low
                else if (elementValue > ub)
                    break; // value too large
                else
                    newPartialSum = partialSum + elementValue;

                assignments[index] = element;

                if (newIndex < pos)
                    findSupportPositive(newIndex, newPartialSum);
                else
                    findSupportNegative(newIndex, newPartialSum);
            }
    }


    void findSupportNegative(int index, long partialSum) {

        int newIndex = index + 1;

        if (index == l - 1) {

            long element = b - partialSum;
            long val = element / a[index];
            long rest = element % a[index];
	    int valInt = (int)val;
            if (rest == 0 && valInt == val && x[index].domain.contains(valInt)) {
                assignments[index] = valInt;

                // store assignments
                for (int i = 0; i < l; i++) {
                    int a = assignments[i];
                    if (support[i] == null)
                        support[i] = new IntervalDomain(a, a);
                    else if (support[i].max() < a)
                        support[i].addLastElement(a);
                    else if (support[i].max() > a)
                        support[i].unionAdapt(a, a);
                }
            }
            return;
        }

        IntDomain currentDom = x[index].dom();
        long newPartialSum = partialSum;
        long w = a[index];

        long lb = b - sumMax + currentDom.min() * w;
        long ub = b - sumMin + currentDom.max() * w;

        if (currentDom.domainID() == IntDomain.IntervalDomainID) {
            int n = ((IntervalDomain) currentDom).size;

            outerloop:
            for (int k = 0; k < n; k++) {
                Interval e = ((IntervalDomain) currentDom).intervals[k];
                int eMin = e.min();
                int eMax = e.max();

                for (int element = eMin; element <= eMax; element++) {

                    long elementValue = (long)element * w;
                    if (elementValue < lb)
                        break outerloop; // value too low
                    else if (elementValue > ub)
                        continue; // value too large
                    else
                        newPartialSum = partialSum + elementValue;

                    assignments[index] = element;

                    findSupportNegative(newIndex, newPartialSum);
                }
            }
        } else
            for (ValueEnumeration val = currentDom.valueEnumeration(); val.hasMoreElements(); ) {
                int element = val.nextElement();

                long elementValue = (long)element * w;
                if (elementValue < lb)
                    break; // value too low
                else if (elementValue > ub)
                    continue; // value too large
                else
                    newPartialSum = partialSum + elementValue;

                assignments[index] = element;

                findSupportNegative(newIndex, newPartialSum);
            }
    }

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : LinearIntDom( [ ");

        for (int i = 0; i < x.length; i++) {
            result.append(x[i]);
            if (i < x.length - 1)
                result.append(", ");
        }
        result.append("], [");

        for (int i = 0; i < a.length; i++) {
            result.append(a[i]);
            if (i < a.length - 1)
                result.append(", ");
        }

        result.append("], ").append(rel2String()).append(", ").append(b).append(" )");

        return result.toString();

    }

}
