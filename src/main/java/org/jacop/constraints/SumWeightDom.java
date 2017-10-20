/*
 * SumWeightDom.java
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
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.jacop.api.SatisfiedPresent;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.*;

/**
 * SumWeightDom constraint implements the weighted summation over several
 * variables . It provides the weighted sum from all variables on the list.
 * The weights are integers.
 * <p>
 * The complexity of domain consistency is exponential in worst case. Use it carefully!
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */


/**
 * @deprecated As of release 4.3.1 replaced by LinearIntDom constraint.
 */
@Deprecated public class SumWeightDom extends Constraint implements UsesQueueVariable, SatisfiedPresent {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies a list of variables being summed.
     */
    public IntVar list[];

    /**
     * It specifies a list of weights associated with the variables being summed.
     */
    public int weights[];

    /**
     * It specifies variable for the overall sum. 
     */
    public int sum;

    /**
     * It specifies variable queue of grounded varibales since last run. 
     */
    LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<IntVar>();

    /**
     * Current minimal value of the expression
     */
    int lMin;

    /**
     * Current maximal value of the expression
     */
    int lMax;

    /**
     * Current domains of varibales
     */
    IntDomain[] lArray;

    Map<Var, Integer> positionMaping;

    boolean backtrackHasOccured = false;

    /**
     * @param list  array of variables to be summed up
     * @param weights variables' weights
     * @param sum  resulting sum
     */
    public SumWeightDom(IntVar[] list, int[] weights, int sum) {
        commonInitialization(list, weights, sum);
    }

    public void commonInitialization(IntVar[] list, int[] weights, int sum) {

        checkInputForNullness(new String[]{"list", "weights"}, new Object[][]{list, { weights }});

        if (list.length != weights.length)
            throw new IllegalArgumentException("SumWeightDom constraint has list and weights of different lengths.");

        queueIndex = 4;

        numberId = idNumber.incrementAndGet();

        this.sum = sum;

        Map<IntVar, Integer> parameters = Var.createEmptyPositioning();

        for (int i = 0; i < list.length; i++) {
            if (weights[i] == 0)
                continue;
            Integer coeff = parameters.getOrDefault(list[i], 0);
            parameters.put(list[i], coeff + weights[i]);
        }

        this.list = new IntVar[parameters.size()];
        this.weights = new int[parameters.size()];

        int i = 0;
        for (Map.Entry<IntVar, Integer> e : parameters.entrySet()) {
            this.list[i] = e.getKey();
            this.weights[i] = e.getValue();
            i++;
        }

        checkForOverflow();

        setScope(list);

    }

    /**
     * @param list array of variables to be summed up
     * @param weights variables' weights
     * @param sum resulting sum
     */
    public SumWeightDom(IntVar[] list, int[] weights, IntVar sum) {

        checkInputForNullness(new String[]{"list", "weights"}, new Object[][]{list, { weights }});
        commonInitialization(Stream.concat(Arrays.stream(list), Stream.of(sum)).toArray(IntVar[]::new),
                             IntStream.concat(Arrays.stream(weights), IntStream.of(-1)).toArray(),
                             0);

    }

    /**
     * It constructs the constraint SumWeightDom.
     * @param list list which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param sum variable containing the sum of weighted list.
     */
    public SumWeightDom(List<? extends IntVar> list, List<Integer> weights, int sum) {
        checkInputForNullness(new String[]{"list", "weights"}, new Object[][]{{list}, { weights }});
        commonInitialization(list.toArray(new IntVar[list.size()]), weights.stream().mapToInt(i -> i).toArray(), sum);

    }

    /**
     * It constructs the constraint SumWeightDom.
     * @param list list which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param sum variable containing the sum of weighted list.
     */
    public SumWeightDom(List<? extends IntVar> list, List<Integer> weights, IntVar sum) {
        checkInputForNullness(new String[]{"list", "weights"}, new Object[][]{{list}, { weights }});
        commonInitialization(Stream.concat(list.stream(), Stream.of(sum)).toArray(IntVar[]::new),
            IntStream.concat(weights.stream().mapToInt(i -> i), IntStream.of(-1)).toArray(),
            0);
    }

    @Override public void removeLevelLate(int level) {

        backtrackHasOccured = true;

        variableQueue.clear();

    }


    /**
     * The sum of grounded variables.
     */
    private TimeStamp<Integer> sumGrounded;

    /**
     * The position for the next grounded variable.
     */
    private TimeStamp<Integer> nextGroundedPosition;

    @Override public void consistency(Store store) {

        if (backtrackHasOccured) {

            backtrackHasOccured = false;

            int pointer = nextGroundedPosition.value();

            lMin = sumGrounded.value();
            lMax = lMin;

            // update lArray domains after backtrack
            for (int i = pointer; i < list.length; i++) {

                IntDomain currentDomain = list[i].domain;

                assert (!currentDomain.singleton()) : "Singletons should not occur in this part of the array";

                lArray[i] = multiplyDom(currentDomain, weights[i]);

                lMin += lArray[i].min();
                lMax += lArray[i].max();

            }

        }

        do {

            store.propagationHasOccurred = false;

            int pointer = nextGroundedPosition.value();

            LinkedHashSet<IntVar> fdvs = variableQueue;
            variableQueue = new LinkedHashSet<IntVar>();

            // check recently grounded variables
            for (IntVar q : fdvs) {

                int i = positionMaping.get(q);

                int valGround = sum - sumGrounded.value() + q.min() * weights[i];
                IntDomain vDom = new IntervalDomain(valGround, valGround);

                for (int j = pointer; j < list.length; j++)
                    vDom = subtractDom(vDom, lArray[j]);

                vDom = divDom(vDom, weights[i]);
                // if (!vDom.contains(q.value()))
                //     System.out.println(q+" in "+vDom);

                q.domain.in(store.level, q, vDom);
            }

            // check still not ground variables
            for (int i = pointer; i < list.length; i++) {

                IntVar v = list[i];

                int pointer1 = nextGroundedPosition.value();

                int sGround = sumGrounded.value();
                IntDomain vDom = new IntervalDomain(sum - sGround, sum - sGround);
                for (int j = pointer1; j < list.length; j++)
                    if (j != i)
                        vDom = subtractDom(vDom, lArray[j]);

                vDom = divDom(vDom, weights[i]);

                v.domain.in(store.level, v, vDom);

            }

        } while (store.propagationHasOccurred);

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public void impose(Store store) {

        sumGrounded = new TimeStamp<Integer>(store, 0);
        nextGroundedPosition = new TimeStamp<Integer>(store, 0);
        positionMaping = Var.positionMapping(list, false, this.getClass());

        store.registerRemoveLevelLateListener(this);

        lArray = new IntDomain[list.length];
        for (int i = 0; i < lArray.length; i++) {
            int min, max;
            if (weights[i] > 0) {
                min = list[i].min() * weights[i];
                max = list[i].max() * weights[i];
            } else {
                min = list[i].max() * weights[i];
                max = list[i].min() * weights[i];
            }
            lArray[i] = new IntervalDomain(min, max);

            lMin += min;
            lMax += max;
        }

        super.impose(store);
        
    }

    @Override public void queueVariable(int level, Var var) {


        if (var.singleton()) {

            int pointer = nextGroundedPosition.value();

            int i = positionMaping.get(var);

            if (i < pointer)
                return;

            int value = ((IntVar) var).min();

            int sumJustGrounded = 0;

            int weightGrounded = weights[i];

            if (pointer < i) {
                IntVar grounded = list[i];
                list[i] = list[pointer];
                list[pointer] = grounded;

                positionMaping.put(list[i], i);
                positionMaping.put(list[pointer], pointer);

                IntDomain temp = lArray[i];
                lArray[i] = lArray[pointer];
                lArray[pointer] = temp;


                weights[i] = weights[pointer];
                weights[pointer] = weightGrounded;

            }

            sumJustGrounded += value * weightGrounded;

            sumGrounded.update(sumGrounded.value() + sumJustGrounded);

            lMin += sumJustGrounded - lArray[pointer].min();
            lMax += sumJustGrounded - lArray[pointer].max();
            lArray[pointer] = new IntervalDomain(sumJustGrounded, sumJustGrounded);

            variableQueue.add((IntVar) var);

            pointer++;
            nextGroundedPosition.update(pointer);

        } else {

            int i = positionMaping.get(var);

            IntDomain old = lArray[i];
            lArray[i] = multiplyDom(((IntVar) var).dom(), weights[i]);

            lMin += lArray[i].min() - old.min();
            lMax += lArray[i].max() - old.max();
        }

    }

    @Override public boolean satisfied() {
        return nextGroundedPosition.value() == list.length && sumGrounded.value() == sum;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : sumWeightDom( [ ");

        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);
            if (i < list.length - 1)
                result.append(", ");
        }
        result.append("], [");

        for (int i = 0; i < weights.length; i++) {
            result.append(weights[i]);
            if (i < weights.length - 1)
                result.append(", ");
        }

        result.append("], ").append(sum).append(" )");

        return result.toString();

    }

    IntDomain multiplyDom(IntDomain d, int c) {
        IntervalDomain temp;
        // System.out.println (d + " * " + c);

        if (c == 1)
            return d;
        else if (c == -1)
            temp = (IntervalDomain) invertDom(d);
        else {
            temp = new IntervalDomain();
            temp.intervals = new Interval[d.getSize()];
            int n = 0;
            for (IntervalEnumeration e1 = d.intervalEnumeration(); e1.hasMoreElements(); ) {
                Interval i = e1.nextElement();

                if (c > 0) {
                    for (int k = i.min(); k <= i.max(); k++)
                        temp.intervals[n++] = new Interval(k * c, k * c);
                } else {// c < 0
                    for (int k = i.max(); k >= i.min(); k--)
                        temp.intervals[n++] = new Interval(k * c, k * c);
                }
            }
            temp.size = n;
        }

        // System.out.println ("result* = " + temp);

        return (IntDomain) temp;

    }

    IntervalDomain invertDom(IntDomain d) {
        IntervalDomain temp = new IntervalDomain();

        if (d.domainID() == IntDomain.IntervalDomainID) {
            int n = ((IntervalDomain) d).size;
            temp.size = n;
            temp.intervals = new Interval[n];
            int k = 0;
            for (int i = n - 1; i >= 0; i--) {
                Interval e = ((IntervalDomain) d).intervals[i];
                temp.intervals[k++] = new Interval(-e.max(), -e.min());
            }
        } else {
            List<Interval> ranges = new ArrayList<Interval>();

            for (IntervalEnumeration e = d.intervalEnumeration(); e.hasMoreElements(); ) {
                Interval i = e.nextElement();
                ranges.add(new Interval(-i.max(), -i.min()));
            }

            int k = 0;
            ((IntervalDomain) temp).intervals = new Interval[ranges.size()];
            for (int i = ranges.size() - 1; i >= 0; i--)
                // temp.unionAdapt(ranges.get(i));
                ((IntervalDomain) temp).intervals[k++] = ranges.get(i);
            ((IntervalDomain) temp).size = k;
        }
        return temp;
    }

    IntDomain divDom(IntDomain d, int c) {

        IntervalDomain temp;
        // System.out.println (d + " / " + c);

        if (c == 1)
            return d;
        else if (c == -1)
            temp = invertDom(d);
        else {

            temp = new IntervalDomain();

            if (c > 0) {

                for (IntervalEnumeration e1 = d.intervalEnumeration(); e1.hasMoreElements(); ) {

                    Interval i = e1.nextElement();
                    int iMin = i.min();
                    int iMax = i.max();

                    int min = (int) Math.round(Math.ceil((float) iMin / c));
                    int max = (int) Math.round(Math.floor((float) iMax / c));
                    if (min <= max)
                        temp.unionAdapt(min, max);
                }
            } else {// c <= 0

                if (d.domainID() == IntDomain.IntervalDomainID) {
                    int n = ((IntervalDomain) d).size;

                    for (int i = n - 1; i >= 0; i--) {
                        Interval e = ((IntervalDomain) d).intervals[i];
                        int iMin = e.min();
                        int iMax = e.max();

                        int min = (int) Math.round(Math.ceil((float) iMax / c));
                        int max = (int) Math.round(Math.floor((float) iMin / c));
                        if (min <= max)
                            temp.unionAdapt(min, max);
                    }
                } else
                    for (IntervalEnumeration e1 = d.intervalEnumeration(); e1.hasMoreElements(); ) {
                        Interval i = e1.nextElement();
                        int iMin = i.min();
                        int iMax = i.max();

                        int min = (int) Math.round(Math.ceil((float) iMax / c));
                        int max = (int) Math.round(Math.floor((float) iMin / c));
                        if (min <= max)
                            temp.unionAdapt(min, max);
                    }
            }
        }

        // System.out.println ("result/ = " + temp);

        return temp;
    }


    // IntDomain plusDom(IntDomain d1, IntDomain d2) {
    // 	IntDomain temp;
    // 	// System.out.println (d1 + " + " + d2);

    // 	temp = new IntervalDomain();

    // 	for (IntervalEnumeration e1 = d1.intervalEnumeration(); e1.hasMoreElements();) {
    // 	    Interval i1 = e1.nextElement(); 
    // 	    int i1min = i1.min(), i1Max = i1.max();

    // 	    for (IntervalEnumeration e2 = d2.intervalEnumeration(); e2.hasMoreElements();) {
    // 		Interval i2 = e2.nextElement();
    // 		// temp.addDom(new IntervalDomain(i1min+i2.min(), i1Max+i2.max()));
    // 		temp.unionAdapt(i1min+i2.min(), i1Max+i2.max());
    // 	    }
    // 	}

    // 	// System.out.println ("result+ = " + temp);

    // 	return temp;
    // }


    IntDomain subtractDom(IntDomain d1, IntDomain d2) {

        IntDomain temp = new IntervalDomain();

        if (d1.singleton()) {
            if (d2.domainID() == IntDomain.IntervalDomainID) {

                // singleton and interval domain
                int d1Value = d1.value();
                int sumMin = sum - lMax + d2.max();
                int sumMax = sum - lMin + d2.min();

                int n = ((IntervalDomain) d2).size;
                int k = 0;
                ((IntervalDomain) temp).intervals = new Interval[n];
                for (int i = n - 1; i >= 0; i--) {
                    Interval e = ((IntervalDomain) d2).intervals[i];
                    int eMin = e.min();
                    int eMax = e.max();

                    if (!(eMin > sumMax || eMax < sumMin))
                        ((IntervalDomain) temp).intervals[k++] = new Interval(d1Value - eMax, d1Value - eMin);
                }
                ((IntervalDomain) temp).size = k;

                // System.out.println("Result = " + temp);

            } else {
                // singleton and NOT interval domain
                List<Interval> ranges = new ArrayList<Interval>();

                int d1Value = d1.value();
                int sumMin = sum - lMax + d2.max();
                int sumMax = sum - lMin + d2.min();

                for (IntervalEnumeration e2 = d2.intervalEnumeration(); e2.hasMoreElements(); ) {
                    Interval i2 = e2.nextElement();
                    int eMin = i2.min();
                    int eMax = i2.max();

                    if (!(eMin > sumMax || eMax < sumMin))
                        ranges.add(new Interval(d1Value - i2.max(), d1Value - i2.min()));
                }

                int k = 0;
                ((IntervalDomain) temp).intervals = new Interval[ranges.size()];
                for (int i = ranges.size() - 1; i >= 0; i--)
                    // temp.unionAdapt(ranges.get(i));
                    ((IntervalDomain) temp).intervals[k++] = ranges.get(i);
                ((IntervalDomain) temp).size = k;
            }
        } else // first domain not singleton
            if (d2.domainID() == IntDomain.IntervalDomainID) {

                // First domain not singleton
                // ArrayList<Interval> ranges = new ArrayList<Interval>();

                int sumMin = sum - lMax + d2.max();
                int sumMax = sum - lMin + d2.min();

                for (IntervalEnumeration e1 = d1.intervalEnumeration(); e1.hasMoreElements(); ) {

                    Interval i1 = e1.nextElement();
                    int i1min = i1.min(), i1max = i1.max();

                    int n = ((IntervalDomain) d2).intervals.length;
                    for (int i = n - 1; i >= 0; i--) {
                        Interval e = ((IntervalDomain) d2).intervals[i];
                        int eMin = e.min();
                        int eMax = e.max();

                        if (!(eMin > sumMax || eMax < sumMin))
                            if (temp.getSize() > 0 && temp.max() <= i1min - eMax)
                                temp.unionAdapt(new Interval(i1min - eMax, i1max - eMin));
                            else
                                temp.unionAdapt(i1min - eMax, i1max - eMin);  // need to check correctness of union
                        //and not only add intervals at the end
                        // as in above cases
                        // ranges.add(new Interval(i1min - eMax, i1max - eMin));
                    }
                }

                // for (int i = ranges.size() - 1 ; i >= 0; i--) {
                //     Interval e = ranges.get(i);
                //     int eMin = e.min();
                //     int eMax = e.max();

                //     if (temp.getSize() > 0 && temp.max() <= eMin)
                //      	temp.unionAdapt(e);
                //     else
                // 	temp.unionAdapt(eMin, eMax);  // need to check correctness of union
                //                                       //and not only add intervals at the end
                //                                       // as in above cases
                // }
            } else { // First domain not singleton and not IntervalDomain

                List<Interval> ranges = new ArrayList<Interval>();

                int sumMin = sum - lMax + d2.max();
                int sumMax = sum - lMin + d2.min();

                for (IntervalEnumeration e1 = d1.intervalEnumeration(); e1.hasMoreElements(); ) {

                    Interval i1 = e1.nextElement();
                    int i1min = i1.min(), i1max = i1.max();

                    for (IntervalEnumeration e2 = d2.intervalEnumeration(); e2.hasMoreElements(); ) {
                        Interval i2 = e2.nextElement();
                        int eMin = i2.min();
                        int eMax = i2.max();

                        if (!(eMin > sumMax || eMax < sumMin))
                            ranges.add(new Interval(i1min - eMax, i1max - eMin));
                    }
                }

                for (int i = ranges.size() - 1; i >= 0; i--)
                    temp.unionAdapt(ranges.get(i).min(), ranges.get(i).max());  // need to check correctness of union
                //and not only add intervals at the end
                // as in above cases
            }

        // System.out.println ("result- = " + temp);

        return temp;

    }


    void checkForOverflow() {

        int sumMin = 0, sumMax = 0;
        for (int i = 0; i < list.length; i++) {
            int n1 = Math.multiplyExact(list[i].min(), weights[i]);
            int n2 = Math.multiplyExact(list[i].max(), weights[i]);

            if (n1 <= n2) {
                sumMin = Math.addExact(sumMin, n1);
                sumMax = Math.addExact(sumMax, n2);
            } else {
                sumMin = Math.addExact(sumMin, n2);
                sumMax = Math.addExact(sumMax, n1);
            }
        }
    }

}
