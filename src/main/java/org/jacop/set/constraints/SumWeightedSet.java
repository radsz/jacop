/*
 * SumWeightedSet.java
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

package org.jacop.set.constraints;

import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.*;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * It computes a weighted sum of the elements in the domain of the given set variable.
 * The sum must be equal to the specified sum variable.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */

public class SumWeightedSet extends Constraint implements SatisfiedPresent {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * A set variable a whose elements contribute with their weight to the sum.
     */
    public SetVar a;

    /**
     * It specifies the list of allowed elements and helps to connect the weight
     * to the element.
     */
    // public int[] elements;

    /**
     * It specifies a weight for every element of the allowed element in the
     * domain of set variable a.
     */
    // public int[] weights;

    /**
     * Integer variable containing the total weight of all elements within a set variable a.
     */
    public IntVar totalWeight;

    /**
     * It specifies if the costs of elements are increasing given the lexical order of the elements.
     */
    boolean increasingCosts;

    /**
     * It provides a quick access to the weights of given elements of the set.
     */
    Map<Integer, Integer> elementWeights;

    /**
     * It constructs a weighted set sum constraint.
     *
     * @param a           a set variable for which the weighted sum of its element is computed.
     * @param elements    it specifies the elements which are allowed and for which the weight is specified.
     * @param weights     the weight for each element present in a.lub().
     * @param totalWeight an integer variable equal to the total weight of the elements in set variable a.
     */
    public SumWeightedSet(SetVar a, int[] elements, int[] weights, IntVar totalWeight) {

        checkInputForNullness(new String[] {"a", "elements", "weights", "totalWeight"},
            new Object[][] {{a}, {elements}, {weights}, {totalWeight}});

        this.numberId = idNumber.incrementAndGet();

        this.totalWeight = totalWeight;
        this.a = a;
        // this.weights = Arrays.copyOf(weights, weights.length);
        // this.elements = Arrays.copyOf(elements, elements.length);

        this.increasingCosts = true;
        for (int i = 0; i < weights.length - 1 && this.increasingCosts; i++)
            if (weights[i] > weights[i + 1])
                this.increasingCosts = false;

        elementWeights = new HashMap<Integer, Integer>(weights.length);
        ValueEnumeration enumer = a.domain.lub().valueEnumeration();
        int i = 0;

        while (enumer.hasMoreElements())
            elementWeights.put(enumer.nextElement(), weights[i++]);

        setScope(a, totalWeight);
    }

    /**
     * It constructs a weighted set sum constraint. This constructor assumes that every element
     * within a set variable has a weight equal to its value.
     *
     * @param a           set variable being used in weighted set constraint.
     * @param totalWeight integer variable containing information about total weight of the elements in set variable a.
     */
    public SumWeightedSet(SetVar a, IntVar totalWeight) {
        this(a, a.domain.lub().toIntArray(), a.domain.lub().toIntArray(), totalWeight);
    }

    /**
     * It constructs a weighted set sum constraint. This constructor assumes that every element
     * within a set variable has a weight equal to its value.
     *
     * @param a           set variable being used in weighted set constraint.
     * @param weights     it specifies a weight for each possible element of a set variable.
     * @param totalWeight integer variable containing information about total weight of the elements in set variable a.
     */
    public SumWeightedSet(SetVar a, int[] weights, IntVar totalWeight) {
        this(a, a.domain.lub().toIntArray(), weights, totalWeight);
    }

    // FIXME, TODO, Analyse all set constraints fixpoints.

    // FIXME, TODO, implement also cardinality reasoning for increasingCosts = false.
    // For example a simple approach could sort weights and ignore elements being removed from lub.
    // More elaborate approach, sort weights, for each weight keep an element responsible for this weight.
    // before considering weight in any calculation check if that element is still in the lub.
    @Override public void consistency(Store store) {

        /**
         * It specifies the consistency rules for this constraint.
         *
         * totalWeight.inMin( glb.weight )
         * totalWeight.inMax( lub.weight )
         *
         * if any element el in lub \ glb has weight such that
         * glb.weight + el.weight > totalweight.max() then el is removed from lub
         *
         * if any element el in lub \ glb has weight such that
         * lub.weight - el.weight < totalweight.min() then el is included in glb.
         *
         * If cardinality specifies that some additional elements must be in glb
         * then take the smallest weights from potential elements and add to minimalWeight.
         *
         * Similarly, if cardinality specifies that some elements from lub can not be
         * taken then reduce the maximal potential weight by the smallest weight of elements
         * from potential elements.
         *
         */

        while (true) {

            int glbSum = 0;
            int lubSum = 0;

            IntDomain glbA = a.domain.glb();
            IntDomain lubA = a.domain.lub();
            IntDomain potentialEl = lubA.subtract(glbA);

            ValueEnumeration enumer = glbA.valueEnumeration();
            while (enumer.hasMoreElements())
                glbSum += elementWeights.get(enumer.nextElement());

            lubSum = glbSum;

            int noOfRequiredEl = a.domain.card().min() - glbA.getSize();
            int weightOfLastRequiredEl = 0;

            if (increasingCosts)
                if (noOfRequiredEl > 0) {
                    enumer = potentialEl.valueEnumeration();
                    while (noOfRequiredEl > 1) {
                        glbSum += elementWeights.get(enumer.nextElement());
                        noOfRequiredEl--;
                    }
                    weightOfLastRequiredEl = elementWeights.get(enumer.nextElement());
                }

            enumer = potentialEl.valueEnumeration();

            Integer el, weight;
            boolean change = false;
            while (enumer.hasMoreElements()) {

                el = enumer.nextElement();
                weight = elementWeights.get(el);

                if (totalWeight.max() < glbSum + weight) {
                    a.domain.inLUBComplement(store.level, a, el);
                    change = true;
                }
            }

            // inLUB above can change GLB due to cardinality constraints. Need to recompute.
            if (change)
                continue;

            int noOfSkippedEl = a.domain.lub().getSize() - a.domain.card().max();
            int weightOfLastSkippedItem = 0;

            enumer = potentialEl.valueEnumeration();

            while (enumer.hasMoreElements()) {

                el = enumer.nextElement();
                weight = elementWeights.get(el);

                if (increasingCosts)
                    if (noOfSkippedEl == 0)
                        lubSum += weight;
                    else {
                        if (noOfSkippedEl == 1)
                            weightOfLastSkippedItem = weight;
                        noOfSkippedEl--;
                    }
                else
                    lubSum += weight;
            }

            enumer = potentialEl.valueEnumeration();
            while (enumer.hasMoreElements()) {

                el = enumer.nextElement();
                weight = elementWeights.get(el);

                if (totalWeight.min() > lubSum + weightOfLastSkippedItem - weight) {
                    a.domain.inGLB(store.level, a, el);
                    change = true;
                }
            }

            // inGLB above can change LUB due to cardinality constraints. Need to recompute.
            if (change)
                continue;

            totalWeight.domain.in(store.level, totalWeight, glbSum + weightOfLastRequiredEl, lubSum + weightOfLastRequiredEl);

            return;
        }

    }

    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        if (var == this.a)
            return SetDomain.ANY;
        else
            return IntDomain.ANY;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        throw new IllegalStateException("Not implemented as more precise version exists.");
    }

    @Override public boolean satisfied() {

        if (!grounded())
            return false;

        ValueEnumeration enumer = a.domain.glb().valueEnumeration();
        int sum = 0;
        while (enumer.hasMoreElements())
            sum += elementWeights.get(enumer.nextElement());
        return totalWeight.value() == sum;

    }

    @Override public String toString() {

        StringBuffer ret = new StringBuffer(id());

        ret.append(" : SumWeightedSet(" + a + ", < ");
        for (Map.Entry<Integer, Integer> entries : elementWeights.entrySet()) {
            int el = entries.getKey();
            int weight = entries.getValue();
            ret.append("<" + el + "," + weight + "> ");
        }
        ret.append(">, ");
        if (totalWeight.singleton()) {
            ret.append(totalWeight.min() + " )");
            return ret.toString();
        } else {
            ret.append(totalWeight.dom() + " )");
            return ret.toString();
        }
    }

}
