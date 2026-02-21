/*
 * SumWeightedSet.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
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

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It computes a weighted sum of the elements in the domain of the given set variable. The sum must
 * be equal to the specified sum variable.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class SumWeightedSet extends Constraint implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** A set variable a whose elements contribute with their weight to the sum. */
  private final SetVar a;

  /** Integer variable containing the total weight of all elements within a set variable a. */
  private final IntVar totalWeight;

  /** It provides a quick access to the weights of given elements of the set. */
  final Map<Integer, Integer> elementWeights;

  /**
   * It specifies if the costs of elements are increasing given the lexical order of the elements.
   */
  boolean increasingCosts;

  /**
   * It constructs a weighted set sum constraint.
   *
   * @param a a set variable for which the weighted sum of its element is computed.
   * @param elements it specifies the elements which are allowed and for which the weight is
   *     specified.
   * @param weights the weight for each element present in a.lub().
   * @param totalWeight an integer variable equal to the total weight of the elements in set
   *     variable a.
   */
  public SumWeightedSet(SetVar a, int[] elements, int[] weights, IntVar totalWeight) {

    checkInputForNullness(
        new String[] {"a", "elements", "weights", "totalWeight"},
        new Object[][] {{a}, {elements}, {weights}, {totalWeight}});

    this.numberId = idNumber.incrementAndGet();

    this.totalWeight = totalWeight;
    this.a = a;

    this.increasingCosts = true;
    for (int i = 0; i < weights.length - 1; i++) {
      if (weights[i] > weights[i + 1]) {
        this.increasingCosts = false;
        break;
      }
    }

    elementWeights = new HashMap<>(weights.length);
    ValueEnumeration enumer = a.domain.lub().valueEnumeration();
    int i = 0;

    while (enumer.hasMoreElements()) {
      elementWeights.put(enumer.nextElement(), weights[i++]);
    }

    setScope(a, totalWeight);
  }

  /**
   * It constructs a weighted set sum constraint. This constructor assumes that every element within
   * a set variable has a weight equal to its value.
   *
   * @param a set variable being used in weighted set constraint.
   * @param totalWeight integer variable containing information about total weight of the elements
   *     in set variable a.
   */
  public SumWeightedSet(SetVar a, IntVar totalWeight) {
    this(a, a.domain.lub().toIntArray(), a.domain.lub().toIntArray(), totalWeight);
  }

  /**
   * It constructs a weighted set sum constraint. This constructor assumes that every element within
   * a set variable has a weight equal to its value.
   *
   * @param a set variable being used in weighted set constraint.
   * @param weights it specifies a weight for each possible element of a set variable.
   * @param totalWeight integer variable containing information about total weight of the elements
   *     in set variable a.
   */
  public SumWeightedSet(SetVar a, int[] weights, IntVar totalWeight) {
    this(a, a.domain.lub().toIntArray(), weights, totalWeight);
  }

  @Override
  public void consistency(Store store) {

    while (true) {
      IntDomain glbA = a.domain.glb();
      IntDomain lubA = a.domain.lub();
      IntDomain potentialEl = lubA.subtract(glbA);

      int glbSum = computeGlbSum(glbA, potentialEl);
      int weightOfLastRequiredEl = computeWeightOfLastRequiredEl(potentialEl);

      if (pruneLubByWeight(store, potentialEl, glbSum)) {
        continue;
      }

      int[] lubResult = computeLubSum(potentialEl);
      int lubSum = lubResult[0];
      int weightOfLastSkippedItem = lubResult[1];

      if (pruneGlbByWeight(store, potentialEl, lubSum, weightOfLastSkippedItem)) {
        continue;
      }

      totalWeight.domain.in(
          store.level,
          totalWeight,
          glbSum + weightOfLastRequiredEl,
          lubSum + weightOfLastRequiredEl);

      return;
    }
  }

  private int computeGlbSum(IntDomain glbA, IntDomain potentialEl) {
    int glbSum = 0;
    ValueEnumeration enumer = glbA.valueEnumeration();
    while (enumer.hasMoreElements()) {
      glbSum += elementWeights.get(enumer.nextElement());
    }

    int noOfRequiredEl = a.domain.card().min() - glbA.getSize();
    if (increasingCosts && noOfRequiredEl > 0) {
      enumer = potentialEl.valueEnumeration();
      while (noOfRequiredEl > 1) {
        glbSum += elementWeights.get(enumer.nextElement());
        noOfRequiredEl--;
      }
    }
    return glbSum;
  }

  private int computeWeightOfLastRequiredEl(IntDomain potentialEl) {
    int weightOfLastRequiredEl = 0;
    int noOfRequiredEl = a.domain.card().min() - a.domain.glb().getSize();
    if (increasingCosts && noOfRequiredEl > 0) {
      ValueEnumeration enumer = potentialEl.valueEnumeration();
      for (int i = 0; i < noOfRequiredEl - 1 && enumer.hasMoreElements(); i++) {
        enumer.nextElement();
      }
      if (enumer.hasMoreElements()) {
        weightOfLastRequiredEl = elementWeights.get(enumer.nextElement());
      }
    }
    return weightOfLastRequiredEl;
  }

  /** Returns true if LUB was pruned (caller should continue the fixpoint loop). */
  private boolean pruneLubByWeight(Store store, IntDomain potentialEl, int glbSum) {
    boolean change = false;
    ValueEnumeration enumer = potentialEl.valueEnumeration();
    while (enumer.hasMoreElements()) {
      int el = enumer.nextElement();
      int weight = elementWeights.get(el);
      if (totalWeight.max() < glbSum + weight) {
        a.domain.inLubComplement(store.level, a, el);
        change = true;
      }
    }
    return change;
  }

  /** Returns {lubSum, weightOfLastSkippedItem}. */
  private int[] computeLubSum(IntDomain potentialEl) {
    int glbSum = 0;
    ValueEnumeration enumer = a.domain.glb().valueEnumeration();
    while (enumer.hasMoreElements()) {
      glbSum += elementWeights.get(enumer.nextElement());
    }
    int lubSum = glbSum;
    int noOfSkippedEl = a.domain.lub().getSize() - a.domain.card().max();
    int weightOfLastSkippedItem = 0;

    enumer = potentialEl.valueEnumeration();
    while (enumer.hasMoreElements()) {
      int el = enumer.nextElement();
      int weight = elementWeights.get(el);
      if (increasingCosts) {
        if (noOfSkippedEl == 0) {
          lubSum += weight;
        } else {
          if (noOfSkippedEl == 1) {
            weightOfLastSkippedItem = weight;
          }
          noOfSkippedEl--;
        }
      } else {
        lubSum += weight;
      }
    }
    return new int[] {lubSum, weightOfLastSkippedItem};
  }

  /** Returns true if GLB was extended (caller should continue the fixpoint loop). */
  private boolean pruneGlbByWeight(
      Store store, IntDomain potentialEl, int lubSum, int weightOfLastSkippedItem) {
    boolean change = false;
    ValueEnumeration enumer = potentialEl.valueEnumeration();
    while (enumer.hasMoreElements()) {
      int el = enumer.nextElement();
      int weight = elementWeights.get(el);
      if (totalWeight.min() > lubSum + weightOfLastSkippedItem - weight) {
        a.domain.inGlb(store.level, a, el);
        change = true;
      }
    }
    return change;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {

    // If consistency function mode
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }
    if (v == this.a) {
      return SetDomain.ANY;
    } else {
      return IntDomain.ANY;
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    throw new IllegalStateException("Not implemented as more precise version exists.");
  }

  @Override
  public boolean satisfied() {

    if (!grounded()) {
      return false;
    }

    ValueEnumeration enumer = a.domain.glb().valueEnumeration();
    int sum = 0;
    while (enumer.hasMoreElements()) {
      sum += elementWeights.get(enumer.nextElement());
    }
    return totalWeight.value() == sum;
  }

  @Override
  public String toString() {

    StringBuilder ret = new StringBuilder(id());

    ret.append(" : SumWeightedSet(").append(a).append(", < ");
    for (Map.Entry<Integer, Integer> entries : elementWeights.entrySet()) {
      int el = entries.getKey();
      int weight = entries.getValue();
      ret.append("<").append(el).append(",").append(weight).append("> ");
    }
    ret.append(">, ");
    if (totalWeight.singleton()) {
      ret.append(totalWeight.min()).append(" )");
      return ret.toString();
    } else {
      ret.append(totalWeight.dom()).append(" )");
      return ret.toString();
    }
  }
}
