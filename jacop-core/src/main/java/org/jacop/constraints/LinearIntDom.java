/*
 * LinearIntDom.java
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * LinearIntDom constraint implements the weighted summation over several variables.
 *
 * <p>sum(i in 1..N)(ai*xi) = b
 *
 * <p>It provides the weighted sum from all variables on the list. The weights are integers. Domain
 * consistency is used.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class LinearIntDom extends LinearInt {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** Limit on the product of sizes of domains when domain consistency is carried out. */
  private static final double LIMIT_DOMAIN_PRUNING = 1e+7;

  /** Defines support (valid values) for each variable. */
  IntervalDomain[] support;

  /** Collects support (valid assignments) for variables. */
  int[] assignments;

  // ================ constructors ===================

  /**
   * It constructs the constraint LinearIntDom.
   *
   * @param list variables which are being multiplied by weights.
   * @param weights weight for each variable.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "{@literal !=}"
   * @param sum the sum of weighted variables.
   */
  public LinearIntDom(IntVar[] list, int[] weights, String rel, int sum) {
    commonInitialization(list[0].getStore(), list, weights, rel, sum);
    numberId = idNumber.incrementAndGet();
    queueIndex = 4;
  }

  /**
   * It constructs the constraint LinearIntDom.
   *
   * @param list variables which are being multiplied by weights.
   * @param weights weight for each variable.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "{@literal !=}"
   * @param sum variable containing the sum of weighted variables.
   */
  public LinearIntDom(IntVar[] list, int[] weights, String rel, IntVar sum) {
    commonInitialization(
        sum.getStore(),
        Stream.concat(Arrays.stream(list), Stream.of(sum)).toArray(IntVar[]::new),
        IntStream.concat(Arrays.stream(weights), IntStream.of(-1)).toArray(),
        rel,
        0);
    numberId = idNumber.incrementAndGet();
    queueIndex = 4;
  }

  /**
   * It constructs the constraint LinearIntDom.
   *
   * @param variables variables which are being multiplied by weights.
   * @param weights weight for each variable.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "{@literal !=}"
   * @param sum variable containing the sum of weighted variables.
   */
  public LinearIntDom(
      List<? extends IntVar> variables, List<Integer> weights, String rel, int sum) {
    commonInitialization(
        variables.getFirst().getStore(),
        variables.toArray(new IntVar[0]),
        weights.stream().mapToInt(i -> i).toArray(),
        rel,
        sum);
    numberId = idNumber.incrementAndGet();
    queueIndex = 4;
  }

  @Override
  public void consistency(Store store) {
    propagate(relationType);
  }

  @Override
  public void notConsistency(Store store) {
    propagate(NEG_REL[relationType]);
  }

  /**
   * Propagates the constraint for the specified relation type.
   *
   * @param rel the relation type for propagation.
   */
  public void propagate(int rel) {

    switch (rel) {
      case EQ:
        if (domainSize() < LIMIT_DOMAIN_PRUNING) {
          computeInit();
          pruneEq(); // domain consistency
        } else {
          // bound consistency
          super.propagate(rel);
        }

        break;

      case NE:
        if (domainSize() < LIMIT_DOMAIN_PRUNING) {
          computeInit();
          pruneNeq();

          computeInit();

          if (!reified && (sumMin > b || sumMax < b)) {
            removeConstraint();
          }
        } else {
          super.propagate(rel);
        }

        break;

      default:
        log.error("Not implemented relation in LinearIntDom; implemented == and != only.");
        break;
    }
  }

  double domainSize() {

    double s = 1;
    for (int i = 0; i < l; i++) {
      s *= x[i].domain.getSize();
    }

    return s;
  }

  void pruneEq() {

    assignments = new int[l];
    support = new IntervalDomain[l];

    findSupport(0, 0L);

    for (int i = 0; i < l; i++) {
      if (support[i] == null) {
        throw Store.failException;
      } else {
        x[i].domain.in(store.level, x[i], support[i]);
      }
    }
  }

  void pruneNeq() {

    assignments = new int[l];
    support = new IntervalDomain[l];

    findSupport(0, 0L);

    for (int i = 0; i < l; i++) {
      if (support[i] == null) {
        removeConstraint();
      } else if (support[i].singleton()) {
        x[i].domain.inComplement(store.level, x[i], support[i].value());
      }
    }
  }

  void findSupport(int index, long sum) {

    findSupportPositive(index, sum);
  }

  /**
   * Finds support for variables in the linear constraint.
   *
   * @param positive true if processing positive coefficients, false for negative coefficients
   * @param index current variable index
   * @param partialSum accumulated sum so far
   */
  void findSupport(boolean positive, int index, long partialSum) {

    int newIndex = index + 1;

    if (index == l - 1) {

      long element = b - partialSum;
      long val = element / a[index];
      long rest = element % a[index];
      int valInt = (int) val;
      if (rest == 0 && valInt == val && x[index].domain.contains(valInt)) {
        assignments[index] = valInt;
        storeAssignmentsToSupport();
      }
      return;
    }

    IntDomain currentDom = x[index].dom();
    long w = a[index];

    // Bounds calculation differs based on positive/negative phase
    long lb;
    long ub;
    if (positive) {
      lb = b - sumMax + currentDom.max() * w;
      ub = b - sumMin + currentDom.min() * w;
    } else {
      lb = b - sumMax + currentDom.min() * w;
      ub = b - sumMin + currentDom.max() * w;
    }

    if (currentDom.domainId() == IntDomain.INTERVAL_DOMAIN_ID) {
      processIntervalDomain(currentDom, index, newIndex, w, lb, ub, partialSum, positive);
    } else {
      processValueEnumeration(currentDom, index, newIndex, w, lb, ub, partialSum, positive);
    }
  }

  void findSupportPositive(int index, long partialSum) {
    findSupport(true, index, partialSum);
  }

  void findSupportNegative(int index, long partialSum) {
    findSupport(false, index, partialSum);
  }

  private void storeAssignmentsToSupport() {
    for (int i = 0; i < l; i++) {
      int a = assignments[i];
      if (support[i] == null) {
        support[i] = new IntervalDomain(a, a);
      } else if (support[i].max() < a) {
        support[i].addLastElement(a);
      } else if (support[i].max() > a) {
        support[i].unionAdapt(a, a);
      }
    }
  }

  /**
   * Processes interval domain by iterating over intervals and their values.
   *
   * @param currentDom the current domain
   * @param index current variable index
   * @param newIndex next variable index
   * @param w weight coefficient
   * @param lb lower bound for element value
   * @param ub upper bound for element value
   * @param partialSum accumulated sum so far
   * @param positive true if processing positive coefficients
   */
  private void processIntervalDomain(
      IntDomain currentDom,
      int index,
      int newIndex,
      long w,
      long lb,
      long ub,
      long partialSum,
      boolean positive) {
    int n = ((IntervalDomain) currentDom).size;

    outerloop:
    for (int k = 0; k < n; k++) {
      Interval e = ((IntervalDomain) currentDom).intervals[k];
      int eMin = e.min();
      int eMax = e.max();

      for (int element = eMin; element <= eMax; element++) {
        if (processElement(element, w, lb, ub, partialSum, positive, index, newIndex)) {
          break outerloop;
        }
      }
    }
  }

  /**
   * Processes domain using value enumeration.
   *
   * @param currentDom the current domain
   * @param index current variable index
   * @param newIndex next variable index
   * @param w weight coefficient
   * @param lb lower bound for element value
   * @param ub upper bound for element value
   * @param partialSum accumulated sum so far
   * @param positive true if processing positive coefficients
   */
  private void processValueEnumeration(
      IntDomain currentDom,
      int index,
      int newIndex,
      long w,
      long lb,
      long ub,
      long partialSum,
      boolean positive) {
    for (ValueEnumeration val = currentDom.valueEnumeration(); val.hasMoreElements(); ) {
      int element = val.nextElement();
      if (processElement(element, w, lb, ub, partialSum, positive, index, newIndex)) {
        break;
      }
    }
  }

  /**
   * Processes a single element value, checking bounds and recursing if valid.
   *
   * @param element the element value to process
   * @param w weight coefficient
   * @param lb lower bound for element value
   * @param ub upper bound for element value
   * @param partialSum accumulated sum so far
   * @param positive true if processing positive coefficients
   * @param index current variable index
   * @param newIndex next variable index
   * @return true if should break the loop, false otherwise
   */
  private boolean processElement(
      int element,
      long w,
      long lb,
      long ub,
      long partialSum,
      boolean positive,
      int index,
      int newIndex) {
    long elementValue = element * w;
    // Loop control differs based on positive/negative phase
    if (positive) {
      if (elementValue < lb) {
        return false; // continue
      } else if (elementValue > ub) {
        return true; // break
      }
    } else {
      if (elementValue < lb) {
        return true; // break
      } else if (elementValue > ub) {
        return false; // continue
      }
    }

    long newPartialSum = partialSum + elementValue;
    assignments[index] = element;

    // Recursion differs based on positive/negative phase
    if (!positive) {
      findSupport(false, newIndex, newPartialSum);
    } else if (newIndex < pos) {
      findSupport(true, newIndex, newPartialSum);
    } else {
      findSupport(false, newIndex, newPartialSum);
    }

    return false; // continue
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : LinearIntDom( [ ");

    for (int i = 0; i < x.length; i++) {
      result.append(x[i]);
      if (i < x.length - 1) {
        result.append(", ");
      }
    }
    result.append("], [");

    for (int i = 0; i < a.length; i++) {
      result.append(a[i]);
      if (i < a.length - 1) {
        result.append(", ");
      }
    }

    result.append("], ").append(rel2String()).append(", ").append(b).append(" )");

    return result.toString();
  }
}
