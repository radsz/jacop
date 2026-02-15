/*
 * SumBool.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * SumBool constraint implements the summation over several 0/1 variables.
 *
 * <p>sum(i in 1..N)(xi) = sum
 *
 * <p>It provides the sum from all variables on the list.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class SumBool extends AbstractSum {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * Constructs a SumBool constraint over an array of 0/1 variables.
   *
   * @param list variables which are being summed.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "{@literal !=}".
   * @param sum variable containing the sum of the boolean variables.
   */
  public SumBool(IntVar[] list, String rel, IntVar sum) {
    super(
        parseRelation(rel),
        sum.getStore(),
        filterAndOverflowStatic(list),
        sum,
        filterAndOverflowStatic(list).length);
    checkInputForNullness(new String[] {"list", "rel", "sum"}, new Object[][] {list, {rel}, {sum}});
    checkInput(list, l -> l.min() >= 0 && l.max() <= 1, "domain must lie within 0..1 domain");

    numberId = idNumber.incrementAndGet();

    if (l <= 2) {
      queueIndex = 0;
    } else {
      queueIndex = 1;
    }

    setScope(Stream.concat(Stream.of(sum), Arrays.stream(list)));
  }

  /**
   * Constructs a SumBool constraint over a list of 0/1 variables.
   *
   * @param variables variables which are being summed.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "{@literal !=}".
   * @param sum variable containing the sum of the boolean variables.
   */
  public SumBool(List<? extends IntVar> variables, String rel, IntVar sum) {
    this(variables.toArray(new IntVar[0]), rel, sum);
  }

  @Override
  public void consistency(Store store) {
    prune(relationType);
  }

  @Override
  public void notConsistency(Store store) {
    prune(NEG_REL[relationType]);
  }

  private void prune(byte rel) {
    int min = sumMin();
    int max = sumMax();

    switch (rel) {
      case EQ -> pruneEq(min, max);
      case LE -> pruneLe(min, max);
      case LT -> pruneLt(min, max);
      case NE -> pruneNe(min, max);
      case GT -> pruneGt(min, max);
      case GE -> pruneGe(min, max);
      default -> throw new RuntimeException("Internal error in SumBool");
    }
  }

  private int sumMin() {
    int min = 0;
    for (int i = 0; i < l; i++) {
      min += x[i].dom().min();
    }
    return min;
  }

  private int sumMax() {
    int max = 0;
    for (int i = 0; i < l; i++) {
      max += x[i].dom().max();
    }
    return max;
  }

  private void pruneEq(int min, int max) {
    sum.domain.in(store.level, sum, min, max);
    if (!sum.singleton() || min == max) {
      return;
    }
    int sumValue = sum.value();
    if (sumValue == min) {
      forceAllToZero();
    }
    if (sumValue == max) {
      forceAllToOne();
    }
  }

  private void forceAllToZero() {
    for (int i = 0; i < l; i++) {
      if (!x[i].singleton()) {
        x[i].domain.inValue(store.level, x[i], 0);
      }
    }
  }

  private void forceAllToOne() {
    for (int i = 0; i < l; i++) {
      if (!x[i].singleton()) {
        x[i].domain.inValue(store.level, x[i], 1);
      }
    }
  }

  private void pruneLe(int min, int max) {
    sum.domain.inMin(store.level, sum, min);
    if (!reified && max <= sum.min()) {
      removeConstraint();
    }
    if (sum.singleton(min) && min != max) {
      forceAllToZero();
    }
  }

  private void pruneLt(int min, int max) {
    sum.domain.inMin(store.level, sum, min + 1);
    if (!reified && max < sum.min()) {
      removeConstraint();
    }
    if (sum.singleton(min + 1) && min != max) {
      forceAllToZero();
    }
  }

  private void pruneNe(int min, int max) {
    if (min == max) {
      sum.domain.inComplement(store.level, sum, min);
    }
    int sumMin = sum.min() - max;
    int sumMax = sum.max() - min;
    if (sumMax - sumMin == 1) {
      for (int i = 0; i < l; i++) {
        if (!x[i].singleton()) {
          x[i].domain.inComplement(store.level, x[i], sumMin + x[i].max());
        }
      }
    }
  }

  private void pruneGt(int min, int max) {
    sum.domain.inMax(store.level, sum, max - 1);
    if (!reified && min > sum.max()) {
      removeConstraint();
    }
    if (sum.singleton(max - 1) && min != max) {
      forceAllToOne();
    }
  }

  private void pruneGe(int min, int max) {
    sum.domain.inMax(store.level, sum, max);
    if (!reified && min >= sum.max()) {
      removeConstraint();
    }
    if (sum.singleton(max) && min != max) {
      forceAllToOne();
    }
  }

  @Override
  public boolean satisfied() {

    return entailed(relationType);
  }

  @Override
  public boolean notSatisfied() {

    return entailed(NEG_REL[relationType]);
  }

  private boolean entailed(byte rel) {

    int min = sumMin();
    int max = sumMax();

    return switch (rel) {
      case EQ -> sum.singleton(min) && min == max;
      case LT -> max < sum.min();
      case LE -> max <= sum.min();
      case NE -> sum.min() > max || sum.max() < min;
      case GT -> min > sum.max();
      case GE -> min >= sum.max();
      default -> false;
    };
  }

  static IntVar[] filterAndOverflowStatic(IntVar[] x) {

    List<IntVar> ls = new ArrayList<>();

    int sMin = 0;
    int sMax = 0;
    for (IntVar intVar : x) {
      int n1 = intVar.min();
      int n2 = intVar.max();

      sMin = Math.addExact(sMin, n1);
      sMax = Math.addExact(sMax, n2);

      if (intVar.max() != 0) {
        ls.add(intVar);
      }
    }

    return ls.toArray(new IntVar[0]);
  }

  @Override
  public String toString() {
    return toStringHelper("SumBool");
  }
}
