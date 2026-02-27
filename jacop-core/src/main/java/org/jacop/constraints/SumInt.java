/*
 * SumInt.java
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
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * SumInt constraint implements the summation over several variables.
 *
 * <p>sum(i in 1..N)(xi) = sum
 *
 * <p>It provides the sum from all variables on the list.
 *
 * <p>This implementaiton is based on "Bounds Consistency Techniques for Long Linear Constraints" by
 * Warwick Harvey and Joachim Schimpf
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class SumInt extends AbstractSum {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies "variability" of each variable. */
  final long[] I;

  /** It specifies sum of lower bounds (min values) and sum of upper bounds (max values). */
  long sumXmin;

  long sumXmax;

  /**
   * Constructs a SumInt constraint with the specified relation.
   *
   * @param list variables which are being multiplied by weights.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "{@literal !=}"
   * @param sum variable containing the sum of weighted variables.
   */
  public SumInt(IntVar[] list, String rel, IntVar sum) {
    super(parseRelation(rel), sum.getStore(), Arrays.copyOf(list, list.length), sum, list.length);
    checkInputForNullness(new String[] {"list", "rel", "sum"}, new Object[][] {list, {rel}, {sum}});

    numberId = idNumber.incrementAndGet();

    this.I = new long[l];

    if (l <= 2) {
      queueIndex = 0;
    } else {
      queueIndex = 1;
    }

    setScope(Stream.concat(Arrays.stream(list), Stream.of(sum)));
  }

  /**
   * It constructs the constraint SumInt.
   *
   * @param variables variables which are being multiplied by weights.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "{@literal !=}"
   * @param sum variable containing the sum of weighted variables.
   */
  public SumInt(List<? extends IntVar> variables, String rel, IntVar sum) {
    this(variables.toArray(IntVar[]::new), rel, sum);
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
   * Propagates bounds consistency for the given relation type.
   *
   * @param rel the relation type code to propagate.
   */
  public void propagate(int rel) {
    computeInit();
    do {
      store.propagationHasOccurred = false;
      applyRelation(rel);
    } while (store.propagationHasOccurred);
  }

  private void applyRelation(int rel) {
    switch (rel) {
      case EQ:
        pruneLtEq(0L);
        pruneGtEq(0L);
        break;
      case LE:
        doRelationLe();
        break;
      case LT:
        doRelationLt();
        break;
      case NE:
        doRelationNe();
        break;
      case GT:
        doRelationGt();
        break;
      case GE:
        doRelationGe();
        break;
      default:
        throw new RuntimeException("Internal error in " + getClass().getName());
    }
  }

  private void doRelationLe() {
    pruneLtEq(0L);
    if (!reified && sumXmax <= sum.min()) {
      removeConstraint();
    }
  }

  private void doRelationLt() {
    pruneLtEq(1L);
    if (!reified && sumXmax < sum.min()) {
      removeConstraint();
    }
  }

  private void doRelationNe() {
    pruneNeq();
    if (!reified && (sumXmin > sum.max() || sumXmax < sum.min())) {
      removeConstraint();
    }
  }

  private void doRelationGt() {
    pruneGtEq(1L);
    if (!reified && sumXmin > sum.max()) {
      removeConstraint();
    }
  }

  private void doRelationGe() {
    pruneGtEq(0L);
    if (!reified && sumXmin >= sum.max()) {
      removeConstraint();
    }
  }

  private void computeInit() {
    long f = 0;
    long e = 0;
    long min;
    long max;

    for (int i = 0; i < l; i++) {
      IntDomain xd = x[i].dom();
      min = xd.min();
      max = xd.max();
      f += min;
      e += max;
      I[i] = max - min;
    }

    sumXmin = f;
    sumXmax = e;
  }

  private void pruneLtEq(long b) {
    pruneDirection(true, b);
  }

  private void pruneGtEq(long b) {
    pruneDirection(false, b);
  }

  /**
   * Prunes variables based on the direction of the constraint.
   *
   * @param isLtEq true for less-than-or-equal pruning, false for greater-than-or-equal pruning
   * @param b the offset value
   */
  private void pruneDirection(boolean isLtEq, long b) {
    if (isLtEq) {
      sum.domain.inMin(store.level, sum, long2int(sumXmin + b));
    } else {
      sum.domain.inMax(store.level, sum, long2int(sumXmax - b));
    }
    long sumBound = isLtEq ? sum.max() : sum.min();
    for (int i = 0; i < l; i++) {
      pruneVariableForDirection(i, isLtEq, b, sumBound);
    }
  }

  private void pruneVariableForDirection(int i, boolean isLtEq, long b, long sumBound) {
    boolean condition = isLtEq ? I[i] > (sumBound - sumXmin - b) : I[i] > -(sumBound - sumXmax + b);
    if (!condition) {
      return;
    }
    if (isLtEq) {
      long min = x[i].min();
      long max = min + I[i];
      if (pruneMax(x[i], sumBound - sumXmin + min - b)) {
        long newMax = x[i].max();
        sumXmax -= max - newMax;
        I[i] = newMax - min;
      }
    } else {
      long max = x[i].max();
      long min = max - I[i];
      if (pruneMin(x[i], sumBound - sumXmax + max + b)) {
        long newMin = x[i].min();
        sumXmin += newMin - min;
        I[i] = max - newMin;
      }
    }
  }

  private void pruneNeq() {

    if (sumXmin == sumXmax) {
      sum.domain.inComplement(store.level, sum, long2int(sumXmin));
    }
    store.propagationHasOccurred = false;

    long min;
    long max;

    for (int i = 0; i < l; i++) {
      min = x[i].min();
      max = min + I[i];

      if (pruneNe(x[i], (long) sum.min() - sumXmax + max, sum.max() - sumXmin + min)) {
        long newMin = x[i].min();
        long newMax = x[i].max();
        sumXmin += newMin - min;
        sumXmax += newMax - max;
        I[i] = newMax - newMin;
      }
    }
  }

  private boolean pruneMin(IntVar x, long min) {
    if (min > (long) x.min()) {
      x.domain.inMin(store.level, x, long2int(min));
      return true;
    } else {
      return false;
    }
  }

  private boolean pruneMax(IntVar x, long max) {
    if (max < (long) x.max()) {
      x.domain.inMax(store.level, x, long2int(max));
      return true;
    } else {
      return false;
    }
  }

  private boolean pruneNe(IntVar x, long min, long max) {

    if (min == max) {
      boolean boundsChanged = min == (long) x.min() || max == (long) x.max();

      x.domain.inComplement(store.level, x, long2int(min));

      return boundsChanged;
    }

    return false;
  }

  /**
   * Computes the minimum and maximum sum bounds from all variables.
   *
   * @return a two-element array where [0] is sMin and [1] is sMax
   */
  private long[] computeSumBounds() {
    long sMin = 0;
    long sMax = 0;

    for (int i = 0; i < l; i++) {
      sMin += x[i].min();
      sMax += x[i].max();
    }

    return new long[] {sMin, sMax};
  }

  /**
   * Checks whether the equality relation is satisfied.
   *
   * @return true if the sum of variables equals the sum variable.
   */
  public boolean satisfiedEq() {

    long[] bounds = computeSumBounds();
    long sMin = bounds[0];
    long sMax = bounds[1];

    return sMax <= (long) sum.min()
        && sMin >= (long) sum.max(); // sMin == sMax && sMin == sum.min() && sMin == sum.max();
  }

  /**
   * Checks whether the not-equal relation is satisfied.
   *
   * @return true if the sum of variables is guaranteed to differ from the sum variable.
   */
  public boolean satisfiedNeq() {

    long[] bounds = computeSumBounds();
    long sMin = bounds[0];
    long sMax = bounds[1];

    return sMin > (long) sum.max() || sMax < (long) sum.min();
  }

  /**
   * Computes the sum of variable bounds in the specified direction.
   *
   * @param useMax true to compute sum of max values, false to compute sum of min values
   * @return the computed sum
   */
  private long computeSumBound(boolean useMax) {
    long sumBound = 0;

    for (int i = 0; i < l; i++) {
      sumBound += useMax ? x[i].max() : x[i].min();
    }

    return sumBound;
  }

  /**
   * Checks whether the less-than or equal relation is satisfied, with an optional offset.
   *
   * @param b the offset (0 for less-or-equal, 1 for strictly less-than).
   * @return true if the relation is satisfied.
   */
  public boolean satisfiedLtEq(int b) {

    long sMax = computeSumBound(true);

    return sMax <= (long) sum.min() - b;
  }

  /**
   * Checks whether the greater-than or equal relation is satisfied, with an optional offset.
   *
   * @param b the offset (0 for greater-or-equal, 1 for strictly greater-than).
   * @return true if the relation is satisfied.
   */
  public boolean satisfiedGtEq(int b) {

    long sMin = computeSumBound(false);

    return sMin >= (long) sum.max() + b;
  }

  @Override
  public boolean satisfied() {

    return entailed(relationType);
  }

  @Override
  public boolean notSatisfied() {

    return entailed(NEG_REL[relationType]);
  }

  private boolean entailed(int rel) {

    return switch (rel) {
      case EQ -> satisfiedEq();
      case LE -> satisfiedLtEq(0);
      case LT -> satisfiedLtEq(1);
      case NE -> satisfiedNeq();
      case GT -> satisfiedGtEq(1);
      case GE -> satisfiedGtEq(0);
      default -> false;
    };
  }

  @Override
  public String toString() {
    return toStringHelper("SumInt");
  }
}
