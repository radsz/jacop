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
import org.jacop.core.Var;

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
public class SumInt extends PrimitiveConstraint {

  /** Defines relations. */
  static final byte eq = 0;

  static final byte le = 1;
  static final byte lt = 2;
  static final byte ne = 3;
  static final byte gt = 4;
  static final byte ge = 5;

  /** Defines negated relations. */
  static final byte[] negRel = {
    ne, // eq=0,
    gt, // le=1,
    ge, // lt=2,
    eq, // ne=3,
    le, // gt=4,
    lt // ge=5;
  };

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies what relations is used by this constraint. */
  public final byte relationType;

  final Store store;

  /** It specifies a list of variables being summed. */
  final IntVar[] x;

  /** It specifies variable for the overall sum. */
  final IntVar sum;

  /** It specifies the number of variables. */
  final int l;

  /** It specifies "variability" of each variable. */
  final long[] I;

  boolean reified = true;

  /** It specifies sum of lower bounds (min values) and sum of upper bounds (max values). */
  long sumXmin;

  long sumXmax;

  int guideValue;

  /**
   * Constructs a SumInt constraint with the specified relation.
   *
   * @param list variables which are being multiplied by weights.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "{@literal !=}"
   * @param sum variable containing the sum of weighted variables.
   */
  public SumInt(IntVar[] list, String rel, IntVar sum) {
    checkInputForNullness(new String[] {"list", "rel", "sum"}, new Object[][] {list, {rel}, {sum}});

    this.relationType = relation(rel);
    this.store = sum.getStore();
    this.sum = sum;

    x = Arrays.copyOf(list, list.length);
    numberId = idNumber.incrementAndGet();

    this.l = x.length;
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
    this(variables.toArray(new IntVar[0]), rel, sum);
  }

  @Override
  public void consistency(Store store) {
    propagate(relationType);
  }

  @Override
  public void notConsistency(Store store) {
    propagate(negRel[relationType]);
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

      switch (rel) {
        case eq:
          pruneLtEq(0L);
          pruneGtEq(0L);

          break;

        case le:
          pruneLtEq(0L);

          if (!reified && sumXmax <= sum.min()) {
            removeConstraint();
          }
          break;

        case lt:
          pruneLtEq(1L);

          if (!reified && sumXmax < sum.min()) {
            removeConstraint();
          }
          break;
        case ne:
          pruneNeq();

          if (!reified && (sumXmin > sum.max() || sumXmax < sum.min())) {
            removeConstraint();
          }
          break;
        case gt:
          pruneGtEq(1L);

          if (!reified && sumXmin > sum.max()) {
            removeConstraint();
          }
          break;
        case ge:
          pruneGtEq(0L);

          if (!reified && sumXmin >= sum.max()) {
            removeConstraint();
          }

          break;
        default:
          throw new RuntimeException("Internal error in " + getClass().getName());
      }

    } while (store.propagationHasOccurred);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void impose(Store store) {

    if (x == null) {
      return;
    }

    reified = false;

    super.impose(store);
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

    sum.domain.inMin(store.level, sum, long2int(sumXmin + b));

    long min;
    long max;
    long sMax = sum.max();

    for (int i = 0; i < l; i++) {
      if (I[i] > (sMax - sumXmin - b)) {
        min = x[i].min();
        max = min + I[i];
        if (pruneMax(x[i], sMax - sumXmin + min - b)) {
          long newMax = x[i].max();
          sumXmax -= max - newMax;
          I[i] = newMax - min;
        }
      }
    }
  }

  private void pruneGtEq(long b) {

    sum.domain.inMax(store.level, sum, long2int(sumXmax - b));

    long min;
    long max;
    long sMin = sum.min();

    for (int i = 0; i < l; i++) {
      if (I[i] > -(sMin - sumXmax + b)) {
        max = x[i].max();
        min = max - I[i];
        if (pruneMin(x[i], sMin - sumXmax + max + b)) {
          long newMin = x[i].min();
          sumXmin += newMin - min;
          I[i] = max - newMin;
        }
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
   * Checks whether the equality relation is satisfied.
   *
   * @return true if the sum of variables equals the sum variable.
   */
  public boolean satisfiedEq() {

    long sMin = 0;
    long sMax = 0;

    for (int i = 0; i < l; i++) {
      sMin += x[i].min();
      sMax += x[i].max();
    }

    return sMax <= (long) sum.min()
        && sMin >= (long) sum.max(); // sMin == sMax && sMin == sum.min() && sMin == sum.max();
  }

  /**
   * Checks whether the not-equal relation is satisfied.
   *
   * @return true if the sum of variables is guaranteed to differ from the sum variable.
   */
  public boolean satisfiedNeq() {

    long sMax = 0;
    long sMin = 0;

    for (int i = 0; i < l; i++) {
      sMin += x[i].min();
      sMax += x[i].max();
    }

    return sMin > (long) sum.max() || sMax < (long) sum.min();
  }

  /**
   * Checks whether the less-than or equal relation is satisfied, with an optional offset.
   *
   * @param b the offset (0 for less-or-equal, 1 for strictly less-than).
   * @return true if the relation is satisfied.
   */
  public boolean satisfiedLtEq(int b) {

    long sMax = 0;

    for (int i = 0; i < l; i++) {
      sMax += x[i].max();
    }

    return sMax <= (long) sum.min() - b;
  }

  /**
   * Checks whether the greater-than or equal relation is satisfied, with an optional offset.
   *
   * @param b the offset (0 for greater-or-equal, 1 for strictly greater-than).
   * @return true if the relation is satisfied.
   */
  public boolean satisfiedGtEq(int b) {

    long sMin = 0;

    for (int i = 0; i < l; i++) {
      sMin += x[i].min();
    }

    return sMin >= (long) sum.max() + b;
  }

  @Override
  public boolean satisfied() {

    return entailed(relationType);
  }

  @Override
  public boolean notSatisfied() {

    return entailed(negRel[relationType]);
  }

  private boolean entailed(int rel) {

    return switch (rel) {
      case eq -> satisfiedEq();
      case le -> satisfiedLtEq(0);
      case lt -> satisfiedLtEq(1);
      case ne -> satisfiedNeq();
      case gt -> satisfiedGtEq(1);
      case ge -> satisfiedGtEq(0);
      default -> false;
    };
  }

  /**
   * Converts a relation string to its internal byte code representation.
   *
   * @param r the relation string (e.g., "==", "{@literal <}", "{@literal >=}").
   * @return the byte code for the relation.
   */
  public byte relation(String r) {
    switch (r) {
      case "==", "=" -> {
        return eq;
      }
      case "<" -> {
        return lt;
      }
      case "<=", "=<" -> {
        return le;
      }
      case "!=" -> {
        return ne;
      }
      case ">" -> {
        return gt;
      }
      case ">=", "=>" -> {
        return ge;
      }
      default -> {
        log.error("Wrong relation symbol in SumInt constraint {}; assumed ==", r);
        return eq;
      }
    }
  }

  /**
   * Returns the string representation of the current relation type.
   *
   * @return the relation as a string (e.g., "==", "{@literal <}", "{@literal >=}").
   */
  public String rel2String() {
    return switch (relationType) {
      case eq -> "==";
      case lt -> "<";
      case le -> "<=";
      case ne -> "!=";
      case gt -> ">";
      case ge -> ">=";
      default -> "?";
    };
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : SumInt( [ ");

    for (int i = 0; i < l; i++) {
      result.append(x[i]);
      if (i < l - 1) {
        result.append(", ");
      }
    }
    result.append("], ");

    result.append(rel2String()).append(", ").append(sum).append(" )");

    return result.toString();
  }

  @Override
  public Constraint getGuideConstraint() {

    IntVar proposedVariable = (IntVar) getGuideVariable();
    if (proposedVariable != null) {
      return new XeqC(proposedVariable, guideValue);
    } else {
      return null;
    }
  }

  @Override
  public int getGuideValue() {
    return guideValue;
  }

  @Override
  public Var getGuideVariable() {

    int regret = 1;
    Var proposedVariable = null;

    for (IntVar v : x) {

      IntDomain listDom = v.dom();

      if (v.singleton()) {
        continue;
      }

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
}
