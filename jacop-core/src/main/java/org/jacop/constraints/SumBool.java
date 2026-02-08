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
import org.jacop.core.IntDomain;
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
public class SumBool extends PrimitiveConstraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);
  /*
   * Defines relations
   */
  static final byte eq = 0;
  static final byte le = 1;
  static final byte lt = 2;
  static final byte ne = 3;
  static final byte gt = 4;
  static final byte ge = 5;
  /*
   * Defines negated relations
   */
  static final byte[] negRel = {
    ne, // eq=0,
    gt, // le=1,
    ge, // lt=2,
    eq, // ne=3,
    le, // gt=4,
    lt // ge=5;
  };
  /*
   * It specifies what relations is used by this constraint
   */
  public final byte relationType;
  final Store store;
  /*
   * It specifies a list of variables being summed.
   */
  final IntVar[] x;
  /*
   * It specifies variable for the overall sum.
   */
  final IntVar sum;
  /*
   * It specifies the number of variables.
   */
  final int l;
  boolean reified = true;

  /**
   * Constructs a SumBool constraint over an array of 0/1 variables.
   *
   * @param list variables which are being summed.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "{@literal !=}".
   * @param sum variable containing the sum of the boolean variables.
   */
  public SumBool(IntVar[] list, String rel, IntVar sum) {
    checkInputForNullness(new String[] {"list", "rel", "sum"}, new Object[][] {list, {rel}, {sum}});
    checkInput(list, l -> l.min() >= 0 && l.max() <= 1, "domain must lie within 0..1 domain");

    numberId = idNumber.incrementAndGet();
    this.relationType = relation(rel);
    this.store = sum.getStore();
    this.sum = sum;
    x = filterAndOverflow(list);
    this.l = x.length;

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
    prune(negRel[relationType]);
  }

  private void prune(byte rel) {

    int min = 0;
    int max = 0;

    for (int i = 0; i < l; i++) {
      IntDomain xd = x[i].dom();
      min += xd.min();
      max += xd.max();
    }

    switch (rel) {
      case eq:
        sum.domain.in(store.level, sum, min, max);

        if (sum.singleton() && min != max) {
          int sumValue = sum.value();
          if (sumValue == min) {
            for (int i = 0; i < l; i++) {
              if (!x[i].singleton()) {
                x[i].domain.inValue(store.level, x[i], 0);
              }
            }
          }

          if (sumValue == max) {
            for (int i = 0; i < l; i++) {
              if (!x[i].singleton()) {
                x[i].domain.inValue(store.level, x[i], 1);
              }
            }
          }
        }
        break;
      case le:
        sum.domain.inMin(store.level, sum, min);

        if (!reified && max <= sum.min()) {
          removeConstraint();
        }

        if (sum.singleton(min) && min != max) {

          for (int i = 0; i < l; i++) {
            if (!x[i].singleton()) {
              x[i].domain.inValue(store.level, x[i], 0);
            }
          }
        }
        break;
      case lt:
        sum.domain.inMin(store.level, sum, min + 1);

        if (!reified && max < sum.min()) {
          removeConstraint();
        }

        if (sum.singleton(min + 1) && min != max) {

          for (int i = 0; i < l; i++) {
            if (!x[i].singleton()) {
              x[i].domain.inValue(store.level, x[i], 0);
            }
          }
        }
        break;
      case ne:
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
        break;
      case gt:
        sum.domain.inMax(store.level, sum, max - 1);

        if (!reified && min > sum.max()) {
          removeConstraint();
        }

        if (sum.singleton(max - 1) && min != max) {

          for (int i = 0; i < l; i++) {
            if (!x[i].singleton()) {
              x[i].domain.inValue(store.level, x[i], 1);
            }
          }
        }
        break;
      case ge:
        sum.domain.inMax(store.level, sum, max);

        if (!reified && min >= sum.max()) {
          removeConstraint();
        }

        if (sum.singleton(max) && min != max) {

          for (int i = 0; i < l; i++) {
            if (!x[i].singleton()) {
              x[i].domain.inValue(store.level, x[i], 1);
            }
          }
        }
        break;

      default:
        throw new RuntimeException("Internal error in SumBool");
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
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

  @Override
  public boolean satisfied() {

    return entailed(relationType);
  }

  @Override
  public boolean notSatisfied() {

    return entailed(negRel[relationType]);
  }

  private boolean entailed(byte rel) {

    int min = 0;
    int max = 0;

    for (int i = 0; i < l; i++) {
      IntDomain xd = x[i].dom();
      min += xd.min();
      max += xd.max();
    }

    return switch (rel) {
      case eq -> sum.singleton(min) && min == max;
      case lt -> max < sum.min();
      case le -> max <= sum.min();
      case ne ->
          sum.min() > max || sum.max() < min; // sum.singleton() && min == max && sum.min() != min;
      case gt -> min > sum.max();
      case ge -> min >= sum.max();
      default -> false;
    };
  }

  /**
   * Converts a relation string to its internal byte representation.
   *
   * @param r the relation string (e.g., "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "!=").
   * @return the byte code representing the relation.
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
   * Converts the internal relation type to its string representation.
   *
   * @return the string representation of the relation (e.g., "==", "{@literal <}", "{@literal >}").
   */
  public String rel2String() {
    return switch (relationType) {
      case eq -> "==";
      case lt -> "<";
      case le -> "<=";
      case ne -> "!=";
      case gt -> ">";
      case ge -> ">=";
      default -> "??";
    };
  }

  IntVar[] filterAndOverflow(IntVar[] x) {

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

    StringBuilder result = new StringBuilder(id());
    result.append(" : SumBool( [ ");

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
}
