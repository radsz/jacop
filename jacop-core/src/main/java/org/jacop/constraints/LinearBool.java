/*
 * LinearBool.java
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
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;

/**
 * Linear constraint over 0/1 variables: w[0]*x[0] + ... + w[n-1]*x[n-1] rel z, where rel is one of
 * {@code ==}, {@code <=} and {@code >=}, and z is a variable or a constant.
 *
 * <p>It prunes the same as {@link LinearInt} (bounds consistency), but keeps the bounds of the sum
 * incrementally: they are updated in {@code queueVariable} when a variable gets fixed, so a call
 * does not have to visit every variable. The variables are kept in decreasing order of the absolute
 * value of their weights, so that the search for values to prune stops at the first weight that
 * fits in the slack of the relation.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class LinearBool extends Constraint implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  static final byte EQ = 0;

  static final byte LE = 1;

  static final byte GE = 2;

  /** The 0/1 variables of the sum, in decreasing order of the absolute value of their weights. */
  final IntVar[] x;

  /** The weights of the variables, none of them 0. */
  final long[] w;

  /** The right hand side variable, null if the right hand side is a constant. */
  final IntVar z;

  /** The right hand side constant, used when z is null. */
  final long c;

  final byte relationType;

  private Map<Var, Integer> position;

  /** Sum of the weights of the variables fixed to 1. */
  private TimeStamp<Long> fixedSum;

  /** Sum of the positive weights of the variables not fixed yet. */
  private TimeStamp<Long> freePositive;

  /** Sum of the negative weights of the variables not fixed yet. */
  private TimeStamp<Long> freeNegative;

  /**
   * It constructs the constraint w[0]*x[0] + ... + w[n-1]*x[n-1] rel z.
   *
   * @param x the 0/1 variables.
   * @param w the weights of the variables.
   * @param rel the relation, one of "==", "<=" and ">=".
   * @param z the right hand side.
   */
  public LinearBool(IntVar[] x, int[] w, String rel, IntVar z) {
    this(x, w, rel, z, 0);
  }

  /**
   * It constructs the constraint w[0]*x[0] + ... + w[n-1]*x[n-1] rel c.
   *
   * @param x the 0/1 variables.
   * @param w the weights of the variables.
   * @param rel the relation, one of "==", "<=" and ">=".
   * @param c the right hand side.
   */
  public LinearBool(IntVar[] x, int[] w, String rel, int c) {
    this(x, w, rel, null, c);
  }

  private LinearBool(IntVar[] x, int[] w, String rel, IntVar z, long c) {

    checkInputForNullness("x", x);
    checkInputForNullness("w", w);
    if (x.length != w.length) {
      throw new IllegalArgumentException(
          "LinearBool has " + x.length + " variables and " + w.length + " weights.");
    }

    numberId = idNumber.incrementAndGet();
    this.relationType = relation(rel);
    this.z = z;
    this.c = c;

    // Repeated variables have their weights added; variables of weight 0 are dropped.
    Map<IntVar, Long> weights = new IdentityHashMap<>();
    List<IntVar> order = new ArrayList<>();
    for (int i = 0; i < x.length; i++) {
      if (x[i].min() < 0 || x[i].max() > 1) {
        throw new IllegalArgumentException(
            "Variable " + x[i] + " of LinearBool must have a domain within 0..1.");
      }
      if (x[i] == z) {
        throw new IllegalArgumentException(
            "Variable " + z + " of LinearBool is both in the sum and its right hand side.");
      }
      if (weights.put(x[i], weights.getOrDefault(x[i], 0L) + w[i]) == null) {
        order.add(x[i]);
      }
    }
    order.removeIf(v -> weights.get(v) == 0L);
    order.sort(Comparator.comparingLong((IntVar v) -> -Math.abs(weights.get(v))));

    this.x = order.toArray(new IntVar[0]);
    this.w = new long[this.x.length];
    long positive = 0;
    long negative = 0;
    for (int i = 0; i < this.x.length; i++) {
      this.w[i] = weights.get(this.x[i]);
      if (this.w[i] > 0) {
        positive = Math.addExact(positive, this.w[i]);
      } else {
        negative = Math.addExact(negative, this.w[i]);
      }
    }
    if (positive > Integer.MAX_VALUE || negative < Integer.MIN_VALUE) {
      throw new ArithmeticException("Overflow occurred in LinearBool: the sum exceeds int.");
    }

    this.queueIndex = 1;

    if (z == null) {
      setScope(this.x);
    } else {
      setScope(Stream.concat(Arrays.stream(this.x), Stream.of(z)));
    }
  }

  /**
   * It constructs the constraint w[0]*x[0] + ... + w[n-1]*x[n-1] rel z.
   *
   * @param x the 0/1 variables.
   * @param w the weights of the variables.
   * @param rel the relation, one of "==", "<=" and ">=".
   * @param z the right hand side.
   */
  public LinearBool(List<? extends IntVar> x, List<Integer> w, String rel, IntVar z) {
    this(x.toArray(new IntVar[0]), w.stream().mapToInt(i -> i).toArray(), rel, z);
  }

  private static byte relation(String rel) {
    if (rel == null) {
      throw new IllegalArgumentException("LinearBool needs a relation.");
    }
    return switch (rel) {
      case "==", "=" -> EQ;
      case "<=" -> LE;
      case ">=" -> GE;
      default ->
          throw new IllegalArgumentException(
              "LinearBool supports relations ==, <= and >=, not " + rel + ".");
    };
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void impose(Store store) {

    position = new IdentityHashMap<>();
    for (int i = 0; i < x.length; i++) {
      position.put(x[i], i);
    }

    long fixed = 0;
    long positive = 0;
    long negative = 0;
    for (int i = 0; i < x.length; i++) {
      if (x[i].singleton()) {
        fixed += x[i].min() * w[i];
      } else if (w[i] > 0) {
        positive += w[i];
      } else {
        negative += w[i];
      }
    }
    fixedSum = new TimeStamp<>(store, fixed);
    freePositive = new TimeStamp<>(store, positive);
    freeNegative = new TimeStamp<>(store, negative);

    super.impose(store);
  }

  @Override
  public void queueVariable(int level, Var v) {
    Integer i = position.get(v);
    // A 0/1 variable changes only when it gets fixed, so this is called once per variable on a
    // path of the search, at the level of the change, where the time stamps record the new sums.
    // The constraint does not implement UsesQueueVariable, which would also call this on imposing.
    if (i != null) {
      assert x[i].singleton() : "LinearBool expects a 0/1 variable to change only when it is fixed";
      long weight = w[i];
      if (x[i].min() == 1) {
        fixedSum.update(fixedSum.value() + weight);
      }
      if (weight > 0) {
        freePositive.update(freePositive.value() - weight);
      } else {
        freeNegative.update(freeNegative.value() - weight);
      }
    }
  }

  @Override
  public void consistency(final Store store) {

    do {
      store.propagationHasOccurred = false;

      long sumMin = fixedSum.value() + freeNegative.value();
      long sumMax = fixedSum.value() + freePositive.value();

      long rhsMin;
      long rhsMax;
      if (z == null) {
        rhsMin = c;
        rhsMax = c;
      } else {
        if (relationType != GE) {
          z.domain.inMin(store.level, z, long2int(sumMin));
        }
        if (relationType != LE) {
          z.domain.inMax(store.level, z, long2int(sumMax));
        }
        rhsMin = z.min();
        rhsMax = z.max();
      }

      // How much the sum may still grow, and how much it may still fall.
      long up = relationType == GE ? Long.MAX_VALUE : rhsMax - sumMin;
      long down = relationType == LE ? Long.MAX_VALUE : sumMax - rhsMin;
      if (up < 0 || down < 0) {
        throw Store.failException;
      }
      long slack = Math.min(up, down);

      for (int i = 0; i < x.length && Math.abs(w[i]) > slack; i++) {
        IntVar v = x[i];
        if (v.singleton()) {
          continue;
        }
        long weight = w[i];
        if (weight > 0) {
          // Setting v to 1 adds weight to the sum, leaving it at 0 keeps weight off the maximum.
          if (weight > up) {
            v.domain.inValue(store.level, v, 0);
          } else if (weight > down) {
            v.domain.inValue(store.level, v, 1);
          }
        } else {
          if (-weight > up) {
            v.domain.inValue(store.level, v, 1);
          } else if (-weight > down) {
            v.domain.inValue(store.level, v, 0);
          }
        }
      }
    } while (store.propagationHasOccurred);
  }

  @Override
  public boolean satisfied() {

    long sum = 0;
    for (int i = 0; i < x.length; i++) {
      if (!x[i].singleton()) {
        return false;
      }
      sum += x[i].min() * w[i];
    }
    if (z == null) {
      return relationHolds(sum, c, c);
    }
    return relationHolds(sum, z.min(), z.max());
  }

  private boolean relationHolds(long sum, long rhsMin, long rhsMax) {
    return switch (relationType) {
      case EQ -> rhsMin == rhsMax && sum == rhsMin;
      case LE -> sum <= rhsMin;
      default -> sum >= rhsMax;
    };
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : LinearBool( [ ");
    for (int i = 0; i < x.length; i++) {
      result.append(x[i]);
      if (i < x.length - 1) {
        result.append(", ");
      }
    }
    result.append("], [");
    for (int i = 0; i < w.length; i++) {
      result.append(w[i]);
      if (i < w.length - 1) {
        result.append(", ");
      }
    }
    String rel =
        switch (relationType) {
          case EQ -> "==";
          case LE -> "<=";
          default -> ">=";
        };
    result.append("], ").append(rel).append(", ").append(z == null ? String.valueOf(c) : z);
    return result.append(" )").toString();
  }
}
