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
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TrailedInts;
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
 * <p>A long constraint with a constant right hand side, imposed at level 0, uses watched
 * propagation instead (Devriendt, Watched Propagation of 0-1 Integer Linear Constraints, CP 2020).
 * Each side of the relation is written as a sum of literals a[i]*l[i] >= d with positive
 * coefficients, where a literal is a variable or its negation. The constraint watches a prefix
 * l[0..k) of the literals in the order of decreasing coefficients, with k extended until the
 * coefficients of the non-false watched literals exceed d by at least the largest coefficient.
 * While they do, no literal can be propagated. The variables of the prefix are watched for the
 * value at which their literal is false ({@link Store#watchValue}), so a variable fixed to the
 * other value, or not yet in the prefix, does not reach the constraint at all, and a watched
 * literal that gets false only lowers the slack; the constraint is queued when the slack falls
 * below the largest coefficient. When the prefix reaches the end, its slack is the slack of the
 * constraint and the literals with larger coefficients are set to true.
 *
 * <p>The prefix length and its slack are restored on backtracking, but the watches are not, as in
 * SAT solvers: a variable beyond the restored prefix stays watched and is ignored when its literal
 * gets false. Since the prefix only grows along a branch, every literal of the prefix that is not
 * false is watched at any time.
 *
 * <p>Watching pays off on long constraints; on short ones with large coefficients the prefix soon
 * holds every literal, and the counters are as fast, hence {@link #WATCH_MIN_LENGTH}.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class LinearBool extends Constraint implements SatisfiedPresent, Copyable<LinearBool> {

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

  /**
   * The smallest number of variables for which a constraint with a constant right hand side uses
   * watched propagation.
   */
  public static final int WATCH_MIN_LENGTH = 32;

  private int watchMinLength = WATCH_MIN_LENGTH;

  private Map<Var, Integer> position;

  /** True if the constraint uses watched propagation, decided when it is imposed. */
  private boolean watched;

  /**
   * The right hand sides d of the two sides, sum of a[i]*l[i] >= d; at most 0 for a side that
   * holds.
   */
  private long[] degree;

  /** The largest coefficient, |w[0]|. */
  private long maxCoefficient;

  /**
   * For each side, the prefix length k and the slack of the prefix: the sum of the coefficients of
   * its literals that are not false minus the right hand side, at indexes K and SLACK; null for a
   * side that always holds. Once the prefix holds every literal, the literals before index START
   * are fixed.
   */
  private TrailedInts[] prefix;

  private static final int K = 0;

  private static final int SLACK = 1;

  private static final int START = 2;

  /** For each side, the variables watched for the value at which their literal is false. */
  private boolean[][] watching;

  /**
   * The counters: sum of the weights of the variables fixed to 1 (FIXED), sum of the positive
   * weights of the variables not fixed yet (FREE_POSITIVE) and sum of their negative weights
   * (FREE_NEGATIVE). They fit in an int, as the sums of the weights do. The variables before index
   * FIXED_BEFORE are fixed.
   */
  private TrailedInts sums;

  private static final int FIXED = 0;

  private static final int FREE_POSITIVE = 1;

  private static final int FREE_NEGATIVE = 2;

  private static final int FIXED_BEFORE = 3;

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

  /** A copy over the counterparts of the variables; the weights, already merged, are shared. */
  private LinearBool(LinearBool original, VarMap map) {
    numberId = idNumber.incrementAndGet();
    this.relationType = original.relationType;
    this.x = map.get(original.x);
    this.w = original.w;
    this.z = original.z == null ? null : map.get(original.z);
    this.c = original.c;
    this.watchMinLength = original.watchMinLength;
    this.queueIndex = 1;
    if (z == null) {
      setScope(this.x);
    } else {
      setScope(Stream.concat(Arrays.stream(this.x), Stream.of(z)));
    }
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

  /**
   * Sets the smallest number of variables for which watched propagation is used; the default is
   * {@link #WATCH_MIN_LENGTH}. It takes effect when the constraint is imposed.
   *
   * @param minLength the smallest number of variables, 0 to always use watched propagation when the
   *     right hand side is a constant.
   */
  public void setWatchMinLength(int minLength) {
    this.watchMinLength = minLength;
  }

  /**
   * Tells whether the constraint uses watched propagation; it is decided when it is imposed.
   *
   * @return true if the constraint uses watched propagation.
   */
  public boolean isWatched() {
    return watched;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void impose(Store store) {

    if (canWatch(store)) {
      imposeWatched(store);
      return;
    }

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
    sums = new TrailedInts(store, 4);
    sums.set(FIXED, (int) fixed);
    sums.set(FREE_POSITIVE, (int) positive);
    sums.set(FREE_NEGATIVE, (int) negative);

    super.impose(store);
  }

  @Override
  public void queueVariable(int level, Var v) {
    Integer i = position.get(v);
    // A 0/1 variable changes only when it gets fixed, so this is called once per variable on a
    // path of the search, at the level of the change, where the trailed counters record the new
    // sums.
    // The constraint does not implement UsesQueueVariable, which would also call this on imposing.
    if (i != null) {
      assert x[i].singleton() : "LinearBool expects a 0/1 variable to change only when it is fixed";
      long weight = w[i];
      if (x[i].min() == 1) {
        sums.set(FIXED, sums.get(FIXED) + (int) weight);
      }
      if (weight > 0) {
        sums.set(FREE_POSITIVE, sums.get(FREE_POSITIVE) - (int) weight);
      } else {
        sums.set(FREE_NEGATIVE, sums.get(FREE_NEGATIVE) - (int) weight);
      }
    }
  }

  @Override
  public void consistency(final Store store) {

    if (watched) {
      consistencyWatched(store);
      return;
    }

    do {
      store.propagationHasOccurred = false;

      long sumMin = (long) sums.get(FIXED) + sums.get(FREE_NEGATIVE);
      long sumMax = (long) sums.get(FIXED) + sums.get(FREE_POSITIVE);

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

      // The slack only falls along a branch, so the variables before start, whose weights exceeded
      // the slack of an earlier call, are fixed.
      int i = sums.get(FIXED_BEFORE);
      for (; i < x.length && Math.abs(w[i]) > slack; i++) {
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
      sums.set(FIXED_BEFORE, i);
    } while (store.propagationHasOccurred);
  }

  /**
   * Watched propagation needs a constant right hand side, enough variables, sums that fit in an int
   * with room for the slack, and level 0, since the watches are kept on backtracking.
   */
  private boolean canWatch(Store store) {
    if (z != null || x.length == 0 || x.length < watchMinLength || store.level != 0) {
      return false;
    }
    long total = 0;
    for (long weight : w) {
      total += Math.abs(weight);
    }
    return 2 * total + Math.abs(c) < Integer.MAX_VALUE;
  }

  private void imposeWatched(Store store) {

    watched = true;
    maxCoefficient = Math.abs(w[0]);
    // w*x is |w|*l - (w < 0 ? |w| : 0) with l = x for w > 0 and l = 1 - x otherwise, and
    // w*x <= c is (-w)*x >= -c.
    long positive = 0;
    long negative = 0;
    for (long weight : w) {
      if (weight > 0) {
        positive += weight;
      } else {
        negative -= weight;
      }
    }
    degree = new long[2];
    degree[0] = relationType == LE ? 0 : c + negative;
    degree[1] = relationType == GE ? 0 : positive - c;
    prefix = new TrailedInts[2];
    for (int side = 0; side < 2; side++) {
      // a side with d <= 0 always holds; it has no prefix and it is never propagated
      if (degree[side] > 0) {
        prefix[side] = new TrailedInts(store, 3);
        prefix[side].set(SLACK, (int) -degree[side]);
      }
    }
    watching = new boolean[2][x.length];

    store.addChanged(this);
    store.countConstraint();
  }

  /** The value of x[i] at which the literal of x[i] is false on the given side. */
  private int falseValue(int side, int i) {
    return (w[i] > 0) == (side == 0) ? 0 : 1;
  }

  @Override
  public boolean valueWatchFired(int level, Var v, int tag) {
    int i = tag >> 1;
    int side = tag & 1;
    if (i >= prefix[side].get(K)) {
      // Beyond the prefix restored by backtracking. The watch is kept: removing it would cost a
      // search of the watch list, and the prefix is likely to grow over the variable again.
      return false;
    }
    int slack = prefix[side].get(SLACK) - (int) Math.abs(w[i]);
    prefix[side].set(SLACK, slack);
    return slack < maxCoefficient;
  }

  private void consistencyWatched(Store store) {
    do {
      store.propagationHasOccurred = false;
      propagateSide(store, 0);
      propagateSide(store, 1);
    } while (store.propagationHasOccurred);
  }

  private void propagateSide(Store store, int side) {

    if (degree[side] <= 0) {
      return;
    }
    int slack = prefix[side].get(SLACK);
    if (slack >= maxCoefficient) {
      return;
    }
    int k = prefix[side].get(K);
    if (k < x.length) {
      // Extend the prefix until it has enough slack. A fixed variable needs no watch: it is not
      // unfixed before the store backtracks to a level where the prefix ends before it.
      while (k < x.length && slack < maxCoefficient) {
        IntVar v = x[k];
        if (!v.singleton()) {
          slack += (int) Math.abs(w[k]);
          if (!watching[side][k]) {
            watching[side][k] = true;
            store.watchValue(v, falseValue(side, k), this, 2 * k + side);
          }
        } else if (v.value() != falseValue(side, k)) {
          slack += (int) Math.abs(w[k]);
        }
        k++;
      }
      prefix[side].set(K, k);
      prefix[side].set(SLACK, slack);
      if (slack >= maxCoefficient) {
        return;
      }
    }

    // The prefix holds every literal, so its slack is the slack of the side.
    if (slack < 0) {
      throw Store.failException;
    }
    // The literals before start have been fixed by an earlier call with a larger slack.
    int i = prefix[side].get(START);
    for (; i < x.length && Math.abs(w[i]) > slack; i++) {
      IntVar v = x[i];
      if (!v.singleton()) {
        v.domain.inValue(store.level, v, 1 - falseValue(side, i));
      }
    }
    prefix[side].set(START, i);
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

  @Override
  public LinearBool copy(VarMap map) {
    return new LinearBool(this, map);
  }
}
