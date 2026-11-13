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
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.LinearExplanation;
import org.jacop.lcg.LinearForm;

/**
 * LinearIntDom constraint implements the weighted summation over several variables.
 *
 * <p>sum(i in 1..N)(ai*xi) = b
 *
 * <p>It provides the weighted sum from all variables on the list. The weights are integers. Domain
 * consistency is used.
 *
 * <p>The supports of an equality are found in one of two ways, whichever is estimated cheaper. The
 * first enumerates the assignments that the bounds allow, at a cost of up to the product of the
 * domain sizes. The second computes sumsets: a forward pass of bitset shifts gives the set of
 * reachable partial sums after each variable, a backward pass keeps the partial sums that can still
 * reach the right-hand side, and a value has a support when its shifted prefix set meets that
 * suffix set. It costs O(Σ |D_i| · W / 64) word operations, where W is the width of the window of
 * partial sums that can still reach the right-hand side, so it stays domain consistent on long
 * equalities with small coefficients where the enumeration would fall back to bounds. This is the
 * dynamic program for knapsack constraints of Trick (Annals of OR 118, 2003) and the sumset view of
 * subset sum of Koiliaris and Xu (SODA 2017; ACM Trans. Algorithms 15(3), 2019) and Bringmann (SODA
 * 2017), on bitsets; their FFT-based sumsets pay off only for sums far wider than those of FlatZinc
 * equalities, so they are not used. The system property {@code
 * org.jacop.constraints.LinearIntDom.sumset} chooses: {@code auto} (default), {@code off} (the
 * enumeration only, as before) or {@code always} (sumsets whenever within their limit).
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class LinearIntDom extends LinearInt {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** Limit on the product of sizes of domains when domain consistency is carried out. */
  private static final double LIMIT_DOMAIN_PRUNING = 1e+7;

  /** Limit on the estimated word operations of one sumset pass. */
  private static final double LIMIT_SUMSET = 1e+7;

  /** Limit on the width, in bits, of a window of partial sums. */
  private static final long LIMIT_SUMSET_WIDTH = 1L << 24;

  /** Sumsets are not used. */
  static final int SUMSET_OFF = 0;

  /** Sumsets are used when they are estimated cheaper than the enumeration. */
  static final int SUMSET_AUTO = 1;

  /** Sumsets are used whenever they are within their limit. */
  static final int SUMSET_ALWAYS = 2;

  private static final int SUMSET_DEFAULT =
      switch (System.getProperty("org.jacop.constraints.LinearIntDom.sumset", "auto")) {
        case "off" -> SUMSET_OFF;
        case "always" -> SUMSET_ALWAYS;
        default -> SUMSET_AUTO;
      };

  /** How the supports of an equality are found, one of the SUMSET_ constants. */
  int sumset = SUMSET_DEFAULT;

  /**
   * It chooses how the supports of an equality are found, for tests and comparisons.
   *
   * @param mode "off" for the enumeration only, "always" for sumsets whenever within their limit,
   *     anything else for the cheaper of the two.
   */
  public void setSumsets(String mode) {
    sumset =
        switch (mode) {
          case "off" -> SUMSET_OFF;
          case "always" -> SUMSET_ALWAYS;
          default -> SUMSET_AUTO;
        };
  }

  /** Statistics: the sumset passes made. */
  long sumsetPasses;

  /** Statistics: the enumeration passes made. */
  long enumerationPasses;

  /** Defines support (valid values) for each variable. */
  IntervalDomain[] support;

  /** Collects support (valid assignments) for variables. */
  int[] assignments;

  // ================ constructors ===================

  private LinearIntDom() {}

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
    checkInputForNullness("list", list);
    checkInputForNullness("weights", weights);
    commonInitialization(storeOf(list), list, weights, rel, sum);
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
    checkInputForNullness("list", list);
    checkInputForNullness("weights", weights);
    checkInputForNullness("sum", new Object[] {sum});
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
        storeOf(variables.toArray(new IntVar[0])),
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
        double size = domainSize();
        double sumsetCost = sumset == SUMSET_OFF ? Double.MAX_VALUE : sumsetCost();
        if (sumsetCost <= LIMIT_SUMSET && (sumset == SUMSET_ALWAYS || sumsetCost < size)) {
          sumsetPasses++;
          pruneEqSumset(); // domain consistency
        } else if (size < LIMIT_DOMAIN_PRUNING) {
          enumerationPasses++;
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
        // domain consistency is implemented for == and != only; other relations use the bounds
        // consistency of LinearInt
        super.propagate(rel);
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

    if (l == 0) {
      // all weights are zero, so the sum is 0
      if (b != 0) {
        throw Store.failException;
      }
      return;
    }

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

  /**
   * Estimates the word operations of {@link #pruneEqSumset()}: each value of each variable costs a
   * shift of a window of partial sums.
   *
   * @return the estimate, or {@link Double#MAX_VALUE} when a window is wider than its limit.
   */
  double sumsetCost() {
    long lo = 0;
    long hi = 0;
    for (int i = 0; i < l; i++) {
      long u = a[i] * x[i].min();
      long v = a[i] * x[i].max();
      lo += Math.min(u, v);
      hi += Math.max(u, v);
    }
    long width = hi - lo + 1;
    double cost = 0;
    for (int i = 0; i < l; i++) {
      // a window is no wider than the sums of the terms before it, nor those after it
      cost += x[i].getSize();
    }
    long words = Math.min(width, LIMIT_SUMSET_WIDTH + 1) / 64 + 2;
    if (width > LIMIT_SUMSET_WIDTH || width <= 0) {
      return Double.MAX_VALUE;
    }
    return cost * words;
  }

  /**
   * Prunes an equality to domain consistency by sumsets. With the terms t_i = a_i x_i and s_k the
   * sum of the first k terms, it computes forward the sets F_k of the values of s_k that the
   * domains reach, kept to the window of values from which b is still reachable, and backward the
   * sets G_k of the values of F_k from which b is reached. A value v of x_k has a support exactly
   * when F_k shifted by a_k v meets G_(k+1).
   */
  void pruneEqSumset() {
    int n = l;
    // bounds of the sums of the terms before k (pre) and from k on (suf)
    long[] preLo = new long[n + 1];
    long[] preHi = new long[n + 1];
    long[] sufLo = new long[n + 1];
    long[] sufHi = new long[n + 1];
    for (int i = 0; i < n; i++) {
      long u = a[i] * x[i].min();
      long v = a[i] * x[i].max();
      preLo[i + 1] = preLo[i] + Math.min(u, v);
      preHi[i + 1] = preHi[i] + Math.max(u, v);
    }
    for (int i = n - 1; i >= 0; i--) {
      long u = a[i] * x[i].min();
      long v = a[i] * x[i].max();
      sufLo[i] = sufLo[i + 1] + Math.min(u, v);
      sufHi[i] = sufHi[i + 1] + Math.max(u, v);
    }
    // the window of s_k: reachable from the left and able to reach b to the right
    long[] lo = new long[n + 1];
    int[] bits = new int[n + 1];
    for (int k = 0; k <= n; k++) {
      long wl = Math.max(preLo[k], b - sufHi[k]);
      long wh = Math.min(preHi[k], b - sufLo[k]);
      if (wl > wh) {
        throw Store.failException;
      }
      lo[k] = wl;
      bits[k] = (int) (wh - wl + 1);
    }
    long[][] reach = new long[n + 1][];
    reach[0] = new long[1];
    reach[0][0] = 1L; // s_0 = 0, inside its window [0, 0]
    for (int k = 0; k < n; k++) {
      long[] next = new long[(bits[k + 1] + 63) >>> 6];
      long w = a[k];
      long[] window = valueWindow(k, lo, bits);
      for (Interval iv : intervals(x[k], window)) {
        for (long v = iv.min(); v <= iv.max(); v++) {
          orShifted(reach[k], next, lo[k] + w * v - lo[k + 1]);
        }
      }
      clearTail(next, bits[k + 1]);
      if (isEmpty(next)) {
        throw Store.failException;
      }
      reach[k + 1] = next;
    }
    if ((reach[n][0] & 1L) == 0) {
      throw Store.failException;
    }
    // backward: the partial sums of F_(k+1) that reach b; G_n = {b}
    long[] back = reach[n];
    IntervalDomain[] supports = new IntervalDomain[n];
    for (int k = n - 1; k >= 0; k--) {
      long[] prev = new long[reach[k].length];
      long w = a[k];
      IntervalDomain supported = new IntervalDomain();
      long[] window = valueWindow(k, lo, bits);
      for (Interval iv : intervals(x[k], window)) {
        for (long v = iv.min(); v <= iv.max(); v++) {
          long shift = lo[k] + w * v - lo[k + 1];
          if (intersectsShifted(reach[k], back, shift)) {
            supported.unionAdapt((int) v, (int) v);
            andOrShifted(back, reach[k], prev, -shift);
          }
        }
      }
      supports[k] = supported;
      back = prev;
    }
    for (int k = 0; k < n; k++) {
      if (supports[k].isEmpty()) {
        throw Store.failException;
      }
      x[k].domain.in(store.level, x[k], supports[k]);
    }
  }

  /** The values v of x_k for which s_k + a_k v can fall in the window of s_(k+1). */
  private long[] valueWindow(int k, long[] lo, int[] bits) {
    long dl = lo[k + 1] - (lo[k] + bits[k] - 1);
    long dh = lo[k + 1] + bits[k + 1] - 1 - lo[k];
    long w = a[k];
    long vl;
    long vh;
    if (w > 0) {
      vl = Math.ceilDiv(dl, w);
      vh = Math.floorDiv(dh, w);
    } else {
      vl = Math.ceilDiv(dh, w);
      vh = Math.floorDiv(dl, w);
    }
    return new long[] {vl, vh};
  }

  /** The intervals of the domain of x within the window [w[0], w[1]]. */
  private static List<Interval> intervals(IntVar x, long[] w) {
    IntDomain d = x.dom();
    List<Interval> out = new java.util.ArrayList<>();
    if (w[0] > w[1]) {
      return out;
    }
    for (IntervalEnumeration e = d.intervalEnumeration(); e.hasMoreElements(); ) {
      Interval iv = e.nextElement();
      long mn = Math.max(iv.min(), w[0]);
      long mx = Math.min(iv.max(), w[1]);
      if (mn <= mx) {
        out.add(new Interval((int) mn, (int) mx));
      }
    }
    return out;
  }

  /** dst |= src shifted up by shift bits (down when shift is negative); dst is not masked. */
  static void orShifted(long[] src, long[] dst, long shift) {
    int srcBits = src.length << 6;
    int dstBits = dst.length << 6;
    if (shift >= dstBits || shift <= -srcBits) {
      return;
    }
    if (shift >= 0) {
      int ws = (int) (shift >>> 6);
      int bs = (int) (shift & 63);
      for (int i = 0; i < src.length && i + ws < dst.length; i++) {
        long v = src[i];
        if (v != 0) {
          dst[i + ws] |= v << bs;
          if (bs != 0 && i + ws + 1 < dst.length) {
            dst[i + ws + 1] |= v >>> (64 - bs);
          }
        }
      }
    } else {
      long s = -shift;
      int ws = (int) (s >>> 6);
      int bs = (int) (s & 63);
      for (int i = ws; i < src.length; i++) {
        long v = src[i];
        if (v != 0) {
          int d = i - ws;
          if (d < dst.length) {
            dst[d] |= v >>> bs;
          }
          if (bs != 0 && d - 1 >= 0 && d - 1 < dst.length) {
            dst[d - 1] |= v << (64 - bs);
          }
        }
      }
    }
  }

  /** Tells whether src shifted up by shift bits meets dst. */
  static boolean intersectsShifted(long[] src, long[] dst, long shift) {
    int srcBits = src.length << 6;
    int dstBits = dst.length << 6;
    if (shift >= dstBits || shift <= -srcBits) {
      return false;
    }
    if (shift >= 0) {
      int ws = (int) (shift >>> 6);
      int bs = (int) (shift & 63);
      for (int i = 0; i < src.length && i + ws < dst.length; i++) {
        long v = src[i];
        if (v != 0) {
          if ((dst[i + ws] & (v << bs)) != 0) {
            return true;
          }
          if (bs != 0 && i + ws + 1 < dst.length && (dst[i + ws + 1] & (v >>> (64 - bs))) != 0) {
            return true;
          }
        }
      }
    } else {
      long s = -shift;
      int ws = (int) (s >>> 6);
      int bs = (int) (s & 63);
      for (int i = ws; i < src.length; i++) {
        long v = src[i];
        if (v != 0) {
          int d = i - ws;
          if (d < dst.length && (dst[d] & (v >>> bs)) != 0) {
            return true;
          }
          if (bs != 0 && d - 1 >= 0 && d - 1 < dst.length && (dst[d - 1] & (v << (64 - bs))) != 0) {
            return true;
          }
        }
      }
    }
    return false;
  }

  /** out |= (src shifted up by shift bits) & mask. */
  private static void andOrShifted(long[] src, long[] mask, long[] out, long shift) {
    long[] tmp = new long[out.length];
    orShifted(src, tmp, shift);
    for (int i = 0; i < out.length; i++) {
      out[i] |= tmp[i] & mask[i];
    }
  }

  private static void clearTail(long[] set, int bits) {
    int rest = bits & 63;
    if (rest != 0) {
      set[set.length - 1] &= (1L << rest) - 1;
    }
  }

  private static boolean isEmpty(long[] set) {
    for (long v : set) {
      if (v != 0) {
        return false;
      }
    }
    return true;
  }

  void pruneNeq() {

    // With two or more unassigned variables every value has a support, since at most one value
    // of the other unassigned variable makes the sum equal to b.
    int free = -1;
    long sum = 0;
    for (int i = 0; i < l; i++) {
      if (x[i].singleton()) {
        sum += a[i] * x[i].value();
      } else if (free == -1) {
        free = i;
      } else {
        return;
      }
    }

    if (free == -1) {
      if (sum == b) {
        throw Store.failException;
      }
      return;
    }

    long rest = b - sum;
    if (rest % a[free] == 0) {
      long val = rest / a[free];
      if (val >= x[free].min() && val <= x[free].max()) {
        x[free].domain.inComplement(store.level, x[free], (int) val);
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
      int eMin = ((IntervalDomain) currentDom).leftElement(k);
      int eMax = ((IntervalDomain) currentDom).rightElement(k);

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
    findSupport(positive && newIndex < pos, newIndex, newPartialSum);

    return false; // continue
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    // pruneEq() and pruneNeq() use the holes of the domains, not only their bounds
    return IntDomain.ANY;
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

  @Override
  public LinearIntDom copy(VarMap map) {
    LinearIntDom copy = new LinearIntDom();
    copy.copyFrom(this, map);
    copy.numberId = idNumber.incrementAndGet();
    copy.queueIndex = 4;
    return copy;
  }

  /**
   * Explains a bound by the bounds of the other variables when they imply it, and otherwise, as for
   * a value without support, by the domains of the other variables; under {@code !=} by the other
   * variables being fixed.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (getClass() != LinearIntDom.class) {
      return false;
    }
    LinearForm f = lcgForm();
    IntVar y = trail.variable(entry);
    int kind = trail.kind(entry);
    if (f.relation() == LinearForm.NE) {
      if (!f.explain(trail, entry, out)) {
        return false;
      }
    } else if (!LinearExplanation.explainChecked(
        trail,
        entry,
        f.vars(),
        f.weights(),
        f.c(),
        f.relation() != LinearForm.GE,
        f.relation() != LinearForm.LE,
        out)) {
      for (Var v : arguments()) {
        if (v != y) {
          trail.atomsBefore((IntVar) v, entry, out);
        }
      }
      if (kind != AtomicTrail.NE) {
        // every value of y on the far side of the new bound is either unsupported by the other
        // domains or a hole, and a hole may well have a support in them: the reason holds all
        // the holes, not only those next to the bound (as for a bound computed by a propagator)
        int v = trail.value(entry);
        EntryList own = new EntryList();
        trail.atomsBefore(y, entry, own);
        for (int k = 0; k < own.size(); k++) {
          int atom = own.get(k);
          int atomKind = trail.kind(atom);
          if (kind == AtomicTrail.GE
              ? atomKind == AtomicTrail.GE || atomKind == AtomicTrail.NE && trail.value(atom) < v
              : atomKind == AtomicTrail.LE || atomKind == AtomicTrail.NE && trail.value(atom) > v) {
            out.add(atom);
          }
        }
      }
      return true;
    }
    addFolded(trail, entry, out);
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (getClass() != LinearIntDom.class) {
      return false;
    }
    LinearForm f = lcgForm();
    // a failure of the equality is a domain without support, which every window shows
    boolean explained =
        f.relation() == LinearForm.EQ
            ? LinearExplanation.explainDomainFailure(trail, f.vars(), f.weights(), f.c(), out)
            : f.explainFailure(trail, out);
    if (!explained) {
      return false;
    }
    addFolded(trail, trail.size(), out);
    return true;
  }
}
