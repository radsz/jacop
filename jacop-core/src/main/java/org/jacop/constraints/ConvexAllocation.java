/*
 * ConvexAllocation.java
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
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Separable convex resource allocation: x[0] + ... + x[n-1] = total and cost &ge;
 * f<sub>0</sub>(x[0]) + ... + f<sub>n-1</sub>(x[n-1]), each f<sub>i</sub> a {@link ConvexCost} that
 * is convex on the initial domain of x[i]. It bounds balancing objectives such as sums of squares
 * or of absolute distances to per-variable targets, with weights, dead zones and a total that is a
 * variable (an upper or lower bound on the sum is a total with that bound).
 *
 * <p>The least cost G(t) of an integer assignment within the bounds of x with sum t is found by the
 * greedy algorithm over marginal costs of Hochbaum's resource allocation framework: since every
 * f<sub>i</sub> is convex, its marginal costs f<sub>i</sub>(v) - f<sub>i</sub>(v - 1) do not
 * decrease, and taking the cheapest units first is optimal (D. S. Hochbaum, "Lower and upper bounds
 * for the allocation problem and other nonlinear optimization problems", Mathematics of Operations
 * Research 19(2), 390-409, 1994). The threshold version is used: for a marginal cost &lambda;, each
 * x[i] takes all units of marginal cost at most &lambda;, and a binary search on &lambda; finds the
 * threshold that reaches t, so G(t) costs O(n log D log M), D the widest domain and M the largest
 * marginal cost.
 *
 * <ul>
 *   <li>cost.min is raised to the least G(t) over the bounds of total, and total is narrowed to the
 *       sums t with G(t) &le; cost.max (G is convex, so these form an interval);
 *   <li>each bound of x[i] is the least or greatest v for which some assignment of the others
 *       within their bounds, with x[i] = v and a total within its bounds, costs at most cost.max.
 *       With at most {@link #EXACT_LIMIT} variables this least cost F<sub>i</sub>(v) is computed
 *       exactly (bounds(Z) consistency for the relaxation) by walking x[i] away from an optimal
 *       assignment while the others follow greedily, O(n) per unit, otherwise it is bounded by
 *       Lagrangian reduced costs at the optimal marginal cost &lambda;, which costs O(n log D) per
 *       pass;
 *   <li>the sum itself is propagated on bounds.
 * </ul>
 *
 * <p>The constraint generalizes the spread constraint (G. Pesant and J.-C. R&eacute;gin, "SPREAD: A
 * balancing constraint based on statistics", CP 2005, LNCS 3709) and the deviation constraint (P.
 * Schaus, Y. Deville, P. Dupont and J.-C. R&eacute;gin, "The deviation constraint", CPAIOR 2007,
 * LNCS 4510), which are the cases f<sub>i</sub>(v) = (n &middot; v - s)<sup>2</sup> and |n &middot;
 * v - s| with a fixed sum s; {@link Spread} and {@link Deviation} remain the faster choice for
 * those.
 *
 * <p>Under lazy clause generation the propagation is explained by the Lagrangian bound at a
 * marginal cost &lambda;: G(t) &ge; &Sigma;<sub>i</sub> min<sub>v</sub>(f<sub>i</sub>(v) - &lambda;
 * v) + &lambda; t, where only the bounds of x[i] that stop it from reaching its unconstrained
 * minimizer for &lambda;, and one bound of total for the sign of &lambda;, take part.
 *
 * <p>Repeated variables in x are treated as independent, which keeps the pruning correct but may
 * make it weaker.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ConvexAllocation extends Constraint
    implements SatisfiedPresent, Explainable, Copyable<ConvexAllocation> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * The largest number of variables for which the bounds of x are computed exactly; above it they
   * use Lagrangian reduced costs. Set by the system property jacop.convexAllocation.exact.
   */
  public static final int EXACT_LIMIT = Integer.getInteger("jacop.convexAllocation.exact", 64);

  private static final long INFINITE = Long.MAX_VALUE;

  /** The allocated variables. */
  final IntVar[] x;

  /** The cost of each variable. */
  final ConvexCost[] f;

  /** The sum of x. */
  final IntVar total;

  /** The bound on the cost. */
  final IntVar cost;

  final int n;

  // the domains of x when the constraint was created, on which the costs are convex and small
  private final long[] min0;
  private final long[] max0;

  // bounds of x in the current pass (or explanation)
  private final long[] lo;
  private final long[] hi;

  // the greatest marginal cost and one less than the least, over the current bounds
  private long lambdaLow;
  private long lambdaHigh;

  // an optimal assignment of the current pass
  private final long[] best;

  // the others' values while walking one variable away from best
  private final long[] walk;

  // the steps a walk makes before the rest of the bound is found by binary search
  private static final int WALK_LIMIT = 256;

  // whether the bounds of x are computed exactly
  private boolean exact;

  // the costs over the initial domains, null for a domain too wide to tabulate
  private final long[][] values;

  private static final int TABLE_LIMIT = 1 << 16;

  /**
   * It constructs the constraint sum of x = total and cost &ge; sum of f[i](x[i]).
   *
   * @param x the allocated variables
   * @param f the cost of each variable, convex on its domain
   * @param total the sum of x
   * @param cost the bound on the cost
   */
  public ConvexAllocation(IntVar[] x, ConvexCost[] f, IntVar total, IntVar cost) {
    checkInputForNullness(
        new String[] {"x", "f", "total", "cost"}, new Object[][] {x, f, {total}, {cost}});
    if (x.length == 0 || x.length != f.length) {
      throw new IllegalArgumentException(
          "ConvexAllocation needs one cost for each variable, at least one variable.");
    }
    this.numberId = idNumber.incrementAndGet();
    this.x = Arrays.copyOf(x, x.length);
    this.f = Arrays.copyOf(f, f.length);
    this.n = x.length;
    this.total = total;
    this.cost = cost;
    this.min0 = new long[n];
    this.max0 = new long[n];
    this.lo = new long[n];
    this.hi = new long[n];
    this.best = new long[n];
    this.walk = new long[n];
    // the sum of all costs, and every marginal cost times a sum of widths, stays far from overflow
    long limit = (1L << 60) / (n + 2);
    long widest = 1;
    long steepest = 1;
    for (int i = 0; i < n; i++) {
      min0[i] = x[i].min();
      max0[i] = x[i].max();
      if (!f[i].isConvexOn(min0[i], max0[i])) {
        throw new IllegalArgumentException(
            "ConvexAllocation needs a convex cost for " + x[i] + ", not " + f[i] + ".");
      }
      try {
        long m = f[i].value(f[i].argMin(min0[i], max0[i]));
        long a = f[i].value(min0[i]);
        long b = f[i].value(max0[i]);
        if (m < -limit || a > limit || b > limit) {
          throw new ArithmeticException();
        }
        widest = Math.max(widest, max0[i] - min0[i] + 1);
        if (min0[i] < max0[i]) {
          steepest = Math.max(steepest, Math.abs(a - f[i].value(min0[i] + 1)));
          steepest = Math.max(steepest, Math.abs(b - f[i].value(max0[i] - 1)));
        }
        if (Math.multiplyHigh(widest, steepest) != 0 || widest * steepest > limit / (n + 2)) {
          throw new ArithmeticException();
        }
      } catch (ArithmeticException e) {
        throw new IllegalArgumentException(
            "ConvexAllocation needs smaller costs for " + x[i] + ", not " + f[i] + ".", e);
      }
    }
    this.values = new long[n][];
    long cells = 0;
    for (int i = 0; i < n; i++) {
      long width = max0[i] - min0[i] + 1;
      if (width <= TABLE_LIMIT && cells + width <= 4L * TABLE_LIMIT) {
        cells += width;
        long[] t = new long[(int) width];
        for (int k = 0; k < t.length; k++) {
          t[k] = f[i].value(min0[i] + k);
        }
        values[i] = t;
      }
    }
    this.exact = n <= EXACT_LIMIT;
    this.queueIndex = 2;
    setScope(Stream.concat(Arrays.stream(x), Stream.of(total, cost)));
  }

  /**
   * It makes the bounds of x come from the Lagrangian reduced costs only, as they do for more than
   * {@link #EXACT_LIMIT} variables, or exact again when that limit allows it.
   *
   * @param lagrangian true for the reduced costs only
   */
  public void lagrangianOnly(boolean lagrangian) {
    exact = !lagrangian && n <= EXACT_LIMIT;
  }

  /**
   * It returns the variable that bounds the cost.
   *
   * @return the cost variable
   */
  public IntVar getCost() {
    return cost;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  // ---- the least costs over the bounds in lo and hi

  // f[j] at v, from the table inside the initial domain
  private long val(int j, long v) {
    long[] t = values[j];
    if (t != null) {
      long k = v - min0[j];
      if (k >= 0 && k < t.length) {
        return t[(int) k];
      }
    }
    return val(j, v);
  }

  private long marginal(int j, long v) {
    long[] t = values[j];
    if (t != null) {
      long k = v - min0[j];
      if (k >= 1 && k < t.length) {
        return t[(int) k] - t[(int) k - 1];
      }
    }
    return val(j, v) - val(j, v - 1);
  }

  // the greatest v in [lo, hi] with v = lo or a marginal cost of v of at most lambda
  private long at(int j, long lambda) {
    long l = lo[j];
    long h = hi[j];
    while (l < h) {
      long m = h - (h - l) / 2;
      if (marginal(j, m) <= lambda) {
        l = m;
      } else {
        h = m - 1;
      }
    }
    return l;
  }

  private long units(int skip, long lambda) {
    long s = 0;
    for (int j = 0; j < n; j++) {
      if (j != skip) {
        s += at(j, lambda);
      }
    }
    return s;
  }

  private long sumAt(int skip, long lambda) {
    long s = 0;
    for (int j = 0; j < n; j++) {
      if (j != skip) {
        s += val(j, at(j, lambda));
      }
    }
    return s;
  }

  private void marginalRange() {
    long low = 0;
    long high = 0;
    for (int j = 0; j < n; j++) {
      if (lo[j] < hi[j]) {
        low = Math.min(low, marginal(j, lo[j] + 1));
        high = Math.max(high, marginal(j, hi[j]));
      }
    }
    lambdaLow = low - 1;
    lambdaHigh = high;
  }

  // the least lambda whose units reach t (lambdaLow when t is the sum of the lower bounds)
  private long threshold(int skip, long t) {
    long l = lambdaLow;
    long h = lambdaHigh;
    while (l < h) {
      long m = l + (h - l) / 2;
      if (units(skip, m) >= t) {
        h = m;
      } else {
        l = m + 1;
      }
    }
    return l;
  }

  // the least cost of the variables but skip with sum t, within the sums of their bounds
  private long least(int skip, long t) {
    long lambda = threshold(skip, t);
    if (lambda == lambdaLow) {
      return sumAt(skip, lambda);
    }
    long before = units(skip, lambda - 1);
    return sumAt(skip, lambda - 1) + (t - before) * lambda;
  }

  // the least cost of the variables but skip with a sum from tlo to thi, INFINITE if none
  private long leastWithin(int skip, long tlo, long thi) {
    long sl = 0;
    long su = 0;
    for (int j = 0; j < n; j++) {
      if (j != skip) {
        sl += lo[j];
        su += hi[j];
      }
    }
    long from = Math.max(tlo, sl);
    long to = Math.min(thi, su);
    if (from > to) {
      return INFINITE;
    }
    long freeLow = units(skip, -1);
    long freeHigh = units(skip, 0);
    if (to < freeLow) {
      return least(skip, to);
    }
    if (from > freeHigh) {
      return least(skip, from);
    }
    return sumAt(skip, 0);
  }

  // the target sum of an optimal assignment with the total in [smin, smax]
  private long target(long smin, long smax) {
    long freeLow = units(-1, -1);
    long freeHigh = units(-1, 0);
    if (smax < freeLow) {
      return smax;
    }
    if (smin > freeHigh) {
      return smin;
    }
    return Math.max(freeLow, smin);
  }

  // an optimal assignment with sum t into best; returns the marginal cost lambda of the last units
  private long optimum(long t) {
    long lambda = threshold(-1, t);
    long rest = t;
    for (int j = 0; j < n; j++) {
      best[j] = lambda == lambdaLow ? lo[j] : at(j, lambda - 1);
      rest -= best[j];
    }
    for (int j = 0; j < n && rest > 0; j++) {
      long more = Math.min(rest, at(j, lambda) - best[j]);
      best[j] += more;
      rest -= more;
    }
    return lambda;
  }

  // ---- propagation

  @Override
  public void consistency(Store store) {
    do {
      store.propagationHasOccurred = false;

      long sl = 0;
      long su = 0;
      for (int j = 0; j < n; j++) {
        lo[j] = x[j].min();
        hi[j] = x[j].max();
        sl += lo[j];
        su += hi[j];
      }
      long smin = Math.max(total.min(), sl);
      long smax = Math.min(total.max(), su);
      if (smin > smax) {
        throw Store.failException;
      }
      if (smin > total.min() || smax < total.max()) {
        total.domain.in(store.level, total, (int) smin, (int) smax);
      }
      boolean changed = false;
      for (int i = 0; i < n; i++) {
        long from = Math.max(lo[i], smin - (su - hi[i]));
        long to = Math.min(hi[i], smax - (sl - lo[i]));
        if (from > lo[i] || to < hi[i]) {
          x[i].domain.in(store.level, x[i], (int) from, (int) to);
          changed = true;
        }
      }
      if (changed) {
        store.propagationHasOccurred = true;
        continue;
      }

      marginalRange();
      long t = target(smin, smax);
      long lambda = optimum(t);
      long lower = 0;
      for (int j = 0; j < n; j++) {
        lower += val(j, best[j]);
      }
      if (lower > cost.max()) {
        throw Store.failException;
      }
      if (lower > cost.min()) {
        cost.domain.inMin(store.level, cost, (int) lower);
      }
      long limit = cost.max();

      narrowTotal(store, smin, smax, t, limit);

      // the marginal costs at which the Lagrangian bound is the least cost
      boolean free = t >= units(-1, -1) && t <= units(-1, 0);
      long alpha = free ? 0 : lambda;
      long beta = free ? 0 : upperDual(lambda, t);

      for (int i = 0; i < n; i++) {
        narrow(store, i, smin, smax, lower, limit, alpha, beta);
      }
    } while (store.propagationHasOccurred);
  }

  // the greatest marginal cost at which the Lagrangian bound for sum t is still the least cost
  private long upperDual(long lambda, long t) {
    if (units(-1, lambda) > t) {
      return lambda;
    }
    long next = INFINITE;
    for (int j = 0; j < n; j++) {
      long v = at(j, lambda);
      if (v < hi[j]) {
        next = Math.min(next, marginal(j, v + 1));
      }
    }
    return next == INFINITE ? lambda : next;
  }

  private void narrowTotal(Store store, long smin, long smax, long t, long limit) {
    long from = smin;
    if (least(-1, smin) > limit) {
      long l = smin;
      long h = t;
      while (l < h) {
        long m = l + (h - l) / 2;
        if (least(-1, m) <= limit) {
          h = m;
        } else {
          l = m + 1;
        }
      }
      from = l;
    }
    long to = smax;
    if (least(-1, smax) > limit) {
      long l = t;
      long h = smax;
      while (l < h) {
        long m = h - (h - l) / 2;
        if (least(-1, m) <= limit) {
          l = m;
        } else {
          h = m - 1;
        }
      }
      to = l;
    }
    if (from > smin || to < smax) {
      total.domain.in(store.level, total, (int) from, (int) to);
    }
  }

  /*
   * The farthest value of x[i] in direction d (1 up, -1 down), at most to bound, whose least cost
   * is within limit. It walks x[i] away from best[i] one unit at a time while the others follow
   * greedily: with x[i] one unit further the others' sum must lie in [smin - v, smax - v], so they
   * give back (or take) a unit when the window forces it or when that unit's marginal cost makes
   * it worth it, always the unit with the greatest (least) marginal cost. From an optimal
   * assignment, and with convex costs, this keeps the others optimal for every v (Hochbaum 1994),
   * so each step costs O(n) instead of a search over lambda. After WALK_LIMIT steps the rest is
   * found by binary search on cost(i, v).
   */
  private long exactBound(int i, int d, long bound, long smin, long smax, long lower, long limit) {
    System.arraycopy(best, 0, walk, 0, n);
    long others = lower - val(i, best[i]);
    long sum = 0;
    for (int j = 0; j < n; j++) {
      if (j != i) {
        sum += walk[j];
      }
    }
    long v = best[i];
    for (int step = 0; step < WALK_LIMIT && v != bound; step++) {
      long next = v + d;
      long from = smin - next;
      long to = smax - next;
      // d = 1: the others give back the unit with the greatest marginal cost
      int pick = -1;
      long gain = 0;
      for (int j = 0; j < n; j++) {
        if (j == i) {
          continue;
        }
        if (d > 0 ? walk[j] > lo[j] : walk[j] < hi[j]) {
          long m = d > 0 ? marginal(j, walk[j]) : marginal(j, walk[j] + 1);
          if (pick < 0 || (d > 0 ? m > gain : m < gain)) {
            pick = j;
            gain = m;
          }
        }
      }
      boolean forced = d > 0 ? sum > to : sum < from;
      boolean worth =
          pick >= 0 && (d > 0 ? gain > 0 && sum - 1 >= from : gain < 0 && sum + 1 <= to);
      if (forced || worth) {
        if (pick < 0) {
          return v;
        }
        walk[pick] -= d;
        sum -= d;
        others -= d * gain;
      }
      if (sum < from || sum > to || val(i, next) + others > limit) {
        return v;
      }
      v = next;
    }
    if (v == bound || cost(i, bound, smin, smax) <= limit) {
      return bound;
    }
    // cost(i, v) is within limit and cost(i, bound) is not
    long l = v;
    long h = bound;
    while (Math.abs(h - l) > 1) {
      long m = l + (h - l) / 2;
      if (cost(i, m, smin, smax) <= limit) {
        l = m;
      } else {
        h = m;
      }
    }
    return l;
  }

  // the least cost with x[i] = v, INFINITE if no assignment of the others fits
  private long cost(int i, long v, long smin, long smax) {
    long rest = leastWithin(i, smin - v, smax - v);
    return rest == INFINITE ? INFINITE : val(i, v) + rest;
  }

  private void narrow(
      Store store, int i, long smin, long smax, long lower, long limit, long alpha, long beta) {
    long centre = best[i];
    // Lagrangian bounds lower + f(v) - f(u) - lambda * (v - u), u the least f(u) - lambda * u
    long ua = at(i, alpha);
    long fa = val(i, ua);
    long ub = at(i, beta);
    long fb = val(i, ub);
    long l = centre;
    long h = hi[i];
    while (l < h) {
      long m = h - (h - l) / 2;
      if (lower + val(i, m) - fa - alpha * (m - ua) <= limit) {
        l = m;
      } else {
        h = m - 1;
      }
    }
    long max = l;
    l = lo[i];
    h = centre;
    while (l < h) {
      long m = l + (h - l) / 2;
      if (lower + val(i, m) - fb - beta * (m - ub) <= limit) {
        h = m;
      } else {
        l = m + 1;
      }
    }
    long min = l;

    if (exact) {
      if (max > centre) {
        max = exactBound(i, 1, max, smin, smax, lower, limit);
      }
      if (min < centre) {
        min = exactBound(i, -1, min, smin, smax, lower, limit);
      }
    }

    if (min > lo[i] || max < hi[i]) {
      x[i].domain.in(store.level, x[i], (int) min, (int) max);
    }
  }

  @Override
  public boolean satisfied() {
    if (!total.singleton()) {
      return false;
    }
    long sum = 0;
    long value = 0;
    for (int i = 0; i < n; i++) {
      if (!x[i].singleton()) {
        return false;
      }
      sum += x[i].value();
      value += val(i, x[i].value());
    }
    return sum == total.value() && value <= cost.min();
  }

  // ---- explanations

  private void boundsBefore(AtomicTrail trail, int position) {
    for (int j = 0; j < n; j++) {
      lo[j] = trail.minBefore(x[j], position);
      hi[j] = trail.maxBefore(x[j], position);
    }
  }

  private boolean rootWithinCreation(AtomicTrail trail) {
    for (int j = 0; j < n; j++) {
      IntDomain d = trail.rootDomain(x[j]);
      if (d.min() < min0[j] || d.max() > max0[j]) {
        return false;
      }
    }
    return true;
  }

  // the Lagrangian bound at lambda of the variables but skip, without the total
  private long lagrangian(int skip, long lambda) {
    long s = 0;
    for (int j = 0; j < n; j++) {
      if (j != skip) {
        long v = at(j, lambda);
        s += val(j, v) - lambda * (v - lo[j]);
      }
    }
    return s;
  }

  // the bounds the Lagrangian bound at lambda depends on, and the bound of total for its sign
  private void lagrangianReason(
      AtomicTrail trail, int position, int skip, long lambda, EntryList out) {
    for (int j = 0; j < n; j++) {
      if (j == skip) {
        continue;
      }
      long v = at(j, lambda);
      if (v == lo[j] && (lo[j] == min0[j] || marginal(j, lo[j]) > lambda)) {
        trail.addLowerBound(x[j], position, out);
      }
      if (v == hi[j] && (hi[j] == max0[j] || marginal(j, hi[j] + 1) < lambda)) {
        trail.addUpperBound(x[j], position, out);
      }
    }
    if (lambda > 0) {
      trail.addLowerBound(total, position, out);
    } else if (lambda < 0) {
      trail.addUpperBound(total, position, out);
    }
  }

  // the marginal cost at which the Lagrangian bound of the variables but skip with a sum in
  // [tlo, thi] is their least cost; the sum range must meet the sums of their bounds
  private long dual(int skip, long tlo, long thi) {
    long freeLow = units(skip, -1);
    long freeHigh = units(skip, 0);
    if (thi < freeLow) {
      return threshold(skip, thi);
    }
    if (tlo > freeHigh) {
      return threshold(skip, tlo);
    }
    return 0;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (getClass() != ConvexAllocation.class || !rootWithinCreation(trail)) {
      return false;
    }
    int kind = trail.kind(entry);
    if (kind != AtomicTrail.GE && kind != AtomicTrail.LE) {
      return false;
    }
    boolean ge = kind == AtomicTrail.GE;
    long bound = trail.value(entry);
    IntVar v = trail.variable(entry);
    boundsBefore(trail, entry);
    long smin = trail.minBefore(total, entry);
    long smax = trail.maxBefore(total, entry);
    long cmax = trail.maxBefore(cost, entry);
    long sl = 0;
    long su = 0;
    for (int j = 0; j < n; j++) {
      sl += lo[j];
      su += hi[j];
    }
    if (sl > smax || su < smin) {
      return false;
    }
    marginalRange();

    if (v == cost) {
      if (!ge) {
        return false;
      }
      long lambda = dual(-1, smin, smax);
      long s = lagrangian(-1, lambda) + lambda * ((lambda >= 0 ? smin : smax) - sl);
      if (s < bound) {
        return false;
      }
      lagrangianReason(trail, entry, -1, lambda, out);
      return true;
    }

    if (v == total) {
      return explainTotal(trail, entry, ge, bound, sl, su, cmax, out);
    }

    for (int i = 0; i < n; i++) {
      if (x[i] == v && explainVariable(trail, entry, i, ge, bound, smin, smax, sl, su, cmax, out)) {
        return true;
      }
    }
    return false;
  }

  private boolean explainTotal(
      AtomicTrail trail,
      int entry,
      boolean ge,
      long bound,
      long sl,
      long su,
      long cmax,
      EntryList out) {
    if (ge ? sl >= bound : su <= bound) {
      for (int j = 0; j < n; j++) {
        if (ge) {
          trail.addLowerBound(x[j], entry, out);
        } else {
          trail.addUpperBound(x[j], entry, out);
        }
      }
      return true;
    }
    // every sum t beyond the bound costs more than cmax: the bound at lambda is linear in t
    long t = ge ? bound - 1 : bound + 1;
    if (t < sl || t > su) {
      return false;
    }
    long lambda = dual(-1, t, t);
    if (ge ? lambda > 0 : lambda < 0) {
      return false;
    }
    if (lagrangian(-1, lambda) + lambda * (t - sl) <= cmax) {
      return false;
    }
    lagrangianReasonFixedSum(trail, entry, lambda, out);
    trail.addUpperBound(cost, entry, out);
    return true;
  }

  private void lagrangianReasonFixedSum(AtomicTrail trail, int entry, long lambda, EntryList out) {
    // the same as lagrangianReason without the bound of total, which is what is explained
    for (int j = 0; j < n; j++) {
      long v = at(j, lambda);
      if (v == lo[j] && (lo[j] == min0[j] || marginal(j, lo[j]) > lambda)) {
        trail.addLowerBound(x[j], entry, out);
      }
      if (v == hi[j] && (hi[j] == max0[j] || marginal(j, hi[j] + 1) < lambda)) {
        trail.addUpperBound(x[j], entry, out);
      }
    }
  }

  private boolean explainVariable(
      AtomicTrail trail,
      int entry,
      int i,
      boolean ge,
      long bound,
      long smin,
      long smax,
      long sl,
      long su,
      long cmax,
      EntryList out) {
    // the sum of the others cannot reach the total
    if (ge ? smin - (su - hi[i]) >= bound : smax - (sl - lo[i]) <= bound) {
      if (ge) {
        trail.addLowerBound(total, entry, out);
      } else {
        trail.addUpperBound(total, entry, out);
      }
      for (int j = 0; j < n; j++) {
        if (j != i) {
          if (ge) {
            trail.addUpperBound(x[j], entry, out);
          } else {
            trail.addLowerBound(x[j], entry, out);
          }
        }
      }
      return true;
    }
    // every value w beyond the bound costs more than cmax: f(w) - lambda * w only grows past w0
    long w0 = ge ? bound - 1 : bound + 1;
    if (w0 < min0[i] || w0 > max0[i]) {
      return false;
    }
    long[] candidates = new long[3];
    int count = 0;
    long olo = sl - lo[i];
    long ohi = su - hi[i];
    long tlo = Math.max(smin - w0, olo);
    long thi = Math.min(smax - w0, ohi);
    if (tlo <= thi) {
      candidates[count++] = dual(i, tlo, thi);
    }
    long t = target(Math.max(smin, sl), Math.min(smax, su));
    boolean free = t >= units(-1, -1) && t <= units(-1, 0);
    long lambda = free ? 0 : threshold(-1, t);
    candidates[count++] = ge ? upperDual(lambda, t) : lambda;
    if (free) {
      count--;
      candidates[count++] = 0;
    }
    for (int k = 0; k < count; k++) {
      long c = candidates[k];
      if (ge ? w0 > min0[i] && marginal(i, w0) > c : w0 < max0[i] && marginal(i, w0 + 1) < c) {
        continue;
      }
      long s = lagrangian(i, c) + val(i, w0) + c * ((c >= 0 ? smin : smax) - w0 - olo);
      if (s > cmax) {
        lagrangianReason(trail, entry, i, c, out);
        trail.addUpperBound(cost, entry, out);
        return true;
      }
    }
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (getClass() != ConvexAllocation.class || !rootWithinCreation(trail)) {
      return false;
    }
    int now = trail.size();
    boundsBefore(trail, now);
    long smin = trail.minBefore(total, now);
    long smax = trail.maxBefore(total, now);
    long cmax = trail.maxBefore(cost, now);
    long sl = 0;
    long su = 0;
    for (int j = 0; j < n; j++) {
      sl += lo[j];
      su += hi[j];
    }
    if (sl > smax || su < smin) {
      boolean low = sl > smax;
      for (int j = 0; j < n; j++) {
        if (low) {
          trail.addLowerBound(x[j], now, out);
        } else {
          trail.addUpperBound(x[j], now, out);
        }
      }
      if (low) {
        trail.addUpperBound(total, now, out);
      } else {
        trail.addLowerBound(total, now, out);
      }
      return true;
    }
    marginalRange();
    long lambda = dual(-1, smin, smax);
    long s = lagrangian(-1, lambda) + lambda * ((lambda >= 0 ? smin : smax) - sl);
    if (s <= cmax) {
      return false;
    }
    lagrangianReason(trail, now, -1, lambda, out);
    trail.addUpperBound(cost, now, out);
    return true;
  }

  @Override
  public boolean checksReasons() {
    return true;
  }

  @Override
  public ConvexAllocation copy(VarMap map) {
    return new ConvexAllocation(map.get(x), f, map.get(total), map.get(cost));
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id()).append(" : ConvexAllocation([");
    for (int i = 0; i < n; i++) {
      if (i > 0) {
        result.append(", ");
      }
      result.append(x[i]);
    }
    result.append("], [");
    for (int i = 0; i < n; i++) {
      if (i > 0) {
        result.append(", ");
      }
      result.append(f[i]);
    }
    result.append("], ").append(total).append(", ").append(cost).append(")");
    return result.toString();
  }
}
