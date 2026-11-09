/*
 * ChanceSum.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.prob.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.Monotone;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Linearizations;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;
import org.jacop.prob.dist.Dist;

/**
 * A chance constraint over independent random weights: {@code Pr(sum(i, W[i] * x[i]) <= c) >=
 * alpha}, where the W[i] are independent discrete random variables of non-negative values, the x[i]
 * non-negative integer variables (usually 0/1) and c an integer variable, the capacity.
 *
 * <p>The probability only decreases when an x[i] grows or c shrinks, so the constraint holds for
 * some assignment of the current domains exactly when it holds with every x[i] at its minimum and c
 * at its maximum. It keeps the distribution of that smallest load, {@code L = sum(i, W[i] *
 * min(x[i]))}, over the loads {@code 0..max(c)} with a convolution per item, and:
 *
 * <ul>
 *   <li>fails when {@code Pr(L <= max(c)) < alpha};
 *   <li>lowers the maximum of each x[j] to the largest value v with {@code Pr(L - W[j] * min(x[j])
 *       + W[j] * v <= max(c)) >= alpha};
 *   <li>raises the minimum of c to the alpha-quantile of L.
 * </ul>
 *
 * This is domain consistent for 0/1 variables x and bounds consistent otherwise. The probabilities
 * are intervals of doubles rounded outward; a comparison with alpha that the intervals leave open
 * is decided on exact BigInteger numerators, so nothing is pruned that exact arithmetic would keep.
 *
 * <p>For lazy clause generation, a pruned value is explained by lower bounds of x and the upper
 * bound of c that already make the probability too small: the items are added largest expected load
 * first, until the load they give alone breaks the constraint.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ChanceSum extends Constraint
    implements SatisfiedPresent,
        Copyable<ChanceSum>,
        Monotone,
        Explainable,
        Linearizations.Relaxable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  // the loads are kept as arrays over 0..max(c)
  private static final int CAP_LIMIT = 1 << 24;

  /** The variables, distinct; the weights of a repeated variable are added up. */
  final IntVar[] x;

  /** The random weight of each variable. */
  final Dist[] w;

  /** The capacity. */
  final IntVar c;

  /** The probability threshold alphaNum / alphaDen. */
  final long alphaNum;

  final long alphaDen;

  // enclosure of alpha
  private final double alphaLo;
  private final double alphaHi;

  // enclosures of the probabilities of the values of each weight
  private final double[][] pLo;
  private final double[][] pHi;

  // the mean of each weight, for the order of explanations
  private final double[] mean;

  // scratch
  private LoadDistribution load;
  private LoadDistribution other;
  private double[] cumLo;
  private double[] cumHi;
  private final double[] range = new double[2];

  /**
   * It constructs the constraint Pr(sum(i, W[i] * x[i]) &lt;= c) &gt;= alphaNum / alphaDen.
   *
   * @param x the variables, at least 0
   * @param w the independent random weights, of values at least 0
   * @param c the capacity
   * @param alphaNum the numerator of the probability threshold
   * @param alphaDen the denominator of the probability threshold, positive
   */
  public ChanceSum(IntVar[] x, Dist[] w, IntVar c, long alphaNum, long alphaDen) {
    checkInputForNullness(new String[] {"x", "w", "c"}, x, w, new Object[] {c});
    if (x.length != w.length) {
      throw new IllegalArgumentException("ChanceSum has x and w of different lengths");
    }
    if (alphaDen <= 0) {
      throw new IllegalArgumentException("ChanceSum needs a positive denominator of alpha");
    }
    Map<IntVar, Dist> merged = new LinkedHashMap<>();
    for (int i = 0; i < x.length; i++) {
      if (x[i].min() < 0) {
        throw new IllegalArgumentException("ChanceSum needs variables of at least 0: " + x[i]);
      }
      if (w[i].min() < 0) {
        throw new IllegalArgumentException("ChanceSum needs weights of values at least 0: " + w[i]);
      }
      if (x[i] == c) {
        throw new IllegalArgumentException("ChanceSum has the capacity among x: " + c);
      }
      merged.merge(x[i], w[i], Dist::plus);
    }
    this.x = merged.keySet().toArray(new IntVar[0]);
    this.w = merged.values().toArray(new Dist[0]);
    this.c = c;
    this.alphaNum = alphaNum;
    this.alphaDen = alphaDen;
    double[] a = org.jacop.prob.num.ProbArith.enclosure(alphaNum, alphaDen);
    alphaLo = a[0];
    alphaHi = a[1];
    int n = this.x.length;
    pLo = new double[n][];
    pHi = new double[n][];
    mean = new double[n];
    for (int i = 0; i < n; i++) {
      double[][] e = LoadDistribution.enclosures(this.w[i]);
      pLo[i] = e[0];
      pHi[i] = e[1];
      mean[i] = (double) this.w[i].meanNumerator() / this.w[i].den();
    }
    numberId = idNumber.incrementAndGet();
    queueIndex = 2;
    setScope(Stream.concat(Arrays.stream(this.x), Stream.of(c)));
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  // the load arrays over 0..cap, reallocated when the capacity grew (after a restart)
  private void ensureCap(int cap) {
    if (cap >= CAP_LIMIT) {
      throw new IllegalArgumentException(
          "ChanceSum needs a capacity below " + CAP_LIMIT + ", has " + cap);
    }
    if (load == null || load.cap != cap) {
      load = new LoadDistribution(cap);
      other = new LoadDistribution(cap);
      cumLo = new double[cap + 1];
      cumHi = new double[cap + 1];
    }
  }

  /**
   * Compares Pr(L &lt;= t) with alpha for the load L of the given multipliers.
   *
   * @return negative when it is certainly below alpha, positive when it is at least alpha
   */
  private int compare(double lo, double hi, long[] m, int count, Dist[] dists, long t) {
    if (hi < alphaLo) {
      return -1;
    }
    if (lo >= alphaHi) {
      return 1;
    }
    return LoadDistribution.exactAtMost(dists, m, count, t, alphaNum, alphaDen) < 0 ? -1 : 1;
  }

  @Override
  public void consistency(Store store) {
    if (alphaNum <= 0) {
      // every load satisfies a threshold of 0
      removeConstraint();
      return;
    }
    if (c.max() < 0) {
      throw Store.failException;
    }
    int cap = c.max();
    ensureCap(cap);
    int n = x.length;
    long[] m = new long[n];
    load.clear();
    for (int i = 0; i < n; i++) {
      m[i] = x[i].min();
      if (m[i] > 0) {
        load.add(w[i], pLo[i], pHi[i], m[i]);
      }
    }
    load.atMost(cap, range);
    if (compare(range[0], range[1], m, n, w, cap) < 0) {
      throw Store.failException;
    }
    load.cumulative(cumLo, cumHi);

    // the capacity: the smallest t with Pr(L <= t) >= alpha
    int t = Math.max(c.min(), 0);
    while (t < cap && compare(cumLo[t], cumHi[t], m, n, w, t) < 0) {
      t++;
    }
    if (t > c.min()) {
      c.domain.inMin(store.level, c, t);
    }

    for (int j = 0; j < n; j++) {
      IntVar v = x[j];
      if (v.singleton()) {
        continue;
      }
      LoadDistribution rest = load;
      if (m[j] > 0) {
        rest = other;
        rest.clear();
        for (int i = 0; i < n; i++) {
          if (i != j && m[i] > 0) {
            rest.add(w[i], pLo[i], pHi[i], m[i]);
          }
        }
        rest.cumulative(cumLo, cumHi);
      }
      // the largest value of x[j] that keeps the probability, by bisection: it holds at the minimum
      long good = v.min();
      long bad = (long) v.max() + 1;
      while (bad - good > 1) {
        long mid = (good + bad) >>> 1;
        if (holdsWith(j, mid, m, cap)) {
          good = mid;
        } else {
          bad = mid;
        }
      }
      if (bad <= v.max()) {
        v.domain.inMax(store.level, v, (int) good);
      }
      if (m[j] > 0) {
        load.cumulative(cumLo, cumHi);
      }
    }
  }

  // whether Pr(L' + W[j] * value <= cap) >= alpha, L' the load without j in cumLo and cumHi
  private boolean holdsWith(int j, long value, long[] m, int cap) {
    double lo = 0;
    double hi = 0;
    Dist d = w[j];
    for (int k = 0; k < d.size(); k++) {
      long rest = cap - value * d.value(k);
      if (rest < 0) {
        break;
      }
      lo = LoadDistribution.down(lo + LoadDistribution.down(pLo[j][k] * cumLo[(int) rest]));
      hi = LoadDistribution.up(hi + LoadDistribution.up(pHi[j][k] * cumHi[(int) rest]));
    }
    if (hi < alphaLo) {
      return false;
    }
    if (lo >= alphaHi) {
      return true;
    }
    long saved = m[j];
    m[j] = value;
    int sign = LoadDistribution.exactAtMost(w, m, m.length, cap, alphaNum, alphaDen);
    m[j] = saved;
    return sign >= 0;
  }

  @Override
  public boolean satisfied() {
    // the largest load against the smallest capacity
    if (c.min() < 0) {
      return alphaNum <= 0;
    }
    int n = x.length;
    long[] m = new long[n];
    for (int i = 0; i < n; i++) {
      m[i] = x[i].max();
    }
    return LoadDistribution.exactAtMost(w, m, n, c.min(), alphaNum, alphaDen) >= 0;
  }

  @Override
  public int freeDirections(Var v) {
    if (v == c) {
      return INCREASE;
    }
    return DECREASE;
  }

  // ---- linear relaxation

  // the scale of the rows, whose coefficients are rounded to multiples of 1 / SCALE
  private static final long SCALE = 1024;

  /**
   * Rows from the Cantelli inequality. With mean mu and variance s of the load, Pr(L &lt;= c) &lt;=
   * s / (s + (mu - c)^2) when c &lt; mu, so the constraint needs mu - c &lt;= k sqrt(s) with k =
   * sqrt((1 - alpha) / alpha). Both mu and an upper bound on s (x^2 &lt;= max(x) x) are linear in
   * x, and sqrt(s) &lt;= (s + s0) / (2 sqrt(s0)) for every s0 &gt; 0, so each s0 gives the valid
   * row sum(i, (mu[i] - k v[i] max(x[i]) / (2 sqrt(s0))) x[i]) - c &lt;= k sqrt(s0) / 2. The rows
   * are scaled and rounded so that each one stays implied: coefficients of x down, the right-hand
   * side up.
   */
  @Override
  public List<LinearForm> relaxation() {
    List<LinearForm> rows = new ArrayList<>();
    if (alphaNum <= 0 || alphaLo <= 0) {
      return rows;
    }
    int n = x.length;
    double[] mu = new double[n];
    double[] spread = new double[n];
    double total = 0;
    for (int i = 0; i < n; i++) {
      Dist d = w[i];
      double second = 0;
      for (int k = 0; k < d.size(); k++) {
        second += (double) d.value(k) * d.value(k) * d.weight(k) / d.den();
      }
      mu[i] = mean[i];
      // the variance, rounded up, times the largest value of x[i]
      spread[i] = Math.max(0, second - mean[i] * mean[i]) * (1 + 1e-9) * x[i].max();
      total += spread[i];
    }
    double k = Math.sqrt(Math.max(0, (1 - alphaLo) / alphaLo)) * (1 + 1e-9);
    IntVar[] vars = Arrays.copyOf(x, n + 1);
    vars[n] = c;
    double[] fractions =
        total > 0 ? new double[] {1.0 / 64, 1.0 / 16, 1.0 / 4, 1.0 / 2, 1} : new double[] {1};
    for (double f : fractions) {
      double s0 = Math.max(total * f, 1e-9);
      double root = Math.sqrt(s0);
      long[] coef = new long[n + 1];
      for (int i = 0; i < n; i++) {
        double a = mu[i] - k * spread[i] / (2 * root);
        // one unit below the scaled value covers the rounding of the doubles
        coef[i] = (long) Math.floor(a * SCALE) - 1;
      }
      coef[n] = -SCALE;
      long rhs = (long) Math.ceil(k * root / 2 * SCALE) + 1;
      rows.add(new LinearForm(vars, coef, rhs, LinearForm.LE));
    }
    return rows;
  }

  // ---- lazy clause generation

  /**
   * Adds to out the bounds before position, with one bound replaced by a hypothesis, that break the
   * constraint, or returns false.
   */
  private boolean contradiction(
      AtomicTrail trail, int position, IntVar hypVar, long hypValue, EntryList out) {
    int n = x.length;
    long[] m = new long[n];
    for (int i = 0; i < n; i++) {
      m[i] = x[i] == hypVar ? hypValue : trail.minBefore(x[i], position);
    }
    long cap = c == hypVar ? hypValue : trail.maxBefore(c, position);
    if (cap < 0) {
      if (alphaNum <= 0) {
        return false;
      }
      if (c != hypVar) {
        trail.addUpperBound(c, position, out);
      }
      return true;
    }
    if (cap >= CAP_LIMIT) {
      return false;
    }
    // the items of positive load, largest expected load first
    List<Integer> items = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      if (m[i] > 0) {
        items.add(i);
      }
    }
    items.sort((p, q) -> Double.compare(mean[q] * m[q], mean[p] * m[p]));
    Dist[] dists = new Dist[items.size()];
    long[] mult = new long[items.size()];
    LoadDistribution prefix = new LoadDistribution((int) cap);
    double[] r = new double[2];
    int used = 0;
    boolean broken = false;
    prefix.atMost(cap, r);
    if (compare(r[0], r[1], mult, 0, dists, cap) < 0) {
      broken = true;
    }
    while (!broken && used < items.size()) {
      int i = items.get(used);
      dists[used] = w[i];
      mult[used] = m[i];
      used++;
      prefix.add(w[i], pLo[i], pHi[i], m[i]);
      prefix.atMost(cap, r);
      broken = compare(r[0], r[1], mult, used, dists, cap) < 0;
    }
    if (!broken) {
      return false;
    }
    for (int k = 0; k < used; k++) {
      IntVar v = x[items.get(k)];
      if (v != hypVar) {
        trail.addBoundReaching(v, position, true, mult[k], out);
      }
    }
    if (c != hypVar) {
      trail.addUpperBound(c, position, out);
    }
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    int kind = trail.kind(entry);
    IntVar y = trail.variable(entry);
    boolean isX = Arrays.asList(x).contains(y);
    // x only loses its upper end, c only its lower end
    if (isX ? kind != AtomicTrail.LE : y != c || kind != AtomicTrail.GE) {
      return false;
    }
    int bound = trail.skippedBound(entry);
    // the negation: x >= bound + 1 for x <= bound, c <= bound - 1 for c >= bound
    long hypothesis = isX ? (long) bound + 1 : (long) bound - 1;
    int mark = out.size();
    if (!contradiction(trail, entry, y, hypothesis, out)) {
      out.truncate(mark);
      return false;
    }
    if (bound != trail.value(entry)) {
      trail.addSkippedHoles(entry, bound, out);
    }
    out.sortUnique(mark);
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int mark = out.size();
    if (!contradiction(trail, trail.size(), null, 0, out)) {
      out.truncate(mark);
      return false;
    }
    out.sortUnique(mark);
    return true;
  }

  @Override
  public ChanceSum copy(VarMap map) {
    return new ChanceSum(map.get(x), w.clone(), map.get(c), alphaNum, alphaDen);
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder();
    result.append(id()).append(" : ChanceSum([");
    for (int i = 0; i < x.length; i++) {
      result.append(w[i]).append(" * ").append(x[i]);
      if (i < x.length - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(c).append(", ").append(alphaNum).append('/').append(alphaDen);
    return result.append(')').toString();
  }
}
