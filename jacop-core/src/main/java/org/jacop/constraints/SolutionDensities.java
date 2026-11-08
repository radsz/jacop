/*
 * SolutionDensities.java
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
import java.util.IdentityHashMap;
import java.util.Map;
import org.jacop.constraints.regular.LayeredGraphConstraint;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.LinearForm;

/**
 * Solution densities of constraints, for counting-based search (Pesant, Quimper and Zanarini,
 * "Counting-Based Search: Branching Heuristics for Constraint Satisfaction Problems", JAIR 43,
 * 2012). The solution density of a variable x and a value v in a constraint c is the share of the
 * solutions of c, over the current domains, in which x takes v. The densities of one variable sum
 * to 1.
 *
 * <ul>
 *   <li>Alldifferent ({@link Alldistinct}, {@link Alldifferent}, {@link Alldiff}): the solutions
 *       are the perfect matchings of the value graph, counted by the permanent of its 0/1 matrix,
 *       which is estimated by the Brégman–Minc upper bound perm(A) &le; &prod;<sub>i</sub>
 *       (d<sub>i</sub>!)<sup>1/d<sub>i</sub></sup> over the row degrees d<sub>i</sub> (Brégman,
 *       Soviet Math. Dokl. 14, 1973; conjectured by Minc 1963). As in Pesant et al., the density of
 *       x = v is the bound of the matrix with x fixed to v, divided by the sum of those bounds over
 *       the values of x. Fixing x = v removes v from every other row that holds it, so the ratio
 *       depends only on the sum, over those rows y, of log f(d<sub>y</sub> - 1) - log
 *       f(d<sub>y</sub>), f(d) = (d!)<sup>1/d</sup>: all the densities of the constraint take one
 *       pass over its domains. Rows of full width added to make the matrix square, as Pesant et al.
 *       do when there are more values than variables, change every value by the same factor, so
 *       they are left out. The Liang–Bai bound, which Pesant et al. combine with this one by a
 *       minimum, is not used: it needs the degrees in sorted order for every pair.
 *   <li>Linear constraints (anything {@link LinearForms#of} reads, with relation =, &le; or &ge;):
 *       the solutions are counted exactly by the dynamic program over partial sums of Trick ("A
 *       dynamic programming approach for consistency and propagation for knapsack constraints",
 *       Annals of OR 118, 2003), the counting algorithm Pesant et al. use for knapsack constraints,
 *       when the partial sums span at most {@link #LINEAR_BUDGET} cells over all variables. Larger
 *       ones, and those with a variable twice, report nothing.
 *   <li>{@link LayeredGraphConstraint} (regular): the paths of the layered graph, counted exactly
 *       by a forward and a backward pass (Pesant et al., Section 4.3).
 * </ul>
 *
 * <p>Counts are kept as doubles normalised per layer, so the densities stay exact ratios without
 * overflow.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class SolutionDensities {

  /** The largest number of partial-sum cells times values the linear count visits. */
  public static final int LINEAR_BUDGET = 1 << 18;

  /** Receives the density of a variable and one of its values. */
  @FunctionalInterface
  public interface Sink {
    /**
     * It receives one density.
     *
     * @param x the variable.
     * @param value a value of its domain.
     * @param density the share of the solutions of the constraint with x = value, in [0, 1].
     */
    void density(IntVar x, int value, double density);
  }

  // log((d!)^(1/d)) by d, grown on demand
  private double[] logFactor = new double[] {Double.NEGATIVE_INFINITY, 0.0d};

  // scratch for the alldifferent pass
  private int[] values = new int[64];
  private double[] valueWeight = new double[64];

  /**
   * It tells whether the constraint has densities.
   *
   * @param c the constraint.
   * @return true for alldifferent, linear and layered-graph constraints.
   */
  public static boolean supports(Constraint c) {
    if (isAlldifferent(c) || c instanceof LayeredGraphConstraint) {
      return true;
    }
    LinearForm f = LinearForms.of(c);
    return f != null && f.relation() != LinearForm.NE && distinct(f.vars());
  }

  /**
   * It tells whether the densities of a supported constraint come from its linear form.
   *
   * @param c the constraint.
   * @return true when it is neither an alldifferent nor a layered graph.
   */
  public static boolean isLinear(Constraint c) {
    return !isAlldifferent(c) && !(c instanceof LayeredGraphConstraint);
  }

  private static boolean isAlldifferent(Constraint c) {
    return c instanceof Alldistinct || c instanceof Alldifferent;
  }

  private static boolean distinct(IntVar[] vars) {
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    for (IntVar x : vars) {
      if (seen.put(x, Boolean.TRUE) != null) {
        return false;
      }
    }
    return true;
  }

  /**
   * It reports the densities of the unfixed variables of a constraint {@link #supports} accepts.
   *
   * @param c the constraint.
   * @param sink receives the densities.
   * @return false if the constraint has no solution over the current domains or is too large to
   *     count; nothing is then reported.
   */
  public boolean densities(Constraint c, Sink sink) {
    if (isAlldifferent(c)) {
      return alldifferent(c.arguments().toArray(new IntVar[0]), sink);
    }
    if (c instanceof LayeredGraphConstraint g) {
      return g.solutionDensities(sink);
    }
    LinearForm f = LinearForms.of(c);
    return f != null && linear(f, sink);
  }

  private double logFactor(int d) {
    if (d >= logFactor.length) {
      int old = logFactor.length;
      logFactor = Arrays.copyOf(logFactor, Math.max(d + 1, 2 * old));
      // log d! = d * logFactor[d]
      double logFact = (old - 1) * logFactor[old - 1];
      for (int k = old; k < logFactor.length; k++) {
        logFact += Math.log(k);
        logFactor[k] = logFact / k;
      }
    }
    return logFactor[d];
  }

  /**
   * Densities of an alldifferent by the Brégman–Minc bound.
   *
   * @param vars the variables.
   * @param sink receives the densities.
   * @return false when nothing was reported.
   */
  public boolean alldifferent(IntVar[] vars, Sink sink) {
    int total = 0;
    for (IntVar y : vars) {
      if (!y.singleton()) {
        total += y.getSize();
      }
    }
    if (total == 0) {
      return false;
    }
    if (values.length < total) {
      values = new int[total];
    }
    int n = 0;
    for (IntVar y : vars) {
      if (!y.singleton()) {
        for (ValueEnumeration e = y.dom().valueEnumeration(); e.hasMoreElements(); ) {
          values[n++] = e.nextElement();
        }
      }
    }
    Arrays.sort(values, 0, n);
    int distinct = 0;
    for (int k = 0; k < n; k++) {
      if (k == 0 || values[k] != values[k - 1]) {
        values[distinct++] = values[k];
      }
    }
    if (valueWeight.length < distinct) {
      valueWeight = new double[Math.max(distinct, 2 * valueWeight.length)];
    }
    Arrays.fill(valueWeight, 0, distinct, 0.0d);
    // the values taken by fixed variables leave no solution to the rows that still hold them
    for (IntVar y : vars) {
      if (y.singleton()) {
        int k = Arrays.binarySearch(values, 0, distinct, y.value());
        if (k >= 0) {
          valueWeight[k] = Double.NEGATIVE_INFINITY;
        }
      }
    }
    for (IntVar y : vars) {
      if (!y.singleton()) {
        int d = y.getSize();
        double delta = logFactor(d - 1) - logFactor(d);
        for (ValueEnumeration e = y.dom().valueEnumeration(); e.hasMoreElements(); ) {
          int k = Arrays.binarySearch(values, 0, distinct, e.nextElement());
          valueWeight[k] += delta;
        }
      }
    }
    // the row of x itself holds every value of x, which shifts all of them by the same amount, so
    // the weight of x = v is valueWeight[v] minus x's own term, the same for each v of x
    for (IntVar x : vars) {
      if (x.singleton()) {
        continue;
      }
      double max = Double.NEGATIVE_INFINITY;
      for (ValueEnumeration e = x.dom().valueEnumeration(); e.hasMoreElements(); ) {
        max = Math.max(max, valueWeight[Arrays.binarySearch(values, 0, distinct, e.nextElement())]);
      }
      if (max == Double.NEGATIVE_INFINITY) {
        return false;
      }
      double sum = 0.0d;
      for (ValueEnumeration e = x.dom().valueEnumeration(); e.hasMoreElements(); ) {
        sum +=
            Math.exp(valueWeight[Arrays.binarySearch(values, 0, distinct, e.nextElement())] - max);
      }
      for (ValueEnumeration e = x.dom().valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        sink.density(
            x, v, Math.exp(valueWeight[Arrays.binarySearch(values, 0, distinct, v)] - max) / sum);
      }
    }
    return true;
  }

  /**
   * Densities of a linear constraint by exact counting over partial sums.
   *
   * @param f the constraint as a linear form.
   * @param sink receives the densities.
   * @return false when nothing was reported.
   */
  public boolean linear(LinearForm f, Sink sink) {
    IntVar[] all = f.vars();
    long[] w = f.weights();
    long c = f.c();
    int n = 0;
    for (IntVar x : all) {
      if (!x.singleton()) {
        n++;
      }
    }
    if (n == 0) {
      return false;
    }
    IntVar[] x = new IntVar[n];
    long[] a = new long[n];
    n = 0;
    for (int i = 0; i < all.length; i++) {
      if (all[i].singleton()) {
        c -= w[i] * all[i].value();
      } else if (w[i] != 0) {
        x[n] = all[i];
        a[n++] = w[i];
      }
    }
    if (n == 0) {
      return false;
    }
    // the prefix sums of the first k terms lie in [lo[k], lo[k] + width[k])
    long[] lo = new long[n + 1];
    long[] hi = new long[n + 1];
    long cells = 0;
    for (int k = 0; k < n; k++) {
      long p = a[k] * x[k].min();
      long q = a[k] * x[k].max();
      lo[k + 1] = lo[k] + Math.min(p, q);
      hi[k + 1] = hi[k] + Math.max(p, q);
      cells += (hi[k] - lo[k] + 1) * (long) x[k].getSize();
      if (cells > LINEAR_BUDGET || hi[k + 1] - lo[k + 1] >= LINEAR_BUDGET) {
        return false;
      }
    }
    // forward[k][s - lo[k]]: the share of assignments of the first k terms that sum to s
    double[][] forward = new double[n + 1][];
    forward[0] = new double[] {1.0d};
    for (int k = 0; k < n; k++) {
      double[] next = new double[(int) (hi[k + 1] - lo[k + 1] + 1)];
      double[] cur = forward[k];
      for (ValueEnumeration e = x[k].dom().valueEnumeration(); e.hasMoreElements(); ) {
        int shift = (int) (lo[k] + a[k] * e.nextElement() - lo[k + 1]);
        for (int s = 0; s < cur.length; s++) {
          next[s + shift] += cur[s];
        }
      }
      forward[k + 1] = normalised(next);
    }
    // backward[k][t]: the share of assignments of terms k.. that, added to a prefix summing to
    // lo[k] + t, satisfy the relation
    double[] back = new double[(int) (hi[n] - lo[n] + 1)];
    double satisfied = 0.0d;
    for (int t = 0; t < back.length; t++) {
      long s = lo[n] + t;
      boolean ok =
          switch (f.relation()) {
            case LinearForm.LE -> s <= c;
            case LinearForm.GE -> s >= c;
            default -> s == c;
          };
      back[t] = ok ? 1.0d : 0.0d;
      satisfied += back[t] * forward[n][t];
    }
    if (satisfied <= 0.0d) {
      return false;
    }
    double[][] counts = new double[n][];
    for (int k = n - 1; k >= 0; k--) {
      double[] cur = forward[k];
      double[] prev = new double[cur.length];
      int size = x[k].getSize();
      counts[k] = new double[size];
      int j = 0;
      for (ValueEnumeration e = x[k].dom().valueEnumeration(); e.hasMoreElements(); j++) {
        int shift = (int) (lo[k] + a[k] * e.nextElement() - lo[k + 1]);
        double count = 0.0d;
        for (int s = 0; s < cur.length; s++) {
          double b = back[s + shift];
          prev[s] += b;
          count += cur[s] * b;
        }
        counts[k][j] = count;
      }
      back = normalised(prev);
    }
    for (int k = 0; k < n; k++) {
      double sum = 0.0d;
      for (double v : counts[k]) {
        sum += v;
      }
      if (sum <= 0.0d) {
        return false;
      }
    }
    for (int k = 0; k < n; k++) {
      double sum = 0.0d;
      for (double v : counts[k]) {
        sum += v;
      }
      int j = 0;
      for (ValueEnumeration e = x[k].dom().valueEnumeration(); e.hasMoreElements(); j++) {
        sink.density(x[k], e.nextElement(), counts[k][j] / sum);
      }
    }
    return true;
  }

  // divides by the sum (or the largest entry), so that long sums do not overflow; densities are
  // ratios within one variable, which a common factor of a layer does not change
  private static double[] normalised(double[] layer) {
    double max = 0.0d;
    for (double v : layer) {
      max = Math.max(max, v);
    }
    if (max > 0.0d && (max > 1e100 || max < 1e-100)) {
      for (int s = 0; s < layer.length; s++) {
        layer[s] /= max;
      }
    }
    return layer;
  }

  /**
   * Normalises the densities of one variable, for layered-graph counts.
   *
   * @param counts the counts of the values, in the order of {@code vals}.
   * @param vals the values.
   * @param size how many entries are used.
   * @param x the variable.
   * @param sink receives the densities.
   * @return false when the counts are all zero.
   */
  public static boolean report(double[] counts, int[] vals, int size, IntVar x, Sink sink) {
    double sum = 0.0d;
    for (int j = 0; j < size; j++) {
      sum += counts[j];
    }
    if (sum <= 0.0d) {
      return false;
    }
    for (int j = 0; j < size; j++) {
      sink.density(x, vals[j], counts[j] / sum);
    }
    return true;
  }
}
