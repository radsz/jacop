/*
 * AlldifferentCuts.java
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

package org.jacop.constraints.lp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;

/**
 * Hall-type inequalities of an all-different constraint, separated from an LP solution by sorting.
 * For a set S of its variables, the values are distinct and come from the union U(S) of their
 * domains, so {@code sum_{i in S} x_i} lies between the sum of the |S| smallest and the sum of the
 * |S| largest values of U(S). Over a common domain these inequalities for all S describe the convex
 * hull of the all-different solutions (Williams and Yan, Representations of the all_different
 * predicate of constraint satisfaction in integer programming, INFORMS Journal on Computing
 * 13(2):96-103, 2001; Lee, All-different polytopes, Journal of Combinatorial Optimization
 * 6(3):335-352, 2002), and for each size |S| the most violated lower inequality is over the |S|
 * variables of smallest value in the LP solution (the upper one over the largest), so sorting the
 * values separates them exactly. With different domains, the union of the domains of each prefix of
 * the order gives a valid inequality that is stronger than the one over the common domain.
 *
 * <p>The domains are those of the first separation, made at the root, so the cuts hold for the
 * whole search.
 */
public final class AlldifferentCuts {

  // the least violation of a cut, above a share of its side
  private static final double MIN_VIOLATION = 1e-4;
  private static final double RELATIVE_VIOLATION = 1e-6;

  private final IntVar[] list;

  // the domains of the variables at the first separation
  private IntDomain[] domains;

  /**
   * A cut over variables of the constraint: {@code sum x[vars] >= bound} when lower, else {@code
   * sum x[vars] <= bound}.
   */
  public static final class Cut {
    private final int[] vars;
    private final boolean lower;
    private final long bound;
    private final double efficacy;

    Cut(int[] vars, boolean lower, long bound, double efficacy) {
      this.vars = vars;
      this.lower = lower;
      this.bound = bound;
      this.efficacy = efficacy;
    }

    /**
     * It returns the variables of the cut.
     *
     * @return their positions in the list of the constraint, a copy
     */
    public int[] vars() {
      return vars.clone();
    }

    /**
     * It tells the sense of the cut.
     *
     * @return true for {@code sum x >= bound}, false for {@code sum x <= bound}
     */
    public boolean lower() {
      return lower;
    }

    /**
     * It returns the side of the cut.
     *
     * @return the side
     */
    public long bound() {
      return bound;
    }

    /**
     * It returns the violation of the cut by the values it was separated from, over its norm.
     *
     * @return the efficacy
     */
    public double efficacy() {
      return efficacy;
    }

    @Override
    public String toString() {
      return "sum x" + Arrays.toString(vars) + (lower ? " >= " : " <= ") + bound;
    }
  }

  /**
   * It creates the separation of the cuts of an all-different constraint.
   *
   * @param list the variables, pairwise distinct
   */
  public AlldifferentCuts(IntVar[] list) {
    this.list = list.clone();
  }

  /**
   * It returns the variables of the constraint.
   *
   * @return the variables, a copy
   */
  public IntVar[] literals() {
    return list.clone();
  }

  /**
   * It returns the copy over the variables of a copied store, with the domains of the first
   * separation when there was one.
   *
   * @param map the variables of the copy
   * @return the copy
   */
  public AlldifferentCuts copy(VarMap map) {
    IntVar[] copied = new IntVar[list.length];
    for (int k = 0; k < copied.length; k++) {
      copied[k] = map.get(list[k]);
    }
    AlldifferentCuts c = new AlldifferentCuts(copied);
    c.domains = domains;
    return c;
  }

  /**
   * It returns the cuts violated by values of the variables, the most effective first. The first
   * call takes the current domains of the variables, which must be those of the root.
   *
   * @param value the value of each variable in the LP solution
   * @param limit the most cuts returned
   * @return the cuts
   */
  public List<Cut> separate(double[] value, int limit) {
    int n = list.length;
    if (domains == null) {
      domains = new IntDomain[n];
      for (int i = 0; i < n; i++) {
        domains[i] = list[i].dom().cloneLight();
      }
    }
    Integer[] order = new Integer[n];
    for (int i = 0; i < n; i++) {
      order[i] = i;
    }
    Arrays.sort(order, Comparator.comparingDouble(i -> value[i]));
    List<Cut> cuts = new ArrayList<>();
    try {
      prefixes(order, value, true, cuts);
      Integer[] reversed = new Integer[n];
      for (int i = 0; i < n; i++) {
        reversed[i] = order[n - 1 - i];
      }
      prefixes(reversed, value, false, cuts);
    } catch (ArithmeticException overflow) {
      // the cuts found so far hold
    }
    cuts.sort(Comparator.comparingDouble(Cut::efficacy).reversed());
    return cuts.size() > limit ? new ArrayList<>(cuts.subList(0, limit)) : cuts;
  }

  // the violated cuts over the prefixes of the order: sum of a prefix >= the sum of the smallest
  // values of the union of its domains (lower), or <= the sum of the largest ones
  private void prefixes(Integer[] order, double[] value, boolean lower, List<Cut> cuts) {
    IntDomain union = new IntervalDomain();
    double sum = 0;
    for (int k = 0; k < order.length; k++) {
      int i = order[k];
      union = union.union(domains[i]);
      sum += value[i];
      if (k == 0) {
        continue; // a variable alone is held by its bounds
      }
      long bound = extremeSum(union, k + 1, lower);
      double violation = lower ? bound - sum : sum - bound;
      if (violation > MIN_VIOLATION + RELATIVE_VIOLATION * Math.abs((double) bound)) {
        int[] vars = new int[k + 1];
        for (int t = 0; t <= k; t++) {
          vars[t] = order[t];
        }
        Arrays.sort(vars);
        cuts.add(new Cut(vars, lower, bound, violation / Math.sqrt(k + 1.0)));
      }
    }
  }

  /**
   * Returns the sum of the k smallest (or largest) values of a domain, or, when it has fewer than k
   * values, a sum that no k distinct values of it reach (the cut then states that no k of the
   * variables are distinct, which is what the domains give).
   *
   * @param d the domain
   * @param k the number of values
   * @param smallest whether the smallest values are summed, else the largest
   * @return the sum
   */
  public static long extremeSum(IntDomain d, int k, boolean smallest) {
    List<int[]> intervals = new ArrayList<>();
    for (IntervalEnumeration en = d.intervalEnumeration(); en.hasMoreElements(); ) {
      var in = en.nextElement();
      intervals.add(new int[] {in.min(), in.max()});
    }
    if (intervals.isEmpty()) {
      return 0;
    }
    long sum = 0;
    long left = k;
    for (int t = 0; t < intervals.size() && left > 0; t++) {
      int[] in = intervals.get(smallest ? t : intervals.size() - 1 - t);
      long size = (long) in[1] - in[0] + 1;
      long take = Math.min(size, left);
      // the take values at the low (or high) end of the interval
      long first = smallest ? in[0] : in[1] - take + 1;
      sum = Math.addExact(sum, Math.multiplyExact(take, first) + take * (take - 1) / 2);
      left -= take;
    }
    if (left > 0) {
      // fewer than k values: as if the values went on past the domain, which no assignment reaches
      long end = smallest ? (long) intervals.get(intervals.size() - 1)[1] : intervals.get(0)[0];
      for (long v = 1; v <= left; v++) {
        sum = Math.addExact(sum, smallest ? end + v : end - v);
      }
    }
    return sum;
  }
}
