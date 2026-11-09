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
 * <p>The same inequalities hold with multiplicities ({@link #except}, {@link #cardinality}): when a
 * value v may be taken by at most u_v of the variables and must be taken by at least l_v of them,
 * the sum over S is at least the least sum of a multiset of |S| values of U(S) that takes v at most
 * min(u_v, |{i in S : v in D_i}|) times and at least l_v - |{i not in S : v in D_i}| times (the
 * rest of the l_v must come from S), and at most the greatest such sum; the greedy choice, the
 * forced copies first and then the smallest (largest) values left, gives it. For the
 * all-different-except-0 constraint 0 has no upper limit; for a global cardinality constraint the
 * limits are the bounds of its counters at the root. With fixed counts these are the inequalities
 * of the permutahedron of a multiset, whose points are the vectors that the multiset majorizes (R.
 * Rado, An inequality, Journal of the London Mathematical Society 27(1):1-6, 1952), and sorting
 * again finds the most violated one of each size over a common domain.
 *
 * <p>The domains and the limits are those of the first separation, made at the root, so the cuts
 * hold for the whole search.
 */
public final class AlldifferentCuts {

  // the least violation of a cut, above a share of its side
  private static final double MIN_VIOLATION = 1e-4;
  private static final double RELATIVE_VIOLATION = 1e-6;

  // no limit on the copies of a value
  private static final long UNLIMITED = Long.MAX_VALUE;

  private final IntVar[] list;

  // the values with their own limits, increasing, or an empty array for a plain all-different
  private final int[] special;

  // the counter of each special value, or null when the limits are fixed
  private final IntVar[] counters;

  // the fixed limits of the special values when there are no counters
  private final long[] fixedLeast;
  private final long[] fixedMost;

  // the most copies of a value that is not special: 1, 0 (closed cardinality) or UNLIMITED
  private final long otherMost;

  // the domains of the variables at the first separation
  private IntDomain[] domains;

  // the limits of the special values at the first separation, the most at most list.length
  private long[] least;
  private long[] most;

  // for each special value, the variables whose domain holds it at the first separation
  private int[] holding;

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
    this(list, new int[0], null, null, null, 1);
  }

  private AlldifferentCuts(
      IntVar[] list,
      int[] special,
      IntVar[] counters,
      long[] fixedLeast,
      long[] fixedMost,
      long otherMost) {
    this.list = list.clone();
    this.special = special;
    this.counters = counters;
    this.fixedLeast = fixedLeast;
    this.fixedMost = fixedMost;
    this.otherMost = otherMost;
  }

  /**
   * It creates the separation of the cuts of an all-different constraint with exceptions: the
   * variables that do not take an exception value are pairwise distinct (alldifferent_except_0 for
   * the exception 0).
   *
   * @param list the variables, pairwise distinct
   * @param exceptions the values that any number of the variables may take
   * @return the separation
   */
  public static AlldifferentCuts except(IntVar[] list, int[] exceptions) {
    int[] values = Arrays.stream(exceptions).sorted().distinct().toArray();
    long[] none = new long[values.length];
    long[] all = new long[values.length];
    Arrays.fill(all, UNLIMITED);
    return new AlldifferentCuts(list, values, null, none, all, 1);
  }

  /**
   * It creates the separation of the cuts of a global cardinality constraint: values[k] is taken by
   * a number of the variables within the bounds of counters[k].
   *
   * @param list the variables, pairwise distinct
   * @param values the counted values, pairwise distinct
   * @param counters the counter of each value
   * @param closed whether the variables take only counted values; otherwise any number of them take
   *     the other values
   * @return the separation
   */
  public static AlldifferentCuts cardinality(
      IntVar[] list, int[] values, IntVar[] counters, boolean closed) {
    Integer[] order = sortedPositions(values);
    int[] v = new int[values.length];
    IntVar[] c = new IntVar[values.length];
    for (int k = 0; k < v.length; k++) {
      v[k] = values[order[k]];
      c[k] = counters[order[k]];
    }
    return new AlldifferentCuts(list, v, c, null, null, closed ? 0 : UNLIMITED);
  }

  /**
   * It creates the separation of the cuts of a global cardinality constraint with fixed bounds:
   * values[k] is taken by between least[k] and most[k] of the variables.
   *
   * @param list the variables, pairwise distinct
   * @param values the counted values, pairwise distinct
   * @param least the least number of variables taking each value
   * @param most the most number of variables taking each value
   * @param closed whether the variables take only counted values
   * @return the separation
   */
  public static AlldifferentCuts cardinality(
      IntVar[] list, int[] values, int[] least, int[] most, boolean closed) {
    Integer[] order = sortedPositions(values);
    int[] v = new int[values.length];
    long[] l = new long[values.length];
    long[] u = new long[values.length];
    for (int k = 0; k < v.length; k++) {
      v[k] = values[order[k]];
      l[k] = least[order[k]];
      u[k] = most[order[k]];
    }
    return new AlldifferentCuts(list, v, null, l, u, closed ? 0 : UNLIMITED);
  }

  private static Integer[] sortedPositions(int[] values) {
    Integer[] order = new Integer[values.length];
    for (int k = 0; k < order.length; k++) {
      order[k] = k;
    }
    Arrays.sort(order, Comparator.comparingInt(k -> values[k]));
    return order;
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
   * It tells whether the constraint is a plain all-different, without values of their own limits.
   *
   * @return true for an all-different
   */
  public boolean plain() {
    return special.length == 0 && otherMost == 1;
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
    IntVar[] copiedCounters = null;
    if (counters != null) {
      copiedCounters = new IntVar[counters.length];
      for (int k = 0; k < counters.length; k++) {
        copiedCounters[k] = map.get(counters[k]);
      }
    }
    AlldifferentCuts c =
        new AlldifferentCuts(copied, special, copiedCounters, fixedLeast, fixedMost, otherMost);
    c.domains = domains;
    c.least = least;
    c.most = most;
    c.holding = holding;
    return c;
  }

  // the domains and the limits of now, the root
  private void init() {
    int n = list.length;
    domains = new IntDomain[n];
    for (int i = 0; i < n; i++) {
      domains[i] = list[i].dom().cloneLight();
    }
    int m = special.length;
    least = new long[m];
    most = new long[m];
    holding = new int[m];
    for (int k = 0; k < m; k++) {
      least[k] = counters != null ? Math.max(0, counters[k].min()) : fixedLeast[k];
      most[k] = Math.min(n, counters != null ? counters[k].max() : fixedMost[k]);
      for (int i = 0; i < n; i++) {
        holding[k] += domains[i].contains(special[k]) ? 1 : 0;
      }
    }
  }

  /**
   * It returns the cuts violated by values of the variables, the most effective first. The first
   * call takes the current domains of the variables (and bounds of the counters), which must be
   * those of the root.
   *
   * @param value the value of each variable in the LP solution, NaN for a variable left out of
   *     every cut (one that is not a column of the LP)
   * @param limit the most cuts returned
   * @return the cuts
   */
  public List<Cut> separate(double[] value, int limit) {
    int n = list.length;
    if (domains == null) {
      init();
    }
    List<Integer> present = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      if (!Double.isNaN(value[i])) {
        present.add(i);
      }
    }
    Integer[] order = present.toArray(new Integer[0]);
    Arrays.sort(order, Comparator.comparingDouble(i -> value[i]));
    List<Cut> cuts = new ArrayList<>();
    try {
      prefixes(order, value, true, cuts);
      Integer[] reversed = new Integer[order.length];
      for (int i = 0; i < order.length; i++) {
        reversed[i] = order[order.length - 1 - i];
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
    int[] inside = new int[special.length];
    double sum = 0;
    for (int k = 0; k < order.length; k++) {
      int i = order[k];
      union = union.union(domains[i]);
      for (int t = 0; t < special.length; t++) {
        inside[t] += domains[i].contains(special[t]) ? 1 : 0;
      }
      sum += value[i];
      if (k == 0) {
        continue; // a variable alone is held by its bounds
      }
      Long bound =
          plain() ? extremeSum(union, k + 1, lower) : multisetSum(union, k + 1, inside, lower);
      if (bound == null) {
        continue;
      }
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
   * Returns the least (or greatest) sum of a multiset of k values of a domain that takes each
   * special value v at least {@code least_v - (holding_v - inside_v)} and at most {@code
   * min(most_v, inside_v)} times and any other value at most otherMost times, or null when the
   * least copies do not fit in k. When the domain runs out of copies the values go on past it, as
   * in {@link #extremeSum}.
   */
  private Long multisetSum(IntDomain d, int k, int[] inside, boolean smallest) {
    // segments of values in increasing order: [from, to] with the copies of each value
    List<long[]> segments = new ArrayList<>();
    long[] forced = new long[special.length];
    long left = k;
    long sum = 0;
    int s = 0;
    for (IntervalEnumeration en = d.intervalEnumeration(); en.hasMoreElements(); ) {
      var in = en.nextElement();
      long from = in.min();
      while (s < special.length && special[s] < from) {
        s++;
      }
      while (s < special.length && special[s] <= in.max()) {
        long v = special[s];
        if (from < v) {
          segments.add(new long[] {from, v - 1, otherMost});
        }
        long cap = Math.min(most[s], inside[s]);
        long need = Math.min(cap, Math.max(0, least[s] - (holding[s] - inside[s])));
        forced[s] = need;
        sum = Math.addExact(sum, Math.multiplyExact(need, v));
        left -= need;
        segments.add(new long[] {v, v, cap - need});
        from = v + 1;
        s++;
      }
      if (from <= in.max()) {
        segments.add(new long[] {from, in.max(), otherMost});
      }
    }
    if (left < 0) {
      return null;
    }
    if (segments.isEmpty()) {
      return 0L;
    }
    for (int t = 0; t < segments.size() && left > 0; t++) {
      long[] g = segments.get(smallest ? t : segments.size() - 1 - t);
      long copies = g[2];
      if (copies == 0) {
        continue;
      }
      long size = g[1] - g[0] + 1;
      if (copies == UNLIMITED || g[0] == g[1]) {
        // one value (or the end of the segment) takes all it can
        long take = copies == UNLIMITED ? left : Math.min(copies, left);
        long at = smallest ? g[0] : g[1];
        sum = Math.addExact(sum, Math.multiplyExact(take, at));
        left -= take;
        continue;
      }
      // a run of distinct values, one copy each
      long take = Math.min(size, left);
      long first = smallest ? g[0] : g[1] - take + 1;
      sum = Math.addExact(sum, Math.multiplyExact(take, first) + take * (take - 1) / 2);
      left -= take;
    }
    if (left > 0) {
      // too few copies: as if the values went on past the domain, which no assignment reaches
      long end = smallest ? segments.get(segments.size() - 1)[1] : segments.get(0)[0];
      for (long v = 1; v <= left; v++) {
        sum = Math.addExact(sum, smallest ? end + v : end - v);
      }
    }
    return sum;
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
