/*
 * ClauseShape.java
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
 * Notwithstanding any other provisions of this License, the copyright
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

package org.jacop.jasat.lcg;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * The clauses of a pseudo-Boolean constraint {@code sum a[i] l[i] >= k} (literals l, weights a > 0)
 * when it is equivalent to a few clauses over its own literals, with no auxiliary variable.
 *
 * <p>The clauses are the prime implicates of the threshold function: a set S of literals is a
 * clause when the literals outside S cannot reach k, {@code sum of a outside S < k}, and no smaller
 * set is. With the weights saturated at k and taken in decreasing order, the set made by adding
 * literals until the sum of the others drops below k is minimal (the last literal added is the
 * smallest one and was needed), so a depth-first walk lists every such clause once (the minimal
 * covers of a knapsack, Balas and Jeroslow, Canonical cuts on the unit hypercube, SIAM J. Appl.
 * Math. 23(1), 1972). A clause {@code l1 or ... or ln} is {@code sum l >= 1}; {@code x -> y1 and
 * y2} is {@code 2 ~x + y1 + y2 >= 2}, two binary clauses; an at most one constraint over n literals
 * is its n (n - 1) / 2 binary exclusions.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class ClauseShape {

  private ClauseShape() {}

  /** The most search steps of one constraint, so a wide sum of many clauses is given up quickly. */
  private static final int STEPS = 100_000;

  /**
   * Returns the clauses of {@code sum a[i] l[i] >= k}, or null when there are more than {@code
   * cap}. An entailed constraint (k at most 0) has none; one that cannot hold has the empty clause.
   *
   * @param a the weights, all positive
   * @param l the literals, distinct variables
   * @param k the right-hand side
   * @param cap the most clauses
   * @return the clauses, or null
   */
  public static List<int[]> clauses(long[] a, int[] l, long k, int cap) {
    List<int[]> out = new ArrayList<>();
    if (k <= 0) {
      return out;
    }
    int n = a.length;
    Integer[] order = new Integer[n];
    long total = 0;
    for (int i = 0; i < n; i++) {
      order[i] = i;
      total += Math.min(a[i], k);
    }
    if (total < k) {
      out.add(new int[0]);
      return out;
    }
    Arrays.sort(order, (x, y) -> Long.compare(Math.min(a[y], k), Math.min(a[x], k)));
    long[] w = new long[n];
    int[] lit = new int[n];
    long[] suffix = new long[n + 1];
    for (int i = 0; i < n; i++) {
      w[i] = Math.min(a[order[i]], k);
      lit[i] = l[order[i]];
    }
    for (int i = n - 1; i >= 0; i--) {
      suffix[i] = suffix[i + 1] + w[i];
    }
    // a set S is a clause when its weight exceeds total - k
    Walk walk = new Walk(w, lit, suffix, total - k, cap, out);
    return walk.run(0, 0, new int[n], 0) ? out : null;
  }

  private static final class Walk {
    final long[] w;
    final int[] lit;
    final long[] suffix;
    final long slack;
    final int cap;
    final List<int[]> out;
    int steps;

    Walk(long[] w, int[] lit, long[] suffix, long slack, int cap, List<int[]> out) {
      this.w = w;
      this.lit = lit;
      this.suffix = suffix;
      this.slack = slack;
      this.cap = cap;
      this.out = out;
    }

    // false when the clauses or the steps run over their limit
    boolean run(int from, long sum, int[] chosen, int size) {
      for (int i = from; i < w.length; i++) {
        if (++steps > STEPS) {
          return false;
        }
        if (sum + suffix[i] <= slack) {
          return true; // the rest cannot make a clause
        }
        chosen[size] = lit[i];
        if (sum + w[i] > slack) {
          if (out.size() >= cap) {
            return false;
          }
          out.add(Arrays.copyOf(chosen, size + 1));
        } else if (!run(i + 1, sum + w[i], chosen, size + 1)) {
          return false;
        }
      }
      return true;
    }
  }
}
