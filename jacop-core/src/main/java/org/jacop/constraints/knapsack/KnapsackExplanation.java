/*
 * KnapsackExplanation.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints.knapsack;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.LinearForm;

/**
 * Explanations of the knapsack constraint by surrogate rows. The constraint is the two equalities
 * sum(w[i] * q[i]) = capacity and sum(p[i] * q[i]) = profit, and any combination b * (sum(p[i] *
 * q[i]) - profit) - a * (sum(w[i] * q[i]) - capacity) = 0 holds too. The bound of the linear
 * relaxation that Knapsack propagates (Dantzig's bound, and the bounds of the items that it makes
 * mandatory or forbidden) is the bound that such a row gives for the ratio a / b of the LP dual of
 * the capacity, which is 0 or the efficiency p[c] / w[c] of an item. An atom is therefore explained
 * by the row, among those of the profit, of the capacity and of the efficiencies of the items,
 * whose bounds imply it, with the reason of the linear explanations (lifted, and checked to imply
 * the atom); the shortest one is kept. Prunings of the dynamic program, which no row implies, keep
 * the generic reason.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class KnapsackExplanation {

  /** The most rows tried for one atom. */
  private static final int ROW_LIMIT = 256;

  /** A row whose terms may reach this magnitude is not used, so that no sum overflows. */
  private static final double MAGNITUDE_LIMIT = 0x1p60;

  private final IntVar[] quantity;
  private final int[] weight;
  private final int[] profit;
  private final IntVar capacity;
  private final IntVar total;

  KnapsackExplanation(
      IntVar[] quantity, int[] weight, int[] profit, IntVar capacity, IntVar total) {
    this.quantity = quantity;
    this.weight = weight;
    this.profit = profit;
    this.capacity = capacity;
    this.total = total;
  }

  /**
   * Adds to {@code out} the reason of an atom: the shortest one of a surrogate row that implies it.
   *
   * @param trail the trail
   * @param entry the entry
   * @param out where the reason entries are added
   * @return false when no row implies the atom
   */
  boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (trail.kind(entry) == AtomicTrail.NE) {
      return false;
    }
    return best(trail, entry, out);
  }

  /**
   * Adds to {@code out} the reason of a failure: the shortest one of a surrogate row that the
   * bounds violate now.
   *
   * @param trail the trail
   * @param out where the reason entries are added
   * @return false when no row is violated
   */
  boolean explainFailure(AtomicTrail trail, EntryList out) {
    return best(trail, -1, out);
  }

  private boolean best(AtomicTrail trail, int entry, EntryList out) {
    EntryList shortest = null;
    EntryList reason = new EntryList();
    for (long[] ratio : ratios()) {
      LinearForm row = row(trail, ratio[0], ratio[1], entry);
      if (row == null) {
        continue;
      }
      reason.clear();
      boolean implied =
          entry < 0 ? row.explainFailure(trail, reason) : row.explain(trail, entry, reason);
      if (implied) {
        reason.sortUnique(0);
        if (shortest == null || reason.size() < shortest.size()) {
          shortest = reason;
          reason = new EntryList();
          if (shortest.size() == 0) {
            break;
          }
        }
      }
    }
    if (shortest == null) {
      return false;
    }
    for (int k = 0; k < shortest.size(); k++) {
      out.add(shortest.get(k));
    }
    return true;
  }

  // the dual ratios a / b tried: 0 (the profit row), infinity (the capacity row) and the
  // efficiencies of the items, at most ROW_LIMIT of them spread over their order
  private List<long[]> ratios() {
    List<long[]> all = new ArrayList<>();
    for (int i = 0; i < quantity.length; i++) {
      long g = gcd(profit[i], weight[i]);
      all.add(new long[] {profit[i] / g, weight[i] / g});
    }
    all.sort((x, y) -> Long.compare(x[0] * y[1], y[0] * x[1]));
    List<long[]> distinct = new ArrayList<>();
    for (long[] r : all) {
      long[] last = distinct.isEmpty() ? null : distinct.get(distinct.size() - 1);
      if (last == null || last[0] != r[0] || last[1] != r[1]) {
        distinct.add(r);
      }
    }
    List<long[]> result = new ArrayList<>();
    result.add(new long[] {0, 1});
    result.add(new long[] {1, 0});
    int step = Math.max(1, (distinct.size() + ROW_LIMIT - 1) / ROW_LIMIT);
    for (int k = 0; k < distinct.size(); k += step) {
      result.add(distinct.get(k));
    }
    return result;
  }

  private static long gcd(long a, long b) {
    while (b != 0) {
      long t = a % b;
      a = b;
      b = t;
    }
    return Math.max(a, 1);
  }

  // the row b * (profits - total) - a * (weights - capacity) = 0 without its zero terms, or null
  // when it could overflow or the entry's variable is not in it
  private LinearForm row(AtomicTrail trail, long a, long b, int entry) {
    int n = quantity.length;
    IntVar[] vars = new IntVar[n + 2];
    long[] coefficients = new long[n + 2];
    int k = 0;
    double magnitude = 0;
    for (int i = 0; i < n; i++) {
      long c = b * profit[i] - a * weight[i];
      if (c != 0) {
        vars[k] = quantity[i];
        coefficients[k++] = c;
        magnitude += Math.abs((double) c) * largest(trail, quantity[i]);
      }
    }
    if (b != 0) {
      vars[k] = total;
      coefficients[k++] = -b;
      magnitude += b * largest(trail, total);
    }
    if (a != 0) {
      vars[k] = capacity;
      coefficients[k++] = a;
      magnitude += a * largest(trail, capacity);
    }
    if (magnitude >= MAGNITUDE_LIMIT) {
      return null;
    }
    if (entry >= 0) {
      IntVar y = trail.variable(entry);
      boolean in = false;
      for (int j = 0; j < k; j++) {
        in |= vars[j] == y;
      }
      if (!in) {
        return null;
      }
    }
    return new LinearForm(Arrays.copyOf(vars, k), Arrays.copyOf(coefficients, k), 0, LinearForm.EQ);
  }

  private static double largest(AtomicTrail trail, IntVar x) {
    IntDomain root = trail.rootDomain(x);
    return Math.max(Math.abs((double) root.min()), Math.abs((double) root.max()));
  }
}
