/*
 * TableClauses.java
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

package org.jacop.constraints.table;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.function.Predicate;
import org.jacop.core.IntVar;
import org.jacop.lcg.LinearForm;

/**
 * The prime implicates of a table over 0/1 variables, as clause rows of the linear relaxation. A
 * clause is a minimal partial assignment that no allowed tuple extends, negated: {@code sum of x
 * over the literals x = 0 + sum of (1 - x) over the literals x = 1 >= 1}. Each prime implicate is a
 * facet-candidate of the convex hull of the tuples that needs no column of its own, unlike the hull
 * over tuple columns of {@link org.jacop.constraints.TableCliques}, so short tables with many
 * tuples, or many tables, get rows that cost the simplex a few nonzeros each.
 *
 * <p>Clauses are found on the ternary lattice of partial assignments ("Prime implicants and prime
 * implicates", Quine, "The problem of simplifying truth functions", American Mathematical Monthly
 * 59, 1952, and the tabular method of McCluskey, Bell System Technical Journal 35, 1956, here on
 * the complement of the allowed set): a partial assignment can be extended to an allowed tuple when
 * either value of one of its free variables can, and a prime implicate is one that cannot while
 * every assignment with one literal fewer can.
 *
 * <p>On the Fortress problems of the XCSP competition (walls enclosing points of a grid), the
 * clauses {@code f_n <= f_c + w_c} of the reachability tables make the relaxation the vertex cut
 * linear program, whose bound is the optimum number of walls (Menger's theorem), as the rows of MIP
 * and CP-SAT give it; without them the relaxation had no row of the tables.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class TableClauses {

  /** The most free 0/1 columns of a table that gets clause rows. */
  static final int MAX_ARITY = Integer.getInteger("org.jacop.lp.tableClauseArity", 10);

  /** The most clause rows of one table; the shortest are kept. */
  static final int MAX_CLAUSES = Integer.getInteger("org.jacop.lp.tableClauses", 32);

  /** The most tuple checks of one table when the allowed assignments are listed. */
  private static final long MAX_CHECKS = 4_000_000;

  private TableClauses() {}

  /**
   * Returns the clause rows of a table.
   *
   * @param x the variables of the columns
   * @param tuples the number of tuples
   * @param accepts whether a tuple of values, one per column, is allowed
   * @return the rows, empty unless the columns not fixed are 0/1 and at most {@link #MAX_ARITY}
   */
  static List<LinearForm> of(IntVar[] x, int tuples, Predicate<int[]> accepts) {
    if (MAX_CLAUSES <= 0) {
      return List.of();
    }
    int arity = x.length;
    int[] values = new int[arity];
    int[] free = new int[arity];
    int n = 0;
    for (int i = 0; i < arity; i++) {
      IntVar v = x[i];
      if (v.singleton()) {
        values[i] = v.value();
      } else if (v.min() == 0 && v.max() == 1) {
        free[n++] = i;
      } else {
        return List.of();
      }
    }
    if (n < 2 || n > MAX_ARITY || (long) tuples << n > MAX_CHECKS) {
      return List.of();
    }
    int full = 1 << n;
    int[] pow3 = new int[n + 1];
    pow3[0] = 1;
    for (int i = 0; i < n; i++) {
      pow3[i + 1] = pow3[i] * 3;
    }
    // digit i of a state is the value of free column i, or 2 when it is not assigned
    boolean[] feasible = new boolean[pow3[n]];
    boolean all = true;
    for (int a = 0; a < full; a++) {
      int state = 0;
      for (int i = 0; i < n; i++) {
        int bit = (a >> i) & 1;
        values[free[i]] = bit;
        state += bit * pow3[i];
      }
      feasible[state] = accepts.test(values);
      all &= feasible[state];
    }
    if (all) {
      return List.of();
    }
    for (int s = 0; s < pow3[n]; s++) {
      for (int i = 0, r = s; i < n; i++, r /= 3) {
        if (r % 3 == 2) {
          feasible[s] = feasible[s - 2 * pow3[i]] || feasible[s - pow3[i]];
          break;
        }
      }
    }
    List<int[]> clauses = new ArrayList<>();
    for (int s = 0; s < pow3[n]; s++) {
      if (feasible[s]) {
        continue;
      }
      boolean prime = true;
      int size = 0;
      for (int i = 0, r = s; i < n && prime; i++, r /= 3) {
        int d = r % 3;
        if (d != 2) {
          size++;
          prime = feasible[s + (2 - d) * pow3[i]];
        }
      }
      // a unit clause is a fact of the domains, which the relaxation has as bounds
      if (prime && size >= 2) {
        clauses.add(new int[] {size, s});
      }
    }
    clauses.sort(Comparator.comparingInt(c -> c[0]));
    List<LinearForm> rows = new ArrayList<>();
    for (int k = 0; k < clauses.size() && k < MAX_CLAUSES; k++) {
      int size = clauses.get(k)[0];
      IntVar[] vars = new IntVar[size];
      long[] weights = new long[size];
      int ones = 0;
      int j = 0;
      for (int i = 0, r = clauses.get(k)[1]; i < n; i++, r /= 3) {
        int d = r % 3;
        if (d == 2) {
          continue;
        }
        // the literal x != d: x for d = 0, 1 - x for d = 1
        vars[j] = x[free[i]];
        weights[j++] = d == 0 ? 1 : -1;
        ones += d;
      }
      rows.add(new LinearForm(vars, weights, 1L - ones, LinearForm.GE));
    }
    return rows;
  }
}
