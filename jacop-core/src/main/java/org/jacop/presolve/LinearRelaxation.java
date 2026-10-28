/*
 * LinearRelaxation.java
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

package org.jacop.presolve;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.LinearForm;

/**
 * Root check of the linear relaxation: is there a real point in the bounds of the variables that
 * satisfies every linear constraint of the store? When there is none, the problem has no solution.
 *
 * <p>Propagation looks at one constraint at a time, so it misses infeasibility that only a sum of
 * constraints shows. On wwtpp-real, the flow equations of each plant, summed over the day, fix the
 * water each plant releases, and the capacity rows, summed over the day, bound the water the plant
 * can take; when the first sum is larger the model is infeasible, which CP-SAT finds in its root LP
 * and JaCoP's search does not find in hours.
 *
 * <p>The check runs phase 1 of a bounded-variable primal simplex on a dense tableau, over the
 * relations given by the constraints' {@link LinearForm}s (other constraints, and the holes of the
 * domains, are relaxed away). The simplex works in floating point, so its answer is never trusted
 * as such: when phase 1 ends with a positive infeasibility, the dual multipliers it gives are
 * rounded to integers and the constraints summed with them in exact arithmetic. The model is
 * reported infeasible only when that sum cannot be satisfied within the bounds of the variables, a
 * Farkas certificate checked exactly. A wrong or inexact simplex can miss an infeasibility, never
 * invent one.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class LinearRelaxation {

  /** Largest tableau, rows times columns, that the check solves; larger relaxations are skipped. */
  static final long MAX_ENTRIES = 4_000_000L;

  private static final double EPS = 1e-9;

  private static final double INF = Double.POSITIVE_INFINITY;

  /**
   * The outcome of a check.
   *
   * @param rows the linear constraints in the relaxation.
   * @param columns the variables in the relaxation.
   * @param iterations the simplex iterations.
   * @param skipped true when the relaxation was too large or the budget ran out.
   * @param infeasible true when an exactly checked certificate shows that no solution exists.
   */
  public record Result(
      int rows, int columns, int iterations, boolean skipped, boolean infeasible) {}

  // one linear relation, as sum(weights * vars) <= c, or = c when equality
  private record Row(IntVar[] vars, long[] weights, long c, boolean equality) {}

  private LinearRelaxation() {}

  /**
   * Checks the linear relaxation of the constraints attached in a store at its fixpoint.
   *
   * @param store the store, consistent.
   * @param budgetMillis the time the simplex may take.
   * @return the outcome; when it is infeasible, the store has no solution.
   */
  public static Result check(Store store, long budgetMillis) {
    return check(Derivation.constraints(store, Derivation.variables(store)), budgetMillis);
  }

  /**
   * Checks the linear relaxation of the given constraints within the current bounds of their
   * variables.
   *
   * @param constraints the constraints; those that state no linear relation are left out.
   * @param budgetMillis the time the simplex may take.
   * @return the outcome; when it is infeasible, the constraints have no common solution.
   */
  public static Result check(List<? extends Constraint> constraints, long budgetMillis) {
    List<Row> rows = new ArrayList<>();
    Map<IntVar, Integer> columns = new IdentityHashMap<>();
    List<IntVar> columnVars = new ArrayList<>();
    for (Constraint constraint : constraints) {
      Row row = row(RedundantConstraints.linearForm(constraint));
      if (row == null || !useful(row)) {
        continue;
      }
      rows.add(row);
      for (IntVar v : row.vars) {
        if (!v.singleton() && columns.putIfAbsent(v, columnVars.size()) == null) {
          columnVars.add(v);
        }
      }
    }
    int m = rows.size();
    int n = columnVars.size();
    if (m == 0 || n == 0) {
      return new Result(m, n, 0, false, false);
    }
    if ((long) m * (n + 2L * m + 1) > MAX_ENTRIES) {
      return new Result(m, n, 0, true, false);
    }
    Simplex lp = new Simplex(rows, columns, columnVars);
    boolean finished = lp.solve(System.nanoTime() + budgetMillis * 1_000_000L);
    boolean infeasible = lp.infeasibility() > 1e-6 && certified(rows, lp.multipliers());
    return new Result(m, n, lp.iterations, !finished, infeasible);
  }

  // the relation as <=, or null for != and constraints without a linear form
  private static Row row(LinearForm f) {
    if (f == null) {
      return null;
    }
    return switch (f.relation()) {
      case LinearForm.LE -> new Row(f.vars(), f.weights(), f.c(), false);
      case LinearForm.EQ -> new Row(f.vars(), f.weights(), f.c(), true);
      case LinearForm.GE -> {
        long[] w = new long[f.weights().length];
        for (int i = 0; i < w.length; i++) {
          w[i] = -f.weights()[i];
        }
        yield new Row(f.vars(), w, -f.c(), false);
      }
      default -> null;
    };
  }

  // an inequality that every point of the bounds satisfies adds nothing to the relaxation
  private static boolean useful(Row row) {
    boolean free = false;
    double largest = 0;
    for (int i = 0; i < row.vars.length; i++) {
      IntVar v = row.vars[i];
      free |= !v.singleton();
      largest += row.weights[i] * (double) (row.weights[i] > 0 ? v.max() : v.min());
    }
    return free && (row.equality || largest > row.c);
  }

  /**
   * Sums the rows with integers close to the given multipliers, in exact arithmetic, and tells
   * whether the sum is violated by every point of the bounds. Multipliers of inequalities must be
   * nonnegative; those of equalities may have any sign.
   */
  static boolean certified(List<Row> rows, double[] multipliers) {
    double largest = 0;
    double smallest = INF;
    for (int i = 0; i < multipliers.length; i++) {
      double mu = rows.get(i).equality ? multipliers[i] : Math.max(0, multipliers[i]);
      multipliers[i] = mu;
      largest = Math.max(largest, Math.abs(mu));
    }
    if (largest == 0) {
      return false;
    }
    for (int i = 0; i < multipliers.length; i++) {
      if (Math.abs(multipliers[i]) < 1e-9 * largest) {
        multipliers[i] = 0;
      } else {
        smallest = Math.min(smallest, Math.abs(multipliers[i]));
      }
    }
    // the multipliers of a vertex are often small integers up to a common factor
    double[] scales = {
      1 / smallest, (1 << 10) / largest, (1 << 20) / largest, (1L << 30) / largest
    };
    for (double scale : scales) {
      if (violated(rows, multipliers, scale)) {
        return true;
      }
    }
    return false;
  }

  private static boolean violated(List<Row> rows, double[] multipliers, double scale) {
    Map<IntVar, BigInteger> sum = new IdentityHashMap<>();
    BigInteger c = BigInteger.ZERO;
    for (int i = 0; i < multipliers.length; i++) {
      long mu = Math.round(multipliers[i] * scale);
      if (mu == 0) {
        continue;
      }
      Row row = rows.get(i);
      BigInteger factor = BigInteger.valueOf(mu);
      for (int k = 0; k < row.vars.length; k++) {
        sum.merge(
            row.vars[k], factor.multiply(BigInteger.valueOf(row.weights[k])), BigInteger::add);
      }
      c = c.add(factor.multiply(BigInteger.valueOf(row.c)));
    }
    BigInteger smallest = BigInteger.ZERO;
    for (Map.Entry<IntVar, BigInteger> e : sum.entrySet()) {
      BigInteger w = e.getValue();
      IntVar v = e.getKey();
      smallest = smallest.add(w.multiply(BigInteger.valueOf(w.signum() > 0 ? v.min() : v.max())));
    }
    return smallest.compareTo(c) > 0;
  }

  /**
   * Phase 1 of the bounded-variable primal simplex. Row i is {@code a_i x + s_i + sigma_i t_i =
   * b_i}, with the slack {@code s_i} in [0, inf) for an inequality and [0, 0] for an equality, and
   * the artificial {@code t_i} in [0, inf) when the starting point violates the row. It minimises
   * the sum of the artificials. At the end, the reduced cost of the slack of a row is that row's
   * multiplier in the Farkas sum.
   */
  private static final class Simplex {

    private final int m;
    private final int n;
    private final int columns;
    // tableau B^-1 [A I diag(sigma)] and the reduced costs of the phase-1 objective
    private final double[][] t;
    private final double[] d;
    private final double[] lower;
    private final double[] upper;
    // value of every variable; for a nonbasic one, the bound it is at
    private final double[] value;
    private final int[] basis;
    private final boolean[] basic;
    int iterations;

    Simplex(List<Row> rows, Map<IntVar, Integer> index, List<IntVar> vars) {
      m = rows.size();
      n = vars.size();
      columns = n + 2 * m;
      t = new double[m][columns];
      d = new double[columns];
      lower = new double[columns];
      upper = new double[columns];
      value = new double[columns];
      basis = new int[m];
      basic = new boolean[columns];
      for (int j = 0; j < n; j++) {
        lower[j] = vars.get(j).min();
        upper[j] = vars.get(j).max();
        value[j] = lower[j];
      }
      for (int i = 0; i < m; i++) {
        Row row = rows.get(i);
        double b = row.c;
        for (int k = 0; k < row.vars.length; k++) {
          IntVar v = row.vars[k];
          if (v.singleton()) {
            b -= row.weights[k] * (double) v.value();
          } else {
            t[i][index.get(v)] += row.weights[k];
          }
        }
        double residual = b;
        for (int j = 0; j < n; j++) {
          residual -= t[i][j] * value[j];
        }
        int slack = n + i;
        int artificial = n + m + i;
        t[i][slack] = 1;
        upper[slack] = row.equality ? 0 : INF;
        if (!row.equality && residual >= 0) {
          basis[i] = slack;
          value[slack] = residual;
          upper[artificial] = 0;
        } else {
          // the artificial takes the residual: sigma = sign(residual), its value |residual|
          double sigma = residual >= 0 ? 1 : -1;
          t[i][artificial] = sigma;
          upper[artificial] = INF;
          basis[i] = artificial;
          value[artificial] = Math.abs(residual);
          if (sigma < 0) {
            for (int j = 0; j < columns; j++) {
              t[i][j] = -t[i][j];
            }
          }
          for (int j = 0; j < columns; j++) {
            d[j] -= t[i][j];
          }
          d[artificial] = 0;
        }
        basic[basis[i]] = true;
      }
    }

    double infeasibility() {
      double sum = 0;
      for (int i = 0; i < m; i++) {
        if (basis[i] >= n + m) {
          sum += value[basis[i]];
        }
      }
      return sum;
    }

    // the Farkas multiplier of each row: the reduced cost of its slack
    double[] multipliers() {
      double[] mu = new double[m];
      for (int i = 0; i < m; i++) {
        mu[i] = d[n + i];
      }
      return mu;
    }

    /** Runs to optimality; returns false when the deadline or the iteration limit stops it. */
    boolean solve(long deadline) {
      int limit = 50 * (m + n) + 1000;
      int stalled = 0;
      double objective = infeasibility();
      while (iterations < limit) {
        if ((iterations & 63) == 0 && System.nanoTime() > deadline) {
          return false;
        }
        if (objective <= EPS) {
          return true;
        }
        int q = entering(stalled > 50);
        if (q < 0) {
          return true;
        }
        iterations++;
        double dir = value[q] <= lower[q] ? 1 : -1;
        double theta = upper[q] - lower[q];
        int r = -1;
        for (int i = 0; i < m; i++) {
          double alpha = t[i][q] * dir;
          int b = basis[i];
          double step;
          if (alpha > EPS) {
            step = (value[b] - lower[b]) / alpha;
          } else if (alpha < -EPS && upper[b] < INF) {
            step = (upper[b] - value[b]) / -alpha;
          } else {
            continue;
          }
          if (step < theta || (step == theta && r >= 0 && basis[i] < basis[r])) {
            theta = Math.max(0, step);
            r = i;
          }
        }
        if (theta == INF) {
          return false; // unbounded, impossible in phase 1 but numerics may say so
        }
        for (int i = 0; i < m; i++) {
          value[basis[i]] -= t[i][q] * dir * theta;
        }
        if (r >= 0) {
          value[q] += dir * theta;
          pivot(r, q);
        } else {
          value[q] = dir > 0 ? upper[q] : lower[q];
        }
        double now = infeasibility();
        stalled = now < objective - EPS ? 0 : stalled + 1;
        objective = now;
      }
      return false;
    }

    // Dantzig's rule, or Bland's when the objective has not moved for a while
    private int entering(boolean bland) {
      int best = -1;
      double bestScore = EPS;
      for (int j = 0; j < columns; j++) {
        if (basic[j] || lower[j] == upper[j]) {
          continue;
        }
        double score = value[j] <= lower[j] ? -d[j] : d[j];
        if (score > bestScore) {
          if (bland) {
            return j;
          }
          best = j;
          bestScore = score;
        }
      }
      return best;
    }

    private void pivot(int r, int q) {
      int leaving = basis[r];
      double alpha = t[r][q];
      // the leaving variable sits at the bound it reached
      value[leaving] =
          Math.abs(value[leaving] - lower[leaving]) <= Math.abs(value[leaving] - upper[leaving])
              ? lower[leaving]
              : upper[leaving];
      if (leaving >= n + m) {
        // an artificial that left is not needed again
        upper[leaving] = 0;
        value[leaving] = 0;
      }
      double[] pr = t[r];
      // the pivot row is sparse: update only its nonzero columns
      int[] nonzero = new int[columns];
      int count = 0;
      for (int j = 0; j < columns; j++) {
        if (pr[j] != 0) {
          pr[j] /= alpha;
          nonzero[count++] = j;
        }
      }
      for (int i = 0; i < m; i++) {
        double f = t[i][q];
        if (i != r && f != 0) {
          double[] row = t[i];
          for (int k = 0; k < count; k++) {
            row[nonzero[k]] -= f * pr[nonzero[k]];
          }
          row[q] = 0;
        }
      }
      double f = d[q];
      if (f != 0) {
        for (int k = 0; k < count; k++) {
          d[nonzero[k]] -= f * pr[nonzero[k]];
        }
        d[q] = 0;
      }
      basic[leaving] = false;
      basic[q] = true;
      basis[r] = q;
    }
  }
}
