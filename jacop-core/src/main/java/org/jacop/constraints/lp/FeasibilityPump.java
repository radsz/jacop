/*
 * FeasibilityPump.java
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
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.Linearizations;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.jalp.RevisedDualSimplex;
import org.jacop.lcg.LinearForm;

/**
 * The feasibility pump of M. Fischetti, F. Glover and A. Lodi ("The feasibility pump", Mathematical
 * Programming 104 (2005) 91-104) over a linear relaxation of the store, to find values for a first
 * solution. The relaxation's solution is rounded, each variable to the value the LP point prefers
 * most; then the LP point closest to the rounding, in the L1 distance over the 0/1 columns, is
 * solved for with the primal simplex from the last basis. The two steps alternate until the LP
 * point is integral on those columns, or the budget is spent. A rounding that repeats is perturbed
 * as in that paper: after a cycle of length one the least certain variables move to their second
 * preferred value, after a longer cycle (and every 100 rounds) each variable moves at random with a
 * probability that grows with its uncertainty.
 *
 * <p>The relaxation has the rows of the linear constraints, the rows of {@link Linearizations} for
 * the others, further rows given (the convex hulls of tables), and the value encodings with their
 * columns {@code [x = v]} ({@link LpColumn}), so that a rounding names a value of each encoded
 * variable. It is built once at the root, apart from the relaxation that propagates, and it changes
 * nothing in the store. The distance leaves out the columns of the variables given as defined (the
 * functionally defined variables of a FlatZinc model, such as the option bits of a class in car
 * sequencing): they follow from the others.
 *
 * <p>The result is given as values of the store's variables, for the search to follow ({@link
 * org.jacop.search.free.IndomainLastSolution#hint}); the propagation of the store decides whether
 * they are a solution.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class FeasibilityPump {

  /** The default largest number of columns of the relaxation. */
  public static final int DEFAULT_MAX_COLUMNS = 200_000;

  /** The default largest number of nonzeros of the relaxation. */
  public static final int DEFAULT_MAX_NONZEROS = 2_000_000;

  /**
   * The largest domain of a variable whose values get columns in the hulls of the tables of the
   * pump ({@link org.jacop.constraints.TableCliques#rows(List, Map, int)}), as for the value
   * encodings: the rounding needs the columns of a table's key to tie the other variables to it.
   */
  public static final int HULL_DOMAIN = 64;

  // the largest domain whose values are scanned for the preferred one
  private static final int SCAN_DOMAIN = 256;

  private static final double EPSILON = 1e-6;

  /**
   * The outcome of a pump.
   *
   * @param vars the variables of the store in the relaxation.
   * @param values their values, from the last rounding.
   * @param integral true if the last LP point was integral on the columns of the distance: the
   *     rounding is then a point of the relaxation.
   * @param iterations the distance problems solved.
   * @param distance the L1 distance over the columns of the distance between the last LP point and
   *     its rounding.
   */
  public record Result(
      IntVar[] vars, int[] values, boolean integral, int iterations, double distance) {}

  private final List<IntVar> columns = new ArrayList<>();
  private final Map<IntVar, Integer> index = new IdentityHashMap<>();
  private final int[][] rowColumns;
  private final double[][] rowWeights;
  private final double[] rowLo;
  private final double[] rowHi;
  // the 0/1 columns of the distance: of model variables and value columns, not arcs or defined
  private final int[] binary;

  // the variables of the store in the relaxation: as columns or through value columns
  private final IntVar[] modelVars;
  private final Map<IntVar, Integer> modelIndex = new IdentityHashMap<>();
  // the column of each model variable, or -1, and its value columns by value, or null
  private final int[] ownColumn;
  private final List<Map<Integer, Integer>> valueColumns = new ArrayList<>();
  // the model variables with a column in the distance, which the perturbations move
  private final boolean[] pumped;

  private long pivots;

  private FeasibilityPump(List<LinearForm> forms, Set<? extends IntVar> defined) {
    List<int[]> cols = new ArrayList<>();
    List<double[]> weights = new ArrayList<>();
    List<double[]> sides = new ArrayList<>();
    for (LinearForm f : forms) {
      if (f.relation() == LinearForm.NE || f.vars().length == 0) {
        continue;
      }
      // repeated columns are merged
      Map<Integer, Double> row = new LinkedHashMap<>();
      for (int i = 0; i < f.vars().length; i++) {
        row.merge(column(f.vars()[i]), (double) f.weights()[i], Double::sum);
      }
      row.values().removeIf(w -> w == 0.0d);
      if (row.isEmpty()) {
        continue;
      }
      int[] c = new int[row.size()];
      double[] w = new double[row.size()];
      int k = 0;
      for (Map.Entry<Integer, Double> e : row.entrySet()) {
        c[k] = e.getKey();
        w[k++] = e.getValue();
      }
      cols.add(c);
      weights.add(w);
      double lo = f.relation() == LinearForm.LE ? Double.NEGATIVE_INFINITY : f.c();
      double hi = f.relation() == LinearForm.GE ? Double.POSITIVE_INFINITY : f.c();
      sides.add(new double[] {lo, hi});
    }
    rowColumns = cols.toArray(new int[0][]);
    rowWeights = weights.toArray(new double[0][]);
    rowLo = new double[sides.size()];
    rowHi = new double[sides.size()];
    for (int i = 0; i < sides.size(); i++) {
      rowLo[i] = sides.get(i)[0];
      rowHi[i] = sides.get(i)[1];
    }
    List<IntVar> model = new ArrayList<>();
    for (IntVar v : columns) {
      IntVar y = modelVariable(v);
      if (y != null && !y.singleton() && !modelIndex.containsKey(y)) {
        modelIndex.put(y, model.size());
        model.add(y);
      }
    }
    modelVars = model.toArray(new IntVar[0]);
    ownColumn = new int[modelVars.length];
    for (int i = 0; i < modelVars.length; i++) {
      Integer j = index.get(modelVars[i]);
      ownColumn[i] = j == null ? -1 : j;
      valueColumns.add(null);
    }
    int[] b = new int[columns.size()];
    int n = 0;
    pumped = new boolean[modelVars.length];
    for (int j = 0; j < columns.size(); j++) {
      IntVar v = columns.get(j);
      Integer i = modelIndex.get(modelVariable(v));
      if (i == null) {
        continue;
      }
      if (v instanceof LpColumn c) {
        if (valueColumns.get(i) == null) {
          valueColumns.set(i, new HashMap<>());
        }
        valueColumns.get(i).put(c.value(), j);
      }
      boolean zeroOne = v instanceof LpColumn || v.min() >= 0 && v.max() <= 1;
      if (zeroOne && !defined.contains(modelVars[i])) {
        b[n++] = j;
        pumped[i] = true;
      }
    }
    binary = Arrays.copyOf(b, n);
  }

  private int column(IntVar v) {
    Integer j = index.get(v);
    if (j == null) {
      j = columns.size();
      index.put(v, j);
      columns.add(v);
    }
    return j;
  }

  // the store's variable of a column: itself, or the variable of a value column; null for others
  private static IntVar modelVariable(IntVar v) {
    if (v instanceof LpColumn c) {
      return c.isFree() || c.isArc() ? null : c.variable();
    }
    return v;
  }

  /**
   * Builds the pump over the constraints of a store at its root fixpoint.
   *
   * @param store the store.
   * @param extra further rows, such as the convex hulls of tables ({@link
   *     org.jacop.constraints.TableCliques}).
   * @param defined the variables defined by others, left out of the distance.
   * @return the pump, or null when the relaxation has no 0/1 column in the distance, or more
   *     columns or nonzeros than {@link #DEFAULT_MAX_COLUMNS} and {@link #DEFAULT_MAX_NONZEROS}.
   */
  public static FeasibilityPump of(
      Store store, Collection<LinearForm> extra, Collection<? extends IntVar> defined) {
    Set<Constraint> constraints = LinearRelaxation.constraintsOf(store);
    List<LinearForm> forms = new ArrayList<>();
    List<LinearForm> relaxed = new ArrayList<>();
    for (Constraint c : constraints) {
      LinearForm f = LinearForms.of(c);
      if (f != null) {
        forms.add(f);
      } else {
        relaxed.addAll(Linearizations.of(c));
      }
    }
    relaxed.addAll(extra);
    relaxed.addAll(Linearizations.encodings(constraints));
    Linearizations.ValueRows values = Linearizations.valueRows(constraints, relaxed, true, true);
    forms.addAll(relaxed);
    forms.addAll(values.kept());
    forms.addAll(values.tried());
    long nonzeros = 0;
    for (LinearForm f : forms) {
      nonzeros += f.vars().length;
    }
    if (nonzeros > DEFAULT_MAX_NONZEROS) {
      return null;
    }
    Set<IntVar> definedSet = Collections.newSetFromMap(new IdentityHashMap<>());
    definedSet.addAll(defined);
    FeasibilityPump pump = new FeasibilityPump(forms, definedSet);
    if (pump.binary.length == 0 || pump.columns.size() > DEFAULT_MAX_COLUMNS) {
      return null;
    }
    return pump;
  }

  /**
   * Returns the number of rows of the relaxation.
   *
   * @return the rows.
   */
  public int rows() {
    return rowLo.length;
  }

  /**
   * Returns the number of 0/1 columns of the distance.
   *
   * @return the 0/1 columns.
   */
  public int binaryColumns() {
    return binary.length;
  }

  /**
   * Returns the pivots of the simplex over all runs.
   *
   * @return the pivots.
   */
  public long pivots() {
    return pivots;
  }

  /**
   * Pumps from the domains the pump was built over.
   *
   * @param iterations the most distance problems to solve.
   * @param deadline the time, in milliseconds of {@link System#currentTimeMillis()}, after which no
   *     further problem is solved.
   * @param rnd the random numbers of the perturbations.
   * @return the last rounding, or null when the relaxation is infeasible or its first solve does
   *     not finish.
   */
  public Result run(int iterations, long deadline, Random rnd) {
    int n = columns.size();
    RevisedDualSimplex lp =
        new RevisedDualSimplex(rowColumns, rowWeights, rowLo, rowHi, new double[n]);
    for (int j = 0; j < n; j++) {
      IntVar v = columns.get(j);
      if (v instanceof LpColumn c) {
        lp.setBounds(j, c.lower(), c.upper());
      } else {
        lp.setBounds(j, v.min(), v.max());
      }
    }
    int limit = 50 * (rows() + n) + 10_000;
    long before = lp.pivots();
    int status = lp.solve(limit);
    pivots += lp.pivots() - before;
    if (status != RevisedDualSimplex.OPTIMAL) {
      return null;
    }
    double[] x = new double[n];
    int[] values = new int[modelVars.length];
    long[] last = {1, 2, 3};
    double[] cost = new double[n];
    int done = 0;
    double distance;
    boolean integral;
    while (true) {
      for (int j = 0; j < n; j++) {
        x[j] = lp.value(j);
      }
      for (int i = 0; i < modelVars.length; i++) {
        values[i] = preferred(i, x);
      }
      distance = 0;
      for (int j : binary) {
        distance += Math.abs(x[j] - roundingOf(j, values));
      }
      integral = distance < EPSILON;
      if (integral || done >= iterations || System.currentTimeMillis() > deadline) {
        break;
      }
      long h = hash(values);
      boolean cycled = h == last[0];
      boolean longer = !cycled && (h == last[1] || h == last[2]);
      if (cycled) {
        perturb(x, values, rnd, false);
      } else if (longer || done > 0 && done % 100 == 0) {
        perturb(x, values, rnd, true);
      }
      last[2] = last[1];
      last[1] = last[0];
      last[0] = h;
      Arrays.fill(cost, 0.0d);
      for (int j : binary) {
        cost[j] = roundingOf(j, values) == 0 ? 1.0d : -1.0d;
      }
      lp.setCost(cost);
      before = lp.pivots();
      status = lp.solvePrimal(limit);
      pivots += lp.pivots() - before;
      done++;
      if (status != RevisedDualSimplex.OPTIMAL) {
        break;
      }
    }
    return new Result(modelVars.clone(), values, integral, done, distance);
  }

  // the rounding of a 0/1 column under the values of the store's variables
  private int roundingOf(int j, int[] values) {
    IntVar v = columns.get(j);
    int i = modelIndex.get(modelVariable(v));
    return v instanceof LpColumn c ? (values[i] == c.value() ? 1 : 0) : values[i];
  }

  // the preference of the LP point for value w of model variable i, at most 1
  private double score(int i, int w, double[] x) {
    Map<Integer, Integer> cols = valueColumns.get(i);
    if (cols != null) {
      Integer j = cols.get(w);
      if (j != null) {
        return x[j];
      }
    }
    return ownColumn[i] < 0 ? 0.0d : 1.0d - Math.min(1.0d, Math.abs(x[ownColumn[i]] - w));
  }

  // the value of the domain of model variable i that the LP point prefers most, the least on ties
  private int preferred(int i, double[] x) {
    IntVar y = modelVars[i];
    if (y.getSize() <= SCAN_DOMAIN) {
      int best = y.min();
      double bestScore = Double.NEGATIVE_INFINITY;
      for (ValueEnumeration e = y.dom().valueEnumeration(); e.hasMoreElements(); ) {
        int w = e.nextElement();
        double sc = score(i, w, x);
        if (sc > bestScore + EPSILON) {
          best = w;
          bestScore = sc;
        }
      }
      return best;
    }
    double target = ownColumn[i] < 0 ? y.min() : x[ownColumn[i]];
    int w = (int) Math.max(y.min(), Math.min(y.max(), Math.round(target)));
    if (y.domain.contains(w)) {
      return w;
    }
    int up = w < y.max() ? y.dom().nextValue(w) : y.max();
    int down = w > y.min() ? y.dom().previousValue(w) : y.min();
    return Math.abs(up - target) <= Math.abs(down - target) ? up : down;
  }

  /**
   * Perturbs a rounding that repeats: after a cycle of length one the T least certain variables of
   * the distance (T random in [10, 30)) move to their second preferred value; after a longer cycle,
   * and every 100 rounds, each one moves when its uncertainty plus max(r - 0.3, 0), with r uniform
   * in [0, 1), is above one half.
   */
  private void perturb(double[] x, int[] values, Random rnd, boolean restart) {
    int m = modelVars.length;
    int[] second = new int[m];
    double[] margin = new double[m];
    double[] uncertainty = new double[m];
    Integer[] order = new Integer[m];
    for (int i = 0; i < m; i++) {
      order[i] = i;
      second[i] = values[i];
      margin[i] = Double.POSITIVE_INFINITY;
      IntVar y = modelVars[i];
      if (!pumped[i] || y.getSize() > SCAN_DOMAIN) {
        continue;
      }
      double best = score(i, values[i], x);
      double next = Double.NEGATIVE_INFINITY;
      for (ValueEnumeration e = y.dom().valueEnumeration(); e.hasMoreElements(); ) {
        int w = e.nextElement();
        double sc = score(i, w, x);
        if (w != values[i] && sc > next) {
          next = sc;
          second[i] = w;
        }
      }
      margin[i] = best - next;
      uncertainty[i] = 1.0d - Math.min(1.0d, Math.max(0.0d, best));
    }
    if (restart) {
      for (int i = 0; i < m; i++) {
        if (second[i] != values[i]
            && uncertainty[i] + Math.max(rnd.nextDouble() - 0.3d, 0.0d) > 0.5d) {
          values[i] = second[i];
        }
      }
      return;
    }
    Arrays.sort(order, (a, b) -> Double.compare(margin[a], margin[b]));
    int flips = Math.min(m, 10 + rnd.nextInt(20));
    for (int k = 0; k < flips && second[order[k]] != values[order[k]]; k++) {
      values[order[k]] = second[order[k]];
    }
  }

  private static long hash(int[] values) {
    long h = 1125899906842597L;
    for (int v : values) {
      h = 31 * h + v;
    }
    return h;
  }
}
