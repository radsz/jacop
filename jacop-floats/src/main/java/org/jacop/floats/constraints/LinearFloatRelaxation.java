/*
 * LinearFloatRelaxation.java
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
 * preservation of specified reasonable legal notices and author attributions
 * in accordance with Section 7 of the GNU Affero General Public License.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.floats.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.constraints.linear.Linear;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.jalp.RevisedDualSimplex;

/**
 * The linear programming relaxation of the linear float constraints of a model, giving a lower
 * bound on a float objective and failing boxes in which the rows have no common point. The rows are
 * the linear constraints over float variables ({@link Linear}, {@link PplusQeqR}, {@link
 * PminusQeqR}, {@link PmulCeqR}, {@link PplusCeqR}, {@link PeqQ}, {@link PlteqQ}, {@link PltQ}); at
 * each call the columns take the bounds of the variables and JaLP's dual simplex ({@link
 * RevisedDualSimplex}) solves min objective from its last basis.
 *
 * <p>The simplex computes in floating point, so neither its objective nor its proof of
 * infeasibility is used as it is. The bound is the safe bound of Neumaier and Shcherbina: for any
 * multipliers y of the rows, {@code c x = y (A x) + (c - y A) x}, and over the box, with {@code A
 * x} in the bounds of the rows, the right side is bounded below by interval arithmetic with outward
 * rounding; y are the duals of the simplex, so the bound is close to the optimum of the relaxation
 * whenever the columns with non-zero reduced cost have finite bounds. A Farkas ray of an infeasible
 * solve is checked the same way: the box fails only when the interval of {@code y A x} over the box
 * misses the interval of {@code y} times the bounds of the rows.
 *
 * <p>A. Neumaier and O. Shcherbina, Safe bounds in linear and mixed-integer linear programming,
 * Mathematical Programming 99 (2004) 283-296.
 *
 * <p>Without it, interval propagation cannot see a combination of rows: on volsay3 (maximise 30a +
 * 40b with 3a + 4b &lt;= 180) every box along the optimal edge looked feasible, and the search
 * could not refute a cost one hundred-thousandth above the optimum.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LinearFloatRelaxation extends Constraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  // bounds beyond this magnitude are infinite for the simplex (they are kept for the safe bound)
  private static final double HUGE = 1e12;

  // multipliers of smaller magnitude are taken as zero: any y gives a valid bound, and a tiny
  // multiplier of a row with an infinite side would make it infinite
  private static final double TINY = 1e-12;

  // whether the products of the model get their envelopes
  private static final boolean PRODUCTS =
      !"false".equals(System.getProperty("org.jacop.floats.lpProducts"));

  private final FloatVar[] columns;

  // the rows of the last solve: the linear rows first, then the rows of the products for the
  // bounds of that solve
  private int[][] rowColumns;

  private double[][] rowWeights;

  private double[] rowLo;

  private double[] rowHi;

  private final int linearRows;

  // the bounds of the columns at this solve, widened by the precision: the propagators accept a box
  // within the precision of their relations, and the relaxation, exact over the reals, is not to be
  // stricter than them
  private final double[] boxLo;

  private final double[] boxHi;

  // the point of the last optimal solve, and the store level of that solve
  private final double[] point;

  private int pointStamp = -1;

  private final Map<FloatVar, Integer> columnOf = new IdentityHashMap<>();

  // the products x * y = z, by column {x, y, z}; x == y for a square
  private final int[][] products;

  private final int objective;

  private final FloatVar cost;

  private final double[] c;

  private RevisedDualSimplex lp;

  private final int pivotLimit;

  private long solves;

  private long bounds;

  private long failures;

  /**
   * Creates the relaxation of the given rows. Each row is {@code rowLo[i] <= sum rowWeights[i][k]
   * rowVars[i][k] <= rowHi[i]}.
   *
   * @param rowVars the variables of each row
   * @param rowWeights the weights of each row
   * @param rowLo the lower bounds of the rows, or negative infinity
   * @param rowHi the upper bounds of the rows, or positive infinity
   * @param cost the objective, minimised
   */
  public LinearFloatRelaxation(
      FloatVar[][] rowVars, double[][] rowWeights, double[] rowLo, double[] rowHi, FloatVar cost) {
    this(rowVars, rowWeights, rowLo, rowHi, new FloatVar[0][], cost);
  }

  /**
   * Creates the relaxation of the given rows and products. Each row is {@code rowLo[i] <= sum
   * rowWeights[i][k] rowVars[i][k] <= rowHi[i]}; each product {x, y, z} is {@code x * y = z}, which
   * the relaxation replaces by its McCormick envelope over the bounds of x and y at each solve (G.
   * P. McCormick, Computability of global solutions to factorable nonconvex programs: Part I -
   * Convex underestimating problems, Mathematical Programming 10 (1976) 147-175), and a square {x,
   * x, z} by its secant and the tangents at the bounds of x.
   *
   * @param rowVars the variables of each row
   * @param rowWeights the weights of each row
   * @param rowLo the lower bounds of the rows, or negative infinity
   * @param rowHi the upper bounds of the rows, or positive infinity
   * @param products the products {x, y, z}
   * @param cost the objective, minimised
   */
  public LinearFloatRelaxation(
      FloatVar[][] rowVars,
      double[][] rowWeights,
      double[] rowLo,
      double[] rowHi,
      FloatVar[][] products,
      FloatVar cost) {
    checkInputForNullness("cost", new Object[] {cost});
    numberId = idNumber.incrementAndGet();
    Map<FloatVar, Integer> index = new IdentityHashMap<>();
    List<FloatVar> cols = new ArrayList<>();
    index.put(cost, 0);
    cols.add(cost);
    int m = rowVars.length;
    this.rowColumns = new int[m][];
    this.rowWeights = new double[m][];
    for (int i = 0; i < m; i++) {
      // merge repeated variables of a row
      Map<Integer, Double> merged = new java.util.LinkedHashMap<>();
      for (int k = 0; k < rowVars[i].length; k++) {
        FloatVar v = rowVars[i][k];
        Integer j = index.get(v);
        if (j == null) {
          j = cols.size();
          index.put(v, j);
          cols.add(v);
        }
        merged.merge(j, rowWeights[i][k], Double::sum);
      }
      merged.values().removeIf(w -> w == 0);
      rowColumns[i] = merged.keySet().stream().mapToInt(Integer::intValue).toArray();
      this.rowWeights[i] = merged.values().stream().mapToDouble(Double::doubleValue).toArray();
    }
    this.products = new int[products.length][3];
    for (int i = 0; i < products.length; i++) {
      for (int k = 0; k < 3; k++) {
        FloatVar v = products[i][k];
        Integer j = index.get(v);
        if (j == null) {
          j = cols.size();
          index.put(v, j);
          cols.add(v);
        }
        this.products[i][k] = j;
      }
    }
    this.linearRows = m;
    this.columns = cols.toArray(new FloatVar[0]);
    this.boxLo = new double[columns.length];
    this.boxHi = new double[columns.length];
    this.point = new double[columns.length];
    for (int j = 0; j < columns.length; j++) {
      columnOf.put(columns[j], j);
    }
    this.rowLo = rowLo.clone();
    this.rowHi = rowHi.clone();
    this.cost = cost;
    this.objective = 0;
    double[] c = new double[columns.length];
    c[objective] = 1;
    this.c = c;
    lp = newSimplex(rowColumns, this.rowWeights, this.rowLo, this.rowHi);
    pivotLimit = 50 * (m + 4 * products.length + columns.length) + 1000;
    queueIndex = 4;
    setScope(columns);
  }

  /**
   * Builds the relaxation of the linear float constraints in the store, or returns null when they
   * do not reach the objective.
   *
   * @param store the store
   * @param cost the objective, minimised
   * @param maxRows the most rows
   * @return the relaxation, not imposed, or null
   */
  public static LinearFloatRelaxation ofModel(Store store, FloatVar cost, int maxRows) {
    List<FloatVar[]> vars = new ArrayList<>();
    List<double[]> weights = new ArrayList<>();
    List<double[]> sides = new ArrayList<>();
    List<FloatVar[]> products = new ArrayList<>();
    for (Constraint c : constraintsOf(store)) {
      addRow(c, vars, weights, sides);
      if (PRODUCTS && c instanceof PmulQeqR p) {
        // SqrtPeqR(x, r) is PmulQeqR(r, r, x)
        products.add(new FloatVar[] {p.p, p.q, p.r});
      }
      if (vars.size() > maxRows) {
        return null;
      }
    }
    boolean reaches = false;
    for (FloatVar[] row : vars) {
      for (FloatVar v : row) {
        reaches |= v == cost;
      }
    }
    // one row: interval propagation of the row already gives what the relaxation would
    if (!reaches || vars.size() + products.size() < 2) {
      return null;
    }
    int m = vars.size();
    double[] lo = new double[m];
    double[] hi = new double[m];
    for (int i = 0; i < m; i++) {
      lo[i] = sides.get(i)[0];
      hi[i] = sides.get(i)[1];
    }
    return new LinearFloatRelaxation(
        vars.toArray(new FloatVar[0][]),
        weights.toArray(new double[0][]),
        lo,
        hi,
        products.toArray(new FloatVar[0][]),
        cost);
  }

  private static Set<Constraint> constraintsOf(Store store) {
    Set<Constraint> constraints = new LinkedHashSet<>();
    for (int i = 0; i < store.size(); i++) {
      if (store.vars[i] instanceof FloatVar) {
        constraints.addAll(store.vars[i].dom().constraints());
      }
    }
    for (Var v : store.variablesHashMap.values()) {
      if (v instanceof FloatVar) {
        constraints.addAll(v.dom().constraints());
      }
    }
    return constraints;
  }

  private static void addRow(
      Constraint c, List<FloatVar[]> vars, List<double[]> weights, List<double[]> sides) {
    double inf = Double.POSITIVE_INFINITY;
    switch (c) {
      case Linear l -> {
        double lo;
        double hi;
        switch (l.relationType) {
          case Linear.EQ -> {
            lo = l.sum;
            hi = l.sum;
          }
          case Linear.LE, Linear.LT -> {
            lo = -inf;
            hi = l.sum;
          }
          case Linear.GE, Linear.GT -> {
            lo = l.sum;
            hi = inf;
          }
          default -> {
            return;
          }
        }
        vars.add(l.list.clone());
        weights.add(l.weights.clone());
        sides.add(new double[] {lo, hi});
      }
      case PplusQeqR p -> {
        vars.add(new FloatVar[] {p.p, p.q, p.r});
        weights.add(new double[] {1, 1, -1});
        sides.add(new double[] {0, 0});
      }
      case PmulCeqR p -> {
        vars.add(new FloatVar[] {p.p, p.r});
        weights.add(new double[] {p.c, -1});
        sides.add(new double[] {0, 0});
      }
      case PplusCeqR p -> {
        vars.add(new FloatVar[] {p.p, p.r});
        weights.add(new double[] {1, -1});
        sides.add(new double[] {-p.c, -p.c});
      }
      default -> {
        // not linear, or not a row of float variables
      }
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void impose(Store store) {
    super.impose(store);
  }

  // solves without a bound or a failure after which the relaxation stops: on arbitrage_loops5 it
  // solved 4 million times for nothing
  private static final int USELESS = 200;

  private boolean off;

  @Override
  public void consistency(Store store) {
    if (off) {
      return;
    }
    if (solves >= USELESS && bounds + failures == 0) {
      off = true;
      return;
    }
    if (fixed()) {
      return;
    }
    int n = columns.length;
    for (int j = 0; j < n; j++) {
      FloatVar v = columns[j];
      boxLo[j] = Math.nextDown(v.min() - FloatDomain.epsilon(v.min()));
      boxHi[j] = Math.nextUp(v.max() + FloatDomain.epsilon(v.max()));
    }
    if (products.length > 0 && !envelope()) {
      return;
    }
    for (int j = 0; j < n; j++) {
      double lo = boxLo[j];
      double hi = boxHi[j];
      lp.setBounds(
          j, lo < -HUGE ? Double.NEGATIVE_INFINITY : lo, hi > HUGE ? Double.POSITIVE_INFINITY : hi);
    }
    solves++;
    int status = lp.solve(pivotLimit);
    if (status == RevisedDualSimplex.INFEASIBLE) {
      if (infeasible(lp.farkas())) {
        failures++;
        throw Store.failException;
      }
      return;
    }
    if (status != RevisedDualSimplex.OPTIMAL) {
      return;
    }
    for (int j = 0; j < n; j++) {
      point[j] = lp.value(j);
    }
    pointStamp = store.level;
    double bound = safeBound(lp.duals());
    if (bound > cost.min()) {
      bounds++;
      cost.domain.inMin(store.level, cost, bound);
    }
  }

  // the rows of the linear constraints and the envelopes of the products over the current bounds,
  // in a new simplex; false when no product has finite bounds
  private boolean envelope() {
    int m = linearRows;
    List<int[]> cols = new ArrayList<>();
    List<double[]> ws = new ArrayList<>();
    List<double[]> sides = new ArrayList<>();
    double inf = Double.POSITIVE_INFINITY;
    for (int[] t : products) {
      double a = boxLo[t[0]];
      double b = boxHi[t[0]];
      double cc = boxLo[t[1]];
      double d = boxHi[t[1]];
      if (!finite(a) || !finite(b) || !finite(cc) || !finite(d)) {
        continue;
      }
      int x = t[0];
      int y = t[1];
      int z = t[2];
      if (z == x || z == y) {
        continue;
      }
      if (x == y) {
        // (x - a)(x - b) <= 0: z - s x <= -ab, with s = a + b rounded; the error of s times |x|
        // goes to the side
        double sum = a + b;
        double err = 2 * Math.ulp(sum) * Math.max(Math.abs(a), Math.abs(b));
        cols.add(new int[] {z, x});
        ws.add(new double[] {1, -sum});
        sides.add(new double[] {-inf, up(up(-mulDown(a, b)) + err)});
        // (x - a)^2 >= 0 and (x - b)^2 >= 0: z - 2a x >= -a^2, z - 2b x >= -b^2
        for (double e : new double[] {a, b}) {
          cols.add(new int[] {z, x});
          ws.add(new double[] {1, -2 * e});
          sides.add(new double[] {down(-mulUp(e, e)), inf});
        }
        continue;
      }
      // (x - a)(y - c) >= 0: z - c x - a y >= -ac, and the three others
      cols.add(new int[] {z, x, y});
      ws.add(new double[] {1, -cc, -a});
      sides.add(new double[] {down(-mulUp(a, cc)), inf});
      cols.add(new int[] {z, x, y});
      ws.add(new double[] {1, -d, -b});
      sides.add(new double[] {down(-mulUp(b, d)), inf});
      cols.add(new int[] {z, x, y});
      ws.add(new double[] {1, -d, -a});
      sides.add(new double[] {-inf, up(-mulDown(a, d))});
      cols.add(new int[] {z, x, y});
      ws.add(new double[] {1, -cc, -b});
      sides.add(new double[] {-inf, up(-mulDown(b, cc))});
    }
    if (cols.isEmpty() && m == 0) {
      return false;
    }
    int total = m + cols.size();
    int[][] rc = Arrays.copyOf(rowColumns, total);
    double[][] rw = Arrays.copyOf(rowWeights, total);
    double[] lo = Arrays.copyOf(rowLo, total);
    double[] hi = Arrays.copyOf(rowHi, total);
    for (int k = 0; k < cols.size(); k++) {
      rc[m + k] = cols.get(k);
      rw[m + k] = ws.get(k);
      lo[m + k] = sides.get(k)[0];
      hi[m + k] = sides.get(k)[1];
    }
    rowColumns = rc;
    rowWeights = rw;
    rowLo = lo;
    rowHi = hi;
    lp = newSimplex(rc, rw, lo, hi);
    return true;
  }

  // a box of variables all fixed to the precision is a solution of the propagators, which need not
  // hold a real point: the relaxation, exact over the reals, would fail the solution when the
  // search
  // assigns it (ex2_1_1, whose float_search precision 1e-6 lets a box cost 2.5e-6 below the
  // optimum)
  private boolean fixed() {
    for (FloatVar v : columns) {
      if (!v.singleton()) {
        return false;
      }
    }
    return true;
  }

  // a simplex that removes its cost perturbation before it returns: the perturbed duals (1.0000026
  // for 1) cost the bound 2.6e-6 times the width of each column
  private RevisedDualSimplex newSimplex(int[][] rc, double[][] rw, double[] lo, double[] hi) {
    RevisedDualSimplex simplex = new RevisedDualSimplex(rc, rw, lo, hi, c, true);
    simplex.setExact(true);
    return simplex;
  }

  private static boolean finite(double v) {
    return v >= -HUGE && v <= HUGE;
  }

  private static double down(double v) {
    return Double.isInfinite(v) ? v : Math.nextDown(v);
  }

  private static double up(double v) {
    return Double.isInfinite(v) ? v : Math.nextUp(v);
  }

  // the Neumaier-Shcherbina bound on the objective over the box for the multipliers y
  private double safeBound(double[] y) {
    int n = columns.length;
    double[] rLo = new double[n];
    double[] rHi = new double[n];
    rLo[objective] = 1;
    rHi[objective] = 1;
    double bound = 0;
    for (int i = 0; i < y.length; i++) {
      double yi = Math.abs(y[i]) < TINY ? 0 : y[i];
      if (yi == 0) {
        continue;
      }
      // y_i times the row side it can reach: c x = y A x + (c - y A) x with A x in the row bounds
      double side = yi > 0 ? mulDown(yi, rowLo[i]) : mulDown(yi, rowHi[i]);
      if (side == Double.NEGATIVE_INFINITY) {
        return Double.NEGATIVE_INFINITY;
      }
      bound = Math.nextDown(bound + side);
      for (int k = 0; k < rowColumns[i].length; k++) {
        int j = rowColumns[i][k];
        double t = yi * rowWeights[i][k];
        // r_j = c_j - sum y_i a_ij
        rLo[j] = Math.nextDown(rLo[j] - Math.nextUp(t));
        rHi[j] = Math.nextUp(rHi[j] - Math.nextDown(t));
      }
    }
    for (int j = 0; j < n; j++) {
      double low = intervalProductMin(rLo[j], rHi[j], boxLo[j], boxHi[j]);
      if (low == Double.NEGATIVE_INFINITY || Double.isNaN(low)) {
        return Double.NEGATIVE_INFINITY;
      }
      bound = Math.nextDown(bound + low);
    }
    return bound;
  }

  // whether the Farkas ray y proves that y (A x) = y s has no solution with x in the box and s in
  // the bounds of the rows
  private boolean infeasible(double[] y) {
    int n = columns.length;
    double[] gLo = new double[n];
    double[] gHi = new double[n];
    double sLo = 0;
    double sHi = 0;
    for (int i = 0; i < y.length; i++) {
      double yi = Math.abs(y[i]) < TINY ? 0 : y[i];
      if (yi == 0) {
        continue;
      }
      double a = mulDown(yi, yi > 0 ? rowLo[i] : rowHi[i]);
      double b = mulUp(yi, yi > 0 ? rowHi[i] : rowLo[i]);
      sLo = Math.nextDown(sLo + a);
      sHi = Math.nextUp(sHi + b);
      for (int k = 0; k < rowColumns[i].length; k++) {
        int j = rowColumns[i][k];
        double t = yi * rowWeights[i][k];
        gLo[j] = Math.nextDown(gLo[j] + Math.nextDown(t));
        gHi[j] = Math.nextUp(gHi[j] + Math.nextUp(t));
      }
    }
    double xLo = 0;
    double xHi = 0;
    for (int j = 0; j < n; j++) {
      double lo = boxLo[j];
      double hi = boxHi[j];
      xLo = Math.nextDown(xLo + intervalProductMin(gLo[j], gHi[j], lo, hi));
      xHi = Math.nextUp(xHi - intervalProductMin(-gHi[j], -gLo[j], lo, hi));
    }
    if (Double.isNaN(xLo) || Double.isNaN(xHi) || Double.isNaN(sLo) || Double.isNaN(sHi)) {
      return false;
    }
    return xHi < sLo || xLo > sHi;
  }

  // the lowest product of two intervals, rounded down; 0 times an infinite bound is 0
  private static double intervalProductMin(double aLo, double aHi, double bLo, double bHi) {
    if (aLo == 0 && aHi == 0) {
      return 0;
    }
    double p =
        Math.min(
            Math.min(mulDown(aLo, bLo), mulDown(aLo, bHi)),
            Math.min(mulDown(aHi, bLo), mulDown(aHi, bHi)));
    return p;
  }

  private static double mulDown(double a, double b) {
    if (a == 0 || b == 0) {
      return 0;
    }
    double p = a * b;
    return Double.isInfinite(p) ? p : Math.nextDown(p);
  }

  private static double mulUp(double a, double b) {
    if (a == 0 || b == 0) {
      return 0;
    }
    double p = a * b;
    return Double.isInfinite(p) ? p : Math.nextUp(p);
  }

  /**
   * Returns the value of a variable at the optimum of the last solve of the relaxation, or NaN when
   * the variable is not in the relaxation or the last solve was not at this store level or above.
   *
   * @param v the variable
   * @param level the store level of the search node
   * @return the value, or NaN
   */
  public double pointValue(FloatVar v, int level) {
    Integer j = columnOf.get(v);
    if (j == null || pointStamp < 0 || pointStamp > level) {
      return Double.NaN;
    }
    return point[j];
  }

  /**
   * Returns the number of rows.
   *
   * @return the rows
   */
  public int rows() {
    return rowColumns.length;
  }

  /**
   * Returns the solves, the bounds it raised and the boxes it failed, for statistics.
   *
   * @return {solves, bounds, failures}
   */
  public long[] counts() {
    return new long[] {solves, bounds, failures};
  }

  @Override
  public String toString() {
    return id()
        + " : LinearFloatRelaxation("
        + rowColumns.length
        + " rows, "
        + columns.length
        + " columns, cost "
        + cost
        + ")";
  }
}
