/*
 * KnapsackDetector.java
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

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds a profit, a sum of 0/1 variables with positive and not all equal coefficients that is
 * bounded from below, together with capacity rows, sums of 0/1 variables with positive coefficients
 * bounded from above, and posts a {@link Knapsack} on a surrogate of the capacity rows as a
 * redundant constraint. The multipliers of the surrogate are the dual values of the linear
 * relaxation max profit, subject to the capacity rows and 0 &lt;= x &lt;= 1, so the Knapsack, which
 * reaches the consistency of the linear relaxation of its own row, prunes with the bound of the
 * relaxation of all rows together. Each linear constraint alone sees only its own row, which is far
 * weaker on multi-dimensional knapsacks.
 *
 * <p>A profit is an int_lin_eq or int_lin_le over 0/1 variables, with all coefficients of one sign,
 * or an int_lin_eq of 0/1 variables and one other variable with coefficient 1 or -1 and right hand
 * side 0, such as the definition of an objective; the other variable is then the profit. Any
 * nonnegative multipliers give a valid surrogate row, so the rounding of the dual values to
 * integers only weakens the bound a little. The Knapsack is posted only when the bound of the
 * relaxation already fixes a variable at the root by its reduced cost, since elsewhere, such as on
 * an objective without a bound yet, it costs time and rarely prunes. All constraints are still
 * posted as usual.
 *
 * <p>Setting the system property {@code org.jacop.fz.knapsack} to false turns the detection off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class KnapsackDetector implements ParserTreeConstants {

  // at most this many surrogate knapsacks per model
  static final int MAX_PROFITS = 8;

  // at most this many profits are tried per model
  static final int MAX_TRIED = 32;

  // at most this many entries of the simplex tableau, rows * (variables + rows)
  static final long MAX_TABLEAU = 200_000L;

  // the dual values are scaled so that the largest is at most this before rounding down
  static final int SCALE = 1000;

  private static final double EPS = 1e-9;

  private final Support support;

  /** A row sum(k) a[k] * x[k] &lt;= bound over 0/1 variables, with all a[k] &gt; 0. */
  private static final class Row {
    final IntVar[] x;
    final int[] a;
    final long bound;

    Row(IntVar[] x, int[] a, long bound) {
      this.x = x;
      this.a = a;
      this.bound = bound;
    }
  }

  /**
   * A profit row, sum(k) a[k] * x[k] = profit, with profit in min..max; the profit is the variable,
   * or a constant when it is null.
   */
  private static final class Profit {
    final IntVar[] x;
    final int[] a;
    final IntVar variable;
    final long min;
    final long max;
    final ASTConstElem node;

    Profit(IntVar[] x, int[] a, IntVar variable, long min, long max, ASTConstElem node) {
      this.x = x;
      this.a = a;
      this.variable = variable;
      this.min = min;
      this.max = max;
      this.node = node;
    }
  }

  private final List<Row> capacities = new ArrayList<>();
  private final List<ASTConstElem> capacityNodes = new ArrayList<>();
  private final List<Profit> profits = new ArrayList<>();

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public KnapsackDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.knapsack is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.knapsack"));
  }

  /**
   * It scans the constraint items of the model and posts a surrogate Knapsack for each profit with
   * capacity rows that bind.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            collect((ASTConstElem) item);
          }
        }
      }
    }
    if (capacities.isEmpty()) {
      return;
    }
    int posted = 0;
    int tried = 0;
    for (Profit p : profits) {
      if (posted == MAX_PROFITS || tried++ == MAX_TRIED) {
        break;
      }
      if (surrogate(p)) {
        posted++;
      }
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private static boolean zeroOne(IntVar v) {
    return v.min() >= 0 && v.max() <= 1;
  }

  private void collect(ASTConstElem node) {
    String name = node.getName();
    boolean equation = name.equals("int_lin_eq");
    if (!equation && !name.equals("int_lin_le")) {
      return;
    }
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] vars = support.getVarArray(child(node, 1));
    if (a == null || vars == null || a.length != vars.length || a.length < 2) {
      return;
    }
    long c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));

    int other = -1;
    int positive = 0;
    int negative = 0;
    for (int k = 0; k < a.length; k++) {
      if (!zeroOne(vars[k])) {
        if (other >= 0) {
          return;
        }
        other = k;
      } else if (a[k] > 0) {
        positive++;
      } else if (a[k] < 0) {
        negative++;
      }
    }

    if (other < 0) {
      if (negative == 0 && positive == a.length) {
        // sum(a * x) <= c (or = c) is a capacity row
        capacities.add(new Row(vars, a, c));
        capacityNodes.add(node);
        if (equation) {
          profit(vars, a, null, c, c, node);
        }
      } else if (positive == 0 && negative == a.length) {
        // sum(-a * x) >= -c (or = -c) is a profit
        profit(vars, negate(a), null, -c, equation ? -c : Long.MAX_VALUE, node);
      }
      return;
    }

    // sum(a * x) + s * y = 0 with s = -sign(a): y is the profit
    int s = a[other];
    if (!equation || c != 0 || Math.abs(s) != 1 || a.length < 3) {
      return;
    }
    if (s == -1
        ? negative != 0 || positive != a.length - 1
        : positive != 0 || negative != a.length - 1) {
      return;
    }
    IntVar[] x = new IntVar[a.length - 1];
    int[] p = new int[a.length - 1];
    for (int k = 0, i = 0; k < a.length; k++) {
      if (k != other) {
        x[i] = vars[k];
        p[i++] = -s * a[k];
      }
    }
    IntVar y = vars[other];
    profit(x, p, y, y.min(), y.max(), node);
  }

  private static int[] negate(int[] a) {
    int[] b = new int[a.length];
    for (int i = 0; i < a.length; i++) {
      b[i] = -a[i];
    }
    return b;
  }

  private void profit(IntVar[] x, int[] p, IntVar y, long min, long max, ASTConstElem node) {
    if (x.length < 3) {
      return;
    }
    boolean distinct = false;
    for (int w : p) {
      distinct |= w != p[0];
    }
    if (distinct) {
      profits.add(new Profit(x, p, y, min, max, node));
    }
  }

  private boolean surrogate(Profit profit) {
    // the 0/1 variables of the profit, with duplicates merged
    // positions by the store index of the variable
    Map<Integer, Integer> index = new HashMap<>();
    List<IntVar> xs = new ArrayList<>();
    List<Long> ps = new ArrayList<>();
    for (int k = 0; k < profit.x.length; k++) {
      Integer i = index.get(profit.x[k].index());
      if (i == null) {
        index.put(profit.x[k].index(), xs.size());
        xs.add(profit.x[k]);
        ps.add((long) profit.a[k]);
      } else {
        ps.set(i, ps.get(i) + profit.a[k]);
      }
    }
    int n = xs.size();
    double[] p = new double[n];
    long pSum = 0;
    for (int j = 0; j < n; j++) {
      if (ps.get(j) <= 0) {
        return false;
      }
      p[j] = ps.get(j);
      pSum += ps.get(j);
    }

    // the capacity rows restricted to the profit's variables (the others can be 0) that bind
    List<double[]> rows = new ArrayList<>();
    List<long[]> weights = new ArrayList<>();
    List<Long> bounds = new ArrayList<>();
    for (int r = 0; r < capacities.size(); r++) {
      if (capacityNodes.get(r) == profit.node) {
        continue;
      }
      Row row = capacities.get(r);
      if (row.bound < 0) {
        return false;
      }
      long[] w = new long[n];
      long sum = 0;
      int shared = 0;
      for (int k = 0; k < row.x.length; k++) {
        Integer j = index.get(row.x[k].index());
        if (j != null) {
          shared += w[j] == 0 ? 1 : 0;
          w[j] += row.a[k];
          sum += row.a[k];
        }
      }
      if (shared >= 2 && sum > row.bound) {
        double[] d = new double[n];
        for (int j = 0; j < n; j++) {
          d[j] = (double) w[j];
        }
        rows.add(d);
        weights.add(w);
        bounds.add(row.bound);
      }
    }
    int m = rows.size();
    if (m == 0 || (long) m * (n + m) > MAX_TABLEAU) {
      return false;
    }

    double[] b = new double[m];
    for (int i = 0; i < m; i++) {
      b[i] = bounds.get(i);
    }
    double[] y = duals(rows.toArray(new double[0][]), b, p);
    if (y == null || !prunes(rows, b, p, y, profit.min)) {
      return false;
    }

    // integer multipliers, the largest at most SCALE, divided by their gcd
    double yMax = 0;
    for (double v : y) {
      yMax = Math.max(yMax, v);
    }
    if (yMax <= EPS) {
      return false;
    }
    long[] u = null;
    long[] w = null;
    long capacity = 0;
    for (long scale = SCALE; scale >= 1; scale /= 10) {
      u = new long[m];
      long g = 0;
      for (int i = 0; i < m; i++) {
        u[i] = (long) Math.floor(y[i] / yMax * scale + EPS);
        g = gcd(g, u[i]);
      }
      for (int i = 0; i < m; i++) {
        u[i] /= g;
      }
      w = new long[n];
      capacity = 0;
      boolean fits = true;
      for (int i = 0; i < m && fits; i++) {
        if (u[i] == 0) {
          continue;
        }
        capacity += u[i] * bounds.get(i);
        for (int j = 0; j < n; j++) {
          w[j] += u[i] * weights.get(i)[j];
        }
        fits = capacity <= IntDomain.MAX_INT;
      }
      for (int j = 0; j < n && fits; j++) {
        fits = w[j] <= IntDomain.MAX_INT;
      }
      if (fits) {
        break;
      }
      w = null;
    }
    if (w == null) {
      return false;
    }

    // items with a surrogate weight 0 are added linearly: profit = knapsack profit + sum(p * x)
    List<IntVar> items = new ArrayList<>();
    List<Integer> itemWeights = new ArrayList<>();
    List<Integer> itemProfits = new ArrayList<>();
    List<IntVar> free = new ArrayList<>();
    List<Integer> freeProfits = new ArrayList<>();
    long itemSum = 0;
    long freeSum = 0;
    for (int j = 0; j < n; j++) {
      if (ps.get(j) > IntDomain.MAX_INT) {
        return false;
      }
      if (w[j] > 0) {
        items.add(xs.get(j));
        itemWeights.add((int) w[j]);
        itemProfits.add((int) (long) ps.get(j));
        itemSum += ps.get(j);
      } else {
        free.add(xs.get(j));
        freeProfits.add((int) (long) ps.get(j));
        freeSum += ps.get(j);
      }
    }
    if (items.size() < 2 || pSum > IntDomain.MAX_INT) {
      return false;
    }
    long low = Math.max(0, profit.min - freeSum);
    long high = Math.min(itemSum, profit.max);
    if (low > high) {
      // the model has no solution, which the constraints posted as usual find
      return false;
    }

    IntVar total = profit.variable;
    if (total == null) {
      total =
          new IntVar(
              support.store, (int) Math.max(profit.min, 0), (int) Math.min(profit.max, pSum));
    }
    IntVar knapsackProfit = total;
    if (!free.isEmpty()) {
      knapsackProfit = new IntVar(support.store, (int) low, (int) high);
      IntVar[] list = new IntVar[free.size() + 2];
      int[] a = new int[free.size() + 2];
      for (int k = 0; k < free.size(); k++) {
        list[k] = free.get(k);
        a[k] = freeProfits.get(k);
      }
      list[free.size()] = knapsackProfit;
      a[free.size()] = 1;
      list[free.size() + 1] = total;
      a[free.size() + 1] = -1;
      support.delayedConstraints.add(new LinearInt(list, a, "==", 0).setDegreeWeight(0));
    }
    IntVar knapsackCapacity = new IntVar(support.store, 0, (int) capacity);
    Knapsack k =
        new Knapsack(
            itemProfits.stream().mapToInt(Integer::intValue).toArray(),
            itemWeights.stream().mapToInt(Integer::intValue).toArray(),
            items.toArray(new IntVar[0]),
            knapsackCapacity,
            knapsackProfit);
    // redundant, so degree-based variable selections see the degrees of the model
    k.setDegreeWeight(0);
    if (support.options.debug()) {
      FzConsole.println("% redundant surrogate " + k);
    }
    support.delayedConstraints.add(k);
    return true;
  }

  /**
   * It tells if the bound of the relaxation already prunes at the root: it is below the minimal
   * profit, or fixing a variable against its value in the relaxation costs more (its reduced cost)
   * than the gap between the bound and the minimal profit. Elsewhere the surrogate costs time and
   * prunes little, for example on a profit that is an objective still without a bound, or on rows
   * whose relaxation is far from the profit asked for.
   */
  private static boolean prunes(List<double[]> a, double[] b, double[] p, double[] y, long min) {
    double bound = 0;
    for (int i = 0; i < b.length; i++) {
      bound += y[i] * b[i];
    }
    double largest = 0;
    for (int j = 0; j < p.length; j++) {
      double reduced = p[j];
      for (int i = 0; i < b.length; i++) {
        reduced -= y[i] * a.get(i)[j];
      }
      bound += Math.max(0, reduced);
      largest = Math.max(largest, Math.abs(reduced));
    }
    return bound - largest < min - EPS;
  }

  private static long gcd(long a, long b) {
    while (b != 0) {
      long t = a % b;
      a = b;
      b = t;
    }
    return a;
  }

  /**
   * It solves max p * x subject to a * x &lt;= b and 0 &lt;= x &lt;= 1, with a &gt;= 0 and b &gt;=
   * 0, by the primal simplex method with bounded variables, starting from x = 0.
   *
   * @param a the rows.
   * @param b the right hand sides.
   * @param p the objective.
   * @return the dual values of the rows, all nonnegative, or null when the iteration limit is
   *     reached before the first improvement.
   */
  public static double[] duals(double[][] a, double[] b, double[] p) {
    int m = a.length;
    int n = p.length;
    int cols = n + m;
    double[][] t = new double[m][cols];
    double[] beta = b.clone();
    int[] basis = new int[m];
    for (int i = 0; i < m; i++) {
      System.arraycopy(a[i], 0, t[i], 0, n);
      t[i][n + i] = 1;
      basis[i] = n + i;
    }
    double[] d = new double[cols];
    System.arraycopy(p, 0, d, 0, n);
    boolean[] upper = new boolean[cols];
    boolean[] basic = new boolean[cols];
    for (int i = 0; i < m; i++) {
      basic[n + i] = true;
    }

    int limit = 50 * cols + 1000;
    for (int iter = 0; iter < limit; iter++) {
      // entering: the largest improvement per unit, Bland's rule after a while against cycling
      boolean bland = iter > 10 * cols;
      int q = -1;
      double best = EPS;
      for (int j = 0; j < cols; j++) {
        if (basic[j]) {
          continue;
        }
        double gain = upper[j] ? -d[j] : d[j];
        if (gain > best) {
          q = j;
          best = gain;
          if (bland) {
            break;
          }
        }
      }
      if (q < 0) {
        break;
      }
      double dir = upper[q] ? -1 : 1;
      double step = q < n ? 1 : Double.POSITIVE_INFINITY;
      int r = -1;
      for (int i = 0; i < m; i++) {
        double alpha = dir * t[i][q];
        double ratio;
        if (alpha > EPS) {
          ratio = beta[i] / alpha;
        } else if (alpha < -EPS && basis[i] < n) {
          ratio = (1 - beta[i]) / -alpha;
        } else {
          continue;
        }
        if (ratio < step - EPS || (r >= 0 && ratio <= step + EPS && basis[i] < basis[r])) {
          step = ratio;
          r = i;
        }
      }
      if (Double.isInfinite(step)) {
        return null;
      }
      step = Math.max(step, 0);
      for (int i = 0; i < m; i++) {
        beta[i] -= dir * step * t[i][q];
      }
      if (r < 0) {
        // the entering variable reaches its other bound
        upper[q] = !upper[q];
        continue;
      }
      int leaving = basis[r];
      upper[leaving] = dir * t[r][q] < 0;
      beta[r] = (upper[q] ? 1 : 0) + dir * step;
      basic[leaving] = false;
      basic[q] = true;
      upper[q] = false;
      basis[r] = q;
      double pivot = t[r][q];
      double[] row = t[r];
      for (int j = 0; j < cols; j++) {
        row[j] /= pivot;
      }
      for (int i = 0; i < m; i++) {
        double f = t[i][q];
        if (i != r) {
          double[] ti = t[i];
          for (int j = 0; j < cols; j++) {
            ti[j] -= f * row[j];
          }
        }
      }
      double f = d[q];
      for (int j = 0; j < cols; j++) {
        d[j] -= f * row[j];
      }
    }

    double[] y = new double[m];
    for (int i = 0; i < m; i++) {
      y[i] = Math.max(0, -d[n + i]);
    }
    return y;
  }
}
