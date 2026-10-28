/*
 * LinearRelaxationCheck.java
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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It checks at the root that the linear relaxation of the model's linear constraints (int_lin_eq,
 * int_lin_le, int_eq and int_le without reification) has a solution within the domains of their
 * variables. Each linear constraint propagates on its own row, so a model whose rows contradict
 * each other only when summed, such as demand above the total capacity of all time steps
 * (wwtpp-real), is proved infeasible only by search, and that search can be hopeless.
 *
 * <p>The relaxation is solved once, by phase one of the primal simplex method with bounded
 * variables. When it has no solution, the dual values of the rows are the multipliers of a Farkas
 * certificate: a combination of the rows whose left hand side cannot reach its right hand side
 * within the domains. The multipliers are rounded to integers and the combination is checked in
 * exact arithmetic, so the floating-point simplex never decides alone; when the check fails,
 * nothing is concluded. Nothing is posted, and no linear programming takes place during search.
 *
 * <p>Setting the system property {@code org.jacop.fz.linearCheck} to false turns the check off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class LinearRelaxationCheck implements ParserTreeConstants {

  /** The largest tableau, rows times columns, that is solved. */
  static final long MAX_TABLEAU = 2_000_000L;

  /** The most tableau entries updated by all pivots together, about a quarter of a second. */
  static final long MAX_WORK = 300_000_000L;

  private static final double EPS = 1e-9;

  private final Support support;

  // the rows a * x <= c, or a * x = c, over the variables at the positions in vars
  private final List<int[]> positions = new ArrayList<>();
  private final List<long[]> coefficients = new ArrayList<>();
  private final List<Long> bounds = new ArrayList<>();
  private final List<Boolean> equations = new ArrayList<>();
  private final Map<IntVar, Integer> index = new HashMap<>();
  private final List<IntVar> vars = new ArrayList<>();

  /**
   * It creates a check reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public LinearRelaxationCheck(Support support) {
    this.support = support;
  }

  /**
   * It tells if the check is on.
   *
   * @return false if the system property org.jacop.fz.linearCheck is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.linearCheck"));
  }

  /**
   * It reads the linear constraints of the model and tells whether their relaxation was proved to
   * have no solution in the current domains.
   *
   * @param astTree the root of the parsed model.
   * @return true when the model has no solution.
   */
  public boolean infeasible(SimpleNode astTree) {
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
    // a single row is as strong as its own constraint
    if (positions.size() < 2
        || (long) positions.size() * (vars.size() + 2L * positions.size()) > MAX_TABLEAU) {
      return false;
    }
    double[] y = farkas();
    if (y == null) {
      return false;
    }
    for (double scale : new double[] {1e3, 1e6, 1e9}) {
      if (certifies(y, scale)) {
        if (support.options.debug()) {
          FzConsole.println(
              "% the linear relaxation of " + positions.size() + " rows has no solution");
        }
        return true;
      }
    }
    return false;
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private void collect(ASTConstElem node) {
    String name = node.getName();
    switch (name) {
      case "int_lin_eq", "int_lin_le" -> {
        int[] a = support.getIntArray(child(node, 0));
        IntVar[] x = support.getVarArray(child(node, 1));
        if (a == null || x == null || a.length != x.length) {
          return;
        }
        long[] w = new long[a.length];
        for (int k = 0; k < a.length; k++) {
          w[k] = a[k];
        }
        long c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        add(x, w, c, name.equals("int_lin_eq"));
      }
      case "int_eq", "int_le" -> {
        if (!(node.jjtGetChild(0) instanceof ASTScalarFlatExpr l)
            || !(node.jjtGetChild(1) instanceof ASTScalarFlatExpr r)) {
          return;
        }
        // x - y <= 0, or = 0
        add(
            new IntVar[] {support.getVariable(l), support.getVariable(r)},
            new long[] {1, -1},
            0,
            name.equals("int_eq"));
      }
      default -> {
        // other constraints are not part of the relaxation
      }
    }
  }

  // a row a * x <= c (or = c); fixed variables go to the right hand side
  private void add(IntVar[] x, long[] a, long c, boolean equation) {
    List<Integer> pos = new ArrayList<>();
    List<Long> coef = new ArrayList<>();
    for (int k = 0; k < x.length; k++) {
      if (a[k] == 0) {
        continue;
      }
      if (x[k].singleton()) {
        c -= a[k] * x[k].value();
        continue;
      }
      Integer p = index.get(x[k]);
      if (p == null) {
        p = vars.size();
        index.put(x[k], p);
        vars.add(x[k]);
      }
      int at = pos.indexOf(p);
      if (at >= 0) {
        coef.set(at, coef.get(at) + a[k]);
      } else {
        pos.add(p);
        coef.add(a[k]);
      }
    }
    if (pos.isEmpty()) {
      return; // constant rows are checked by their own constraints
    }
    positions.add(pos.stream().mapToInt(Integer::intValue).toArray());
    coefficients.add(coef.stream().mapToLong(Long::longValue).toArray());
    bounds.add(c);
    equations.add(equation);
  }

  /**
   * Phase one of the simplex method on the rows, with the variables shifted to [0, max - min]: a
   * slack for each inequality, an artificial for each row whose slack cannot start the basis, and
   * the sum of the artificials minimised.
   *
   * @return the multipliers of the rows of a combination the domains cannot satisfy, or null when
   *     the relaxation has a solution or the iterations run out
   */
  private double[] farkas() {
    int m = positions.size();
    int n = vars.size();
    double[] upperBound = new double[n + 2 * m];
    double[] lower = new double[n];
    for (int j = 0; j < n; j++) {
      lower[j] = vars.get(j).min();
      upperBound[j] = (double) vars.get(j).max() - vars.get(j).min();
    }
    // the column that starts the basis of each row, its cost and the sign of the row
    int cols = n + 2 * m;
    double[][] t = new double[m][cols];
    double[] beta = new double[m];
    int[] basis = new int[m];
    int[] unit = new int[m];
    double[] sign = new double[m];
    double[] cost = new double[cols];
    for (int i = 0; i < m; i++) {
      double rhs = bounds.get(i);
      int[] pos = positions.get(i);
      long[] a = coefficients.get(i);
      for (int k = 0; k < pos.length; k++) {
        rhs -= a[k] * lower[pos[k]];
      }
      sign[i] = rhs < 0 ? -1 : 1;
      for (int k = 0; k < pos.length; k++) {
        t[i][pos[k]] = sign[i] * a[k];
      }
      int slack = n + i;
      int artificial = n + m + i;
      upperBound[slack] = equations.get(i) ? 0 : Double.POSITIVE_INFINITY;
      upperBound[artificial] = Double.POSITIVE_INFINITY;
      t[i][slack] = sign[i];
      beta[i] = sign[i] * rhs;
      if (sign[i] > 0 && !equations.get(i)) {
        unit[i] = slack;
      } else {
        unit[i] = artificial;
        t[i][artificial] = 1;
        cost[artificial] = 1;
      }
      basis[i] = unit[i];
    }

    // reduced costs d = cost - cost_B * T
    double[] d = cost.clone();
    for (int i = 0; i < m; i++) {
      if (cost[basis[i]] != 0) {
        for (int j = 0; j < cols; j++) {
          d[j] -= t[i][j];
        }
      }
    }
    boolean[] upper = new boolean[cols];
    boolean[] basic = new boolean[cols];
    for (int i = 0; i < m; i++) {
      basic[basis[i]] = true;
    }

    long limit = Math.min(50L * cols + 1000, MAX_WORK / ((long) m * cols));
    long iter = 0;
    for (; iter < limit; iter++) {
      // entering: the steepest decrease of the sum, Bland's rule after a while against cycling
      boolean bland = iter > 10 * cols;
      int q = -1;
      double best = EPS;
      for (int j = 0; j < cols; j++) {
        if (basic[j] || upperBound[j] == 0) {
          continue;
        }
        double gain = upper[j] ? d[j] : -d[j];
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
      double step = upperBound[q];
      int r = -1;
      for (int i = 0; i < m; i++) {
        double alpha = dir * t[i][q];
        double ratio;
        if (alpha > EPS) {
          ratio = beta[i] / alpha;
        } else if (alpha < -EPS && upperBound[basis[i]] < Double.POSITIVE_INFINITY) {
          ratio = (upperBound[basis[i]] - beta[i]) / -alpha;
        } else {
          continue;
        }
        if (ratio < step - EPS || (r >= 0 && ratio <= step + EPS && basis[i] < basis[r])) {
          step = ratio;
          r = i;
        }
      }
      if (Double.isInfinite(step)) {
        return null; // unbounded decrease of a sum of nonnegative values: numerical trouble
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
      beta[r] = (upper[q] ? upperBound[q] : 0) + dir * step;
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
        if (i != r && f != 0) {
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
    if (iter == limit) {
      return null;
    }
    double sum = 0;
    for (int i = 0; i < m; i++) {
      if (cost[basis[i]] != 0) {
        sum += beta[i];
      }
    }
    if (sum <= 1e-6) {
      return null;
    }
    // the dual value of row i is cost - d of its starting column; the row was multiplied by sign
    double[] y = new double[m];
    for (int i = 0; i < m; i++) {
      double dual = cost[unit[i]] - d[unit[i]];
      y[i] = -sign[i] * dual;
    }
    return y;
  }

  /**
   * It rounds the multipliers to integers, the largest to about the scale, and tells whether the
   * combination of the rows they give is a valid row (nonnegative multipliers on inequalities)
   * whose left hand side cannot reach its right hand side in the domains, all in exact arithmetic.
   */
  private boolean certifies(double[] y, double scale) {
    double max = 0;
    for (double v : y) {
      max = Math.max(max, Math.abs(v));
    }
    if (max == 0) {
      return false;
    }
    int m = y.length;
    BigInteger[] combined = new BigInteger[vars.size()];
    Arrays.fill(combined, BigInteger.ZERO);
    BigInteger rhs = BigInteger.ZERO;
    for (int i = 0; i < m; i++) {
      long w = Math.round(y[i] / max * scale);
      if (w < 0 && !equations.get(i)) {
        w = 0; // rounding noise on an inequality
      }
      if (w == 0) {
        continue;
      }
      BigInteger bw = BigInteger.valueOf(w);
      int[] pos = positions.get(i);
      long[] a = coefficients.get(i);
      for (int k = 0; k < pos.length; k++) {
        combined[pos[k]] = combined[pos[k]].add(bw.multiply(BigInteger.valueOf(a[k])));
      }
      rhs = rhs.add(bw.multiply(BigInteger.valueOf(bounds.get(i))));
    }
    // the smallest value of the combined left hand side in the domains
    BigInteger least = BigInteger.ZERO;
    for (int j = 0; j < combined.length; j++) {
      IntVar x = vars.get(j);
      int s = combined[j].signum();
      if (s != 0) {
        least = least.add(combined[j].multiply(BigInteger.valueOf(s > 0 ? x.min() : x.max())));
      }
    }
    return least.compareTo(rhs) > 0;
  }
}
