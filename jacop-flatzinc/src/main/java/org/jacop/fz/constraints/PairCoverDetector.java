/*
 * PairCoverDetector.java
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
import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * It finds pairs of items that must be put together into some bins of a bounded capacity, and posts
 * for each item a lower bound on the number of bins it is in. A model has 0/1 variables x[g][i]
 * (item i is in bin g), a capacity {@code sum(i) x[g][i] <= c[g]} for each bin, and for each
 * demanded pair {i, j} literals b[g] with {@code b[g] -> x[g][i] /\ x[g][j]} and the demand {@code
 * sum(g) b[g] >= k}: the SONET ring problem (CSPLib prob056, the Sonet2 COP family of the 2026
 * XCSP3 competition), where an item is a node, a bin a ring and a pair a demand to be routed on a
 * ring both nodes are on. A bin with item i covers at most c[g] - 1 of the pairs of i, so with D(i)
 * the sum of the demands k over the pairs of i,
 *
 * <pre>
 *   sum(g) (c[g] - 1) * x[g][i] &gt;= D(i),
 * </pre>
 *
 * and with equal capacities c, {@code sum(g) x[g][i] >= ceil(D(i) / (c - 1))}: the implied
 * constraint of B. M. Smith, Symmetry and Search in a Network Design Problem, CPAIOR 2005, LNCS
 * 3524, pp. 336-350. The linear relaxation of the model gives only the bound D(i) / (c - 1) summed
 * over the items, and lazy clause generation spends minutes to raise the bound by search; with the
 * implied constraints the optima of Sonet2-3-4, 3-5, 5-5 and 6-5 are proved in seconds and 6-4, 7-4
 * and 8-4 are infeasible at the root (the bounds add up to more than the capacity of all rings).
 *
 * <p>An item is a position in the capacity rows: the variable at position i of the row of bin g is
 * x[g][i]. A demand is used only when all its literals b[g] are pair literals of distinct bins over
 * the same two positions; any labelling of the positions of a row makes the bound valid, the
 * positions only decide which demands are recognised. The capacity rows are {@code int_lin_le} and
 * {@code bool_lin_le} with unit coefficients over 0/1 variables, each variable in one row; the pair
 * literals are {@code int_lin_le_imp([-1, -1], [x, y], -2, b)}, {@code int_lin_le_reif} of the same
 * form and {@code array_bool_and([x, y], b)}; the demands are {@code jacop_among(b, {1}, n)} with n
 * at least k, {@code int_lin_le([-1, ...], b, -k)}, {@code bool_clause(b, [])} and {@code
 * array_bool_or(b, true)}. The constraints are redundant.
 *
 * <p>Setting the system property {@code org.jacop.fz.pairCover} to false turns the detection off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class PairCoverDetector {

  // the most pair literals scanned
  private static final int MAX_LITERALS = 2_000_000;

  private final Support support;

  // bool2int: the integer view to its Boolean
  private final Map<IntVar, IntVar> boolOf = new IdentityHashMap<>();

  // b -> x /\ y, the two variables of each pair literal
  private final Map<IntVar, IntVar[]> pairOf = new IdentityHashMap<>();

  // the capacity rows (variables, capacity), read after all bool2int
  private final List<IntVar[]> rowVars = new ArrayList<>();
  private final List<Integer> rowCaps = new ArrayList<>();

  // the demands (literals, k)
  private final List<IntVar[]> demandLits = new ArrayList<>();
  private final List<Integer> demandKs = new ArrayList<>();

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public PairCoverDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.pairCover is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.pairCover"));
  }

  /**
   * It scans the constraint items of the model and posts the bounds on the bins of each item. It is
   * called after the constraints of the model are posted.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    if (rowVars.isEmpty() || demandLits.isEmpty() || pairOf.isEmpty()) {
      return;
    }

    // the bin and the position of each variable of one capacity row
    Map<IntVar, int[]> place = new IdentityHashMap<>();
    Map<IntVar, Boolean> twice = new IdentityHashMap<>();
    List<IntVar[]> rows = new ArrayList<>();
    List<Integer> caps = new ArrayList<>();
    for (int r = 0; r < rowVars.size(); r++) {
      IntVar[] x = rowVars.get(r);
      for (int i = 0; i < x.length; i++) {
        x[i] = canonical(x[i]);
      }
      int g = rows.size();
      rows.add(x);
      caps.add(rowCaps.get(r));
      for (int i = 0; i < x.length; i++) {
        if (place.put(x[i], new int[] {g, i}) != null) {
          twice.put(x[i], Boolean.TRUE);
        }
      }
    }

    // the demand of each pair of positions, the largest when several demands name it
    Map<Long, Integer> demand = new LinkedHashMap<>();
    int scanned = 0;
    for (int d = 0; d < demandLits.size(); d++) {
      IntVar[] b = demandLits.get(d);
      scanned += b.length;
      if (scanned > MAX_LITERALS) {
        return;
      }
      long key = pairKey(b, place, twice);
      if (key >= 0) {
        demand.merge(key, demandKs.get(d), Math::max);
      }
    }
    if (demand.isEmpty()) {
      return;
    }

    // D(i), the demands over the pairs of each position
    Map<Integer, Integer> degree = new HashMap<>();
    for (Map.Entry<Long, Integer> e : demand.entrySet()) {
      degree.merge((int) (e.getKey() >>> 32), e.getValue(), Integer::sum);
      degree.merge((int) (long) e.getKey(), e.getValue(), Integer::sum);
    }

    int posted = 0;
    for (Map.Entry<Integer, Integer> e : degree.entrySet()) {
      if (post(e.getKey(), e.getValue(), rows, caps, twice)) {
        posted++;
      }
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% pair cover: "
              + rows.size()
              + " bins, "
              + demand.size()
              + " demanded pairs, "
              + posted
              + " item bounds");
    }
  }

  // the pair of positions (i < j) of a demand as i << 32 | j, -1 when it is not over pair literals
  // of distinct bins all over the same two positions
  private long pairKey(IntVar[] b, Map<IntVar, int[]> place, Map<IntVar, Boolean> twice) {
    long key = -1;
    boolean[] bins = new boolean[0];
    for (IntVar lit : b) {
      IntVar[] xy = pairOf.get(canonical(lit));
      if (xy == null || twice.containsKey(xy[0]) || twice.containsKey(xy[1])) {
        return -1;
      }
      int[] p = place.get(xy[0]);
      int[] q = place.get(xy[1]);
      if (p == null || q == null || p[0] != q[0] || p[1] == q[1]) {
        return -1;
      }
      int g = p[0];
      if (g >= bins.length) {
        bins = Arrays.copyOf(bins, Math.max(g + 1, 2 * bins.length));
      }
      if (bins[g]) {
        // two literals of one bin: the bin may count the pair twice
        return -1;
      }
      bins[g] = true;
      long k = ((long) Math.min(p[1], q[1]) << 32) | Math.max(p[1], q[1]);
      if (key >= 0 && key != k) {
        return -1;
      }
      key = k;
    }
    return key;
  }

  // sum(g) (c[g] - 1) * x[g][i] >= D(i), over the bins with position i
  private boolean post(
      int i, int degree, List<IntVar[]> rows, List<Integer> caps, Map<IntVar, Boolean> twice) {
    List<IntVar> x = new ArrayList<>();
    List<Integer> w = new ArrayList<>();
    for (int g = 0; g < rows.size(); g++) {
      IntVar[] row = rows.get(g);
      int c = caps.get(g);
      if (i < row.length && c > 1 && !twice.containsKey(row[i])) {
        x.add(row[i]);
        w.add(c - 1);
      }
    }
    if (x.isEmpty()) {
      // no bin can cover a pair of i: the demands fail by themselves
      return false;
    }
    int common = w.getFirst();
    for (int a : w) {
      if (a != common) {
        common = 0;
        break;
      }
    }
    int[] weights = new int[x.size()];
    int rhs = degree;
    if (common > 0) {
      Arrays.fill(weights, 1);
      rhs = (degree + common - 1) / common;
    } else {
      for (int k = 0; k < weights.length; k++) {
        weights[k] = w.get(k);
      }
    }
    if (rhs <= 1 && common > 0) {
      // one bin: the demands state it already
      return false;
    }
    support.pose(new LinearInt(x.toArray(new IntVar[0]), weights, ">=", rhs));
    return true;
  }

  private IntVar canonical(IntVar v) {
    IntVar b = boolOf.get(v);
    return b == null ? v : b;
  }

  private static boolean binary(IntVar v) {
    return v.min() >= 0 && v.max() <= 1;
  }

  private static boolean allBinary(IntVar[] v) {
    for (IntVar x : v) {
      if (!binary(x)) {
        return false;
      }
    }
    return true;
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "bool2int" -> {
        IntVar b = variable(node, 0);
        IntVar i = variable(node, 1);
        if (b != i) {
          boolOf.put(i, b);
        }
      }
      case "int_lin_le", "bool_lin_le" -> linearLe(node);
      case "int_lin_le_imp", "int_lin_le_reif" -> {
        int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        if (a != null
            && a.length == 2
            && v.length == 2
            && a[0] == -1
            && a[1] == -1
            && c == -2
            && allBinary(v)
            && v[0] != v[1]) {
          pair(variable(node, 3), v[0], v[1]);
        }
      }
      case "array_bool_and" -> {
        IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        if (v.length == 2 && v[0] != v[1]) {
          pair(variable(node, 1), v[0], v[1]);
        }
      }
      case "jacop_among" -> {
        IntDomain s = support.getSetLiteral(node, 1);
        IntVar[] b = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar n = variable(node, 2);
        if (s.getSize() == 1 && s.min() == 1 && n.min() >= 1 && allBinary(b)) {
          demand(b, n.min());
        }
      }
      case "bool_clause" -> {
        IntVar[] neg = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        if (neg.length == 0) {
          demand(support.getVarArray((SimpleNode) node.jjtGetChild(0)), 1);
        }
      }
      case "array_bool_or" -> {
        IntVar r = variable(node, 1);
        if (r.min() == 1) {
          demand(support.getVarArray((SimpleNode) node.jjtGetChild(0)), 1);
        }
      }
      default -> {
        // not read
      }
    }
  }

  // sum(x) <= c, a capacity row; sum(-b) <= -k, a demand
  private void linearLe(ASTConstElem node) {
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (a == null || a.length != v.length || a.length < 2 || !allBinary(v)) {
      return;
    }
    boolean plus = true;
    boolean minus = true;
    for (int x : a) {
      plus &= x == 1;
      minus &= x == -1;
    }
    if (plus && c >= 1 && c < v.length) {
      rowVars.add(v.clone());
      rowCaps.add(c);
    } else if (minus && c <= -1) {
      demand(v, -c);
    }
  }

  private void pair(IntVar b, IntVar x, IntVar y) {
    pairOf.put(canonical(b), new IntVar[] {canonical(x), canonical(y)});
  }

  private void demand(IntVar[] b, int k) {
    demandLits.add(b);
    demandKs.add(k);
  }

  private IntVar variable(ASTConstElem node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }
}
