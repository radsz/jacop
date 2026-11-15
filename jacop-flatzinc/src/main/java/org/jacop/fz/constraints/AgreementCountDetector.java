/*
 * AgreementCountDetector.java
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * It posts the pigeonhole bound on the number of equal pairs of a group of variables whose pairs
 * all have an equality indicator. When m variables take their values among q values, at least
 * {@code r * C(b + 1, 2) + (q - r) * C(b, 2)} pairs of them are equal, with {@code m = b * q + r},
 * since the number of equal pairs is a convex function of the number of variables taking each value
 * and is least when they are spread evenly. A model that bounds the agreements of words through
 * indicators of their letters, such as the codes of the XCSP3 problem Hamming (2024 competition,
 * {@code sum(k) (x[i][k] != x[j][k]) >= d} for every pair of words i, j), never states that bound:
 * summed over the letters of each position it contradicts the distance constraints summed over the
 * pairs of words. With it JaCoP proves Hamming-20-10-05-09 and Hamming-30-15-07-14 unsatisfiable at
 * the root, where before it found no answer in 600 s. The argument is the counting bound of coding
 * theory (the Plotkin bound, M. Plotkin, Binary codes with specified minimum distance, IRE
 * Transactions on Information Theory 6(4), 1960, pp. 445-450, in its q-ary form).
 *
 * <p>An indicator a of {@code x = y} only needs {@code x = y -> a}: it is {@code r} of {@code
 * int_eq_reif(x, y, r)} or {@code int_lin_eq_reif([c, -c], [x, y], 0, r)}, and {@code 1 - r} of
 * {@code int_ne_reif}, {@code int_ne_imp}, {@code int_lin_ne_reif} and {@code int_lin_ne_imp} on
 * the same arguments. Since {@code a >= [x = y]}, the sum of the indicators of a group is at least
 * its number of equal pairs, so {@code sum(a) >= bound} is implied (a redundant constraint in the
 * sense of B. M. Smith, Modelling, in F. Rossi, P. van Beek and T. Walsh (eds.), Handbook of
 * Constraint Programming, Elsevier, 2006, chapter 11). The groups are the connected components of
 * the graph of the indicated pairs that are complete graphs, with fewer distinct values than
 * variables.
 *
 * <p>By default the bounds are only checked at the root: they are added, with multiplier one, to
 * the model's {@code int_lin_le} rows that bound agreements over the same indicators from above
 * (the distance constraints), and when the sum has no solution in the domains, a Farkas certificate
 * checked in exact arithmetic, the model is infeasible. Posted as constraints for search the bounds
 * made the satisfiable Hamming instances slower (the linear relaxation is called at every node and
 * changes the search), so they are posted only when the property {@code
 * org.jacop.fz.agreementCount} is {@code rows}.
 *
 * <p>Setting the system property {@code org.jacop.fz.agreementCount} to false turns the detection
 * off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class AgreementCountDetector {

  // the most pairs of a group
  static final int MAX_PAIRS = 200_000;

  private final Support support;

  // an indicator of x = y: the Boolean r, which holds when x = y (positive) or fails when x = y
  private record Indicator(IntVar r, boolean positive) {}

  // the first indicator of each pair, by both of its variables
  private final Map<IntVar, Map<IntVar, Indicator>> pairs = new IdentityHashMap<>();

  // the indicators, by their Boolean
  private final Map<IntVar, Indicator> indicators = new IdentityHashMap<>();

  // the model's rows a * v <= c, kept when every v is an indicator
  private record Row(IntVar[] v, int[] a, long c) {}

  private final List<Row> rows = new ArrayList<>();

  // the sum of the bounds and of the model's upper bounds on agreements over the same indicators,
  // as sum(k * v) <= rhs: the Farkas combination of all of them with multiplier one
  private final Map<IntVar, Long> combination = new IdentityHashMap<>();
  private long rhs;

  private boolean infeasible;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public AgreementCountDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.agreementCount is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.agreementCount"));
  }

  // rows: the bounds are also posted as constraints for search, not only checked at the root
  private static boolean postRows() {
    return "rows".equalsIgnoreCase(System.getProperty("org.jacop.fz.agreementCount"));
  }

  /**
   * It tells whether the bounds contradict the model's upper bounds on agreements at the root. It
   * is valid after {@link #detect}.
   *
   * @return true when the model has no solution.
   */
  public boolean infeasible() {
    return infeasible;
  }

  /**
   * It scans the constraint items of the model and posts the bounds. It is called after the
   * constraints of the model are posted.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    if (pairs.isEmpty()) {
      return;
    }
    int groups = 0;
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    for (IntVar start : new ArrayList<>(pairs.keySet())) {
      if (seen.containsKey(start)) {
        continue;
      }
      List<IntVar> group = new ArrayList<>();
      Deque<IntVar> open = new ArrayDeque<>();
      open.push(start);
      seen.put(start, true);
      while (!open.isEmpty()) {
        IntVar v = open.pop();
        group.add(v);
        for (IntVar w : pairs.get(v).keySet()) {
          if (seen.put(w, true) == null) {
            open.push(w);
          }
        }
      }
      if (post(group)) {
        groups++;
      }
    }
    if (groups > 0) {
      check();
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% agreement count: " + groups + " groups" + (infeasible ? ", infeasible" : ""));
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "int_eq_reif" -> scalars(node, true);
      case "int_ne_reif", "int_ne_imp" -> scalars(node, false);
      case "int_lin_eq_reif" -> linear(node, true);
      case "int_lin_ne_reif", "int_lin_ne_imp" -> linear(node, false);
      case "int_lin_le" -> {
        int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        if (a != null && v != null && a.length == v.length && a.length > 1) {
          rows.add(new Row(v, a, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2))));
        }
      }
      default -> {
        // not read
      }
    }
  }

  private void scalars(ASTConstElem node, boolean positive) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    if (p1.getType() == 0 || p2.getType() == 0) {
      return;
    }
    add(
        support.getVariable(p1),
        support.getVariable(p2),
        support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2)),
        positive);
  }

  private void linear(ASTConstElem node, boolean positive) {
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (a == null || a.length != 2 || v.length != 2 || a[0] == 0 || a[0] != -a[1]) {
      return;
    }
    if (support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)) != 0) {
      return;
    }
    add(v[0], v[1], support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3)), positive);
  }

  private void add(IntVar x, IntVar y, IntVar r, boolean positive) {
    if (x == y || x.singleton() || y.singleton() || r.min() < 0 || r.max() > 1) {
      return;
    }
    Indicator i = new Indicator(r, positive);
    if (indicators.putIfAbsent(r, i) != null && indicators.get(r).positive() != positive) {
      return; // one Boolean as two indicators of opposite senses: not read
    }
    if (pairs.computeIfAbsent(x, k -> new IdentityHashMap<>()).putIfAbsent(y, i) == null) {
      pairs.computeIfAbsent(y, k -> new IdentityHashMap<>()).put(x, i);
    }
  }

  // posts the bound of a connected group when its pairs are all indicated and it is positive
  private boolean post(List<IntVar> group) {
    int m = group.size();
    long all = (long) m * (m - 1) / 2;
    if (m < 3 || all > MAX_PAIRS) {
      return false;
    }
    IntDomain values = new IntervalDomain();
    for (IntVar v : group) {
      if (pairs.get(v).size() != m - 1) {
        return false;
      }
      values = values.union(v.domain);
    }
    long q = values.getSize();
    if (q >= m) {
      return false;
    }
    long b = m / q;
    long r = m % q;
    long bound = r * (b + 1) * b / 2 + (q - r) * b * (b - 1) / 2;
    // sum of the positive indicators - sum of the negative ones >= bound - (negative ones)
    Map<IntVar, Integer> weights = new LinkedHashMap<>();
    long limit = bound;
    for (int i = 0; i < m; i++) {
      Map<IntVar, Indicator> row = pairs.get(group.get(i));
      for (int j = i + 1; j < m; j++) {
        Indicator a = row.get(group.get(j));
        weights.merge(a.r(), a.positive() ? 1 : -1, Integer::sum);
        if (!a.positive()) {
          limit--;
        }
      }
    }
    List<IntVar> vars = new ArrayList<>();
    List<Integer> coefficients = new ArrayList<>();
    for (Map.Entry<IntVar, Integer> e : weights.entrySet()) {
      if (e.getValue() != 0) {
        vars.add(e.getKey());
        coefficients.add(e.getValue());
      }
    }
    if (vars.isEmpty()) {
      return false;
    }
    // the bound as -sum(w * r) <= -limit in the combination
    for (int k = 0; k < vars.size(); k++) {
      combination.merge(vars.get(k), (long) -coefficients.get(k), Long::sum);
      grouped.put(vars.get(k), true);
    }
    rhs -= limit;
    if (postRows()) {
      int[] w = coefficients.stream().mapToInt(Integer::intValue).toArray();
      support.pose(new LinearInt(vars.toArray(new IntVar[0]), w, ">=", (int) limit));
    }
    return true;
  }

  // the indicators of the groups with a bound
  private final Map<IntVar, Boolean> grouped = new IdentityHashMap<>();

  // adds the model's upper bounds on agreements over the grouped indicators to the combination
  // and tells whether it has no solution in the domains (all multipliers one: a Farkas certificate
  // checked in exact arithmetic)
  private void check() {
    for (Row row : rows) {
      boolean upper = true;
      for (int k = 0; k < row.v().length && upper; k++) {
        Indicator i = indicators.get(row.v()[k]);
        // an upper bound on agreements: positive weights on equality indicators, negative ones on
        // difference indicators
        upper =
            grouped.containsKey(row.v()[k])
                && i != null
                && (i.positive() ? row.a()[k] >= 0 : row.a()[k] <= 0);
      }
      if (!upper) {
        continue;
      }
      for (int k = 0; k < row.v().length; k++) {
        combination.merge(row.v()[k], (long) row.a()[k], Long::sum);
      }
      rhs += row.c();
    }
    long least = 0;
    for (Map.Entry<IntVar, Long> e : combination.entrySet()) {
      long k = e.getValue();
      least += k > 0 ? k * e.getKey().min() : k * e.getKey().max();
    }
    infeasible = least > rhs;
  }
}
