/*
 * FactoredRowDetector.java
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
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * It multiplies a linear row by a variable that the model already multiplies with every variable of
 * the row, and posts the product row as a redundant linear constraint. For a row {@code sum(i) a[i]
 * * x[i] <= b} and products {@code z[i] = x[i] * m} ({@code int_times}) of every {@code x[i]} with
 * one variable {@code m >= 0} it posts {@code sum(i) a[i] * z[i] - b * m <= 0}; for an equality row
 * the product row is an equality for any sign of {@code m}, and for {@code m <= 0} the inequality
 * is reversed. This is the first level of the reformulation-linearization technique (RLT),
 * restricted to the products the model already has, so that no new variable is introduced: H. D.
 * Sherali and W. P. Adams, "A hierarchy of relaxations between the continuous and convex hull
 * representations for zero-one programming problems", SIAM Journal on Discrete Mathematics 3(3),
 * 1990, and H. D. Sherali and C. H. Tuncbilek, "A global optimization algorithm for polynomial
 * programming problems using a reformulation-linearization technique", Journal of Global
 * Optimization 2, 1992.
 *
 * <p>Cutting stock models with a pattern per stock piece flatten to this form: the pattern of piece
 * {@code c} fits, {@code sum(p) size[p] * x[c,p] <= s}, and {@code m[c]} copies of it are cut, the
 * demand rows summing {@code x[c,p] * m[c]}. The product rows {@code sum(p) size[p] * x[c,p] * m[c]
 * <= s * m[c]} give the linear relaxation the material bound {@code s * sum(m) >= sum(p) size[p] *
 * number[p]}: it proves the optimum of the 2019 MiniZinc Challenge instances of stack-cuttingstock
 * d3, d5 and d14 at the root, where the relaxation without them has the bound 10 of 16 on d3.
 *
 * <p>Setting the system property {@code org.jacop.fz.factoredRows} to false turns the detection
 * off. Rows with more than {@code org.jacop.fz.factoredRows.maxTerms} terms (default 1000) are left
 * out, and at most {@code org.jacop.fz.factoredRows.maxRows} rows (default 10000) are posted.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class FactoredRowDetector {

  private static final int MAX_TERMS =
      Integer.getInteger("org.jacop.fz.factoredRows.maxTerms", 1000);

  private static final int MAX_ROWS =
      Integer.getInteger("org.jacop.fz.factoredRows.maxRows", 10000);

  private final Support support;

  // the constraints other detectors replaced
  private final Set<SimpleNode> replaced;

  // x -> (m -> z) for every z = x * m of the model, in both orders of the factors
  private final Map<IntVar, Map<IntVar, IntVar>> products = new IdentityHashMap<>();

  private final List<ASTConstElem> rows = new ArrayList<>();

  // the rows posted, by their variables, factor and relation, so that a row is posted once
  private final Set<List<Object>> posted = new HashSet<>();

  private int count;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   * @param replaced the constraints other detectors replaced, which are not read.
   */
  public FactoredRowDetector(Support support, Set<SimpleNode> replaced) {
    this.support = support;
    this.replaced = replaced;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.factoredRows is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.factoredRows"));
  }

  /**
   * It scans the model and posts the product rows.
   *
   * @param astTree the root of the parsed model.
   * @return the number of rows posted.
   */
  public int detect(SimpleNode astTree) {
    if (!support.hasConstraint(astTree, Set.of("int_times"))) {
      return 0;
    }
    support.forEachConstraint(astTree, this::collect);
    if (products.isEmpty()) {
      return 0;
    }
    for (ASTConstElem row : rows) {
      if (count >= MAX_ROWS) {
        break;
      }
      support.checkTimeOut();
      row(row);
    }
    if (count > 0 && (support.options.debug() || support.options.searchStatistics())) {
      FzConsole.println("%%%mzn-stat: factoredRows=" + count);
    }
    return count;
  }

  private void collect(ASTConstElem node) {
    if (replaced.contains(node)) {
      return;
    }
    switch (node.getName()) {
      case "int_times" -> {
        IntVar x = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
        IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
        IntVar z = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
        if (x.singleton() || y.singleton() || z.singleton()) {
          return;
        }
        products.computeIfAbsent(x, k -> new LinkedHashMap<>()).putIfAbsent(y, z);
        products.computeIfAbsent(y, k -> new LinkedHashMap<>()).putIfAbsent(x, z);
      }
      case "int_lin_le", "int_lin_eq" -> rows.add(node);
      default -> {
        // neither a product nor a row
      }
    }
  }

  private void row(ASTConstElem node) {
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int b = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    boolean eq = "int_lin_eq".equals(node.getName());
    if (a == null || x == null || a.length != x.length || x.length < 2 || x.length > MAX_TERMS) {
      return;
    }
    // the factors that multiply every variable of the row
    Map<IntVar, IntVar> first = null;
    for (IntVar v : x) {
      if (v.singleton()) {
        return;
      }
      Map<IntVar, IntVar> f = products.get(v);
      if (f == null) {
        return;
      }
      if (first == null) {
        first = f;
      }
    }
    for (IntVar m : first.keySet()) {
      if (count >= MAX_ROWS) {
        return;
      }
      post(a, x, b, eq, m);
    }
  }

  private void post(int[] a, IntVar[] x, int b, boolean eq, IntVar m) {
    if (!eq && m.min() < 0 && m.max() > 0) {
      return;
    }
    // m * (sum a x - b) {<=, =} 0: sum a z - b m {<=, =} 0, reversed for m <= 0
    Map<IntVar, Long> terms = new LinkedHashMap<>();
    for (int i = 0; i < x.length; i++) {
      IntVar z = products.get(x[i]).get(m);
      if (z == null) {
        return;
      }
      terms.merge(z, (long) a[i], Long::sum);
    }
    terms.merge(m, -(long) b, Long::sum);
    terms.values().removeIf(c -> c == 0L);
    if (terms.size() < 2) {
      return;
    }
    IntVar[] vars = new IntVar[terms.size()];
    int[] w = new int[terms.size()];
    int k = 0;
    long reach = 0;
    for (Map.Entry<IntVar, Long> e : terms.entrySet()) {
      long c = e.getValue();
      IntVar v = e.getKey();
      if (c > Integer.MAX_VALUE || c < -Integer.MAX_VALUE) {
        return;
      }
      reach += Math.abs(c) * Math.max(Math.abs((long) v.min()), Math.abs((long) v.max()));
      if (reach > Integer.MAX_VALUE) {
        return;
      }
      vars[k] = v;
      w[k++] = (int) c;
    }
    String rel = eq ? "==" : (m.min() >= 0 ? "<=" : ">=");
    if (!posted.add(List.of(List.of((Object[]) vars), m, rel, terms.values().toString()))) {
      return;
    }
    support.pose(new LinearInt(vars, w, rel, 0));
    count++;
  }
}
