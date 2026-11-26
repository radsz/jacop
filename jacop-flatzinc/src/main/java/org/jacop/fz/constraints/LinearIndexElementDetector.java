/*
 * LinearIndexElementDetector.java
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
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import org.jacop.constraints.TableCliques;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;
import org.jacop.fz.constraints.FzItems.ConstElement;

/**
 * Element constraints over constant arrays whose index is a linear function of a few variables
 * become one table over those variables and the looked-up values.
 *
 * <p>MiniZinc flattens a lookup {@code c = cost[a, b, w]} of a constant multi-dimensional array
 * into {@code i = w + n_w * b + n_w * n_b * a + k}, posted as {@code int_lin_eq} (with the domain
 * annotation), and one element {@code c = cost'[i]} over the array laid out in one dimension. The
 * index has one value per combination, thousands for the 2019 MiniZinc Challenge
 * liner-sf-repositioning models, so the bounds of c lose a value only when every index value with a
 * cost beyond it is gone, and under lazy clause generation the reason of a cost bound is one {@code
 * i != v} atom per such value, while the domain-consistent linear constraint explains each index
 * hole by the atoms of all three variables (fm3_3: 324 atoms per element reason, 718 per linear
 * failure, learnt clauses of 237 literals and 340 conflicts per second).
 *
 * <p>When the index occurs only in its definition and in such elements, the definition and the
 * elements are replaced by the table {@code (a, b, w, c_1, ..., c_m)} of the combinations whose
 * index is in the index domain and in every array; the index itself leaves the model. This is the
 * multi-dimensional element of Gecode and Chuffed's table decomposition of it, and the expansion of
 * element constraints over the values of an affine index done by the presolve of CP-SAT (L. Perron,
 * F. Didier and S. Gay, The CP-SAT-LP Solver, CP 2023, LIPIcs 280, 3:1-3:2).
 *
 * <p>An index defined from one variable alone is left to the element.
 *
 * <p>The system property {@code org.jacop.fz.linearIndexElement=false} turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LinearIndexElementDetector extends ModelRewrite {

  // the element constraints over an array of constants that are read
  private static final Set<String> ELEMENTS =
      Set.of(
          "array_int_element", "array_var_int_element", "jacop_array_var_int_element_nonshifted");

  /** At most this many combinations of the defining variables (the rows of the table). */
  static final int MAX_ROWS = 1 << 15;

  /** At most this many variables in the definition of the index, besides the index. */
  static final int MAX_TERMS = 4;

  private int tables;

  /** The definition index = sign * (constant - sum coefficients[k] * vars[k]). */
  private static final class Definition {
    private final ASTConstElem node;
    private final IntVar[] vars;
    private final long[] coefficients;
    private final long constant;

    Definition(ASTConstElem node, IntVar[] vars, long[] coefficients, long constant) {
      this.node = node;
      this.vars = vars;
      this.coefficients = coefficients;
      this.constant = constant;
    }

    ASTConstElem node() {
      return node;
    }

    IntVar[] vars() {
      return vars;
    }

    long[] coefficients() {
      return coefficients;
    }

    long constant() {
      return constant;
    }
  }

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   * @param kept the variables of the solve item and of the output, which stay in the model.
   */
  public LinearIndexElementDetector(Support support, Set<IntVar> kept) {
    super(support, kept);
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.linearIndexElement is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.linearIndexElement"));
  }

  /**
   * It scans the constraint items of the model and posts one table for each index variable that a
   * linear equality defines and that only elements over constant arrays read.
   *
   * @param astTree the root of the parsed model.
   * @param skipped constraint nodes that are not posted.
   */
  public void detect(SimpleNode astTree, Set<SimpleNode> skipped) {
    List<ASTConstElem> all = FzItems.constraints(astTree, skipped);
    Map<IntVar, List<ConstElement>> elements = new IdentityHashMap<>();
    List<IntVar> order = new ArrayList<>();
    for (ASTConstElem c : all) {
      collect(c, elements, order);
    }
    if (order.isEmpty()) {
      return;
    }
    // the definitions of the indexes, then every other constraint an index occurs in
    Map<IntVar, Definition> definitions = new IdentityHashMap<>();
    Set<IntVar> other = Collections.newSetFromMap(new IdentityHashMap<>());
    for (ASTConstElem c : all) {
      Definition d = definition(c, elements);
      if (d != null && !definitions.containsKey(index(d))) {
        definitions.put(index(d), d);
      }
    }
    if (definitions.isEmpty()) {
      return;
    }
    for (ASTConstElem c : all) {
      for (int k = 0; k < c.jjtGetNumChildren(); k++) {
        occur((SimpleNode) c.jjtGetChild(k), c, definitions, elements, other);
      }
    }
    for (IntVar z : order) {
      Definition d = definitions.get(z);
      if (d != null
          && !other.contains(z)
          && !kept.contains(z)
          && support.reif.variablesOf(z).isEmpty()
          && support.imply.variablesOf(z).isEmpty()
          && support.reif.size(z) == 0
          && support.imply.size(z) == 0) {
        post(z, d, elements.get(z));
      }
    }
    if (support.options.debug() && tables > 0) {
      FzConsole.println(
          "% linear index element detector: "
              + tables
              + " tables of "
              + (replaced.size() - tables)
              + " elements");
    }
  }

  private void collect(
      ASTConstElem node, Map<IntVar, List<ConstElement>> groups, List<IntVar> order) {
    if (!ELEMENTS.contains(node.getName())) {
      return;
    }
    Optional<ConstElement> read = FzItems.constElement(support, node);
    if (read.isEmpty()) {
      return;
    }
    ConstElement element = read.get();
    IntVar index = element.index();
    if (element.value() == index) {
      return;
    }
    List<ConstElement> group = groups.get(index);
    if (group == null) {
      group = new ArrayList<>();
      groups.put(index, group);
      order.add(index);
    }
    group.add(element);
  }

  // the index a definition defines
  private static IntVar index(Definition d) {
    return d.vars()[d.vars().length - 1];
  }

  // int_lin_eq with an element index of coefficient +-1 and two to MAX_TERMS other variables,
  // whose combinations are few; the index goes last in vars, with coefficient 0. An index shifted
  // from one variable stays an element: the table would only copy it (stable-goods 2020 s-d19 lost
  // its first solution in the default search with 75 such tables).
  private Definition definition(ASTConstElem c, Map<IntVar, List<ConstElement>> elements) {
    if (!c.getName().equals("int_lin_eq")) {
      return null;
    }
    int[] a = support.getIntArray((SimpleNode) c.jjtGetChild(0));
    IntVar[] v = support.getVarArray((SimpleNode) c.jjtGetChild(1));
    if (a == null || v.length < 3 || v.length > MAX_TERMS + 1) {
      return null;
    }
    int at = -1;
    for (int t = 0; t < v.length; t++) {
      if (Math.abs(a[t]) == 1 && elements.containsKey(v[t])) {
        at = t;
        break;
      }
    }
    if (at < 0) {
      return null;
    }
    IntVar z = v[at];
    long sign = a[at];
    long rows = 1;
    IntVar[] vars = new IntVar[v.length];
    long[] coefficients = new long[v.length];
    int n = 0;
    for (int t = 0; t < v.length; t++) {
      if (t == at) {
        continue;
      }
      if (v[t] == z || a[t] == 0 || v[t].singleton()) {
        return null;
      }
      for (int u = 0; u < n; u++) {
        if (vars[u] == v[t]) {
          return null;
        }
      }
      rows *= v[t].getSize();
      if (rows > MAX_ROWS) {
        return null;
      }
      // z = sign * (r - sum a_t x_t), since 1/sign = sign
      vars[n] = v[t];
      coefficients[n++] = sign * a[t];
    }
    vars[n] = z;
    long r = support.getInt((ASTScalarFlatExpr) c.jjtGetChild(2));
    return new Definition(c, vars, coefficients, sign * r);
  }

  // records the indexes that occur in c, unless c is their definition or one of their elements
  private void occur(
      SimpleNode arg,
      ASTConstElem c,
      Map<IntVar, Definition> definitions,
      Map<IntVar, List<ConstElement>> elements,
      Set<IntVar> other) {
    if (arg.getId() == JJTARRAYLITERAL) {
      for (int i = 0; i < arg.jjtGetNumChildren(); i++) {
        occur((SimpleNode) arg.jjtGetChild(i), c, definitions, elements, other);
      }
      return;
    }
    if (!(arg instanceof ASTScalarFlatExpr e)) {
      return;
    }
    for (IntVar v : FzItems.variables(support, e)) {
      Definition d = v == null ? null : definitions.get(v);
      if (d == null || c == d.node()) {
        continue;
      }
      boolean own = false;
      for (ConstElement el : elements.get(v)) {
        if (el.node() == c && c.jjtGetChild(0) == e) {
          own = true;
          break;
        }
      }
      if (!own) {
        other.add(v);
      }
    }
  }

  private void post(IntVar z, Definition d, List<ConstElement> group) {
    int terms = d.vars().length - 1;
    // the columns: the defining variables, then each distinct value variable once
    Map<IntVar, Integer> column = new LinkedHashMap<>();
    for (int t = 0; t < terms; t++) {
      column.put(d.vars()[t], t);
    }
    int[] columnOf = new int[group.size()];
    for (int e = 0; e < group.size(); e++) {
      IntVar v = group.get(e).value();
      Integer c = column.get(v);
      if (c == null) {
        c = column.size();
        column.put(v, c);
      }
      columnOf[e] = c;
    }
    IntVar[] vars = column.keySet().toArray(new IntVar[0]);
    int[][] values = new int[terms][];
    for (int t = 0; t < terms; t++) {
      values[t] = d.vars()[t].dom().toIntArray();
    }
    List<int[]> rows = new ArrayList<>();
    int[] at = new int[terms];
    while (true) {
      int[] row = row(z, d, group, columnOf, vars.length, values, at);
      if (row != null) {
        rows.add(row);
      }
      int t = terms - 1;
      while (t >= 0 && ++at[t] == values[t].length) {
        at[t] = 0;
        t--;
      }
      if (t < 0) {
        break;
      }
    }
    if (rows.isEmpty()) {
      throw Store.failException;
    }
    int[][] tuples = rows.toArray(new int[0][]);
    if (vars.length <= TableCliques.MAX_ARITY) {
      support.dictionary.addTable(vars, tuples);
    }
    support.pose(new HybridTable(vars, tuples));
    replaced.add(d.node());
    for (ConstElement e : group) {
      replaced.add(e.node());
    }
    removed.add(z);
    tables++;
  }

  /**
   * The row of one combination of the defining variables, or null when its index is out of the
   * index domain or of an array, or two arrays of one column disagree.
   */
  private static int[] row(
      IntVar z,
      Definition d,
      List<ConstElement> group,
      int[] columnOf,
      int arity,
      int[][] values,
      int[] at) {
    int terms = values.length;
    int[] row = new int[arity];
    boolean[] set = new boolean[arity];
    long index = d.constant();
    for (int t = 0; t < terms; t++) {
      int v = values[t][at[t]];
      row[t] = v;
      set[t] = true;
      index -= d.coefficients()[t] * v;
    }
    if (index < z.min() || index > z.max() || !z.dom().contains((int) index)) {
      return null;
    }
    for (int e = 0; e < group.size(); e++) {
      ConstElement el = group.get(e);
      long k = index - el.first();
      if (k < 0 || k >= el.array().length) {
        return null;
      }
      int v = el.array()[(int) k];
      int c = columnOf[e];
      if (set[c] ? row[c] != v : !el.value().dom().contains(v)) {
        return null;
      }
      row[c] = v;
      set[c] = true;
    }
    return row;
  }
}
