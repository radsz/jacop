/*
 * ArgMaxFunctionDetector.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.ArgMaxMonotone;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * An arg_max over values that are nondecreasing functions of other variables runs on those
 * variables.
 *
 * <p>MiniZinc flattens {@code arg_max(t in T)(a[h, t] * e[p[t]])} into one variable per value,
 * defined by {@code y = a * v} and {@code v = e[p]} (an element over a constant array). ArgMax over
 * the y explains its pruning with bounds of the y, each private to one arg_max, so under LCG a
 * clause learnt for one arg_max does not apply to the next and the clauses grow long (MiniZinc
 * Challenge 2025 tower: 70 arg_max over 15 tower powers, average learnt clause 72 literals, no
 * proof in 800 s where CP-SAT, whose presolve turns y into an affine function of the element's
 * encoding, proves in 171 s). {@link ArgMaxMonotone} takes the composed function of each position
 * as a table over the shared variable p, and explains with the bounds of p.
 *
 * <p>Each value of the list is followed back through at most one two-variable linear equality
 * {@code y = m * v + c} and one element {@code v = e[p]} over a constant array (or the equality
 * alone, over a variable with a small domain); positions whose function is not nondecreasing keep
 * the value itself. The definitions stay posted, so the values are still computed. The system
 * property {@code org.jacop.fz.argMaxFunctions=false} turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ArgMaxFunctionDetector {

  /** The largest table built for one position. */
  static final int MAX_TABLE = 1 << 16;

  private final Support support;

  private final Set<SimpleNode> excluded;

  private final Set<SimpleNode> replaced = new HashSet<>();

  /** y = m * v + c. */
  private record Affine(IntVar v, long m, long c) {}

  /** v = array[p - first]. */
  private record Element(IntVar p, int[] array, int first) {}

  private final Map<IntVar, Affine> affine = new IdentityHashMap<>();

  private final Map<IntVar, Element> element = new IdentityHashMap<>();

  private final List<ASTConstElem> argMaxes = new ArrayList<>();

  private int posted;

  private int lifted;

  /**
   * It creates a detector.
   *
   * @param support the support of the FlatZinc front end.
   * @param excluded the constraints other detectors replaced; they are neither read nor rewritten.
   */
  public ArgMaxFunctionDetector(Support support, Set<SimpleNode> excluded) {
    this.support = support;
    this.excluded = excluded;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.argMaxFunctions is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.argMaxFunctions"));
  }

  /**
   * The arg_max constraints replaced by {@link ArgMaxMonotone}.
   *
   * @return their nodes
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  /**
   * It scans the model and posts an ArgMaxMonotone for each arg_max with a position whose value is
   * a function of another variable.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    if (argMaxes.isEmpty()) {
      return;
    }
    for (ASTConstElem node : argMaxes) {
      rewrite(node);
    }
    if (support.options.debug() && posted > 0) {
      FzConsole.println(
          "% arg_max function detector: "
              + posted
              + " arg_max over functions, "
              + lifted
              + " positions");
    }
  }

  private IntVar aVar(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private void collect(ASTConstElem node) {
    if (excluded.contains(node)) {
      return;
    }
    switch (node.getName()) {
      case "jacop_maximum_arg_int" -> argMaxes.add(node);
      case "int_lin_eq" -> linear(node);
      case "array_int_element" -> elementOf(node, 1);
      case "jacop_array_var_int_element_nonshifted" ->
          elementOf(node, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
      case "array_var_int_element" -> elementOf(node, 1);
      default -> {
        // not a definition
      }
    }
  }

  // a[k] * x[k] + a[o] * x[o] = c with a[k] = +-1: x[k] = a[k] * c - a[k] * a[o] * x[o]
  private void linear(ASTConstElem node) {
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (a == null || a.length != 2 || x.length != 2 || x[0] == x[1]) {
      return;
    }
    long c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    for (int k = 0; k < 2; k++) {
      int o = 1 - k;
      if (Math.abs(a[k]) == 1 && a[o] != 0 && !x[k].singleton() && !x[o].singleton()) {
        affine.putIfAbsent(x[k], new Affine(x[o], -(long) a[k] * a[o], (long) a[k] * c));
      }
    }
  }

  private void elementOf(ASTConstElem node, int first) {
    IntVar p = aVar(node, 0);
    IntVar v = aVar(node, 2);
    if (p.singleton() || v.singleton() || p == v) {
      return;
    }
    IntVar[] vars = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int[] array = new int[vars.length];
    for (int k = 0; k < vars.length; k++) {
      if (!vars[k].singleton()) {
        return;
      }
      array[k] = vars[k].value();
    }
    if (array.length > 0) {
      element.putIfAbsent(v, new Element(p, array, first));
    }
  }

  private void rewrite(ASTConstElem node) {
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    IntVar index = aVar(node, 1);
    int offset = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int n = x.length;
    IntVar[] args = new IntVar[n];
    int[][] tables = new int[n][];
    int[] firsts = new int[n];
    int found = 0;
    for (int k = 0; k < n; k++) {
      args[k] = x[k];
      if (function(x[k], k, args, tables, firsts)) {
        found++;
      }
    }
    if (found == 0) {
      return;
    }
    support.pose(new ArgMaxMonotone(args, tables, firsts, index, offset - 1));
    replaced.add(node);
    posted++;
    lifted += found;
  }

  // the function of x[k] over another variable, into args, tables and firsts
  private boolean function(IntVar y, int k, IntVar[] args, int[][] tables, int[] firsts) {
    long m = 1;
    long c = 0;
    IntVar v = y;
    Affine a = affine.get(y);
    Element e = element.get(y);
    if (e == null && a != null) {
      m = a.m();
      c = a.c();
      v = a.v();
      e = element.get(v);
    }
    int[] table;
    int from;
    IntVar p;
    if (e != null) {
      p = e.p();
      from = e.first();
      table = new int[e.array().length];
      for (int i = 0; i < table.length; i++) {
        long t = m * e.array()[i] + c;
        if (t != (int) t) {
          return false;
        }
        table[i] = (int) t;
      }
    } else if (v != y) {
      // y = m * v + c over the domain of v
      p = v;
      long span = (long) v.max() - v.min() + 1;
      if (span > MAX_TABLE) {
        return false;
      }
      from = v.min();
      table = new int[(int) span];
      for (int i = 0; i < table.length; i++) {
        long t = m * (from + (long) i) + c;
        if (t != (int) t) {
          return false;
        }
        table[i] = (int) t;
      }
    } else {
      return false;
    }
    for (int i = 1; i < table.length; i++) {
      if (table[i] < table[i - 1]) {
        return false;
      }
    }
    args[k] = p;
    tables[k] = table;
    firsts[k] = from;
    return true;
  }
}
