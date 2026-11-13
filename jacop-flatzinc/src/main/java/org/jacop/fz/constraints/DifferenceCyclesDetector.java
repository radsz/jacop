/*
 * DifferenceCyclesDetector.java
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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.DifferenceCycles;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It reads the difference constraints {@code k (x - y) <= c} of a model, the ones that always hold
 * ({@code int_lin_le}, {@code int_lin_eq}, {@code int_le}, {@code int_lt}) and the half-reified and
 * reified ones ({@code int_lin_le_imp}, {@code int_lin_le_reif}, {@code int_lin_eq_imp}, {@code
 * int_lin_eq_reif}, {@code int_le_imp}, {@code int_le_reif}, {@code int_lt_imp}, {@code
 * int_lt_reif}), and posts a redundant {@link DifferenceCycles} over them, which fails as soon as
 * the ones that hold make a cycle of negative weight (incremental negative-cycle detection of
 * Cotton and Maler, SAT 2006, after Ramalingam, Song, Joskowicz and Miller, Algorithmica 1999). It
 * is posted only when a conditional difference constraint lies on a cycle of the graph of all of
 * them, as in job shop and RCPSP/max models with precedences chosen by 0/1 variables.
 *
 * <p>Setting the system property {@code org.jacop.fz.differenceCycles} to false turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class DifferenceCyclesDetector implements ParserTreeConstants {

  // arcs whose weight is the bound of a third variable of a row, and the m >= x arcs of max and min
  private static final boolean OFFSETS =
      !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.differenceOffsets"));

  // arcs of the elements y = a[index] over arrays of variables, conditional on the index
  private static final boolean ELEMENTS =
      !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.differenceElements"));

  private final Support support;

  private final List<IntVar> xs = new ArrayList<>();
  private final List<IntVar> ys = new ArrayList<>();
  private final List<Integer> cs = new ArrayList<>();
  private final List<IntVar> bs = new ArrayList<>();
  private final List<Integer> vs = new ArrayList<>();
  private final List<IntVar> os = new ArrayList<>();
  private final List<Integer> ss = new ArrayList<>();
  private final Store scratch = new Store();
  private final Map<Integer, IntVar> constants = new HashMap<>();

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public DifferenceCyclesDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.differenceCycles is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.differenceCycles"));
  }

  /**
   * It reads the difference constraints of the model and adds a redundant {@link DifferenceCycles}
   * to the delayed constraints when one of the conditional ones can be on a cycle.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    long start = System.nanoTime();
    support.forEachConstraint(astTree, this::collect);
    if (bs.stream().allMatch(b -> b == null) && os.stream().allMatch(o -> o == null)) {
      return;
    }
    int m = xs.size();
    int[] c = new int[m];
    int[] v = new int[m];
    int[] s = new int[m];
    for (int i = 0; i < m; i++) {
      c[i] = cs.get(i);
      v[i] = vs.get(i);
      s[i] = ss.get(i);
    }
    DifferenceCycles cycles =
        new DifferenceCycles(
            xs.toArray(new IntVar[0]),
            ys.toArray(new IntVar[0]),
            c,
            bs.toArray(new IntVar[0]),
            v,
            os.toArray(new IntVar[0]),
            s);
    if (support.options.debug()) {
      FzConsole.println(
          "% difference cycles: "
              + m
              + " difference constraints, "
              + cycles.conditionalArcs()
              + " conditional and "
              + cycles.offsetArcs()
              + " with offsets on cycles, "
              + (System.nanoTime() - start) / 1_000_000
              + " ms");
    }
    if (cycles.conditionalArcs() == 0 && cycles.offsetArcs() == 0) {
      return;
    }
    // redundant, so degree-based variable selections see the degrees of the model
    cycles.setDegreeWeight(0);
    support.delayedConstraints.add(cycles);
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "int_lin_le" -> linear(node, null, false, false);
      case "int_lin_eq" -> linear(node, null, true, false);
      case "int_lin_le_imp" -> linear(node, aVar(node, 3), false, false);
      case "int_lin_le_reif" -> linear(node, aVar(node, 3), false, true);
      case "int_lin_eq_imp", "int_lin_eq_reif" -> linear(node, aVar(node, 3), true, false);
      case "int_le" -> difference(aVar(node, 0), aVar(node, 1), 0, null, 1);
      case "int_max" -> {
        if (OFFSETS) {
          // m >= x and m >= y
          difference(aVar(node, 0), aVar(node, 2), 0, null, 1);
          difference(aVar(node, 1), aVar(node, 2), 0, null, 1);
        }
      }
      case "int_min" -> {
        if (OFFSETS) {
          // m <= x and m <= y
          difference(aVar(node, 2), aVar(node, 0), 0, null, 1);
          difference(aVar(node, 2), aVar(node, 1), 0, null, 1);
        }
      }
      case "array_var_int_element" -> {
        if (ELEMENTS) {
          element(node, 1);
        }
      }
      case "jacop_array_var_int_element_nonshifted" -> {
        if (ELEMENTS) {
          element(node, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
        }
      }
      case "int_lt" -> difference(aVar(node, 0), aVar(node, 1), -1, null, 1);
      case "int_le_imp" -> difference(aVar(node, 0), aVar(node, 1), 0, aVar(node, 2), 1);
      case "int_lt_imp" -> difference(aVar(node, 0), aVar(node, 1), -1, aVar(node, 2), 1);
      case "int_le_reif" -> {
        // x <= y, or y < x when false
        difference(aVar(node, 0), aVar(node, 1), 0, aVar(node, 2), 1);
        difference(aVar(node, 1), aVar(node, 0), -1, aVar(node, 2), 0);
      }
      case "int_lt_reif" -> {
        // x < y, or y <= x when false
        difference(aVar(node, 0), aVar(node, 1), -1, aVar(node, 2), 1);
        difference(aVar(node, 1), aVar(node, 0), 0, aVar(node, 2), 0);
      }
      default -> {
        // not a difference constraint
      }
    }
  }

  // constants come from a scratch store, so that reading the model adds no variable to it; arcs
  // through constants are dropped and constant literals are resolved before the constraint is built
  private IntVar aVar(ASTConstElem node, int i) {
    return scalar(node, i);
  }

  private IntVar scalar(SimpleNode node, int i) {
    ASTScalarFlatExpr e = (ASTScalarFlatExpr) node.jjtGetChild(i);
    int type = e.getType();
    if (type == 0 || type == 1) {
      return constant(e.getInt());
    }
    if (type == 2 && support.dictionary.getVariable(e.getIdent()) == null) {
      return constant(support.dictionary.getInt(e.getIdent()));
    }
    return support.getVariable(e);
  }

  // the two variables of an array of length two, or null
  private IntVar[] pair(SimpleNode array) {
    if (array.getId() == JJTARRAYLITERAL) {
      if (array.jjtGetNumChildren() != 2) {
        return null;
      }
      return new IntVar[] {scalar(array, 0), scalar(array, 1)};
    }
    if (array.getId() == JJTSCALARFLATEXPR && ((ASTScalarFlatExpr) array).getType() == 2) {
      IntVar[] x = support.dictionary.getVariableArray(((ASTScalarFlatExpr) array).getIdent());
      return x != null && x.length == 2 ? x : null;
    }
    return null;
  }

  private IntVar constant(int c) {
    return constants.computeIfAbsent(c, k -> new IntVar(scratch, k, k));
  }

  // k * x0 - k * x1 <= c (or = c) over two variables, conditional on literal when it is not null
  private void linear(ASTConstElem node, IntVar literal, boolean equation, boolean reified) {
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    if (OFFSETS && literal == null && a != null && a.length == 3) {
      offsetRow(node, a, equation);
      return;
    }
    if (a == null || a.length != 2 || a[0] != -a[1] || a[0] == 0 || a[0] == Integer.MIN_VALUE) {
      return;
    }
    IntVar[] x = pair((SimpleNode) node.jjtGetChild(1));
    if (x == null) {
      return;
    }
    long c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    long k = Math.abs(a[0]);
    // plus - minus <= floor(c / k)
    IntVar plus = a[0] > 0 ? x[0] : x[1];
    IntVar minus = a[0] > 0 ? x[1] : x[0];
    difference(plus, minus, Math.floorDiv(c, k), literal, 1);
    if (equation && c % k == 0) {
      difference(minus, plus, -c / k, literal, 1);
    }
    if (reified && !equation) {
      // false: k (plus - minus) >= c + 1, so minus - plus <= -ceil((c + 1) / k)
      difference(minus, plus, -Math.floorDiv(c + k, k), literal, 0);
    }
  }

  // a row a0 x0 + a1 x1 + a2 x2 <= c (or = c) of unit coefficients: for each pair of opposite
  // coefficients, x - y <= c - s * z with the third variable z as the offset of the arc
  private void offsetRow(ASTConstElem node, int[] a, boolean equation) {
    for (int k : a) {
      if (k != 1 && k != -1) {
        return;
      }
    }
    SimpleNode array = (SimpleNode) node.jjtGetChild(1);
    IntVar[] x = vars(array, 3);
    if (x == null) {
      return;
    }
    long c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    for (int i = 0; i < 3; i++) {
      for (int j = 0; j < 3; j++) {
        if (i == j || a[i] != 1 || a[j] != -1) {
          continue;
        }
        int r = 3 - i - j;
        // x[i] - x[j] <= c - a[r] x[r]
        offsetDifference(x[i], x[j], c, x[r], a[r]);
        if (equation) {
          // x[j] - x[i] <= -c + a[r] x[r]
          offsetDifference(x[j], x[i], -c, x[r], -a[r]);
        }
      }
    }
  }

  // x - y <= c - s * z
  private void offsetDifference(IntVar x, IntVar y, long c, IntVar z, int s) {
    if (z.singleton()) {
      difference(x, y, c - (long) s * z.value(), null, 1);
      return;
    }
    if (x == y
        || x.singleton()
        || y.singleton()
        || c < Integer.MIN_VALUE
        || c > Integer.MAX_VALUE) {
      return;
    }
    xs.add(x);
    ys.add(y);
    cs.add((int) c);
    bs.add(null);
    vs.add(1);
    os.add(z);
    ss.add(s);
  }

  // y = a[index - first]: for each value j of the index, y - a[j] <= 0 and a[j] - y <= 0 hold
  // when index == j
  private void element(ASTConstElem node, int first) {
    IntVar index = aVar(node, 0);
    IntVar[] a = vars((SimpleNode) node.jjtGetChild(1), -1);
    IntVar y = aVar(node, 2);
    if (a == null || y.singleton()) {
      return;
    }
    for (ValueEnumeration e = index.dom().valueEnumeration(); e.hasMoreElements(); ) {
      int j = e.nextElement();
      int at = j - first;
      if (at < 0 || at >= a.length) {
        continue;
      }
      IntVar b = index.singleton() ? null : index;
      conditional(y, a[at], 0, b, j);
      conditional(a[at], y, 0, b, j);
    }
  }

  // x - y <= c when literal == value, for a literal of any domain
  private void conditional(IntVar x, IntVar y, long c, IntVar literal, int value) {
    if (literal == null || literal.min() >= 0 && literal.max() <= 1) {
      difference(x, y, c, literal, value);
      return;
    }
    if (x == y || x.singleton() || y.singleton()) {
      return;
    }
    xs.add(x);
    ys.add(y);
    cs.add((int) c);
    bs.add(literal);
    vs.add(value);
    os.add(null);
    ss.add(1);
  }

  // the variables of an array (of length n, or any length for n < 0), or null
  private IntVar[] vars(SimpleNode array, int n) {
    IntVar[] x;
    if (array.getId() == JJTARRAYLITERAL) {
      x = new IntVar[array.jjtGetNumChildren()];
      for (int i = 0; i < x.length; i++) {
        x[i] = scalar(array, i);
      }
    } else if (array.getId() == JJTSCALARFLATEXPR && ((ASTScalarFlatExpr) array).getType() == 2) {
      x = support.dictionary.getVariableArray(((ASTScalarFlatExpr) array).getIdent());
    } else {
      return null;
    }
    return x == null || n >= 0 && x.length != n ? null : x;
  }

  // x - y <= c when literal is null or literal == value
  private void difference(IntVar x, IntVar y, long c, IntVar literal, int value) {
    // an arc through a constant is on no cycle of the variables; it never reaches the constraint,
    // so
    // the scratch constants stay out of it
    if (x == y
        || x.singleton()
        || y.singleton()
        || c < Integer.MIN_VALUE
        || c > Integer.MAX_VALUE) {
      return;
    }
    IntVar b = literal;
    if (b != null && b.singleton()) {
      if (b.value() != value) {
        return;
      }
      b = null;
    }
    if (b != null && (b.min() < 0 || b.max() > 1)) {
      return;
    }
    xs.add(x);
    ys.add(y);
    cs.add((int) c);
    bs.add(b);
    vs.add(value);
    os.add(null);
    ss.add(1);
  }
}
