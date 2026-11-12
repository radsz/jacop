/*
 * SequenceMddDetector.java
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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.SequenceMdd;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds circuits whose arcs carry times and posts a {@link SequenceMdd} on them as a redundant
 * constraint. A routing model with time windows writes, for the arc of node i,
 *
 * <ul>
 *   <li>successor form: {@code arr[succ[i]] = dep[i] + time[i, succ[i]]} (or {@code >=}), flattened
 *       into an element of the variable array {@code arr} and an element of the constant row {@code
 *       time[i, ..]}, both indexed by {@code succ[i]}, and a linear constraint over the two element
 *       values and {@code dep[i]};
 *   <li>predecessor form: {@code arrival[l] = departure[pred[l]] + duration[l, pred[l]]}, the same
 *       with the element of the variable array giving the departure of the predecessor.
 * </ul>
 *
 * <p>The time a node is left is linked to the time it is reached by the longest chain of difference
 * constraints between them ({@code int_max}, {@code int_le}, and linear constraints of two
 * variables with coefficients 1 and -1), such as {@code ser >= arr, dep >= ser + s} or {@code
 * departure = max(arrival, early)}. The diagram starts at a node whose departure is fixed (the
 * depot), else at a node whose departure is not linked to its arrival.
 *
 * <p>The system property {@code org.jacop.fz.sequenceMdd} set to false turns the detection off;
 * {@code org.jacop.fz.sequenceMddWidth} (default 64) is the width of the diagram and {@code
 * org.jacop.fz.sequenceMddNodes} (default 32) the largest circuit it is posted on.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class SequenceMddDetector implements ParserTreeConstants {

  private static final int WIDTH = Integer.getInteger("org.jacop.fz.sequenceMddWidth", 64);

  private static final int MAX_NODES = Integer.getInteger("org.jacop.fz.sequenceMddNodes", 32);

  // the longest chain of difference constraints from an arrival to the departure
  private static final int CHAIN = 3;

  private final Support support;

  private final List<Circuit> circuits = new ArrayList<>();

  // the elements indexed by each variable, with a constant or a variable array
  private final Map<IntVar, List<Element>> elements = new IdentityHashMap<>();

  // the linear constraints of three unit terms, by each of their variables
  private final Map<IntVar, List<Linear>> linears = new IdentityHashMap<>();

  // y >= x + c, by x
  private final Map<IntVar, List<Edge>> edges = new IdentityHashMap<>();

  // the equations of unit coefficients with three or more terms, candidates for a cost
  private final List<Linear> sums = new ArrayList<>();

  // a circuit's variables and the value that stands for node 0
  private static final class Circuit {
    final IntVar[] x;
    final int offset;

    Circuit(IntVar[] x, int offset) {
      this.x = x;
      this.offset = offset;
    }
  }

  // value = array[index - first] (constants when vars is null)
  private static final class Element {
    final IntVar value;
    final int[] constants;
    final IntVar[] vars;
    final int first;

    Element(IntVar value, int[] constants, IntVar[] vars, int first) {
      this.value = value;
      this.constants = constants;
      this.vars = vars;
      this.first = first;
    }
  }

  // sum(a[k] * x[k]) = rhs (or <= rhs)
  private static final class Linear {
    final int[] a;
    final IntVar[] x;
    final int rhs;
    final boolean equation;

    Linear(int[] a, IntVar[] x, int rhs, boolean equation) {
      this.a = a;
      this.x = x;
      this.rhs = rhs;
      this.equation = equation;
    }
  }

  private record Edge(IntVar to, long c) {}

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public SequenceMddDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.sequenceMdd is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.sequenceMdd"));
  }

  /**
   * It scans the constraint items of the model and posts a SequenceMdd on each circuit with timed
   * arcs.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    for (Circuit c : circuits) {
      if (c.x.length >= 3 && c.x.length <= MAX_NODES) {
        post(c);
      }
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_circuit" -> circuits.add(new Circuit(support.getVarArray(child(node, 0)), 1));
      case "jacop_circuit_offset" ->
          circuits.add(
              new Circuit(
                  support.getVarArray(child(node, 0)),
                  support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1))));
      case "array_int_element" -> element(node, support.getIntArray(child(node, 1)), null, 1);
      case "array_var_int_element" -> varElement(node, 1);
      case "jacop_array_var_int_element_nonshifted" ->
          varElement(node, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
      case "int_lin_eq", "int_lin_le" -> linear(node);
      case "int_max" -> {
        IntVar a = var(node, 0);
        IntVar b = var(node, 1);
        IntVar m = var(node, 2);
        edge(a, m, 0);
        edge(b, m, 0);
      }
      case "int_le" -> edge(var(node, 0), var(node, 1), 0);
      case "int_eq" -> {
        edge(var(node, 0), var(node, 1), 0);
        edge(var(node, 1), var(node, 0), 0);
      }
      default -> {
        // not part of a timed circuit
      }
    }
  }

  private IntVar var(ASTConstElem node, int k) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(k));
  }

  private void edge(IntVar from, IntVar to, long c) {
    if (from != to && !(from.singleton() && to.singleton())) {
      edges.computeIfAbsent(from, k -> new ArrayList<>()).add(new Edge(to, c));
    }
  }

  private void varElement(ASTConstElem node, int first) {
    IntVar[] vars = support.getVarArray(child(node, 1));
    int[] constants = new int[vars.length];
    boolean all = true;
    for (int k = 0; k < vars.length; k++) {
      if (vars[k].singleton()) {
        constants[k] = vars[k].value();
      } else {
        all = false;
      }
    }
    if (all) {
      element(node, constants, null, first);
    } else {
      element(node, null, vars, first);
    }
  }

  private void element(ASTConstElem node, int[] constants, IntVar[] vars, int first) {
    if (constants == null && vars == null) {
      return;
    }
    IntVar index = var(node, 0);
    IntVar value = var(node, 2);
    if (!index.singleton()) {
      elements
          .computeIfAbsent(index, k -> new ArrayList<>())
          .add(new Element(value, constants, vars, first));
    }
  }

  private void linear(ASTConstElem node) {
    boolean equation = "int_lin_eq".equals(node.getName());
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] x = support.getVarArray(child(node, 1));
    if (a == null || a.length != x.length) {
      return;
    }
    int rhs = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    for (int c : a) {
      if (c != 1 && c != -1) {
        return;
      }
    }
    if (x.length == 2 && a[0] != a[1]) {
      // a[0] x0 + a[1] x1 <= rhs with opposite signs: the positive one at most the other + rhs
      IntVar pos = a[0] == 1 ? x[0] : x[1];
      IntVar neg = a[0] == 1 ? x[1] : x[0];
      // pos - neg <= rhs: neg >= pos - rhs
      edge(pos, neg, -(long) rhs);
      if (equation) {
        edge(neg, pos, rhs);
      }
    } else if (x.length == 3) {
      Linear l = new Linear(a, x, rhs, equation);
      for (IntVar v : x) {
        linears.computeIfAbsent(v, k -> new ArrayList<>()).add(l);
      }
    }
    if (equation && x.length >= 3) {
      sums.add(new Linear(a, x, rhs, true));
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  // the timed arc of one circuit variable: later >= earlier + row[value]
  private static final class Timed {
    boolean pred;
    IntVar[] times;
    int timesFirst;
    IntVar own;
    int[] row;
    int rowFirst;
    long shift;
  }

  private Timed timed(IntVar x) {
    List<Element> list = elements.get(x);
    if (list == null) {
      return null;
    }
    for (Element w : list) {
      if (w.constants == null) {
        continue;
      }
      for (Element z : list) {
        if (z.vars == null) {
          continue;
        }
        for (Linear l : linears.getOrDefault(w.value, List.of())) {
          Timed t = match(l, w, z);
          if (t != null) {
            return t;
          }
        }
      }
    }
    return null;
  }

  private static Timed match(Linear l, Element w, Element z) {
    int cw = 0;
    int cz = 0;
    int cb = 0;
    IntVar b = null;
    for (int k = 0; k < 3; k++) {
      if (l.x[k] == w.value) {
        cw = l.a[k];
      } else if (l.x[k] == z.value) {
        cz = l.a[k];
      } else {
        cb = l.a[k];
        b = l.x[k];
      }
    }
    if (cw == 0 || cz == 0 || b == null) {
      return null;
    }
    long rhs = l.rhs;
    if (cw == -1) {
      if (!l.equation) {
        return null;
      }
      cw = 1;
      cz = -cz;
      cb = -cb;
      rhs = -rhs;
    }
    Timed t = new Timed();
    if (cb == 1 && cz == -1) {
      // b + w - z <= rhs: z >= b + w - rhs, the time at the successor
      t.pred = false;
    } else if (cz == 1 && cb == -1) {
      // z + w - b <= rhs: b >= z + w - rhs, the time at this node after its predecessor
      t.pred = true;
    } else {
      return null;
    }
    t.times = z.vars;
    t.timesFirst = z.first;
    t.own = b;
    t.row = w.constants;
    t.rowFirst = w.first;
    t.shift = -rhs;
    return t;
  }

  private void post(Circuit c) {
    int n = c.x.length;
    IntVar[] in = new IntVar[n];
    IntVar[] out = new IntVar[n];
    int[][] travel = new int[n][n];
    for (int[] row : travel) {
      Arrays.fill(row, SequenceMdd.NONE);
    }
    Boolean pred = null;
    IntVar[] times = null;
    int found = 0;
    for (int i = 0; i < n; i++) {
      Timed t = timed(c.x[i]);
      if (t == null) {
        continue;
      }
      if (pred != null && (pred != t.pred || !sameTimes(times, t.times))) {
        return;
      }
      pred = t.pred;
      times = t.times;
      // node of value v is v - offset; times[v - first], row[v - rowFirst]
      for (int j = 0; j < n; j++) {
        int v = c.offset + j;
        int ti = v - t.timesFirst;
        int ri = v - t.rowFirst;
        if (ti < 0 || ti >= t.times.length || ri < 0 || ri >= t.row.length) {
          continue;
        }
        long d = t.row[ri] + t.shift;
        if (d < Integer.MIN_VALUE / 4 || d > Integer.MAX_VALUE / 4) {
          return;
        }
        IntVar other = t.times[ti];
        if (t.pred) {
          // arc j -> i: own (in[i]) >= times[j] (out[j]) + d
          if (!setOnce(out, j, other)) {
            return;
          }
          travel[j][i] = (int) d;
        } else {
          // arc i -> j: times[j] (in[j]) >= own (out[i]) + d
          if (!setOnce(in, j, other)) {
            return;
          }
          travel[i][j] = (int) d;
        }
      }
      if (!(t.pred ? setOnce(in, i, t.own) : setOnce(out, i, t.own))) {
        return;
      }
      found++;
    }
    if (pred == null || 2 * found < n) {
      return;
    }
    int[] delta = new int[n];
    int start = -1;
    for (int j = 0; j < n; j++) {
      delta[j] = link(in[j], out[j]);
      if (out[j] != null && out[j].singleton() && start < 0) {
        start = j;
      }
    }
    if (start < 0) {
      for (int j = 0; j < n && start < 0; j++) {
        if (delta[j] == SequenceMdd.NONE) {
          start = j;
        }
      }
    }
    if (start < 0) {
      start = 0;
    }
    Cost cost = cost(c, pred);
    SequenceMdd mdd =
        cost == null
            ? new SequenceMdd(c.x, pred, c.offset, in, out, travel, delta, start, WIDTH)
            : new SequenceMdd(
                c.x,
                pred,
                c.offset,
                in,
                out,
                travel,
                delta,
                start,
                WIDTH,
                cost.costs,
                cost.cost,
                cost.offset);
    mdd.setDegreeWeight(0);
    if (support.options.debug()) {
      FzConsole.println("% redundant " + mdd);
    }
    support.delayedConstraints.add(mdd);
  }

  // cost = sum of arc costs + offset
  private static final class Cost {
    final int[][] costs;
    final IntVar cost;
    final long offset;

    Cost(int[][] costs, IntVar cost, long offset) {
      this.costs = costs;
      this.cost = cost;
      this.offset = offset;
    }
  }

  /*
   * An equation s * sum(i)(w[i]) - s * cost = rhs whose w[i] are values of elements of constant
   * rows indexed by distinct circuit variables: cost = sum of arc costs - s * rhs.
   */
  private Cost cost(Circuit c, boolean pred) {
    int n = c.x.length;
    Map<IntVar, Integer> nodeOf = new IdentityHashMap<>();
    Map<IntVar, Element> rowOf = new IdentityHashMap<>();
    for (int i = 0; i < n; i++) {
      for (Element e : elements.getOrDefault(c.x[i], List.of())) {
        if (e.constants != null && !e.value.singleton()) {
          nodeOf.putIfAbsent(e.value, i);
          rowOf.putIfAbsent(e.value, e);
        }
      }
    }
    for (Linear l : sums) {
      Cost found = costOf(l, c, pred, nodeOf, rowOf);
      if (found != null) {
        return found;
      }
    }
    return null;
  }

  private static Cost costOf(
      Linear l, Circuit c, boolean pred, Map<IntVar, Integer> nodeOf, Map<IntVar, Element> rowOf) {
    int n = c.x.length;
    IntVar cost = null;
    int costCoefficient = 0;
    int sign = 0;
    boolean[] seen = new boolean[n];
    long[][] costs = new long[n][n];
    int terms = 0;
    for (int k = 0; k < l.x.length; k++) {
      Integer i = nodeOf.get(l.x[k]);
      if (i == null) {
        if (cost != null) {
          return null;
        }
        cost = l.x[k];
        costCoefficient = l.a[k];
        continue;
      }
      if (seen[i] || sign != 0 && sign != l.a[k]) {
        return null;
      }
      seen[i] = true;
      sign = l.a[k];
      terms++;
      Element e = rowOf.get(l.x[k]);
      for (int j = 0; j < n; j++) {
        int idx = c.offset + j - e.first;
        long w = idx >= 0 && idx < e.constants.length ? e.constants[idx] : 0;
        if (pred) {
          // the element of pred[i] gives the cost of the arc j -> i
          costs[j][i] = w;
        } else {
          costs[i][j] = w;
        }
      }
    }
    if (cost == null || costCoefficient != -sign || 2 * terms < n) {
      return null;
    }
    int[][] result = new int[n][n];
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (costs[i][j] < Integer.MIN_VALUE / 4 || costs[i][j] > Integer.MAX_VALUE / 4) {
          return null;
        }
        result[i][j] = (int) costs[i][j];
      }
    }
    return new Cost(result, cost, -(long) sign * l.rhs);
  }

  private static boolean sameTimes(IntVar[] a, IntVar[] b) {
    if (a == b) {
      return true;
    }
    if (a == null || b == null || a.length != b.length) {
      return false;
    }
    for (int k = 0; k < a.length; k++) {
      if (a[k] != b[k]) {
        return false;
      }
    }
    return true;
  }

  private static boolean setOnce(IntVar[] array, int j, IntVar v) {
    if (array[j] == null) {
      array[j] = v;
      return true;
    }
    return array[j] == v;
  }

  // the longest chain of difference constraints from the arrival to the departure, or NONE
  private int link(IntVar from, IntVar to) {
    if (from == null || to == null) {
      return SequenceMdd.NONE;
    }
    if (from == to) {
      return 0;
    }
    long best = longest(from, to, CHAIN);
    if (best == Long.MIN_VALUE || best < Integer.MIN_VALUE / 4 || best > Integer.MAX_VALUE / 4) {
      return SequenceMdd.NONE;
    }
    return (int) best;
  }

  private long longest(IntVar from, IntVar to, int depth) {
    long best = Long.MIN_VALUE;
    for (Edge e : edges.getOrDefault(from, List.of())) {
      if (e.to == to) {
        best = Math.max(best, e.c);
      } else if (depth > 1 && !e.to.singleton()) {
        long rest = longest(e.to, to, depth - 1);
        if (rest != Long.MIN_VALUE) {
          best = Math.max(best, e.c + rest);
        }
      }
    }
    return best;
  }
}
