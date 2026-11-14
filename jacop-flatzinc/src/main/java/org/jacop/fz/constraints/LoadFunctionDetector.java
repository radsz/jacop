/*
 * LoadFunctionDetector.java
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
import java.util.Arrays;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.lp.TimeIndexedBound;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Finds the variables of a FlatZinc model that are functions of one bin load of a bin packing, for
 * the arc-flow blocks of {@link TimeIndexedBound}: there each load has a column per value, and a
 * variable y = g(load) gets the exact row y = &Sigma;<sub>L</sub> g(L) [load = L]. That is how the
 * load cost of the balanced academic curriculum (gbac: the square of the distance of the load to a
 * band) and the loss of a steel mill slab (a table over the load) reach the objective.
 *
 * <p>A function is built from the load through the top-level constraints that define one variable
 * from others: int_lin_eq over two variables with a unit coefficient on the defined one, int_plus,
 * int_minus, int_times, int_max, int_min, int_abs, int_pow, and element over a constant table. Each
 * such constraint holds in every solution, so the row is valid whatever the search does.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LoadFunctionDetector implements ParserTreeConstants {

  /** The values of a load at most for its functions to be tabulated. */
  static final int MAX_VALUES = 100_000;

  private final Support support;

  // a definition: out = op(a, b) (b null for unary), or out = table[a - offset]
  private record Def(String op, IntVar out, IntVar a, IntVar b, long k, long c, int[] table) {

    @Override
    public boolean equals(Object o) {
      return this == o;
    }

    @Override
    public int hashCode() {
      return System.identityHashCode(this);
    }

    @Override
    public String toString() {
      return "Def[" + op + ", " + out + "]";
    }
  }

  private final List<Def> defs = new ArrayList<>();
  private final Map<IntVar, List<Def>> uses = new IdentityHashMap<>();
  private final List<IntVar> loads = new ArrayList<>();

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public LoadFunctionDetector(Support support) {
    this.support = support;
  }

  /**
   * It scans the constraint items of the model and returns the functions of the bin loads.
   *
   * @param astTree the root of the parsed model.
   * @return the functions, one for each variable and load it is a function of
   */
  public List<TimeIndexedBound.LoadFunction> detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    List<TimeIndexedBound.LoadFunction> out = new ArrayList<>();
    Map<IntVar, Boolean> seenLoads = new IdentityHashMap<>();
    for (IntVar load : loads) {
      if (seenLoads.put(load, Boolean.TRUE) == null && !load.singleton()) {
        functionsOf(load, out);
      }
    }
    return out;
  }

  private void collect(ASTConstElem node) {
    try {
      switch (node.getName()) {
        case "jacop_bin_packing" -> {
          for (IntVar v : support.getVarArray(child(node, 1))) {
            loads.add(v);
          }
        }
        case "int_lin_eq" -> equation(node);
        case "int_plus", "int_minus", "int_times", "int_max", "int_min", "int_pow" ->
            def(node.getName(), aVar(node, 2), aVar(node, 0), aVar(node, 1), 0, 0, null);
        case "int_abs" -> def("int_abs", aVar(node, 1), aVar(node, 0), null, 0, 0, null);
        case "array_int_element", "array_var_int_element" -> element(node, 1);
        case "jacop_array_var_int_element_nonshifted" ->
            element(node, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
        default -> {
          // not a definition
        }
      }
    } catch (RuntimeException e) {
      // an argument of another shape: not a definition
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private IntVar aVar(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private void def(String op, IntVar out, IntVar a, IntVar b, long k, long c, int[] table) {
    if (out == null || out.singleton() || a == null) {
      return;
    }
    Def d = new Def(op, out, a, b, k, c, table);
    defs.add(d);
    uses.computeIfAbsent(a, v -> new ArrayList<>()).add(d);
    if (b != null && b != a) {
      uses.computeIfAbsent(b, v -> new ArrayList<>()).add(d);
    }
  }

  // a y + b x = c with |a| = 1 defines y = a (c - b x)
  private void equation(ASTConstElem node) {
    int[] w = support.getIntArray(child(node, 0));
    IntVar[] x = support.getVarArray(child(node, 1));
    if (w == null || w.length != 2 || x.length != 2 || x[0] == x[1]) {
      return;
    }
    long c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    for (int k = 0; k < 2; k++) {
      if (Math.abs(w[k]) == 1) {
        def("lin", x[k], x[1 - k], null, w[1 - k] * (long) w[k], c * w[k], null);
      }
    }
  }

  // z = table[index - offset + 1], over a constant table
  private void element(ASTConstElem node, long offset) {
    int[] table = support.getIntArray(child(node, 1));
    if (table == null) {
      IntVar[] vs = support.getVarArray(child(node, 1));
      table = new int[vs.length];
      for (int i = 0; i < vs.length; i++) {
        if (!vs[i].singleton()) {
          return;
        }
        table[i] = vs[i].value();
      }
    }
    def("element", aVar(node, 2), aVar(node, 0), null, offset, 0, table);
  }

  // the variables defined from the load alone (and constants), with their values over its domain
  private void functionsOf(IntVar load, List<TimeIndexedBound.LoadFunction> out) {
    long lo = load.min();
    long size = (long) load.max() - lo + 1;
    if (size > MAX_VALUES) {
      return;
    }
    Map<IntVar, long[]> values = new IdentityHashMap<>();
    long[] id = new long[(int) size];
    for (int i = 0; i < id.length; i++) {
      id[i] = lo + i;
    }
    values.put(load, id);
    Deque<IntVar> queue = new ArrayDeque<>();
    queue.add(load);
    while (!queue.isEmpty()) {
      IntVar v = queue.poll();
      for (Def d : uses.getOrDefault(v, List.of())) {
        if (values.containsKey(d.out())) {
          continue;
        }
        long[] f = evaluate(d, values, id.length);
        if (f != null) {
          values.put(d.out(), f);
          queue.add(d.out());
          out.add(new TimeIndexedBound.LoadFunction(d.out(), load, lo, f));
        }
      }
    }
  }

  // the values of the defined variable for each load value, or null when an argument is not known
  private static long[] evaluate(Def d, Map<IntVar, long[]> values, int n) {
    long[] a = operand(d.a(), values, n);
    long[] b = d.b() == null ? null : operand(d.b(), values, n);
    if (a == null || d.b() != null && b == null) {
      return null;
    }
    long[] f = new long[n];
    for (int i = 0; i < n; i++) {
      long x = a[i];
      long y = b == null ? 0 : b[i];
      f[i] =
          x == TimeIndexedBound.NONE || y == TimeIndexedBound.NONE
              ? TimeIndexedBound.NONE
              : apply(d, x, y);
    }
    return f;
  }

  private static long[] operand(IntVar v, Map<IntVar, long[]> values, int n) {
    long[] f = values.get(v);
    if (f == null && v.singleton()) {
      f = new long[n];
      Arrays.fill(f, v.value());
    }
    return f;
  }

  // op(x, y), NONE when undefined or out of the int range
  private static long apply(Def d, long x, long y) {
    long r;
    try {
      r =
          switch (d.op()) {
            case "lin" -> Math.subtractExact(d.c(), Math.multiplyExact(d.k(), x));
            case "int_plus" -> Math.addExact(x, y);
            case "int_minus" -> Math.subtractExact(x, y);
            case "int_times" -> Math.multiplyExact(x, y);
            case "int_max" -> Math.max(x, y);
            case "int_min" -> Math.min(x, y);
            case "int_abs" -> Math.abs(x);
            case "int_pow" -> power(x, y);
            case "element" -> {
              long i = x - d.k();
              yield i >= 0 && i < d.table().length ? d.table()[(int) i] : TimeIndexedBound.NONE;
            }
            default -> TimeIndexedBound.NONE;
          };
    } catch (ArithmeticException e) {
      return TimeIndexedBound.NONE;
    }
    if (r != TimeIndexedBound.NONE && (r < Integer.MIN_VALUE || r > Integer.MAX_VALUE)) {
      return TimeIndexedBound.NONE;
    }
    return r;
  }

  private static long power(long x, long e) {
    if (e < 0 || e > 62) {
      return TimeIndexedBound.NONE;
    }
    long r = 1;
    for (long k = 0; k < e; k++) {
      r = Math.multiplyExact(r, x);
    }
    return r;
  }
}
