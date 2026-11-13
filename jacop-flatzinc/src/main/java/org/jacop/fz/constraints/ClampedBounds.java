/*
 * ClampedBounds.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.Node;
import org.jacop.fz.SimpleNode;

/**
 * Decides whether narrowing declared domains to JaCoP's integer range cut off no solution that
 * matters, so that a completed search may still claim optimality or unsatisfiability.
 *
 * <p>It reads the model's linear constraints (int_lin_eq, int_lin_le, int_eq, int_le, int_lt) as
 * they are written and propagates their bounds in 64-bit arithmetic from the declared domains,
 * which are not narrowed, together with the bound a better solution puts on the objective. This is
 * feasibility-based bound tightening, the bound propagation of MIP presolve (Savelsbergh,
 * Preprocessing and probing techniques for mixed integer programming problems, ORSA Journal on
 * Computing 6(4), 1994). A narrowed variable is harmless when
 *
 * <ul>
 *   <li>the propagated bounds keep it inside JaCoP's range on the side that was cut, or leave no
 *       solution at all;
 *   <li>it occurs in no constraint and is not the objective, so any of its values can replace a cut
 *       one;
 *   <li>it occurs only in int_lin_le rows that it satisfies better the further it goes towards the
 *       cut side, and the end of JaCoP's range already satisfies each of them for every value the
 *       propagated bounds leave to the other variables of the row (which are not moved): a cut
 *       value can then be replaced by the end of the range. This is the dual reasoning of MIP
 *       presolve on variable locks (Achterberg, Constraint Integer Programming, PhD thesis, TU
 *       Berlin, 2007).
 * </ul>
 *
 * When every narrowed variable is harmless, every solution of the model as declared (with the
 * objective so bounded) maps to a solution of the narrowed model with the same objective value.
 */
public final class ClampedBounds {

  // bounds at or beyond this magnitude count as infinite
  public static final long INF = Long.MAX_VALUE / 4;

  // the most rounds of bound propagation over all rows
  private static final int MAX_ROUNDS = 64;

  private final Map<IntVar, Integer> ids = new IdentityHashMap<>();
  private final List<IntVar> vars = new ArrayList<>();
  private long[] declaredLow = new long[16];
  private long[] declaredHigh = new long[16];
  private final Function<IntVar, long[]> declared;

  // linear rows: sum(coefficient * var) <= rhs, or = rhs when equal
  private final List<long[]> coefficients = new ArrayList<>();
  private final List<int[]> rowVars = new ArrayList<>();
  private final List<long[]> rhs = new ArrayList<>();
  private final BitSet equal = new BitSet();

  // the narrowed variables, by id, and how they occur
  private final List<Integer> clamped = new ArrayList<>();
  // ids of narrowed variables -> number of constraints that are not linear rows
  private final Map<Integer, int[]> otherOccurrences = new HashMap<>();
  // ids of narrowed variables -> rows they occur in
  private final Map<Integer, List<Integer>> rowsOf = new HashMap<>();

  /**
   * Collects the linear rows of the model and the occurrences of its narrowed variables.
   *
   * @param support the support of the FlatZinc front end
   * @param astTree the root of the parsed model
   * @param narrowed the narrowed variables, after aliases
   * @param declared the declared bounds {low, high} of a variable, as written in the model
   */
  public ClampedBounds(
      Support support,
      SimpleNode astTree,
      List<IntVar> narrowed,
      Function<IntVar, long[]> declared) {
    this.declared = declared;
    for (IntVar v : narrowed) {
      int id = id(v);
      if (!otherOccurrences.containsKey(id)) {
        clamped.add(id);
        otherOccurrences.put(id, new int[1]);
        rowsOf.put(id, new ArrayList<>());
      }
    }
    support.forEachConstraint(astTree, node -> collect(support, node));
  }

  private int id(IntVar v) {
    Integer id = ids.get(v);
    if (id == null) {
      id = vars.size();
      ids.put(v, id);
      vars.add(v);
      if (id == declaredLow.length) {
        declaredLow = Arrays.copyOf(declaredLow, 2 * id);
        declaredHigh = Arrays.copyOf(declaredHigh, 2 * id);
      }
      long[] b = declared.apply(v);
      declaredLow[id] = Math.max(-INF, b[0]);
      declaredHigh[id] = Math.min(INF, b[1]);
    }
    return id;
  }

  private void collect(Support support, ASTConstElem node) {
    int row = coefficients.size();
    boolean linear = row(support, node);
    List<IntVar> occurring = new ArrayList<>();
    occurrences(support, node, occurring);
    for (IntVar v : occurring) {
      Integer id = ids.get(v);
      if (id == null || !otherOccurrences.containsKey(id)) {
        continue;
      }
      if (linear) {
        List<Integer> rows = rowsOf.get(id);
        if (rows.isEmpty() || rows.getLast() != row) {
          rows.add(row);
        }
      } else {
        otherOccurrences.get(id)[0]++;
      }
    }
  }

  // adds the constraint as a linear row when it is one
  private boolean row(Support support, ASTConstElem node) {
    String name = node.getName();
    try {
      switch (name) {
        case "int_lin_eq", "int_lin_le" -> {
          int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
          IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
          if (a == null || a.length != x.length) {
            return false;
          }
          long b = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
          long[] c = new long[a.length];
          for (int i = 0; i < a.length; i++) {
            c[i] = a[i];
          }
          add(c, x, b, "int_lin_eq".equals(name));
          return true;
        }
        case "int_eq", "int_le", "int_lt" -> {
          IntVar x = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
          IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
          add(
              new long[] {1, -1},
              new IntVar[] {x, y},
              "int_lt".equals(name) ? -1 : 0,
              "int_eq".equals(name));
          return true;
        }
        default -> {
          return false;
        }
      }
    } catch (RuntimeException _) {
      // a form this reading does not cover: the constraint counts as an occurrence of any kind
      return false;
    }
  }

  private void add(long[] c, IntVar[] x, long b, boolean eq) {
    int[] ix = new int[x.length];
    for (int i = 0; i < x.length; i++) {
      ix[i] = id(x[i]);
    }
    coefficients.add(c);
    rowVars.add(ix);
    rhs.add(new long[] {b});
    equal.set(coefficients.size() - 1, eq);
  }

  // every variable a constraint names, also through arrays; more than it uses is safe
  private void occurrences(Support support, Node node, List<IntVar> out) {
    if (node instanceof ASTScalarFlatExpr e && (e.getType() == 2 || e.getType() == 3)) {
      IntVar[] array = support.dictionary.getVariableArray(e.getIdent());
      if (array != null) {
        out.addAll(Arrays.asList(array));
      } else {
        IntVar v = support.dictionary.getVariable(e.getIdent());
        if (v != null) {
          out.add(v);
        }
      }
    }
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      occurrences(support, node.jjtGetChild(i), out);
    }
  }

  /**
   * Tells whether the narrowing cut off no solution of the model whose objective is within the
   * given bounds.
   *
   * @param objective the variable of the objective, or null
   * @param low the least value of the objective of the solutions that matter
   * @param high the largest value of the objective of the solutions that matter
   * @return true if every such solution maps to a solution of the narrowed model with the same
   *     objective value.
   */
  public boolean harmless(IntVar objective, long low, long high) {
    int n = vars.size();
    long[] lo = Arrays.copyOf(declaredLow, n);
    long[] hi = Arrays.copyOf(declaredHigh, n);
    Integer objectiveId = objective == null ? null : ids.get(objective);
    if (objectiveId != null) {
      lo[objectiveId] = Math.max(lo[objectiveId], Math.max(-INF, low));
      hi[objectiveId] = Math.min(hi[objectiveId], Math.min(INF, high));
    } else if (objective != null && (low > -INF || high < INF)) {
      // the objective occurs in no row: its own declared bound decides
      long[] b = declared.apply(objective);
      if (Math.max(b[0], low) > Math.min(b[1], high)) {
        return true;
      }
    }
    if (!propagate(lo, hi)) {
      return true; // no solution of the model has such an objective
    }
    List<Integer> moved = new ArrayList<>();
    for (int id : clamped) {
      boolean cutLow = declaredLow[id] < IntDomain.MIN_INT;
      boolean cutHigh = declaredHigh[id] > IntDomain.MAX_INT;
      boolean lowKept = !cutLow || lo[id] >= IntDomain.MIN_INT;
      boolean highKept = !cutHigh || hi[id] <= IntDomain.MAX_INT;
      if (!lowKept || !highKept) {
        moved.add(id);
      }
    }
    for (int id : moved) {
      if (!movable(id, objectiveId, lo, hi, moved)) {
        return false;
      }
    }
    return true;
  }

  // a narrowed variable whose cut values can be replaced by the end of JaCoP's range
  private boolean movable(int id, Integer objectiveId, long[] lo, long[] hi, List<Integer> moved) {
    if (objectiveId != null && objectiveId == id || otherOccurrences.get(id)[0] > 0) {
      return false;
    }
    boolean cutLow = lo[id] < IntDomain.MIN_INT;
    boolean cutHigh = hi[id] > IntDomain.MAX_INT;
    if (cutLow && cutHigh) {
      // moving one way breaks the rows the other way needs
      return rowsOf.get(id).isEmpty();
    }
    // the value the cut ones move to, which the variable's own bounds must allow
    long to = cutHigh ? IntDomain.MAX_INT : IntDomain.MIN_INT;
    if (to < lo[id] || to > hi[id]) {
      return false;
    }
    for (int r : rowsOf.get(id)) {
      if (equal.get(r)) {
        return false;
      }
      long[] c = coefficients.get(r);
      int[] x = rowVars.get(r);
      long a = 0;
      long rest = 0;
      for (int i = 0; i < x.length; i++) {
        if (x[i] == id) {
          a = add(a, c[i]);
        } else {
          if (moved.contains(x[i])) {
            return false; // another variable of the row moves too
          }
          rest = add(rest, termMax(c[i], lo[x[i]], hi[x[i]]));
        }
      }
      // moving towards the cut side must not raise the row: a <= 0 when cut high, a >= 0 when low
      if (cutHigh ? a > 0 : a < 0) {
        return false;
      }
      if (add(multiply(a, to), rest) > rhs.get(r)[0]) {
        return false;
      }
    }
    return true;
  }

  // bound propagation over the rows; false when some bounds cross
  private boolean propagate(long[] lo, long[] hi) {
    int rows = coefficients.size();
    for (int round = 0; round < MAX_ROUNDS; round++) {
      boolean changed = false;
      for (int r = 0; r < rows; r++) {
        long[] c = coefficients.get(r);
        int[] x = rowVars.get(r);
        long b = rhs.get(r)[0];
        int k = x.length;
        // sums of the finite term bounds and the number of infinite ones
        long minSum = 0;
        long maxSum = 0;
        int minInf = 0;
        int maxInf = 0;
        long[] tMin = new long[k];
        long[] tMax = new long[k];
        for (int i = 0; i < k; i++) {
          tMin[i] = termMin(c[i], lo[x[i]], hi[x[i]]);
          tMax[i] = termMax(c[i], lo[x[i]], hi[x[i]]);
          if (tMin[i] <= -INF) {
            minInf++;
          } else {
            minSum = add(minSum, tMin[i]);
          }
          if (tMax[i] >= INF) {
            maxInf++;
          } else {
            maxSum = add(maxSum, tMax[i]);
          }
        }
        for (int i = 0; i < k; i++) {
          if (c[i] == 0) {
            continue;
          }
          // c[i] * x[i] <= b - (min of the other terms)
          int othersInf = minInf - (tMin[i] <= -INF ? 1 : 0);
          if (othersInf == 0) {
            long others = tMin[i] <= -INF ? minSum : add(minSum, -tMin[i]);
            long bound = add(b, -others);
            if (bound < INF && bound > -INF) {
              changed |=
                  c[i] > 0
                      ? lower(hi, x[i], Math.floorDiv(bound, c[i]))
                      : raise(lo, x[i], ceilDiv(bound, c[i]));
            }
          }
          if (equal.get(r)) {
            // c[i] * x[i] >= b - (max of the other terms)
            int othersMaxInf = maxInf - (tMax[i] >= INF ? 1 : 0);
            if (othersMaxInf == 0) {
              long others = tMax[i] >= INF ? maxSum : add(maxSum, -tMax[i]);
              long bound = add(b, -others);
              if (bound < INF && bound > -INF) {
                changed |=
                    c[i] > 0
                        ? raise(lo, x[i], ceilDiv(bound, c[i]))
                        : lower(hi, x[i], Math.floorDiv(bound, c[i]));
              }
            }
          }
          if (lo[x[i]] > hi[x[i]]) {
            return false;
          }
        }
      }
      if (!changed) {
        break;
      }
    }
    return true;
  }

  private static boolean lower(long[] hi, int v, long bound) {
    if (bound < hi[v]) {
      hi[v] = bound;
      return true;
    }
    return false;
  }

  private static boolean raise(long[] lo, int v, long bound) {
    if (bound > lo[v]) {
      lo[v] = bound;
      return true;
    }
    return false;
  }

  private static long ceilDiv(long a, long b) {
    return -Math.floorDiv(-a, b);
  }

  // saturating sum of two values within [-INF, INF]
  static long add(long a, long b) {
    long s = a + b; // no overflow: both are at most INF = Long.MAX_VALUE / 4 in magnitude
    return Math.clamp(s, -INF, INF);
  }

  // saturating product
  static long multiply(long a, long b) {
    if (a == 0 || b == 0) {
      return 0;
    }
    long p;
    try {
      p = Math.multiplyExact(a, b);
    } catch (ArithmeticException _) {
      return (a > 0) == (b > 0) ? INF : -INF;
    }
    if (Math.abs(a) >= INF || Math.abs(b) >= INF) {
      return (a > 0) == (b > 0) ? INF : -INF;
    }
    return Math.clamp(p, -INF, INF);
  }

  private static long termMin(long c, long lo, long hi) {
    return multiply(c, c >= 0 ? lo : hi);
  }

  private static long termMax(long c, long lo, long hi) {
    return multiply(c, c >= 0 ? hi : lo);
  }
}
