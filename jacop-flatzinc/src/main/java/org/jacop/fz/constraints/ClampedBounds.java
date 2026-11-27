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

import java.math.BigDecimal;
import java.math.MathContext;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.floats.core.FloatVar;
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

  // functional constraints whose result is bounded by its arguments: {kind, result, args...}, or
  // for an element over constants {ELEMENT_CONST, result, low, high}
  private final List<long[]> functions = new ArrayList<>();
  // the narrowed products posted saturated
  private final Set<IntVar> saturated;
  private static final int TIMES = 0;
  private static final int MAX = 1;
  private static final int MIN = 2;
  private static final int ABS = 3;
  private static final int DIV = 4;
  private static final int MOD = 5;
  private static final int ELEMENT_CONST = 6;
  private static final int HULL = 7;
  private static final int POW = 8;

  // the float variables int2float makes equal to an integer variable, by the integer's id
  private final Map<FloatVar, Integer> intImages = new IdentityHashMap<>();
  // the float rows as read: {coefficients, terms (FloatVar or Double), rhs, kind}, resolved once
  // every int2float is known
  private final List<Object[]> floatRowsRead = new ArrayList<>();
  // float rows over integer images: sum(a * x) <= b (both directions when equal), exact values
  private final List<BigDecimal[]> floatCoefficients = new ArrayList<>();
  private final List<int[]> floatRowVars = new ArrayList<>();
  private final List<BigDecimal> floatRhs = new ArrayList<>();
  private final BitSet floatEqual = new BitSet();

  // the reified equalities of the model: each control variable maps to the pairs of variables
  // whose equality it reifies, read to bound a variable that an if-then-else makes equal to one of
  // several values
  private final Map<IntVar, List<IntVar[]>> equalityReifications = new IdentityHashMap<>();
  // the conditions and branches of the Boolean if-then-else constraints whose result is true
  private final List<IntVar[][]> trueIfThenElses = new ArrayList<>();

  /**
   * Collects the linear rows of the model and the occurrences of its narrowed variables.
   *
   * @param support the support of the FlatZinc front end
   * @param astTree the root of the parsed model
   * @param narrowed the narrowed variables, after aliases
   * @param declared the declared bounds {low, high} of a variable, as written in the model
   * @param saturated the narrowed products posted saturated (XmulYeqZSaturated), which lose no
   *     solution: they are left out; read when the narrowing is checked, as the products are posted
   *     after the rows are read
   */
  public ClampedBounds(
      Support support,
      SimpleNode astTree,
      List<IntVar> narrowed,
      Function<IntVar, long[]> declared,
      Set<IntVar> saturated) {
    this.declared = declared;
    this.saturated = saturated;
    for (IntVar v : narrowed) {
      int id = id(v);
      if (!otherOccurrences.containsKey(id)) {
        clamped.add(id);
        otherOccurrences.put(id, new int[1]);
        rowsOf.put(id, new ArrayList<>());
      }
    }
    support.forEachConstraint(astTree, node -> collect(support, node));
    for (Object[] row : floatRowsRead) {
      floatRow((double[]) row[0], (Object[]) row[1], (Double) row[2], (Boolean) row[3]);
    }
    for (IntVar[][] ite : trueIfThenElses) {
      chosenValue(ite[0], ite[1]);
    }
  }

  /**
   * Bounds a variable that a Boolean if-then-else with a true result makes equal to one of several
   * values. The if-then-else makes the branch of its first true condition true. When a condition is
   * fixed true and every branch that can be chosen reifies the equality of one variable with some
   * value, every solution gives the variable one of those values, so it lies in their hull.
   *
   * @param c the conditions
   * @param x the branches
   */
  private void chosenValue(IntVar[] c, IntVar[] x) {
    List<List<IntVar[]>> chosen = new ArrayList<>();
    boolean total = false;
    for (int i = 0; i < c.length && i < x.length && !total; i++) {
      if (c[i].singleton(0) || x[i].singleton(0)) {
        continue; // never chosen, or chosen only in no solution
      }
      List<IntVar[]> pairs = equalityReifications.get(x[i]);
      if (pairs == null || x[i].singleton(1)) {
        return;
      }
      chosen.add(pairs);
      total = c[i].singleton(1);
    }
    if (!total || chosen.isEmpty()) {
      return;
    }
    for (IntVar[] first : chosen.getFirst()) {
      for (IntVar v : first) {
        if (v.singleton()) {
          continue;
        }
        IntVar[] values = new IntVar[chosen.size()];
        for (int i = 0; i < chosen.size() && values != null; i++) {
          values[i] = otherSide(chosen.get(i), v);
          if (values[i] == null) {
            values = null;
          }
        }
        if (values != null) {
          functions.add(withArgs(HULL, v, values));
        }
      }
    }
  }

  // the other side of a reified equality over v, or null
  private static IntVar otherSide(List<IntVar[]> pairs, IntVar v) {
    for (IntVar[] p : pairs) {
      if (p[0] == v && p[1] != v) {
        return p[1];
      }
      if (p[1] == v && p[0] != v) {
        return p[0];
      }
    }
    return null;
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
    if (!linear) {
      function(support, node);
    }
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

  // notes a constraint that bounds a result by its arguments (interval arithmetic, forwards only)
  private void function(Support support, ASTConstElem node) {
    String name = node.getName();
    try {
      switch (name) {
        case "int_times", "int_max", "int_min", "int_div", "int_mod", "int_pow" -> {
          IntVar x = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
          IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
          IntVar z = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
          int kind =
              switch (name) {
                case "int_times" -> TIMES;
                case "int_max" -> MAX;
                case "int_min" -> MIN;
                case "int_div" -> DIV;
                case "int_pow" -> POW;
                default -> MOD;
              };
          functions.add(new long[] {kind, id(z), id(x), id(y)});
        }
        case "int_abs" -> {
          IntVar x = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
          IntVar z = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
          functions.add(new long[] {ABS, id(z), id(x)});
        }
        case "jacop_maximum", "jacop_minimum" -> {
          IntVar z = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
          IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
          functions.add(withArgs(name.endsWith("maximum") ? MAX : MIN, z, x));
        }
        case "array_int_element" -> {
          int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(1));
          IntVar z = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
          if (a != null && a.length > 0) {
            functions.add(
                new long[] {
                  ELEMENT_CONST,
                  id(z),
                  Arrays.stream(a).min().getAsInt(),
                  Arrays.stream(a).max().getAsInt()
                });
          }
        }
        case "array_var_int_element" -> {
          IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
          IntVar z = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
          functions.add(withArgs(HULL, z, x));
        }
        case "int_eq_reif" -> {
          IntVar u = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
          IntVar v = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
          IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
          equalityReifications.computeIfAbsent(b, _ -> new ArrayList<>()).add(new IntVar[] {u, v});
        }
        case "jacop_if_then_else_bool" -> {
          IntVar[] c = support.getVarArray((SimpleNode) node.jjtGetChild(0));
          IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
          IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
          if (y.singleton(1)) {
            trueIfThenElses.add(new IntVar[][] {c, x});
          }
        }
        case "jacop_table_int" -> {
          // each variable takes a value of its column of the tuples
          IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
          int[] t = support.getIntArray((SimpleNode) node.jjtGetChild(1));
          if (t != null && x.length > 0 && t.length > 0 && t.length % x.length == 0) {
            for (int i = 0; i < x.length; i++) {
              long low = Long.MAX_VALUE;
              long high = Long.MIN_VALUE;
              for (int j = i; j < t.length; j += x.length) {
                low = Math.min(low, t[j]);
                high = Math.max(high, t[j]);
              }
              functions.add(new long[] {ELEMENT_CONST, id(x[i]), low, high});
            }
          }
        }
        case "jacop_count_values" -> {
          // each counter counts some of the variables: it lies within 0..n
          IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
          IntVar[] counter = support.getVarArray((SimpleNode) node.jjtGetChild(2));
          for (IntVar c : counter) {
            functions.add(new long[] {ELEMENT_CONST, id(c), 0, x.length});
          }
        }
        case "int2float" -> {
          IntVar x = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
          ASTScalarFlatExpr y = (ASTScalarFlatExpr) node.jjtGetChild(1);
          FloatVar f = y.getType() == 2 ? support.dictionary.getFloatVariable(y.getIdent()) : null;
          if (f != null && !intImages.containsKey(f)) {
            intImages.put(f, id(x));
          }
        }
        case "float_lin_le", "float_lin_lt", "float_lin_eq" -> {
          // read without creating variables for the constants; a strict row is read as a <= row
          double[] a = support.getFloatArray((SimpleNode) node.jjtGetChild(0));
          Object[] terms = floatTerms(support, (SimpleNode) node.jjtGetChild(1));
          ASTScalarFlatExpr rhs = (ASTScalarFlatExpr) node.jjtGetChild(2);
          // a literal or a parameter (getFloat of an unknown array element gives no value)
          double b =
              rhs.getType() == 5
                  ? rhs.getFloat()
                  : rhs.getType() == 2 ? support.dictionary.getFloat(rhs.getIdent()) : Double.NaN;
          if (a != null && terms != null && a.length == terms.length) {
            floatRowsRead.add(new Object[] {a, terms, b, "float_lin_eq".equals(name)});
          }
        }
        case "bool2int" -> {
          IntVar z = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
          functions.add(new long[] {ELEMENT_CONST, id(z), 0, 1});
        }
        default -> {
          // no bound on a result
        }
      }
    } catch (RuntimeException _) {
      // a form this reading does not cover: no bound is taken from it
    }
  }

  // the terms of a float array argument, each a FloatVar or a Double constant; null for a form
  // this reading does not cover
  private static Object[] floatTerms(Support support, SimpleNode node) {
    if (node instanceof ASTScalarFlatExpr e) {
      FloatVar[] array =
          e.getType() == 2 ? support.dictionary.getVariableFloatArray(e.getIdent()) : null;
      return array == null ? null : Arrays.copyOf(array, array.length, Object[].class);
    }
    Object[] terms = new Object[node.jjtGetNumChildren()];
    for (int i = 0; i < terms.length; i++) {
      if (!(node.jjtGetChild(i) instanceof ASTScalarFlatExpr e)) {
        return null;
      }
      switch (e.getType()) {
        case 5 -> terms[i] = e.getFloat();
        case 2 -> {
          FloatVar v = support.dictionary.getFloatVariable(e.getIdent());
          terms[i] = v != null ? v : (Object) support.dictionary.getFloat(e.getIdent());
        }
        case 3 -> {
          FloatVar[] array = support.dictionary.getVariableFloatArray(e.getIdent());
          if (array == null || e.getInt() < 0 || e.getInt() >= array.length) {
            return null;
          }
          terms[i] = array[e.getInt()];
        }
        default -> {
          return null;
        }
      }
    }
    return terms;
  }

  // keeps a float row whose every term is a constant or the image of an integer variable
  private void floatRow(double[] a, Object[] terms, double b, boolean eq) {
    if (!Double.isFinite(b)) {
      return;
    }
    BigDecimal rhs = new BigDecimal(b);
    List<BigDecimal> c = new ArrayList<>();
    List<Integer> x = new ArrayList<>();
    for (int i = 0; i < a.length; i++) {
      if (!Double.isFinite(a[i])) {
        return;
      }
      if (a[i] == 0) {
        continue;
      }
      Integer image = terms[i] instanceof FloatVar f ? intImages.get(f) : null;
      if (terms[i] instanceof Double d && Double.isFinite(d)) {
        rhs = rhs.subtract(new BigDecimal(a[i]).multiply(new BigDecimal(d)));
      } else if (image != null) {
        c.add(new BigDecimal(a[i]));
        x.add(image);
      } else {
        return; // a float variable of its own: its bounds are not read
      }
    }
    floatCoefficients.add(c.toArray(new BigDecimal[0]));
    floatRowVars.add(x.stream().mapToInt(Integer::intValue).toArray());
    floatRhs.add(rhs);
    floatEqual.set(floatRhs.size() - 1, eq);
  }

  // the slack a bound from a float row is widened by, relative to the magnitudes summed: the rows
  // hold the doubles written for decimal constants, and float propagation accepts values within
  // its precision of a bound
  private static final BigDecimal SLACK = new BigDecimal("1e-6");
  private static final BigDecimal BIG_INF = BigDecimal.valueOf(INF);

  // bound propagation over the float rows: each integer x of a row with coefficient a gets
  // a * x <= b - (min of the other terms), widened outwards; false when some bounds cross
  private boolean propagateFloatRows(long[] lo, long[] hi, boolean[] changed) {
    for (int r = 0; r < floatRhs.size(); r++) {
      BigDecimal[] c = floatCoefficients.get(r);
      int[] x = floatRowVars.get(r);
      for (int direction = 0; direction < (floatEqual.get(r) ? 2 : 1); direction++) {
        // direction 1 reads the equal row as -sum(a * x) <= -b
        BigDecimal b = direction == 0 ? floatRhs.get(r) : floatRhs.get(r).negate();
        for (int i = 0; i < x.length; i++) {
          BigDecimal ai = direction == 0 ? c[i] : c[i].negate();
          BigDecimal others = BigDecimal.ZERO;
          BigDecimal magnitude = b.abs();
          boolean finite = true;
          for (int j = 0; j < x.length && finite; j++) {
            if (j == i) {
              continue;
            }
            BigDecimal aj = direction == 0 ? c[j] : c[j].negate();
            long v = aj.signum() > 0 ? lo[x[j]] : hi[x[j]];
            if (v <= -INF || v >= INF) {
              finite = false;
            } else {
              BigDecimal term = aj.multiply(BigDecimal.valueOf(v));
              others = others.add(term);
              magnitude = magnitude.add(term.abs());
            }
          }
          if (!finite) {
            continue;
          }
          // ai * x <= b - others + slack
          BigDecimal bound = b.subtract(others).add(SLACK.multiply(magnitude.add(BigDecimal.ONE)));
          if (ai.signum() > 0) {
            // rounded up, then down to an integer: never below the exact bound's floor
            BigDecimal q = bound.divide(ai, new MathContext(40, RoundingMode.CEILING));
            BigDecimal f = q.setScale(0, RoundingMode.FLOOR);
            if (f.compareTo(BIG_INF) < 0) {
              changed[0] |= lower(hi, x[i], f.max(BIG_INF.negate()).longValue());
            }
          } else {
            // dividing by a negative coefficient turns the bound into a lower one
            BigDecimal q = bound.divide(ai, new MathContext(40, RoundingMode.FLOOR));
            BigDecimal f = q.setScale(0, RoundingMode.CEILING);
            if (f.compareTo(BIG_INF.negate()) > 0) {
              changed[0] |= raise(lo, x[i], f.min(BIG_INF).longValue());
            }
          }
          if (lo[x[i]] > hi[x[i]]) {
            return false;
          }
        }
      }
    }
    return true;
  }

  private long[] withArgs(int kind, IntVar z, IntVar[] x) {
    long[] f = new long[2 + x.length];
    f[0] = kind;
    f[1] = id(z);
    for (int i = 0; i < x.length; i++) {
      f[2 + i] = id(x[i]);
    }
    return f;
  }

  // narrows the results of the functional constraints to the bounds of their arguments; false when
  // some bounds cross
  private boolean propagateFunctions(long[] lo, long[] hi, boolean[] changed) {
    for (long[] f : functions) {
      int z = (int) f[1];
      long low;
      long high;
      switch ((int) f[0]) {
        case TIMES -> {
          int x = (int) f[2];
          int y = (int) f[3];
          long[] p = {
            multiply(lo[x], lo[y]),
            multiply(lo[x], hi[y]),
            multiply(hi[x], lo[y]),
            multiply(hi[x], hi[y])
          };
          low = Arrays.stream(p).min().getAsLong();
          high = Arrays.stream(p).max().getAsLong();
        }
        case MAX, MIN, HULL -> {
          boolean max = f[0] == MAX;
          boolean min = f[0] == MIN;
          low = max ? -INF : INF;
          high = min ? INF : -INF;
          for (int i = 2; i < f.length; i++) {
            int x = (int) f[i];
            if (max) {
              low = Math.max(low, lo[x]);
              high = Math.max(high, hi[x]);
            } else if (min) {
              low = Math.min(low, lo[x]);
              high = Math.min(high, hi[x]);
            } else {
              low = Math.min(low, lo[x]);
              high = Math.max(high, hi[x]);
            }
          }
        }
        case ABS -> {
          int x = (int) f[2];
          long m = Math.max(Math.abs(lo[x]), Math.abs(hi[x]));
          low = lo[x] > 0 ? lo[x] : hi[x] < 0 ? -hi[x] : 0;
          high = m;
        }
        case DIV -> {
          // |x div y| <= |x|
          int x = (int) f[2];
          long m = Math.max(Math.abs(lo[x]), Math.abs(hi[x]));
          low = -m;
          high = m;
        }
        case MOD -> {
          // |x mod y| <= |x| and < |y|
          int x = (int) f[2];
          int y = (int) f[3];
          long m =
              Math.min(
                  Math.max(Math.abs(lo[x]), Math.abs(hi[x])),
                  Math.max(Math.abs(lo[y]), Math.abs(hi[y])));
          low = -m;
          high = m;
        }
        case POW -> {
          long[] b = power(lo[(int) f[2]], hi[(int) f[2]], lo[(int) f[3]], hi[(int) f[3]]);
          low = b[0];
          high = b[1];
        }
        default -> {
          low = f[2];
          high = f[3];
        }
      }
      changed[0] |= raise(lo, z, Math.max(-INF, low));
      changed[0] |= lower(hi, z, Math.min(INF, high));
      if (lo[z] > hi[z]) {
        return false;
      }
    }
    return true;
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
      IntVar[] array = support.dictionary.getDeclaredVariableArray(e.getIdent());
      if (array != null) {
        out.addAll(Arrays.asList(array));
      } else {
        IntVar v = support.dictionary.getVariable(e);
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
    if (keptWithinRange()) {
      // bounds on the objective only narrow the propagated bounds further
      return true;
    }
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
      if (saturated.contains(vars.get(id))) {
        continue;
      }
      boolean cutLow = declaredLow[id] < IntDomain.MIN_INT;
      boolean cutHigh = declaredHigh[id] > IntDomain.MAX_INT;
      boolean lowKept = !cutLow || lo[id] >= IntDomain.MIN_INT;
      boolean highKept = !cutHigh || hi[id] <= IntDomain.MAX_INT;
      if (!lowKept || !highKept) {
        moved.add(id);
      }
    }
    for (int id : moved) {
      if (!movable(id, objectiveId, lo, hi, moved) && !freeFactor(id, objectiveId, lo, hi)) {
        return false;
      }
    }
    return true;
  }

  /**
   * A narrowed variable c cut on its high side that matters only through a product p = f * c with f
   * >= 0, while p stays within the range: in a solution with c beyond the range, f >= 1 would give
   * c <= f * c = p <= MAX_INT, so f = 0 and p = 0 whatever c is, and c can take its least value
   * instead. Rules: c is not the objective, is cut on its high side only (lo[c] within the range),
   * occurs in no constraint but that int_times (with f and p other variables) and rows over c and
   * fixed variables (which its least value satisfies), f has lo[f] >= 0 and stays within the range,
   * and p stays within the range.
   */
  private boolean freeFactor(int c, Integer objectiveId, long[] lo, long[] hi) {
    if (objectiveId != null && objectiveId == c || otherOccurrences.get(c)[0] != 1) {
      return false;
    }
    if (lo[c] < IntDomain.MIN_INT || lo[c] > IntDomain.MAX_INT || hi[c] <= IntDomain.MAX_INT) {
      return false;
    }
    for (int r : rowsOf.get(c)) {
      long[] a = coefficients.get(r);
      int[] x = rowVars.get(r);
      long sum = 0;
      for (int i = 0; i < x.length; i++) {
        if (x[i] != c && lo[x[i]] != hi[x[i]]) {
          return false; // a row over c and a variable that is not fixed
        }
        // c takes its least value, the other variables are fixed
        sum = add(sum, multiply(a[i], lo[x[i]]));
      }
      long b = rhs.get(r)[0];
      if (equal.get(r) ? sum != b : sum > b) {
        return false; // the least value of c does not satisfy the row
      }
    }
    long[] product = null;
    for (long[] f : functions) {
      for (int i = 1; i < f.length && f[0] != ELEMENT_CONST; i++) {
        if (f[i] == c) {
          if (product != null || f[0] != TIMES || i == 1) {
            return false; // c in another function, or the result of one
          }
          product = f;
        }
      }
    }
    if (product == null) {
      return false;
    }
    int p = (int) product[1];
    int factor = (int) (product[2] == c ? product[3] : product[2]);
    if (product[2] == product[3] || p == factor || p == c) {
      return false;
    }
    return lo[factor] >= 0
        && hi[factor] <= IntDomain.MAX_INT
        && lo[p] >= IntDomain.MIN_INT
        && hi[p] <= IntDomain.MAX_INT;
  }

  // whether the rows and functions keep every narrowed variable within JaCoP's range, whatever
  // the objective; computed once, as the solver asks again at every better solution
  private volatile Boolean keptWithinRange;

  private boolean keptWithinRange() {
    Boolean kept = keptWithinRange;
    if (kept == null) {
      long[] lo = Arrays.copyOf(declaredLow, vars.size());
      long[] hi = Arrays.copyOf(declaredHigh, vars.size());
      kept = true;
      if (propagate(lo, hi)) {
        for (int id : clamped) {
          if (!saturated.contains(vars.get(id))
              && (lo[id] < IntDomain.MIN_INT || hi[id] > IntDomain.MAX_INT)) {
            kept = false;
            break;
          }
        }
      }
      keptWithinRange = kept;
    }
    return kept;
  }

  /**
   * Tells whether the rows keep every narrowed variable within JaCoP's range, so that the narrowing
   * cut off no solution at all. A solution whose cut values harmless() moves to the end of the
   * range is another solution, which an enumeration of all solutions misses.
   *
   * @return true if no solution of the model has a value beyond the range.
   */
  public boolean noSolutionCut() {
    long[] lo = Arrays.copyOf(declaredLow, vars.size());
    long[] hi = Arrays.copyOf(declaredHigh, vars.size());
    if (!propagate(lo, hi)) {
      return true;
    }
    for (int id : clamped) {
      if (lo[id] < IntDomain.MIN_INT || hi[id] > IntDomain.MAX_INT) {
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
      boolean[] functionChanged = {false};
      if (!propagateFunctions(lo, hi, functionChanged)
          || !propagateFloatRows(lo, hi, functionChanged)) {
        return false;
      }
      if (!changed && !functionChanged[0]) {
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
  // bounds of x^e for x in xLow..xHigh and a fixed exponent e >= 0; unbounded otherwise
  private static long[] power(long xLow, long xHigh, long eLow, long eHigh) {
    if (eLow != eHigh || eLow < 0 || eLow > 64) {
      return new long[] {-INF, INF};
    }
    long low = 1;
    long high = 1;
    long a = Math.max(Math.abs(xLow), Math.abs(xHigh));
    for (int i = 0; i < eLow; i++) {
      high = multiply(high, a);
    }
    if (eLow == 0) {
      return new long[] {1, 1};
    }
    if (eLow % 2 == 0) {
      // even: from the value nearest zero to the largest magnitude
      long near = xLow <= 0 && xHigh >= 0 ? 0 : Math.min(Math.abs(xLow), Math.abs(xHigh));
      for (int i = 0; i < eLow; i++) {
        low = multiply(low, near);
      }
      return new long[] {low, high};
    }
    // odd: increasing
    low = xLow;
    high = xHigh;
    for (int i = 1; i < eLow; i++) {
      low = multiply(low, xLow);
      high = multiply(high, xHigh);
    }
    return new long[] {low, high};
  }

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
