/*
 * FznBuilder.java
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

package org.jacop.decomposition;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.decomposition.FznModel.Decl;
import org.jacop.decomposition.FznModel.Expr;
import org.jacop.decomposition.FznModel.Ident;
import org.jacop.decomposition.FznModel.SetLit;

/**
 * Writes FlatZinc built-in constraints and auxiliary variables for a decomposition. Constants are
 * folded the way the MiniZinc compiler folds them, so that a decomposition never posts a built-in
 * whose arguments are all fixed.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class FznBuilder {

  /** Bound used for variables without a declared domain. */
  static final long UNBOUNDED = 1L << 40;

  /** A constant or a variable, of type int or bool. */
  record Term(String var, long value, boolean bool) {

    boolean isConst() {
      return var == null;
    }

    boolean isTrue() {
      return isConst() && value != 0;
    }

    boolean isFalse() {
      return isConst() && value == 0;
    }

    String text() {
      if (var != null) {
        return var;
      }
      return bool ? Boolean.toString(value != 0) : Long.toString(value);
    }
  }

  static final Term TRUE = new Term(null, 1, true);
  static final Term FALSE = new Term(null, 0, true);

  final FznModel model;
  final List<String> declarations = new ArrayList<>();
  final List<String> constraints = new ArrayList<>();
  private final Map<String, long[]> bounds = new LinkedHashMap<>();
  private final String prefix;
  private int counter;

  FznBuilder(FznModel model, String prefix) {
    this.model = model;
    this.prefix = prefix;
  }

  static Term constant(long v) {
    return new Term(null, v, false);
  }

  static Term bool(boolean v) {
    return v ? TRUE : FALSE;
  }

  // ---------------------------------------------------------------------------------------------
  // Arguments.

  Term term(Expr e) {
    boolean isBool = model.isBool(e);
    Long c = model.constant(e);
    if (c != null) {
      return new Term(null, c, isBool);
    }
    Expr r = model.resolveParam(e);
    if (r instanceof Ident(String name)) {
      Decl d = model.decls.get(name);
      if (d != null && d.isVar && !d.isArray) {
        return new Term(name, 0, isBool);
      }
    }
    throw new UnsupportedOperationException("not a scalar int or bool: " + FznModel.render(e));
  }

  List<Term> array(Expr e) {
    List<Term> result = new ArrayList<>();
    for (Expr element : model.elements(e)) {
      result.add(term(element));
    }
    return result;
  }

  long[] intArray(Expr e) {
    List<Expr> elements = model.elements(e);
    long[] result = new long[elements.size()];
    for (int i = 0; i < result.length; i++) {
      Long c = model.constant(elements.get(i));
      if (c == null) {
        throw new UnsupportedOperationException("expected a fixed array");
      }
      result[i] = c;
    }
    return result;
  }

  long intArg(Expr e) {
    Long c = model.constant(e);
    if (c == null) {
      throw new UnsupportedOperationException("expected a parameter: " + FznModel.render(e));
    }
    return c;
  }

  long lb(Term t) {
    if (t.isConst()) {
      return t.value;
    }
    long[] b = bounds.get(t.var);
    if (b != null) {
      return b[0];
    }
    SetLit d = model.domain(new Ident(t.var));
    return d == null ? -UNBOUNDED : d.min();
  }

  long ub(Term t) {
    if (t.isConst()) {
      return t.value;
    }
    long[] b = bounds.get(t.var);
    if (b != null) {
      return b[1];
    }
    SetLit d = model.domain(new Ident(t.var));
    return d == null ? UNBOUNDED : d.max();
  }

  boolean bounded(Term t) {
    return lb(t) > -UNBOUNDED && ub(t) < UNBOUNDED;
  }

  // ---------------------------------------------------------------------------------------------
  // Variables.

  private String fresh() {
    String name;
    do {
      name = prefix + counter++;
    } while (model.decls.containsKey(name));
    return name;
  }

  Term newInt(long lo, long hi) {
    String name = fresh();
    if (lo <= -UNBOUNDED || hi >= UNBOUNDED) {
      declarations.add("var int: " + name + " :: var_is_introduced");
      bounds.put(name, new long[] {Math.max(lo, -UNBOUNDED), Math.min(hi, UNBOUNDED)});
    } else {
      declarations.add("var " + lo + ".." + hi + ": " + name + " :: var_is_introduced");
      bounds.put(name, new long[] {lo, hi});
    }
    return new Term(name, 0, false);
  }

  Term newBool() {
    String name = fresh();
    declarations.add("var bool: " + name + " :: var_is_introduced");
    bounds.put(name, new long[] {0, 1});
    return new Term(name, 0, true);
  }

  // ---------------------------------------------------------------------------------------------
  // Posting.

  void post(String name, Object... args) {
    StringBuilder b = new StringBuilder(name).append('(');
    for (int i = 0; i < args.length; i++) {
      if (i > 0) {
        b.append(',');
      }
      b.append(render(args[i]));
    }
    constraints.add(b.append(')').toString());
  }

  private static String render(Object arg) {
    return switch (arg) {
      case Term t -> t.text();
      case Long l -> Long.toString(l);
      case Integer i -> Integer.toString(i);
      case String s -> s;
      case SetLit s -> FznModel.renderSet(s);
      case Expr e -> FznModel.render(e);
      case long[] a -> {
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < a.length; i++) {
          b.append(i > 0 ? "," : "").append(a[i]);
        }
        yield b.append(']').toString();
      }
      case List<?> list -> {
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < list.size(); i++) {
          b.append(i > 0 ? "," : "").append(render(list.get(i)));
        }
        yield b.append(']').toString();
      }
      default -> throw new IllegalArgumentException("cannot render " + arg);
    };
  }

  /** Posts a constraint that can never hold. */
  void fail() {
    post("bool_eq", TRUE, FALSE);
  }

  // ---------------------------------------------------------------------------------------------
  // Linear expressions: sum(coefs[i] * xs[i]) rel rhs, rel in {eq, ne, le}.

  private record Linear(long[] coefs, List<Term> vars, long rhs) {}

  private static Linear normalize(long[] coefs, List<Term> xs, long rhs) {
    Map<String, Long> merged = new LinkedHashMap<>();
    for (int i = 0; i < coefs.length; i++) {
      Term t = xs.get(i);
      if (t.bool && !t.isConst()) {
        throw new IllegalArgumentException("bool variable in a linear constraint: " + t.var);
      }
      if (t.isConst()) {
        rhs -= coefs[i] * t.value;
      } else {
        merged.merge(t.var, coefs[i], Long::sum);
      }
    }
    merged.values().removeIf(c -> c == 0);
    long[] c = new long[merged.size()];
    List<Term> v = new ArrayList<>();
    int k = 0;
    for (Map.Entry<String, Long> e : merged.entrySet()) {
      c[k++] = e.getValue();
      v.add(new Term(e.getKey(), 0, false));
    }
    return new Linear(c, v, rhs);
  }

  private static boolean holds(long lhs, String rel, long rhs) {
    return switch (rel) {
      case "eq" -> lhs == rhs;
      case "ne" -> lhs != rhs;
      case "le" -> lhs <= rhs;
      default -> throw new IllegalArgumentException(rel);
    };
  }

  /** Bounds of sum(coefs * vars). */
  private long[] range(Linear l) {
    long lo = 0;
    long hi = 0;
    for (int i = 0; i < l.coefs.length; i++) {
      Term t = l.vars.get(i);
      if (!bounded(t)) {
        return null;
      }
      long a = l.coefs[i] * lb(t);
      long b = l.coefs[i] * ub(t);
      lo += Math.min(a, b);
      hi += Math.max(a, b);
    }
    return new long[] {lo, hi};
  }

  /** Posts sum(coefs * xs) rel rhs at the root. */
  void linear(long[] coefs, List<Term> xs, String rel, long rhs) {
    Linear l = normalize(coefs, xs, rhs);
    if (l.coefs.length == 0) {
      if (!holds(0, rel, l.rhs)) {
        fail();
      }
      return;
    }
    post("int_lin_" + rel, l.coefs, l.vars, l.rhs);
  }

  /** Returns a Boolean equivalent to sum(coefs * xs) rel rhs. */
  Term linearReif(long[] coefs, List<Term> xs, String rel, long rhs) {
    Linear l = normalize(coefs, xs, rhs);
    if (l.coefs.length == 0) {
      return bool(holds(0, rel, l.rhs));
    }
    long[] r = range(l);
    if (r != null) {
      switch (rel) {
        case "le" -> {
          if (r[1] <= l.rhs) {
            return TRUE;
          }
          if (r[0] > l.rhs) {
            return FALSE;
          }
        }
        case "eq" -> {
          if (r[0] > l.rhs || r[1] < l.rhs) {
            return FALSE;
          }
          if (r[0] == r[1]) {
            return TRUE;
          }
        }
        case "ne" -> {
          if (r[0] > l.rhs || r[1] < l.rhs) {
            return TRUE;
          }
          if (r[0] == r[1]) {
            return FALSE;
          }
        }
        default -> throw new IllegalArgumentException(rel);
      }
    }
    Term b = newBool();
    if (l.coefs.length == 1 && l.coefs[0] == 1) {
      post("int_" + rel + "_reif", l.vars.get(0), constant(l.rhs), b);
    } else if (l.coefs.length == 2 && l.coefs[0] == 1 && l.coefs[1] == -1 && l.rhs == 0) {
      post("int_" + rel + "_reif", l.vars.get(0), l.vars.get(1), b);
    } else {
      post("int_lin_" + rel + "_reif", l.coefs, l.vars, l.rhs, b);
    }
    return b;
  }

  // Comparisons of two int terms.

  Term eqReif(Term a, Term b) {
    if (a.bool || b.bool) {
      return boolEqReif(a, b);
    }
    return linearReif(new long[] {1, -1}, List.of(a, b), "eq", 0);
  }

  Term neReif(Term a, Term b) {
    return not(eqReif(a, b));
  }

  Term leReif(Term a, Term b) {
    if (a.bool || b.bool) {
      return or(List.of(not(a), b));
    }
    return linearReif(new long[] {1, -1}, List.of(a, b), "le", 0);
  }

  Term ltReif(Term a, Term b) {
    if (a.bool || b.bool) {
      return and(List.of(not(a), b));
    }
    return linearReif(new long[] {1, -1}, List.of(a, b), "le", -1);
  }

  /** Posts a = b at the root. */
  void eq(Term a, Term b) {
    if (a.isConst() && b.isConst()) {
      if (a.value != b.value) {
        fail();
      }
      return;
    }
    post(a.bool || b.bool ? "bool_eq" : "int_eq", a, b);
  }

  void le(Term a, Term b) {
    if (a.isConst() && b.isConst()) {
      if (a.value > b.value) {
        fail();
      }
      return;
    }
    post(a.bool || b.bool ? "bool_le" : "int_le", a, b);
  }

  void lt(Term a, Term b) {
    if (a.isConst() && b.isConst()) {
      if (a.value >= b.value) {
        fail();
      }
      return;
    }
    post(a.bool || b.bool ? "bool_lt" : "int_lt", a, b);
  }

  void ne(Term a, Term b) {
    if (a.isConst() && b.isConst()) {
      if (a.value == b.value) {
        fail();
      }
      return;
    }
    if (a.bool || b.bool) {
      post("bool_not", a, b);
    } else {
      post("int_ne", a, b);
    }
  }

  /** Posts a Boolean term as true at the root. */
  void require(Term b) {
    if (b.isConst()) {
      if (b.value == 0) {
        fail();
      }
      return;
    }
    post("bool_eq", b, TRUE);
  }

  // Boolean connectives.

  Term not(Term a) {
    if (a.isConst()) {
      return bool(a.value == 0);
    }
    Term r = newBool();
    post("bool_not", a, r);
    return r;
  }

  Term boolEqReif(Term a, Term b) {
    if (a.isConst() && b.isConst()) {
      return bool(a.value == b.value);
    }
    if (a.isConst()) {
      return a.value != 0 ? b : not(b);
    }
    if (b.isConst()) {
      return b.value != 0 ? a : not(a);
    }
    Term r = newBool();
    post("bool_eq_reif", a, b, r);
    return r;
  }

  Term and(List<Term> xs) {
    List<Term> rest = new ArrayList<>();
    for (Term t : xs) {
      if (t.isFalse()) {
        return FALSE;
      }
      if (!t.isConst()) {
        rest.add(t);
      }
    }
    if (rest.isEmpty()) {
      return TRUE;
    }
    if (rest.size() == 1) {
      return rest.get(0);
    }
    Term r = newBool();
    post("array_bool_and", rest, r);
    return r;
  }

  Term or(List<Term> xs) {
    List<Term> rest = new ArrayList<>();
    for (Term t : xs) {
      if (t.isTrue()) {
        return TRUE;
      }
      if (!t.isConst()) {
        rest.add(t);
      }
    }
    if (rest.isEmpty()) {
      return FALSE;
    }
    if (rest.size() == 1) {
      return rest.get(0);
    }
    Term r = newBool();
    post("array_bool_or", rest, r);
    return r;
  }

  /** Posts the clause (or pos) \/ (or not neg) at the root. */
  void clause(List<Term> pos, List<Term> neg) {
    List<Term> p = new ArrayList<>();
    List<Term> n = new ArrayList<>();
    for (Term t : pos) {
      if (t.isTrue()) {
        return;
      }
      if (!t.isConst()) {
        p.add(t);
      }
    }
    for (Term t : neg) {
      if (t.isFalse()) {
        return;
      }
      if (!t.isConst()) {
        n.add(t);
      }
    }
    if (p.isEmpty() && n.isEmpty()) {
      fail();
    } else if (p.size() == 1 && n.isEmpty()) {
      require(p.get(0));
    } else if (n.size() == 1 && p.isEmpty()) {
      post("bool_eq", n.get(0), FALSE);
    } else {
      post("bool_clause", p, n);
    }
  }

  /** Posts b1 = b2 for two Booleans at the root. */
  void boolEq(Term a, Term b) {
    if (a.isConst() && !b.isConst()) {
      post("bool_eq", b, a);
    } else {
      eq(a, b);
    }
  }

  Term bool2int(Term b) {
    if (b.isConst()) {
      return constant(b.value);
    }
    Term r = newInt(0, 1);
    post("bool2int", b, r);
    return r;
  }

  /** Returns a variable (or constant) equal to sum(coefs * xs) + c. */
  Term sum(long[] coefs, List<Term> xs, long c) {
    Linear l = normalize(coefs, xs, -c);
    if (l.coefs.length == 0) {
      return constant(-l.rhs);
    }
    if (l.coefs.length == 1 && l.coefs[0] == 1 && l.rhs == 0) {
      return l.vars.get(0);
    }
    long[] r = range(l);
    Term s = r == null ? newInt(-UNBOUNDED, UNBOUNDED) : newInt(r[0] - l.rhs, r[1] - l.rhs);
    long[] coefs2 = new long[l.coefs.length + 1];
    System.arraycopy(l.coefs, 0, coefs2, 0, l.coefs.length);
    coefs2[l.coefs.length] = -1;
    List<Term> vars = new ArrayList<>(l.vars);
    vars.add(s);
    post("int_lin_eq", coefs2, vars, l.rhs);
    return s;
  }

  /** Returns a * b. */
  Term times(Term a, Term b) {
    if (a.isConst()) {
      return sum(new long[] {a.value}, List.of(b), 0);
    }
    if (b.isConst()) {
      return sum(new long[] {b.value}, List.of(a), 0);
    }
    long[] p = {lb(a) * lb(b), lb(a) * ub(b), ub(a) * lb(b), ub(a) * ub(b)};
    long lo = Math.min(Math.min(p[0], p[1]), Math.min(p[2], p[3]));
    long hi = Math.max(Math.max(p[0], p[1]), Math.max(p[2], p[3]));
    Term r = bounded(a) && bounded(b) ? newInt(lo, hi) : newInt(-UNBOUNDED, UNBOUNDED);
    post("int_times", a, b, r);
    return r;
  }

  /** Posts x in s at the root. */
  void in(Term x, SetLit s) {
    if (x.isConst()) {
      if (!s.contains(x.value)) {
        fail();
      }
      return;
    }
    if (bounded(x) && s.ranges().length == 2 && lb(x) >= s.min() && ub(x) <= s.max()) {
      return;
    }
    post("set_in", x, s);
  }

  Term inReif(Term x, SetLit s) {
    if (x.isConst()) {
      return bool(s.contains(x.value));
    }
    if (s.isEmpty() || bounded(x) && (ub(x) < s.min() || lb(x) > s.max())) {
      return FALSE;
    }
    if (s.ranges().length == 2 && bounded(x) && lb(x) >= s.min() && ub(x) <= s.max()) {
      return TRUE;
    }
    Term b = newBool();
    post("set_in_reif", x, s, b);
    return b;
  }

  /** Returns the FlatZinc text of the new variable declarations, one item per line. */
  String declarationText() {
    StringBuilder b = new StringBuilder();
    for (String d : declarations) {
      b.append(d).append(";\n");
    }
    return b.toString();
  }

  String constraintText() {
    StringBuilder b = new StringBuilder();
    for (String c : constraints) {
      b.append("constraint ").append(c).append(";\n");
    }
    return b.toString();
  }
}
