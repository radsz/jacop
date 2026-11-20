/*
 * FznModel.java
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
 * preservation of specified reasonable legal notices and author attributions
 * in material modified versions of this work.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.xcsp;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * The FlatZinc model the XCSP3 reader builds. It flattens XCSP3 expressions into the FlatZinc
 * built-ins the JaCoP MiniZinc library produces (linear rows, reified comparisons, clauses,
 * int_times, ...), with each common subexpression introduced once, so that the FlatZinc front end
 * of JaCoP sees the model as it would see one flattened by MiniZinc.
 *
 * <p>Parameters (tables) and constraints are written to temporary files as they come; the variables
 * are written at the end, since unary constraints narrow their domains.
 */
final class FznModel {

  /** A literal: a Boolean variable or its negation, or a constant (var null). */
  record Lit(FznVar b, boolean neg) {
    static final Lit TRUE = new Lit(null, false);
    static final Lit FALSE = new Lit(null, true);

    boolean isConstant() {
      return b == null;
    }

    boolean isTrue() {
      return b == null && !neg;
    }

    boolean isFalse() {
      return b == null && neg;
    }

    Lit not() {
      return new Lit(b, !neg);
    }

    static Lit of(boolean v) {
      return v ? TRUE : FALSE;
    }
  }

  // bounds of introduced variables: the FlatZinc front end works on ints
  static final long MIN = org.jacop.core.IntDomain.MIN_INT;
  static final long MAX = org.jacop.core.IntDomain.MAX_INT;

  final List<FznVar> vars = new ArrayList<>();
  private final Map<String, FznVar> names = new HashMap<>();
  private final Map<String, Object> memo = new HashMap<>();
  private int introduced;
  private long constraints;

  private final Path consFile;
  private final Path paramsFile;
  private final Writer cons;
  private final Writer params;

  /** Set when a constraint is false on its own: the model has no solution. */
  boolean inconsistent;

  FznModel(Path dir) {
    try {
      consFile = Files.createTempFile(dir, "xcsp", ".cons");
      paramsFile = Files.createTempFile(dir, "xcsp", ".pars");
      cons =
          new BufferedWriter(Files.newBufferedWriter(consFile, StandardCharsets.US_ASCII), 1 << 16);
      params =
          new BufferedWriter(
              Files.newBufferedWriter(paramsFile, StandardCharsets.US_ASCII), 1 << 16);
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    }
  }

  long constraintCount() {
    return constraints;
  }

  // ------------------------------------------------------------------ variables

  /**
   * A new variable of the model.
   *
   * @param name the wanted name (a FlatZinc identifier); made unique
   * @param dom the domain
   * @param bool true for a FlatZinc Boolean variable
   * @param aux true for an introduced variable
   * @return the variable
   */
  FznVar newVar(String name, Dom dom, boolean bool, boolean aux) {
    String n = name;
    while (names.containsKey(n)) {
      n = n + "_";
    }
    FznVar x = new FznVar(vars.size(), n, bool, dom, aux);
    vars.add(x);
    names.put(n, x);
    return x;
  }

  FznVar aux(long min, long max) {
    min = Math.max(min, MIN);
    max = Math.min(max, MAX);
    if (min > max) {
      inconsistent = true;
      max = min;
    }
    return newVar("X_INTRODUCED_" + introduced++ + "_", Dom.range(min, max), false, true);
  }

  FznVar auxBool() {
    return newVar("X_INTRODUCED_" + introduced++ + "_", Dom.BOOL, true, true);
  }

  /** The 0/1 integer variable of a Boolean variable. */
  FznVar intView(FznVar b) {
    if (!b.bool) {
      return b;
    }
    if (b.intView == null) {
      FznVar i = aux(0, 1);
      i.defined = true;
      b.intView = i;
      i.boolView = b;
      constraint("bool2int(" + b.name + "," + i.name + ")", i);
    }
    return b.intView;
  }

  /** The Boolean variable of a 0/1 integer variable. */
  FznVar boolView(FznVar x) {
    if (x.bool) {
      return x;
    }
    if (x.boolView == null) {
      FznVar b = auxBool();
      b.defined = true;
      x.boolView = b;
      b.intView = x;
      constraint("bool2int(" + b.name + "," + x.name + ")", b);
    }
    return x.boolView;
  }

  /** The variable holding the negation of a Boolean variable. */
  FznVar notVar(FznVar b) {
    if (b.notView == null) {
      FznVar nb = auxBool();
      nb.defined = true;
      b.notView = nb;
      nb.notView = b;
      constraint("bool_not(" + b.name + "," + nb.name + ")", nb);
    }
    return b.notView;
  }

  // ------------------------------------------------------------------ output

  void constraint(String text) {
    constraint(text, null);
  }

  void constraint(String text, FznVar defines) {
    try {
      cons.write("constraint ");
      cons.write(text);
      if (defines != null) {
        cons.write(":: defines_var(");
        cons.write(defines.name);
        cons.write(')');
      }
      cons.write(";\n");
      constraints++;
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    }
  }

  /** A fresh parameter name. */
  String paramName(String prefix) {
    return prefix + "_XCSP_" + introduced++ + "_";
  }

  /** Writes a parameter declaration line (it must end with ';'). */
  Writer params() {
    return params;
  }

  // ------------------------------------------------------------------ memo

  @SuppressWarnings("unchecked")
  <T> T memo(String key) {
    return (T) memo.get(key);
  }

  void memo(String key, Object value) {
    memo.put(key, value);
  }

  // ------------------------------------------------------------------ atoms

  /** The FlatZinc text of a literal as a Boolean argument (a variable or true/false). */
  String boolAtom(Lit l) {
    if (l.isConstant()) {
      return l.isTrue() ? "true" : "false";
    }
    return l.neg() ? notVar(l.b()).name : l.b().name;
  }

  /** The FlatZinc text of a linear expression as an integer argument. */
  String intAtom(Lin l) {
    if (l.isConstant()) {
      return Long.toString(l.c);
    }
    return var(l).name;
  }

  /** The variable equal to a linear expression (introduced when needed). */
  FznVar var(Lin l) {
    if (l.isVariable()) {
      return l.v[0];
    }
    if (l.isConstant()) {
      FznVar x = memo("const:" + l.c);
      if (x == null) {
        x = aux(l.c, l.c);
        memo("const:" + l.c, x);
      }
      return x;
    }
    String key = "lin:" + l.key();
    FznVar x = memo(key);
    if (x == null) {
      x = aux(l.min(), l.max());
      x.defined = true;
      Lin e = l.copy();
      e.add(x, -1);
      linear("eq", e, x);
      memo(key, x);
    }
    return x;
  }

  /** A linear expression of a literal: its 0/1 value. */
  Lin lin(Lit l) {
    if (l.isConstant()) {
      return Lin.constant(l.isTrue() ? 1 : 0);
    }
    FznVar i = intView(l.b());
    if (!l.neg()) {
      return Lin.of(i);
    }
    Lin r = Lin.constant(1);
    r.add(i, -1);
    return r;
  }

  // ------------------------------------------------------------------ linear constraints

  private static String coefs(Lin l) {
    StringBuilder s = new StringBuilder("[");
    for (int i = 0; i < l.n; i++) {
      if (i > 0) {
        s.append(',');
      }
      s.append(l.a[i]);
    }
    return s.append(']').toString();
  }

  private static String names(Lin l) {
    StringBuilder s = new StringBuilder("[");
    for (int i = 0; i < l.n; i++) {
      if (i > 0) {
        s.append(',');
      }
      s.append(l.v[i].name);
    }
    return s.append(']').toString();
  }

  // writes int_lin_<rel>(a, x, -c) for l rel 0, rel in eq, ne, le
  private void linear(String rel, Lin l, FznVar defines) {
    constraint(
        "int_lin_" + rel + "(" + coefs(l) + "," + names(l) + "," + Bounds.mul(-1, l.c) + ")",
        defines);
  }

  /**
   * Posts {@code l op 0}.
   *
   * @param op eq, ne, lt, le, gt or ge
   * @param l the expression
   */
  void post(String op, Lin l) {
    switch (op) {
      case "lt" -> {
        l = l.copy();
        l.c = Bounds.add(l.c, 1);
        op = "le";
      }
      case "gt" -> {
        l = l.negate();
        l.c = Bounds.add(l.c, 1);
        op = "le";
      }
      case "ge" -> {
        l = l.negate();
        op = "le";
      }
      default -> {
        // eq, ne, le
      }
    }
    long lo = l.min();
    long hi = l.max();
    switch (op) {
      case "eq" -> {
        if (lo > 0 || hi < 0) {
          fail();
          return;
        }
        if (lo == 0 && hi == 0) {
          return;
        }
      }
      case "ne" -> {
        if (lo > 0 || hi < 0) {
          return;
        }
        if (lo == 0 && hi == 0) {
          fail();
          return;
        }
      }
      case "le" -> {
        if (hi <= 0) {
          return;
        }
        if (lo > 0) {
          fail();
          return;
        }
      }
      default -> throw new XcspException("unknown relation " + op);
    }
    if (l.n == 1) {
      unary(op, l.a[0], l.v[0], l.c);
      return;
    }
    if (l.n == 2 && l.c == 0 && l.a[0] == -l.a[1] && Math.abs(l.a[0]) == 1) {
      FznVar x = l.a[0] == 1 ? l.v[0] : l.v[1];
      FznVar y = l.a[0] == 1 ? l.v[1] : l.v[0];
      // x - y op 0
      constraint("int_" + op + "(" + x.name + "," + y.name + ")");
      return;
    }
    linear(op, normalize(op, l), null);
  }

  /**
   * Posts {@code l = 0} as the definition of x (FlatZinc {@code defines_var}), as MiniZinc marks a
   * variable that an equation defines, when x is a model variable not defined yet with a unit
   * coefficient in a row of at least two other terms; otherwise as {@link #post(String, Lin)}.
   *
   * @param l the row
   * @param x the variable
   */
  void postDefining(Lin l, FznVar x) {
    int at = -1;
    for (int i = 0; i < l.n; i++) {
      if (l.v[i] == x) {
        at = i;
      }
    }
    if (at < 0
        || x.defined
        || x.bool
        || l.n < 3
        || Math.abs(l.a[at]) != 1
        || l.min() > 0
        || l.max() < 0) {
      post("eq", l);
      return;
    }
    x.defined = true;
    linear("eq", l, x);
  }

  // divides a row by the gcd of its coefficients
  private static Lin normalize(String op, Lin l) {
    long g = l.gcd();
    if (g == 1) {
      return l;
    }
    if (op.equals("le")) {
      Lin r = new Lin();
      for (int i = 0; i < l.n; i++) {
        r.add(l.v[i], l.a[i] / g);
      }
      // sum a x <= -c  ->  sum (a/g) x <= floor(-c/g)
      r.c = -Math.floorDiv(-l.c, g);
      return r;
    }
    if (l.c % g != 0) {
      return l; // eq: no solution, ne: always true; left to the solver
    }
    Lin r = new Lin();
    for (int i = 0; i < l.n; i++) {
      r.add(l.v[i], l.a[i] / g);
    }
    r.c = l.c / g;
    return r;
  }

  // a * x + c op 0 on the domain of x
  private void unary(String op, long a, FznVar x, long c) {
    Dom d = x.dom;
    switch (op) {
      case "eq" -> {
        if (c % a != 0) {
          fail();
          return;
        }
        d = d.intersect(Dom.value(-c / a));
      }
      case "ne" -> {
        if (c % a == 0) {
          d = d.minus(-c / a);
        }
      }
      default -> {
        if (a > 0) {
          d = d.intersect(Long.MIN_VALUE, Math.floorDiv(-c, a));
        } else {
          d = d.intersect(Math.ceilDiv(c, -a), Long.MAX_VALUE);
        }
      }
    }
    restrict(x, d);
  }

  /** Narrows the domain of a variable. */
  void restrict(FznVar x, Dom d) {
    Dom n = x.dom.intersect(d);
    if (n.isEmpty()) {
      fail();
      return;
    }
    x.dom = n;
    if (x.boolView != null) {
      x.boolView.dom = x.boolView.dom.intersect(n);
    }
    if (x.bool && x.intView != null) {
      x.intView.dom = x.intView.dom.intersect(n);
    }
  }

  void fail() {
    inconsistent = true;
  }

  /**
   * The literal of {@code l op 0}.
   *
   * @param op eq, ne, lt, le, gt or ge
   * @param l the expression
   * @return the literal
   */
  Lit lit(String op, Lin l) {
    switch (op) {
      case "ne":
        return lit("eq", l).not();
      case "gt":
        return lit("le", l).not();
      case "lt":
        l = l.copy();
        l.c = Bounds.add(l.c, 1);
        op = "le";
        break;
      case "ge":
        l = l.negate();
        op = "le";
        break;
      default:
        break;
    }
    long lo = l.min();
    long hi = l.max();
    if (op.equals("eq")) {
      if (lo > 0 || hi < 0) {
        return Lit.FALSE;
      }
      if (lo == 0 && hi == 0) {
        return Lit.TRUE;
      }
    } else {
      if (hi <= 0) {
        return Lit.TRUE;
      }
      if (lo > 0) {
        return Lit.FALSE;
      }
    }
    l = normalize(op, l);
    if (l.n == 1) {
      return unaryLit(op, l.a[0], l.v[0], l.c);
    }
    String key = "lit:" + op + ":" + l.key();
    Lit known = memo(key);
    if (known != null) {
      return known;
    }
    FznVar r = auxBool();
    r.defined = true;
    if (l.n == 2 && l.c == 0 && l.a[0] == -l.a[1] && Math.abs(l.a[0]) == 1) {
      FznVar x = l.a[0] == 1 ? l.v[0] : l.v[1];
      FznVar y = l.a[0] == 1 ? l.v[1] : l.v[0];
      constraint("int_" + op + "_reif(" + x.name + "," + y.name + "," + r.name + ")", r);
    } else {
      constraint(
          "int_lin_"
              + op
              + "_reif("
              + coefs(l)
              + ","
              + names(l)
              + ","
              + Bounds.mul(-1, l.c)
              + ","
              + r.name
              + ")",
          r);
    }
    Lit result = new Lit(r, false);
    memo(key, result);
    return result;
  }

  // a * x + c op 0, op eq or le
  private Lit unaryLit(String op, long a, FznVar x, long c) {
    Dom d = x.dom;
    if (op.equals("eq")) {
      if (c % a != 0) {
        return Lit.FALSE;
      }
      return valueLit(x, -c / a);
    }
    // x <= k or x >= k
    long k;
    boolean upper = a > 0;
    if (upper) {
      k = Math.floorDiv(-c, a);
      if (d.max() <= k) {
        return Lit.TRUE;
      }
      if (d.min() > k) {
        return Lit.FALSE;
      }
    } else {
      k = Math.ceilDiv(c, -a);
      if (d.min() >= k) {
        return Lit.TRUE;
      }
      if (d.max() < k) {
        return Lit.FALSE;
      }
    }
    if (x.boolView != null || d.isZeroOne()) {
      // 0/1: x <= 0 is not x, x >= 1 is x
      Lit b = new Lit(boolView(x), false);
      return upper ? b.not() : b;
    }
    String key = "le:" + x.id + ":" + (upper ? "u" : "l") + k;
    Lit known = memo(key);
    if (known != null) {
      return known;
    }
    FznVar r = auxBool();
    r.defined = true;
    if (upper) {
      constraint("int_le_reif(" + x.name + "," + k + "," + r.name + ")", r);
    } else {
      constraint("int_le_reif(" + k + "," + x.name + "," + r.name + ")", r);
    }
    Lit result = new Lit(r, false);
    memo(key, result);
    return result;
  }

  /** The literal of {@code x = v}. */
  Lit valueLit(FznVar x, long v) {
    if (!x.dom.contains(v)) {
      return Lit.FALSE;
    }
    if (x.dom.isSingleton()) {
      return Lit.TRUE;
    }
    if (x.dom.isZeroOne()) {
      Lit b = new Lit(boolView(x), false);
      return v == 1 ? b : b.not();
    }
    String key = "eqv:" + x.id + ":" + v;
    Lit known = memo(key);
    if (known != null) {
      return known;
    }
    FznVar r = auxBool();
    r.defined = true;
    constraint("int_eq_reif(" + x.name + "," + v + "," + r.name + ")", r);
    Lit result = new Lit(r, false);
    memo(key, result);
    return result;
  }

  /** The literal of {@code x in d}. */
  Lit inLit(Lin l, Dom d) {
    if (l.isConstant()) {
      return Lit.of(d.contains(l.c));
    }
    FznVar x = var(l);
    Dom both = x.dom.intersect(d);
    if (both.isEmpty()) {
      return Lit.FALSE;
    }
    if (both.equals(x.dom)) {
      return Lit.TRUE;
    }
    if (both.isSingleton()) {
      return valueLit(x, both.min());
    }
    Dom out = x.dom.minus(d);
    if (out.isSingleton()) {
      return valueLit(x, out.min()).not();
    }
    if (both.isInterval()) {
      if (both.min() == x.min()) {
        return lit("le", linMinus(x, both.max()));
      }
      if (both.max() == x.max()) {
        return lit("ge", linMinus(x, both.min()));
      }
    }
    String key = "in:" + x.id + ":" + both;
    Lit known = memo(key);
    if (known != null) {
      return known;
    }
    FznVar r = auxBool();
    r.defined = true;
    constraint("set_in_reif(" + x.name + "," + both.toFzn() + "," + r.name + ")", r);
    Lit result = new Lit(r, false);
    memo(key, result);
    return result;
  }

  private static Lin linMinus(FznVar x, long k) {
    Lin l = Lin.of(x);
    l.c = -k;
    return l;
  }

  // ------------------------------------------------------------------ Boolean constraints

  /** Posts a literal as true. */
  void post(Lit l) {
    if (l.isConstant()) {
      if (l.isFalse()) {
        fail();
      }
      return;
    }
    FznVar b = l.b();
    restrict(b, Dom.value(l.neg() ? 0 : 1));
  }

  /** Posts the disjunction of literals. */
  void clause(List<Lit> lits) {
    List<String> pos = new ArrayList<>();
    List<String> neg = new ArrayList<>();
    Lit single = null;
    int count = 0;
    for (Lit l : lits) {
      if (l.isTrue()) {
        return;
      }
      if (l.isFalse()) {
        continue;
      }
      if (l.b().dom.isSingleton()) {
        boolean value = (l.b().dom.min() == 1) != l.neg();
        if (value) {
          return;
        }
        continue;
      }
      count++;
      single = l;
      (l.neg() ? neg : pos).add(l.b().name);
    }
    if (count == 0) {
      fail();
      return;
    }
    if (count == 1) {
      post(single);
      return;
    }
    constraint("bool_clause(" + list(pos) + "," + list(neg) + ")");
  }

  static String list(List<String> items) {
    return "[" + String.join(",", items) + "]";
  }

  /** The literal of the disjunction. */
  Lit or(List<Lit> lits) {
    List<Lit> keep = new ArrayList<>();
    for (Lit l : lits) {
      if (l.isTrue()) {
        return Lit.TRUE;
      }
      if (!l.isFalse()) {
        keep.add(l);
      }
    }
    if (keep.isEmpty()) {
      return Lit.FALSE;
    }
    if (keep.size() == 1) {
      return keep.get(0);
    }
    List<String> pos = new ArrayList<>();
    List<String> neg = new ArrayList<>();
    StringBuilder key = new StringBuilder("or:");
    for (Lit l : keep) {
      (l.neg() ? neg : pos).add(l.b().name);
      key.append(l.neg() ? '-' : '+').append(l.b().id).append(',');
    }
    Lit known = memo(key.toString());
    if (known != null) {
      return known;
    }
    FznVar r = auxBool();
    r.defined = true;
    if (neg.isEmpty()) {
      constraint("array_bool_or(" + list(pos) + "," + r.name + ")", r);
    } else {
      constraint("bool_clause_reif(" + list(pos) + "," + list(neg) + "," + r.name + ")", r);
    }
    Lit result = new Lit(r, false);
    memo(key.toString(), result);
    return result;
  }

  /** The literal of the conjunction. */
  Lit and(List<Lit> lits) {
    List<Lit> negated = new ArrayList<>(lits.size());
    boolean allPositive = true;
    for (Lit l : lits) {
      negated.add(l.not());
      allPositive &= l.isConstant() || !l.neg();
    }
    if (allPositive && lits.size() > 1) {
      List<String> pos = new ArrayList<>();
      StringBuilder key = new StringBuilder("and:");
      for (Lit l : lits) {
        if (l.isFalse()) {
          return Lit.FALSE;
        }
        if (!l.isTrue()) {
          pos.add(l.b().name);
          key.append(l.b().id).append(',');
        }
      }
      if (pos.isEmpty()) {
        return Lit.TRUE;
      }
      if (pos.size() > 1) {
        Lit known = memo(key.toString());
        if (known != null) {
          return known;
        }
        FznVar r = auxBool();
        r.defined = true;
        constraint("array_bool_and(" + list(pos) + "," + r.name + ")", r);
        Lit result = new Lit(r, false);
        memo(key.toString(), result);
        return result;
      }
    }
    return or(negated).not();
  }

  /** The literal of a = b. */
  Lit iff(Lit a, Lit b) {
    if (a.isConstant()) {
      return a.isTrue() ? b : b.not();
    }
    if (b.isConstant()) {
      return b.isTrue() ? a : a.not();
    }
    boolean flip = a.neg() != b.neg();
    if (a.b() == b.b()) {
      return Lit.of(!flip);
    }
    FznVar x = a.b().id < b.b().id ? a.b() : b.b();
    FznVar y = x == a.b() ? b.b() : a.b();
    String key = "iff:" + x.id + ":" + y.id;
    Lit known = memo(key);
    if (known == null) {
      FznVar r = auxBool();
      r.defined = true;
      constraint("bool_eq_reif(" + x.name + "," + y.name + "," + r.name + ")", r);
      known = new Lit(r, false);
      memo(key, known);
    }
    return flip ? known.not() : known;
  }

  /** Posts a = b. */
  void postIff(Lit a, Lit b) {
    if (a.isConstant()) {
      post(a.isTrue() ? b : b.not());
      return;
    }
    if (b.isConstant()) {
      post(b.isTrue() ? a : a.not());
      return;
    }
    boolean flip = a.neg() != b.neg();
    if (a.b() == b.b()) {
      if (flip) {
        fail();
      }
      return;
    }
    constraint("bool_" + (flip ? "not" : "eq") + "(" + a.b().name + "," + b.b().name + ")");
  }

  /** The literal of a xor b. */
  Lit xor(Lit a, Lit b) {
    return iff(a, b).not();
  }

  // ------------------------------------------------------------------ writing

  /**
   * Writes the whole FlatZinc model.
   *
   * @param out the FlatZinc file
   * @param outputs the output annotations of the XCSP3 variables, one declaration per line
   * @param solve the solve item
   * @throws IOException when a file cannot be written or read
   */
  void write(Path out, List<String> outputs, String solve) throws IOException {
    cons.close();
    params.close();
    try (Writer w =
        new BufferedWriter(Files.newBufferedWriter(out, StandardCharsets.US_ASCII), 1 << 16)) {
      try (var in = Files.newBufferedReader(paramsFile, StandardCharsets.US_ASCII)) {
        in.transferTo(w);
      }
      for (FznVar x : vars) {
        declare(w, x);
      }
      for (String o : outputs) {
        w.write(o);
        w.write('\n');
      }
      if (inconsistent) {
        // the instance has no solution: a model the front end refutes at once
        w.write("constraint bool_eq(true,false);\n");
      }
      w.flush();
      try (var in = Files.newBufferedReader(consFile, StandardCharsets.US_ASCII)) {
        in.transferTo(w);
      }
      w.write(solve);
      w.write('\n');
    } finally {
      Files.deleteIfExists(consFile);
      Files.deleteIfExists(paramsFile);
    }
  }

  /** Names of output variables, set by the reader. */
  final java.util.Set<FznVar> outputVars = new java.util.HashSet<>();

  private void declare(Writer w, FznVar x) throws IOException {
    Dom d = x.dom;
    if (d.isEmpty()) {
      inconsistent = true;
      d = Dom.value(0);
    }
    if (x.bool) {
      w.write("var bool: ");
      w.write(x.name);
      annotations(w, x);
      if (d.isSingleton()) {
        w.write(d.min() == 1 ? " = true" : " = false");
      }
      w.write(";\n");
      return;
    }
    w.write("var ");
    if (d.isInterval()) {
      w.write(Long.toString(d.min()));
      w.write("..");
      w.write(Long.toString(d.max()));
    } else {
      w.write(d.toFzn());
    }
    w.write(": ");
    w.write(x.name);
    annotations(w, x);
    w.write(";\n");
  }

  private void annotations(Writer w, FznVar x) throws IOException {
    if (outputVars.contains(x)) {
      w.write(":: output_var");
    }
    if (x.introduced) {
      w.write(":: var_is_introduced");
    }
    if (x.defined) {
      w.write(":: is_defined_var");
    }
  }
}
