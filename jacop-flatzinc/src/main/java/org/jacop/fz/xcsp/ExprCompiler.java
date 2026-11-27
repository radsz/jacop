/*
 * ExprCompiler.java
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

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import org.jacop.fz.xcsp.FznModel.Lit;

/**
 * Flattens XCSP3 expressions into the {@link FznModel}: integer expressions into linear forms over
 * (introduced) variables, Boolean expressions into literals, and top-level constraints into
 * FlatZinc constraints. Semantics as in the XCSP3 specification: {@code div} and {@code mod}
 * truncate as in Java (as MiniZinc's), integers are true when not 0, Booleans are 0/1 integers.
 */
final class ExprCompiler {

  private static final Set<String> BOOLEAN_OPS =
      Set.of(
          "eq", "ne", "lt", "le", "gt", "ge", "and", "or", "not", "imp", "iff", "xor", "in",
          "notin");

  private static final Set<String> COMPARISONS = Set.of("eq", "ne", "lt", "le", "gt", "ge");

  private final FznModel m;

  ExprCompiler(FznModel m) {
    this.m = m;
  }

  boolean isBoolean(Expr e) {
    return switch (e.kind) {
      case VAR -> e.var.bool;
      case OP ->
          BOOLEAN_OPS.contains(e.op)
              || e.op.equals("if") && isBoolean(e.args[1]) && isBoolean(e.args[2]);
      default -> false;
    };
  }

  // ------------------------------------------------------------------ integers

  /** The linear form of an integer expression. */
  Lin lin(Expr e) {
    switch (e.kind) {
      case INT:
        return Lin.constant(e.value);
      case VAR:
        return Lin.of(m.intView(e.var));
      case PAR:
      case RANGE:
        throw new XcspException("unexpected " + e + " in an integer expression");
      default:
        break;
    }
    Expr[] a = e.args;
    switch (e.op) {
      case "add":
        {
          Lin s = new Lin();
          for (Expr x : a) {
            s.add(lin(x), 1);
          }
          return s;
        }
      case "sub":
        {
          arity(e, 2);
          Lin s = lin(a[0]).copy();
          s.add(lin(a[1]), -1);
          return s;
        }
      case "neg":
        arity(e, 1);
        return lin(a[0]).negate();
      case "mul":
        return product(e);
      case "sqr":
        {
          arity(e, 1);
          Lin x = lin(a[0]);
          if (x.isConstant()) {
            return Lin.constant(Math.multiplyExact(x.c, x.c));
          }
          return Lin.of(times(x, x, null));
        }
      default:
        break;
    }
    if (BOOLEAN_OPS.contains(e.op) || e.op.equals("if") && isBoolean(e)) {
      return m.lin(lit(e));
    }
    return Lin.of(op(e, null));
  }

  private static void arity(Expr e, int n) {
    if (e.args.length != n) {
      throw new XcspException(e.op + " expects " + n + " arguments: " + e);
    }
  }

  private Lin product(Expr e) {
    long scale = 1;
    List<Lin> factors = new ArrayList<>();
    for (Expr x : e.args) {
      Lin l = lin(x);
      if (l.isConstant()) {
        scale = Math.multiplyExact(scale, l.c);
      } else {
        factors.add(l);
      }
    }
    if (scale == 0 || factors.isEmpty()) {
      return Lin.constant(scale);
    }
    Lin p = factors.get(0);
    for (int i = 1; i < factors.size(); i++) {
      p = Lin.of(times(p, factors.get(i), null));
    }
    Lin r = new Lin();
    r.add(p, scale);
    return r;
  }

  /** The variable of an integer expression. */
  FznVar var(Expr e) {
    if (e.kind == Expr.Kind.VAR) {
      return m.intView(e.var);
    }
    return m.var(lin(e));
  }

  /** The FlatZinc integer argument of an expression: a constant or a variable name. */
  String atom(Expr e) {
    return m.intAtom(lin(e));
  }

  private FznVar define(String key, String call, long min, long max, Object goal) {
    if (goal instanceof Long c) {
      // the result is a constant: written in place of the result (as MiniZinc does)
      if (c < min || c > max) {
        m.fail();
        return null;
      }
      m.constraint(call.replace("@R", Long.toString(c)));
      return null;
    }
    FznVar target = (FznVar) goal;
    if (target == null) {
      FznVar known = m.memo(key);
      if (known != null) {
        return known;
      }
    }
    FznVar r = target;
    if (r == null) {
      r = m.aux(min, max);
      r.defined = true;
      m.memo(key, r);
    } else {
      m.restrict(r, Dom.range(min, max));
    }
    m.constraint(call.replace("@R", r.name), r.introduced ? r : null);
    return r;
  }

  // x * y
  FznVar times(Lin x, Lin y, Object target) {
    String ax = m.intAtom(x);
    String ay = m.intAtom(y);
    long[] c = {
      Bounds.mul(x.min(), y.min()),
      Bounds.mul(x.min(), y.max()),
      Bounds.mul(x.max(), y.min()),
      Bounds.mul(x.max(), y.max())
    };
    long lo = Math.min(Math.min(c[0], c[1]), Math.min(c[2], c[3]));
    long hi = Math.max(Math.max(c[0], c[1]), Math.max(c[2], c[3]));
    boolean xFirst = ax.compareTo(ay) <= 0;
    String a1 = xFirst ? ax : ay;
    String a2 = xFirst ? ay : ax;
    return define("times:" + a1 + "," + a2, "int_times(" + a1 + "," + a2 + ",@R)", lo, hi, target);
  }

  /**
   * The variable of a non-linear integer operation.
   *
   * @param e the operation
   * @param target the variable that must hold the result, or null for a new one
   * @return the variable
   */
  FznVar op(Expr e, Object target) {
    Expr[] a = e.args;
    switch (e.op) {
      case "mul":
      case "sqr":
        return result(lin(e), target);
      case "div":
      case "mod":
        {
          arity(e, 2);
          Lin x = lin(a[0]);
          Lin y = lin(a[1]);
          long[] b = e.op.equals("div") ? divBounds(x, y) : modBounds(x, y);
          String ax = m.intAtom(x);
          String ay = m.intAtom(y);
          String name = e.op.equals("div") ? "int_div" : "int_mod";
          return define(
              name + ":" + ax + "," + ay, name + "(" + ax + "," + ay + ",@R)", b[0], b[1], target);
        }
      case "abs":
      case "dist":
        {
          Lin x;
          if (e.op.equals("abs")) {
            arity(e, 1);
            x = lin(a[0]);
          } else {
            arity(e, 2);
            x = diff(lin(a[0]), lin(a[1]));
          }
          if (x.min() >= 0) {
            return result(x, target);
          }
          if (x.max() <= 0) {
            return result(x.negate(), target);
          }
          String ax = m.intAtom(x);
          long hi = Math.max(Bounds.abs(x.min()), Bounds.abs(x.max()));
          return define("abs:" + ax, "int_abs(" + ax + ",@R)", 0, hi, target);
        }
      case "pow":
        {
          arity(e, 2);
          Lin x = lin(a[0]);
          Lin y = lin(a[1]);
          if (y.isConstant() && y.c == 0) {
            return result(Lin.constant(1), target);
          }
          if (y.isConstant() && y.c == 1) {
            return result(x, target);
          }
          if (y.isConstant() && y.c == 2) {
            return target == null ? times(x, x, null) : times(x, x, target);
          }
          long m1 = Math.max(Bounds.abs(x.min()), Bounds.abs(x.max()));
          long e1 = Math.max(0, y.max());
          // x ^ 0 = 1, also for x = 0
          long hi = Math.max(Bounds.pow(m1, Math.min(e1, 64)), y.min() <= 0 ? 1 : 0);
          long lo = x.min() >= 0 ? 0 : -hi;
          String ax = m.intAtom(x);
          String ay = m.intAtom(y);
          return define(
              "pow:" + ax + "," + ay, "int_pow(" + ax + "," + ay + ",@R)", lo, hi, target);
        }
      case "min":
      case "max":
        return minMax(e.op.equals("min"), a, target);
      case "if":
        {
          arity(e, 3);
          Lit c = lit(a[0]);
          if (c.isConstant()) {
            return result(lin(c.isTrue() ? a[1] : a[2]), target);
          }
          Lin x = lin(a[1]);
          Lin y = lin(a[2]);
          String ac = m.boolAtom(c);
          String ax = m.intAtom(x);
          String ay = m.intAtom(y);
          return define(
              "ite:" + ac + "," + ax + "," + ay,
              "jacop_if_then_else_int([" + ac + ",true],[" + ax + "," + ay + "],@R)",
              Math.min(x.min(), y.min()),
              Math.max(x.max(), y.max()),
              target);
        }
      default:
        throw new XcspException("unsupported integer operator " + e.op + " in " + e);
    }
  }

  // the variable of a linear expression, or the target posted equal to it
  private FznVar result(Lin l, Object target) {
    if (target == null) {
      return m.var(l);
    }
    if (target instanceof Long c) {
      m.post("eq", diff(Lin.constant(c), l));
      return null;
    }
    m.post("eq", diff(Lin.of((FznVar) target), l));
    return (FznVar) target;
  }

  static Lin diff(Lin x, Lin y) {
    Lin d = x.copy();
    d.add(y, -1);
    return d;
  }

  private FznVar minMax(boolean min, Expr[] a, Object target) {
    List<String> atoms = new ArrayList<>();
    long lo = Long.MAX_VALUE;
    long hi = Long.MIN_VALUE;
    long lo2 = Long.MAX_VALUE;
    long hi2 = Long.MIN_VALUE;
    for (Expr x : a) {
      Lin l = lin(x);
      atoms.add(m.intAtom(l));
      lo = Math.min(lo, l.min());
      hi = Math.max(hi, l.max());
      lo2 = Math.min(lo2, l.max());
      hi2 = Math.max(hi2, l.min());
    }
    if (atoms.size() == 1) {
      return result(lin(a[0]), target);
    }
    // min lies in [min of mins, min of maxes], max in [max of mins, max of maxes]
    long rlo = min ? lo : hi2;
    long rhi = min ? lo2 : hi;
    String name = min ? "min" : "max";
    if (atoms.size() == 2) {
      return define(
          name + ":" + atoms,
          "int_" + name + "(" + atoms.get(0) + "," + atoms.get(1) + ",@R)",
          rlo,
          rhi,
          target);
    }
    return define(
        name + ":" + atoms,
        (min ? "jacop_minimum(@R," : "jacop_maximum(@R,") + FznModel.list(atoms) + ")",
        rlo,
        rhi,
        target);
  }

  private static long[] divBounds(Lin x, Lin y) {
    if (y.isConstant() && y.c != 0) {
      long k = y.c;
      long a = x.min() / k;
      long b = x.max() / k;
      return new long[] {Math.min(a, b), Math.max(a, b)};
    }
    long mx = Math.max(Bounds.abs(x.min()), Bounds.abs(x.max()));
    if (x.min() >= 0 && y.min() >= 0) {
      return new long[] {0, mx};
    }
    return new long[] {-mx, mx};
  }

  private static long[] modBounds(Lin x, Lin y) {
    long my = Math.max(Bounds.abs(y.min()), Bounds.abs(y.max())) - 1;
    long mx = Math.max(Bounds.abs(x.min()), Bounds.abs(x.max()));
    long hi = Math.max(0, Math.min(my, mx));
    long lo = x.min() >= 0 ? 0 : -hi;
    long up = x.max() <= 0 ? 0 : hi;
    return new long[] {lo, up};
  }

  // ------------------------------------------------------------------ Booleans

  /**
   * The 0/1 form of e where only e being true matters (a term of a sum bounded below with a
   * positive coefficient): an integer comparison is half reified. Other expressions as {@link
   * #lin(Expr)}.
   */
  Lin halfLin(Expr e) {
    if (e.kind == Expr.Kind.OP
        && e.args.length == 2
        && !isBoolean(e.args[0])
        && !isBoolean(e.args[1])) {
      switch (e.op) {
        case "eq", "ne", "lt", "le", "gt", "ge" -> {
          return m.lin(clauseLit(e));
        }
        default -> {
          // other operators as lin
        }
      }
    }
    return lin(e);
  }

  // the literals of a clause posted at the top level
  private List<Lit> clauseLits(Expr[] a) {
    List<Lit> r = new ArrayList<>(a.length);
    for (Expr x : a) {
      r.add(clauseLit(x));
    }
    return r;
  }

  /**
   * The literal of e where it occurs only positively in a clause posted at the top level: an
   * integer comparison is half reified, as MiniZinc does.
   */
  private Lit clauseLit(Expr e) {
    if (e.kind == Expr.Kind.OP
        && e.args.length == 2
        && !isBoolean(e.args[0])
        && !isBoolean(e.args[1])) {
      switch (e.op) {
        case "eq", "ne", "lt", "le", "gt", "ge" -> {
          return m.halfLit(e.op, diff(lin(e.args[0]), lin(e.args[1])));
        }
        default -> {
          // other operators are fully reified
        }
      }
    }
    return lit(e);
  }

  /** The literal of a Boolean expression (an integer one is true when not 0). */
  Lit lit(Expr e) {
    switch (e.kind) {
      case INT:
        return Lit.of(e.value != 0);
      case VAR:
        if (e.var.bool) {
          return new Lit(e.var, false);
        }
        return m.lit("ne", Lin.of(e.var));
      case OP:
        break;
      default:
        throw new XcspException("unexpected " + e + " in a Boolean expression");
    }
    Expr[] a = e.args;
    switch (e.op) {
      case "eq":
        if (a.length == 2 && isBoolean(a[0]) && isBoolean(a[1])) {
          return m.iff(lit(a[0]), lit(a[1]));
        }
        if (a.length > 2) {
          List<Lit> all = new ArrayList<>();
          for (int i = 1; i < a.length; i++) {
            all.add(lit(Expr.op("eq", a[0], a[i])));
          }
          return m.and(all);
        }
        return m.lit("eq", diff(lin(a[0]), lin(a[1])));
      case "ne":
        if (a.length == 2 && isBoolean(a[0]) && isBoolean(a[1])) {
          return m.iff(lit(a[0]), lit(a[1])).not();
        }
        if (a.length > 2) {
          return lit(Expr.op("eq", a)).not();
        }
        return m.lit("ne", diff(lin(a[0]), lin(a[1])));
      case "lt":
      case "le":
      case "gt":
      case "ge":
        {
          if (a.length < 2) {
            throw new XcspException(e.op + " needs two arguments: " + e);
          }
          List<Lit> all = new ArrayList<>();
          for (int i = 0; i + 1 < a.length; i++) {
            all.add(m.lit(e.op, diff(lin(a[i]), lin(a[i + 1]))));
          }
          return all.size() == 1 ? all.get(0) : m.and(all);
        }
      case "not":
        arity(e, 1);
        return lit(a[0]).not();
      case "and":
        return m.and(lits(a));
      case "or":
        return m.or(lits(a));
      case "imp":
        arity(e, 2);
        return m.or(List.of(lit(a[0]).not(), lit(a[1])));
      case "iff":
        {
          if (a.length == 2) {
            return m.iff(lit(a[0]), lit(a[1]));
          }
          List<Lit> all = new ArrayList<>();
          Lit first = lit(a[0]);
          for (int i = 1; i < a.length; i++) {
            all.add(m.iff(first, lit(a[i])));
          }
          return m.and(all);
        }
      case "xor":
        {
          Lit r = lit(a[0]);
          for (int i = 1; i < a.length; i++) {
            r = m.xor(r, lit(a[i]));
          }
          return r;
        }
      case "in":
      case "notin":
        {
          arity(e, 2);
          Lit r = in(a[0], a[1]);
          return e.op.equals("in") ? r : r.not();
        }
      case "if":
        {
          arity(e, 3);
          Lit c = lit(a[0]);
          Lit x = lit(a[1]);
          Lit y = lit(a[2]);
          return m.or(List.of(m.and(List.of(c, x)), m.and(List.of(c.not(), y))));
        }
      default:
        return m.lit("ne", lin(e));
    }
  }

  private List<Lit> lits(Expr[] a) {
    List<Lit> r = new ArrayList<>(a.length);
    for (Expr x : a) {
      r.add(lit(x));
    }
    return r;
  }

  // the domain of the constant items of a set, or null when an item is not a constant
  private static Dom constantSet(Expr s) {
    if (s.kind == Expr.Kind.RANGE) {
      return Dom.range(s.value, s.value2);
    }
    if (!s.isOp("set")) {
      return null;
    }
    Dom.Builder b = new Dom.Builder();
    long[] v = new long[s.args.length];
    int n = 0;
    for (Expr x : s.args) {
      if (x.kind == Expr.Kind.INT) {
        v[n++] = x.value;
      } else if (x.kind != Expr.Kind.RANGE) {
        return null;
      }
    }
    Dom d = Dom.of(v, n);
    for (Expr x : s.args) {
      if (x.kind == Expr.Kind.RANGE) {
        d = d.union(Dom.range(x.value, x.value2));
      }
    }
    return d.union(b.build());
  }

  private Lit in(Expr x, Expr s) {
    Dom d = constantSet(s);
    if (d != null) {
      return m.inLit(lin(x), d);
    }
    if (!s.isOp("set")) {
      throw new XcspException("in expects a set: " + s);
    }
    List<Lit> any = new ArrayList<>();
    for (Expr v : s.args) {
      any.add(lit(Expr.op("eq", x, v)));
    }
    return m.or(any);
  }

  // ------------------------------------------------------------------ constraints

  /** Posts a Boolean expression as a constraint. */
  void post(Expr e) {
    switch (e.kind) {
      case INT:
        if (e.value == 0) {
          m.fail();
        }
        return;
      case VAR:
        m.post(lit(e));
        return;
      case OP:
        break;
      default:
        throw new XcspException("unexpected " + e + " as a constraint");
    }
    Expr[] a = e.args;
    switch (e.op) {
      case "and":
        for (Expr x : a) {
          post(x);
        }
        return;
      case "or":
        m.clause(clauseLits(a));
        return;
      case "imp":
        {
          arity(e, 2);
          Lit c = lit(a[0]).not();
          if (a[1].isOp("and")) {
            for (Expr x : a[1].args) {
              m.clause(List.of(c, clauseLit(x)));
            }
            return;
          }
          List<Lit> lits = new ArrayList<>();
          lits.add(c);
          if (a[1].isOp("or")) {
            lits.addAll(clauseLits(a[1].args));
          } else {
            lits.add(clauseLit(a[1]));
          }
          m.clause(lits);
          return;
        }
      case "not":
        arity(e, 1);
        m.post(lit(a[0]).not());
        return;
      case "iff":
        if (a.length == 2) {
          m.postIff(lit(a[0]), lit(a[1]));
          return;
        }
        Lit first = lit(a[0]);
        for (int i = 1; i < a.length; i++) {
          m.postIff(first, lit(a[i]));
        }
        return;
      case "xor":
        if (a.length == 2) {
          m.postIff(lit(a[0]), lit(a[1]).not());
          return;
        }
        List<String> xs = new ArrayList<>();
        for (Lit l : lits(a)) {
          xs.add(m.boolAtom(l));
        }
        m.constraint("array_bool_xor(" + FznModel.list(xs) + ")");
        return;
      case "in":
      case "notin":
        {
          arity(e, 2);
          Dom d = constantSet(a[1]);
          if (d != null && a[0].kind == Expr.Kind.VAR) {
            FznVar x = a[0].var;
            m.restrict(x, e.op.equals("in") ? d : x.dom.minus(d));
            return;
          }
          m.post(lit(e));
          return;
        }
      case "eq":
        if (a.length == 2) {
          postEq(a[0], a[1]);
          return;
        }
        for (int i = 1; i < a.length; i++) {
          postEq(a[0], a[i]);
        }
        return;
      default:
        if (COMPARISONS.contains(e.op)) {
          if (a.length == 2 && (e.op.equals("ne")) && isBoolean(a[0]) && isBoolean(a[1])) {
            m.postIff(lit(a[0]), lit(a[1]).not());
            return;
          }
          if (a.length == 2) {
            m.post(e.op, diff(lin(a[0]), lin(a[1])));
            return;
          }
          if (e.op.equals("ne")) {
            m.post(lit(e));
            return;
          }
          for (int i = 0; i + 1 < a.length; i++) {
            m.post(e.op, diff(lin(a[i]), lin(a[i + 1])));
          }
          return;
        }
        m.post(lit(e));
    }
  }

  private static final Set<String> DEFINING =
      Set.of("mul", "div", "mod", "abs", "dist", "pow", "min", "max", "if", "sqr");

  private void postEq(Expr x, Expr y) {
    if (isBoolean(x) && isBoolean(y)) {
      m.postIff(lit(x), lit(y));
      return;
    }
    if (definesInto(x, y) || definesInto(y, x)) {
      return;
    }
    Lin d = diff(lin(x), lin(y));
    if (x.kind == Expr.Kind.VAR && !x.var.bool) {
      m.postDefining(d, x.var);
    } else if (y.kind == Expr.Kind.VAR && !y.var.bool) {
      m.postDefining(d, y.var);
    } else {
      m.post("eq", d);
    }
  }

  // x = op(...) with x an integer variable: the operation is posted with x as its result
  private boolean definesInto(Expr x, Expr y) {
    if (y.kind != Expr.Kind.OP || !DEFINING.contains(y.op)) {
      return false;
    }
    Object target;
    if (x.kind == Expr.Kind.INT) {
      target = x.value;
    } else if (x.kind == Expr.Kind.VAR && !x.var.bool) {
      target = x.var;
    } else {
      return false;
    }
    if (y.op.equals("sqr")) {
      Lin l = lin(y.args[0]);
      if (l.isConstant()) {
        return false;
      }
      times(l, l, target);
      return true;
    }
    if (y.op.equals("mul")) {
      List<Lin> factors = new ArrayList<>();
      for (Expr f : y.args) {
        Lin l = lin(f);
        if (l.isConstant()) {
          return false;
        }
        factors.add(l);
      }
      if (factors.size() != 2) {
        return false;
      }
      times(factors.get(0), factors.get(1), target);
      return true;
    }
    op(y, target);
    return true;
  }
}
