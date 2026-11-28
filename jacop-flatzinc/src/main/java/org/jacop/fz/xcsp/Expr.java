/*
 * Expr.java
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

/**
 * An XCSP3 expression in functional notation ({@code add(x[0],mul(2,y))}): an integer, a variable,
 * a parameter {@code %i} of a group or slide template, or an operator applied to arguments. {@code
 * set(...)} and ranges {@code a..b} appear as the second argument of {@code in} and {@code notin}.
 */
final class Expr {

  enum Kind {
    INT,
    VAR,
    PAR,
    OP,
    RANGE
  }

  /** The parameter index of {@code %...}: every argument after the highest numbered one. */
  static final int REST = -1;

  final Kind kind;
  final long value;
  final long value2;
  final FznVar var;
  final String op;
  final Expr[] args;

  private Expr(Kind kind, long value, long value2, FznVar var, String op, Expr[] args) {
    this.kind = kind;
    this.value = value;
    this.value2 = value2;
    this.var = var;
    this.op = op;
    this.args = args;
  }

  static Expr of(long v) {
    return new Expr(Kind.INT, v, 0, null, null, null);
  }

  static Expr of(FznVar x) {
    return new Expr(Kind.VAR, 0, 0, x, null, null);
  }

  static Expr par(int i) {
    return new Expr(Kind.PAR, i, 0, null, null, null);
  }

  static Expr range(long a, long b) {
    return new Expr(Kind.RANGE, a, b, null, null, null);
  }

  static Expr op(String op, Expr... args) {
    return new Expr(Kind.OP, 0, 0, null, op, args);
  }

  boolean isInt() {
    return kind == Kind.INT;
  }

  boolean isVar() {
    return kind == Kind.VAR;
  }

  boolean isOp(String name) {
    return kind == Kind.OP && op.equals(name);
  }

  /** Whether the expression holds a parameter of a template. */
  boolean hasParameters() {
    if (kind == Kind.PAR) {
      return true;
    }
    if (kind == Kind.OP) {
      for (Expr a : args) {
        if (a.hasParameters()) {
          return true;
        }
      }
    }
    return false;
  }

  /** The highest parameter number, or -1. */
  int maxParameter() {
    if (kind == Kind.PAR) {
      return (int) value;
    }
    int m = -1;
    if (kind == Kind.OP) {
      for (Expr a : args) {
        m = Math.max(m, a.maxParameter());
      }
    }
    return m;
  }

  /**
   * The expression with each parameter replaced by its argument.
   *
   * @param actual the arguments of the template, %0 first
   * @param restFrom the first argument %... stands for
   * @return the bound expression
   */
  Expr bind(List<Expr> actual, int restFrom) {
    switch (kind) {
      case PAR:
        if (value == REST) {
          throw new XcspException("%... outside the arguments of an operator");
        }
        if (value >= actual.size()) {
          throw new XcspException("parameter %" + value + " has no argument");
        }
        return actual.get((int) value);
      case OP:
        List<Expr> out = new ArrayList<>(args.length);
        boolean changed = false;
        for (Expr a : args) {
          if (a.kind == Kind.PAR && a.value == REST) {
            for (int i = restFrom; i < actual.size(); i++) {
              out.add(actual.get(i));
            }
            changed = true;
          } else {
            Expr b = a.bind(actual, restFrom);
            changed |= b != a;
            out.add(b);
          }
        }
        return changed ? op(op, out.toArray(new Expr[0])) : this;
      default:
        return this;
    }
  }

  @Override
  public String toString() {
    switch (kind) {
      case INT:
        return Long.toString(value);
      case VAR:
        return var.name;
      case PAR:
        return value == REST ? "%..." : "%" + value;
      case RANGE:
        return value + ".." + value2;
      default:
        StringBuilder s = new StringBuilder(op).append('(');
        for (int i = 0; i < args.length; i++) {
          if (i > 0) {
            s.append(',');
          }
          s.append(args[i]);
        }
        return s.append(')').toString();
    }
  }

  /** Resolves the variable names of an expression. */
  interface Names {
    /**
     * The variable of an id such as {@code x[2][3]}.
     *
     * @param id the id
     * @return the variable
     */
    FznVar variable(String id);
  }

  /** A parser of the functional notation. */
  static final class Parser {
    private final CharSequence s;
    private final Names names;
    private int p;

    Parser(CharSequence s, Names names) {
      this.s = s;
      this.names = names;
    }

    /**
     * Parses one whole expression.
     *
     * @param text the expression
     * @param names the variables
     * @return the expression
     */
    static Expr parse(CharSequence text, Names names) {
      Parser parser = new Parser(text, names);
      Expr e = parser.expr();
      parser.skip();
      if (parser.p != text.length()) {
        throw new XcspException("unexpected text after expression: " + text);
      }
      return e;
    }

    private void skip() {
      while (p < s.length() && Character.isWhitespace(s.charAt(p))) {
        p++;
      }
    }

    Expr expr() {
      skip();
      if (p >= s.length()) {
        throw new XcspException("expression expected");
      }
      char c = s.charAt(p);
      if (c == '%') {
        p++;
        if (s.length() >= p + 3
            && s.charAt(p) == '.'
            && s.charAt(p + 1) == '.'
            && s.charAt(p + 2) == '.') {
          p += 3;
          return par(REST);
        }
        int start = p;
        while (p < s.length() && Character.isDigit(s.charAt(p))) {
          p++;
        }
        return par(Integer.parseInt(s, start, p, 10));
      }
      if (c == '-' || c == '+' || Character.isDigit(c)) {
        long v = number();
        skip();
        if (p + 1 < s.length() && s.charAt(p) == '.' && s.charAt(p + 1) == '.') {
          p += 2;
          skip();
          return range(v, number());
        }
        return of(v);
      }
      int start = p;
      while (p < s.length()) {
        char d = s.charAt(p);
        if (Character.isLetterOrDigit(d) || d == '_' || d == '[' || d == ']') {
          p++;
        } else {
          break;
        }
      }
      if (start == p) {
        throw new XcspException("unexpected character '" + c + "' in expression " + s);
      }
      String word = s.subSequence(start, p).toString();
      skip();
      if (p < s.length() && s.charAt(p) == '(') {
        p++;
        List<Expr> args = new ArrayList<>(3);
        skip();
        if (p < s.length() && s.charAt(p) == ')') {
          p++;
          return op(word, new Expr[0]);
        }
        while (true) {
          args.add(expr());
          skip();
          if (p >= s.length()) {
            throw new XcspException("missing ) in " + s);
          }
          char d = s.charAt(p++);
          if (d == ')') {
            break;
          }
          if (d != ',') {
            throw new XcspException("expected , or ) in " + s);
          }
        }
        return op(word, args.toArray(new Expr[0]));
      }
      if (word.equals("true")) {
        return of(1);
      }
      if (word.equals("false")) {
        return of(0);
      }
      return of(names.variable(word));
    }

    private long number() {
      skip();
      int start = p;
      if (p < s.length() && (s.charAt(p) == '-' || s.charAt(p) == '+')) {
        p++;
      }
      while (p < s.length() && Character.isDigit(s.charAt(p))) {
        p++;
      }
      String t = s.subSequence(start, p).toString();
      if (t.equals("+inf")) {
        return Long.MAX_VALUE;
      }
      try {
        return Long.parseLong(t.startsWith("+") ? t.substring(1) : t);
      } catch (NumberFormatException e) {
        throw new XcspException("bad integer '" + t + "' in " + s);
      }
    }
  }
}
