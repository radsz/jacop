/*
 * FznModel.java
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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * A small FlatZinc reader that keeps every item's text, so that a model can be written back with
 * some constraints replaced. It resolves parameters, variable domains and arrays well enough for
 * the decompositions in {@link StdDecompositions}; anything it does not need stays as raw text.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class FznModel {

  /** Kind of a top-level FlatZinc item. */
  enum ItemKind {
    PREDICATE,
    PARAMETER,
    VARIABLE,
    CONSTRAINT,
    SOLVE
  }

  /** One top-level item: its text (without the closing semicolon) and its parsed form. */
  static final class Item {
    final ItemKind kind;
    final String text;
    Decl decl;
    Constraint constraint;

    Item(ItemKind kind, String text) {
      this.kind = kind;
      this.text = text;
    }
  }

  /** Base type of a declaration. */
  enum BaseType {
    INT,
    BOOL,
    FLOAT,
    SET
  }

  /** A parameter or variable declaration. */
  static final class Decl {
    String name;
    boolean isVar;
    boolean isArray;
    BaseType type;

    /** Integer domain of a variable (or of array elements), null when unbounded or not int. */
    SetLit domain;

    /** Value of a parameter, or the assigned value of a variable (alias or array literal). */
    Expr value;

    String annotations = "";
  }

  /** A constraint item. */
  record Constraint(int index, String name, List<Expr> args, String annotations) {}

  /** Expression of the FlatZinc grammar. */
  sealed interface Expr permits IntLit, BoolLit, FloatLit, StrLit, SetLit, Ident, ArrayLit, Call {}

  record IntLit(long value) implements Expr {}

  record BoolLit(boolean value) implements Expr {}

  record FloatLit(String text) implements Expr {}

  record StrLit(String text) implements Expr {}

  /**
   * A set literal as sorted, disjoint, non-adjacent intervals {@code [lo0, hi0, lo1, hi1, ...]}.
   */
  record SetLit(long[] ranges) implements Expr {

    static SetLit of(long[] sortedDistinctValues) {
      List<Long> ranges = new ArrayList<>();
      for (int i = 0; i < sortedDistinctValues.length; i++) {
        long lo = sortedDistinctValues[i];
        while (i + 1 < sortedDistinctValues.length
            && sortedDistinctValues[i + 1] == sortedDistinctValues[i] + 1) {
          i++;
        }
        ranges.add(lo);
        ranges.add(sortedDistinctValues[i]);
      }
      return new SetLit(ranges.stream().mapToLong(Long::longValue).toArray());
    }

    static SetLit range(long lo, long hi) {
      return lo > hi ? new SetLit(new long[0]) : new SetLit(new long[] {lo, hi});
    }

    boolean isEmpty() {
      return ranges.length == 0;
    }

    long min() {
      return ranges[0];
    }

    long max() {
      return ranges[ranges.length - 1];
    }

    long size() {
      long size = 0;
      for (int i = 0; i < ranges.length; i += 2) {
        size += ranges[i + 1] - ranges[i] + 1;
      }
      return size;
    }

    boolean contains(long v) {
      for (int i = 0; i < ranges.length; i += 2) {
        if (v >= ranges[i] && v <= ranges[i + 1]) {
          return true;
        }
      }
      return false;
    }

    /** All values; only for small sets. */
    long[] values() {
      if (size() > 10_000_000) {
        throw new UnsupportedOperationException("set too large to enumerate");
      }
      long[] values = new long[(int) size()];
      int k = 0;
      for (int i = 0; i < ranges.length; i += 2) {
        for (long v = ranges[i]; v <= ranges[i + 1]; v++) {
          values[k++] = v;
        }
      }
      return values;
    }
  }

  record Ident(String name) implements Expr {}

  record ArrayLit(List<Expr> elements) implements Expr {}

  /** An annotation call or an array access {@code a[i]} (name "[]"). */
  record Call(String name, List<Expr> args) implements Expr {}

  final List<Item> items = new ArrayList<>();
  final Map<String, Decl> decls = new HashMap<>();
  final List<Constraint> constraints = new ArrayList<>();
  Item solve;

  /** Kind of the solve item: satisfy, minimize or maximize. */
  String solveKind;

  /** Objective expression of an optimisation problem, otherwise null. */
  Expr objective;

  static FznModel parse(String text) {
    FznModel model = new FznModel();
    for (String itemText : splitItems(text)) {
      model.addItem(itemText);
    }
    return model;
  }

  private void addItem(String text) {
    Lexer lexer = new Lexer(text);
    String first = lexer.peek();
    if ("predicate".equals(first)) {
      items.add(new Item(ItemKind.PREDICATE, text));
    } else if ("constraint".equals(first)) {
      lexer.next();
      Expr call = lexer.expr();
      String annotations = lexer.rest();
      Call c = (Call) call;
      Constraint constraint = new Constraint(constraints.size(), c.name(), c.args(), annotations);
      constraints.add(constraint);
      Item item = new Item(ItemKind.CONSTRAINT, text);
      item.constraint = constraint;
      items.add(item);
    } else if ("solve".equals(first)) {
      lexer.next();
      StringBuilder annotations = new StringBuilder();
      while ("::".equals(lexer.peek())) {
        lexer.next();
        annotations.append(" :: ").append(render(lexer.expr()));
      }
      solveKind = lexer.next();
      if (!"satisfy".equals(solveKind)) {
        objective = lexer.expr();
      }
      solve = new Item(ItemKind.SOLVE, text);
      solve.decl = new Decl();
      solve.decl.annotations = annotations.toString();
      items.add(solve);
    } else {
      Decl decl = lexer.declaration();
      Item item = new Item(decl.isVar ? ItemKind.VARIABLE : ItemKind.PARAMETER, text);
      item.decl = decl;
      decls.put(decl.name, decl);
      items.add(item);
    }
  }

  /** Splits FlatZinc text into items at top-level semicolons, dropping comments. */
  static List<String> splitItems(String text) {
    List<String> result = new ArrayList<>();
    StringBuilder current = new StringBuilder();
    int depth = 0;
    boolean inString = false;
    for (int i = 0; i < text.length(); i++) {
      char ch = text.charAt(i);
      if (inString) {
        current.append(ch);
        if (ch == '\\' && i + 1 < text.length()) {
          current.append(text.charAt(++i));
        } else if (ch == '"') {
          inString = false;
        }
        continue;
      }
      switch (ch) {
        case '%' -> {
          while (i < text.length() && text.charAt(i) != '\n') {
            i++;
          }
          current.append(' ');
        }
        case '"' -> {
          inString = true;
          current.append(ch);
        }
        case '(', '[', '{' -> {
          depth++;
          current.append(ch);
        }
        case ')', ']', '}' -> {
          depth--;
          current.append(ch);
        }
        case ';' -> {
          if (depth == 0) {
            String item = current.toString().strip();
            if (!item.isEmpty()) {
              result.add(item);
            }
            current.setLength(0);
          } else {
            current.append(ch);
          }
        }
        default -> current.append(ch);
      }
    }
    if (!current.toString().isBlank()) {
      result.add(current.toString().strip());
    }
    return result;
  }

  // ---------------------------------------------------------------------------------------------
  // Resolution helpers used by the decompositions.

  /** Resolves an identifier to its parameter value, following aliases; other expressions as is. */
  Expr resolveParam(Expr e) {
    while (e instanceof Ident(String name)) {
      Decl d = decls.get(name);
      if (d == null || d.isVar || d.value == null) {
        return e;
      }
      e = d.value;
    }
    return e;
  }

  /** Elements of an array argument (a literal or the name of an array parameter or variable). */
  List<Expr> elements(Expr e) {
    if (e instanceof Ident(String name)) {
      Decl d = decls.get(name);
      if (d == null || !d.isArray || d.value == null) {
        throw new UnsupportedOperationException("not an array: " + name);
      }
      e = d.value;
    }
    if (e instanceof ArrayLit(List<Expr> elements)) {
      return elements;
    }
    throw new UnsupportedOperationException("not an array: " + render(e));
  }

  /** Returns the constant value of an int or bool expression, or null for a variable. */
  Long constant(Expr e) {
    Expr r = resolveParam(e);
    if (r instanceof IntLit(long value)) {
      return value;
    }
    if (r instanceof BoolLit(boolean value)) {
      return value ? 1L : 0L;
    }
    if (r instanceof Ident(String name)) {
      Decl d = decls.get(name);
      if (d != null && d.isVar && d.value != null && !d.isArray) {
        return constant(d.value);
      }
      if (d != null && d.isVar && d.domain != null && d.domain.size() == 1) {
        return d.domain.min();
      }
    }
    return null;
  }

  /** The integer domain of a variable or constant, or null when unbounded. */
  SetLit domain(Expr e) {
    Long c = constant(e);
    if (c != null) {
      return SetLit.range(c, c);
    }
    Expr r = resolveParam(e);
    if (r instanceof Ident(String name)) {
      Decl d = decls.get(name);
      if (d == null) {
        throw new UnsupportedOperationException("unknown identifier " + name);
      }
      if (d.type == BaseType.BOOL) {
        return SetLit.range(0, 1);
      }
      if (d.domain != null) {
        return d.domain;
      }
      if (d.value instanceof Ident) {
        return domain(d.value);
      }
      return null;
    }
    throw new UnsupportedOperationException("not an int expression " + render(e));
  }

  /** Whether an expression is of type bool. */
  boolean isBool(Expr e) {
    Expr r = resolveParam(e);
    if (r instanceof BoolLit) {
      return true;
    }
    if (r instanceof Ident(String name)) {
      Decl d = decls.get(name);
      return d != null && d.type == BaseType.BOOL;
    }
    return false;
  }

  /** A set argument. */
  SetLit set(Expr e) {
    Expr r = resolveParam(e);
    if (r instanceof SetLit s) {
      return s;
    }
    throw new UnsupportedOperationException("not a set " + render(e));
  }

  static String render(Expr e) {
    return switch (e) {
      case IntLit(long value) -> Long.toString(value);
      case BoolLit(boolean value) -> Boolean.toString(value);
      case FloatLit(String text) -> text;
      case StrLit(String text) -> text;
      case SetLit s -> renderSet(s);
      case Ident(String name) -> name;
      case ArrayLit(List<Expr> elements) -> {
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < elements.size(); i++) {
          if (i > 0) {
            b.append(',');
          }
          b.append(render(elements.get(i)));
        }
        yield b.append(']').toString();
      }
      case Call(String name, List<Expr> args) -> {
        if ("[]".equals(name)) {
          yield render(args.get(0)) + "[" + render(args.get(1)) + "]";
        }
        StringBuilder b = new StringBuilder(name).append('(');
        for (int i = 0; i < args.size(); i++) {
          if (i > 0) {
            b.append(',');
          }
          b.append(render(args.get(i)));
        }
        yield b.append(')').toString();
      }
    };
  }

  static String renderSet(SetLit s) {
    if (s.isEmpty()) {
      return "{}";
    }
    if (s.ranges().length == 2) {
      return s.min() + ".." + s.max();
    }
    StringBuilder b = new StringBuilder("{");
    long[] values = s.values();
    for (int i = 0; i < values.length; i++) {
      if (i > 0) {
        b.append(',');
      }
      b.append(values[i]);
    }
    return b.append('}').toString();
  }

  // ---------------------------------------------------------------------------------------------

  /** Tokenizer and recursive-descent parser for one item. */
  static final class Lexer {
    private final List<String> tokens = new ArrayList<>();
    private final List<Integer> offsets = new ArrayList<>();
    private final String text;
    private int pos;

    Lexer(String text) {
      this.text = text;
      int i = 0;
      while (i < text.length()) {
        char ch = text.charAt(i);
        if (Character.isWhitespace(ch)) {
          i++;
          continue;
        }
        int start = i;
        if (ch == '"') {
          i++;
          while (i < text.length() && text.charAt(i) != '"') {
            i += text.charAt(i) == '\\' ? 2 : 1;
          }
          i++;
        } else if (text.startsWith("::", i) || text.startsWith("..", i)) {
          i += 2;
        } else if (Character.isLetter(ch) || ch == '_') {
          while (i < text.length()
              && (Character.isLetterOrDigit(text.charAt(i)) || text.charAt(i) == '_')) {
            i++;
          }
        } else if (Character.isDigit(ch)
            || ch == '-' && i + 1 < text.length() && Character.isDigit(text.charAt(i + 1))) {
          i++;
          while (i < text.length() && isNumberChar(text, i)) {
            i++;
          }
        } else {
          i++;
        }
        tokens.add(text.substring(start, i));
        offsets.add(start);
      }
    }

    private static boolean isNumberChar(String text, int i) {
      char ch = text.charAt(i);
      if (Character.isDigit(ch) || ch == 'x' || ch == 'o' || ch == 'b') {
        return true;
      }
      if (ch >= 'a' && ch <= 'f' || ch >= 'A' && ch <= 'F') {
        return true;
      }
      if (ch == '.' && !text.startsWith("..", i)) {
        return true;
      }
      return (ch == '-' || ch == '+') && (text.charAt(i - 1) == 'e' || text.charAt(i - 1) == 'E');
    }

    String peek() {
      return pos < tokens.size() ? tokens.get(pos) : null;
    }

    String next() {
      return tokens.get(pos++);
    }

    void expect(String token) {
      String t = next();
      if (!token.equals(t)) {
        throw new IllegalStateException("expected " + token + " but found " + t + " in " + text);
      }
    }

    /** Raw text from the current token on. */
    String rest() {
      return pos < tokens.size() ? text.substring(offsets.get(pos)).strip() : "";
    }

    Decl declaration() {
      Decl decl = new Decl();
      if ("array".equals(peek())) {
        next();
        expect("[");
        while (!"]".equals(next())) {
          // index set, not needed
        }
        expect("of");
        decl.isArray = true;
      }
      if ("var".equals(peek())) {
        next();
        decl.isVar = true;
      }
      parseType(decl);
      expect(":");
      decl.name = next();
      StringBuilder annotations = new StringBuilder();
      while ("::".equals(peek())) {
        next();
        annotations.append(" :: ").append(render(expr()));
      }
      decl.annotations = annotations.toString();
      if ("=".equals(peek())) {
        next();
        decl.value = expr();
      }
      return decl;
    }

    private void parseType(Decl decl) {
      String t = peek();
      switch (t) {
        case "int" -> {
          next();
          decl.type = BaseType.INT;
        }
        case "bool" -> {
          next();
          decl.type = BaseType.BOOL;
        }
        case "float" -> {
          next();
          decl.type = BaseType.FLOAT;
        }
        case "set" -> {
          next();
          expect("of");
          decl.type = BaseType.SET;
          if ("int".equals(peek())) {
            next();
          } else if (expr() instanceof SetLit universe) {
            decl.domain = universe;
          }
        }
        default -> {
          Expr domain = expr();
          if (domain instanceof SetLit s) {
            decl.type = BaseType.INT;
            decl.domain = s;
          } else if (domain instanceof Call(String name, List<Expr> args) && "..f".equals(name)) {
            decl.type = BaseType.FLOAT;
          } else {
            throw new IllegalStateException("unknown type in " + text);
          }
        }
      }
    }

    Expr expr() {
      String t = next();
      Expr result;
      if ("[".equals(t)) {
        List<Expr> elements = new ArrayList<>();
        while (!"]".equals(peek())) {
          elements.add(expr());
          if (",".equals(peek())) {
            next();
          }
        }
        next();
        result = new ArrayLit(elements);
      } else if ("{".equals(t)) {
        List<Long> values = new ArrayList<>();
        while (!"}".equals(peek())) {
          values.add(Long.parseLong(next()));
          if (",".equals(peek())) {
            next();
          }
        }
        next();
        result =
            SetLit.of(values.stream().mapToLong(Long::longValue).sorted().distinct().toArray());
      } else if ("true".equals(t) || "false".equals(t)) {
        result = new BoolLit("true".equals(t));
      } else if (t.startsWith("\"")) {
        result = new StrLit(t);
      } else if (Character.isDigit(t.charAt(0)) || t.charAt(0) == '-') {
        boolean isFloat = t.contains(".") || t.contains("e") || t.contains("E");
        isFloat &= !t.startsWith("0x");
        if (isFloat) {
          result = new FloatLit(t);
        } else {
          result = new IntLit(Long.decode(t));
        }
      } else {
        String name = t;
        if ("(".equals(peek())) {
          next();
          List<Expr> args = new ArrayList<>();
          while (!")".equals(peek())) {
            args.add(expr());
            if (",".equals(peek())) {
              next();
            }
          }
          next();
          result = new Call(name, args);
        } else if ("[".equals(peek())) {
          next();
          Expr index = expr();
          expect("]");
          result = new Call("[]", List.of(new Ident(name), index));
        } else {
          result = new Ident(name);
        }
      }
      if ("..".equals(peek())) {
        next();
        Expr upper = expr();
        if (result instanceof IntLit(long lo) && upper instanceof IntLit(long hi)) {
          return SetLit.range(lo, hi);
        }
        return new Call("..f", List.of(result, upper));
      }
      return result;
    }
  }
}
