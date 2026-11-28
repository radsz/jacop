/*
 * XcspReader.java
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

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.io.Writer;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import javax.xml.stream.XMLInputFactory;
import javax.xml.stream.XMLStreamConstants;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.XMLStreamReader;
import org.jacop.fz.xcsp.FznModel.Lit;

/**
 * Reads an XCSP3-core instance (https://xcsp.org, format 3.2) with the JDK's streaming XML parser
 * and writes it as a FlatZinc model in the dialect of JaCoP's MiniZinc library, so that JaCoP's
 * FlatZinc front end solves it with all its model analysis. Groups, slides and blocks are expanded
 * as they are read; tables are parsed from the text as it streams in and written once.
 */
public final class XcspReader {

  private static final Set<String> FZN_KEYWORDS =
      Set.of(
          "ann",
          "annotation",
          "any",
          "array",
          "bool",
          "case",
          "constraint",
          "default",
          "diff",
          "div",
          "else",
          "elseif",
          "endif",
          "enum",
          "false",
          "float",
          "function",
          "if",
          "in",
          "include",
          "int",
          "intersect",
          "let",
          "list",
          "maximize",
          "minimize",
          "mod",
          "not",
          "of",
          "op",
          "opt",
          "output",
          "par",
          "predicate",
          "record",
          "satisfy",
          "set",
          "solve",
          "string",
          "subset",
          "superset",
          "symdiff",
          "test",
          "then",
          "true",
          "tuple",
          "type",
          "union",
          "var",
          "where",
          "xor");

  /** An element of the XML tree of one constraint (constraints are small, tables aside). */
  static final class Elem {
    final String name;
    final Map<String, String> attrs = new HashMap<>(4);
    final List<Elem> children = new ArrayList<>(4);
    final StringBuilder text = new StringBuilder();
    Table table;
    Expr parsed; // the expression of an intension template, parsed once
    int maxParameter = -2; // -2: not computed

    Elem(String name) {
      this.name = name;
    }

    Elem child(String n) {
      for (Elem c : children) {
        if (c.name.equals(n)) {
          return c;
        }
      }
      return null;
    }

    List<Elem> all(String n) {
      List<Elem> r = new ArrayList<>();
      for (Elem c : children) {
        if (c.name.equals(n)) {
          r.add(c);
        }
      }
      return r;
    }

    String attr(String n) {
      return attrs.get(n);
    }

    String trimmed() {
      return text.toString().trim();
    }
  }

  /** An XCSP3 array of variables. */
  static final class ArrayOfVars {
    final String id;
    final int[] dims;
    final FznVar[] cells;

    ArrayOfVars(String id, int[] dims) {
      this.id = id;
      this.dims = dims;
      long n = 1;
      for (int d : dims) {
        n *= d;
      }
      if (n > Integer.MAX_VALUE - 8) {
        throw new XcspException("array " + id + " too large");
      }
      cells = new FznVar[(int) n];
    }

    String cellId(int flat) {
      StringBuilder s = new StringBuilder(id);
      int[] idx = new int[dims.length];
      for (int d = dims.length - 1; d >= 0; d--) {
        idx[d] = flat % dims[d];
        flat /= dims[d];
      }
      for (int i : idx) {
        s.append('[').append(i).append(']');
      }
      return s.toString();
    }
  }

  /** A declared XCSP3 variable, in declaration order, for the output. */
  record Declared(String id, ArrayOfVars array, FznVar var) {}

  final FznModel m;
  final ExprCompiler ec;
  private final Map<String, FznVar> singles = new HashMap<>();
  private final Map<String, ArrayOfVars> arrays = new HashMap<>();
  final List<Declared> declared = new ArrayList<>();
  private final Map<String, Table> tableKeys = new HashMap<>();

  // symbolic values, numbered in order of appearance
  private final Map<String, Integer> symbols = new LinkedHashMap<>();
  final Map<FznVar, Boolean> symbolic = new HashMap<>();

  boolean optimization;
  boolean minimize;
  FznVar objective;
  String type = "CSP";

  private final Expr.Names names = this::variable;

  XcspReader(Path tmpDir) {
    m = new FznModel(tmpDir);
    ec = new ExprCompiler(m);
  }

  /** The symbols of symbolic variables, by their numbers. */
  String[] symbolTable() {
    String[] t = new String[symbols.size()];
    for (Map.Entry<String, Integer> e : symbols.entrySet()) {
      t[e.getValue()] = e.getKey();
    }
    return t;
  }

  // ------------------------------------------------------------------ XML

  void read(InputStream in) {
    XMLInputFactory f = XMLInputFactory.newFactory();
    f.setProperty(XMLInputFactory.IS_COALESCING, false);
    f.setProperty(XMLInputFactory.SUPPORT_DTD, false);
    f.setProperty(XMLInputFactory.IS_SUPPORTING_EXTERNAL_ENTITIES, false);
    try {
      XMLStreamReader r = f.createXMLStreamReader(in);
      while (r.hasNext()) {
        int ev = r.next();
        if (ev != XMLStreamConstants.START_ELEMENT) {
          continue;
        }
        switch (r.getLocalName()) {
          case "instance" -> {
            String t = r.getAttributeValue(null, "type");
            if (t != null) {
              type = t;
            }
          }
          case "variables" -> variables(r);
          case "constraints" -> constraints(r);
          case "objectives" -> objectives(r);
          default -> skip(r);
        }
      }
      r.close();
    } catch (XMLStreamException e) {
      throw new XcspException("XML error: " + e.getMessage());
    }
  }

  // skips the current element
  private static void skip(XMLStreamReader r) throws XMLStreamException {
    int depth = 1;
    while (depth > 0) {
      int ev = r.next();
      if (ev == XMLStreamConstants.START_ELEMENT) {
        depth++;
      } else if (ev == XMLStreamConstants.END_ELEMENT) {
        depth--;
      }
    }
  }

  // reads the current element and its subtree
  private Elem elem(XMLStreamReader r) throws XMLStreamException {
    Elem e = new Elem(r.getLocalName());
    for (int i = 0; i < r.getAttributeCount(); i++) {
      e.attrs.put(r.getAttributeLocalName(i), r.getAttributeValue(i));
    }
    if (e.name.equals("supports") || e.name.equals("conflicts")) {
      Table t = new Table(e.name.equals("conflicts"), symbols);
      while (true) {
        int ev = r.next();
        if (ev == XMLStreamConstants.CHARACTERS
            || ev == XMLStreamConstants.CDATA
            || ev == XMLStreamConstants.SPACE) {
          t.feed(r.getTextCharacters(), r.getTextStart(), r.getTextLength());
        } else if (ev == XMLStreamConstants.END_ELEMENT) {
          break;
        } else if (ev == XMLStreamConstants.START_ELEMENT) {
          throw new XcspException("element inside " + e.name);
        }
      }
      t.end();
      e.table = t;
      return e;
    }
    while (true) {
      int ev = r.next();
      switch (ev) {
        case XMLStreamConstants.START_ELEMENT -> e.children.add(elem(r));
        case XMLStreamConstants.CHARACTERS, XMLStreamConstants.CDATA, XMLStreamConstants.SPACE ->
            e.text.append(r.getTextCharacters(), r.getTextStart(), r.getTextLength());
        case XMLStreamConstants.END_ELEMENT -> {
          return e;
        }
        default -> {
          // comments, processing instructions
        }
      }
    }
  }

  // ------------------------------------------------------------------ variables

  private void variables(XMLStreamReader r) throws XMLStreamException {
    while (true) {
      int ev = r.next();
      if (ev == XMLStreamConstants.END_ELEMENT) {
        return;
      }
      if (ev != XMLStreamConstants.START_ELEMENT) {
        continue;
      }
      Elem e = elem(r);
      switch (e.name) {
        case "var" -> declareVar(e);
        case "array" -> declareArray(e);
        default -> throw new XcspException("unknown element " + e.name + " in variables");
      }
    }
  }

  private static String fznName(String id) {
    StringBuilder s = new StringBuilder();
    for (int i = 0; i < id.length(); i++) {
      char c = id.charAt(i);
      if (Character.isLetterOrDigit(c) && c < 128) {
        s.append(c);
      } else if (c == '[') {
        s.append('_');
      } else if (c != ']') {
        s.append('_');
      }
    }
    if (s.isEmpty() || !Character.isLetter(s.charAt(0))) {
      s.insert(0, 'v');
    }
    String n = s.toString();
    if (FZN_KEYWORDS.contains(n) || n.startsWith("X_INTRODUCED_")) {
      n = n + "_";
    }
    return n;
  }

  private boolean isSymbolic(Elem e) {
    return "symbolic".equals(e.attr("type"));
  }

  private Dom domain(String text, boolean symbolicVar) {
    String[] tokens = text.trim().split("\\s+");
    if (tokens.length == 1 && tokens[0].isEmpty()) {
      throw new XcspException("empty domain");
    }
    if (symbolicVar) {
      long[] v = new long[tokens.length];
      for (int i = 0; i < tokens.length; i++) {
        v[i] = symbols.computeIfAbsent(tokens[i], k -> symbols.size());
      }
      return Dom.of(v, v.length);
    }
    Dom d = Dom.EMPTY;
    long[] single = new long[tokens.length];
    int n = 0;
    for (String t : tokens) {
      int dots = t.indexOf("..");
      if (dots >= 0) {
        long lo = bound(t.substring(0, dots));
        long hi = bound(t.substring(dots + 2));
        d = d.union(Dom.range(lo, hi));
      } else {
        single[n++] = bound(t);
      }
    }
    if (n > 0) {
      d = d.union(Dom.of(single, n));
    }
    return d;
  }

  private static long bound(String t) {
    return switch (t) {
      case "-infinity", "-inf" -> FznModel.MIN;
      case "+infinity", "+inf", "infinity", "inf" -> FznModel.MAX;
      default -> {
        try {
          yield Long.parseLong(t.startsWith("+") ? t.substring(1) : t);
        } catch (NumberFormatException e) {
          throw new XcspException("bad integer '" + t + "'");
        }
      }
    };
  }

  private FznVar newXcspVar(String id, Dom d, boolean symbolicVar) {
    if (d.isEmpty()) {
      m.fail();
      d = Dom.value(0);
    }
    boolean bool = !symbolicVar && d.equals(Dom.BOOL);
    FznVar x = m.newVar(fznName(id), d, bool, false);
    if (symbolicVar) {
      symbolic.put(x, Boolean.TRUE);
    }
    return x;
  }

  private void declareVar(Elem e) {
    String id = e.attr("id");
    String as = e.attr("as");
    FznVar x;
    if (as != null) {
      FznVar like = singles.get(as);
      if (like == null) {
        throw new XcspException("unknown variable " + as);
      }
      x = newXcspVar(id, like.dom, symbolic.containsKey(like));
    } else {
      x = newXcspVar(id, domain(e.trimmed(), isSymbolic(e)), isSymbolic(e));
    }
    singles.put(id, x);
    declared.add(new Declared(id, null, x));
  }

  private static int[] dims(String size) {
    List<Integer> d = new ArrayList<>();
    int i = 0;
    while (i < size.length()) {
      int open = size.indexOf('[', i);
      if (open < 0) {
        break;
      }
      int close = size.indexOf(']', open);
      d.add(Integer.parseInt(size.substring(open + 1, close).trim()));
      i = close + 1;
    }
    return d.stream().mapToInt(Integer::intValue).toArray();
  }

  private void declareArray(Elem e) {
    String id = e.attr("id");
    String as = e.attr("as");
    if (as != null) {
      ArrayOfVars like = arrays.get(as);
      if (like == null) {
        throw new XcspException("unknown array " + as);
      }
      String size = e.attr("size");
      ArrayOfVars a = new ArrayOfVars(id, size != null ? dims(size) : like.dims.clone());
      if (a.cells.length == like.cells.length) {
        for (int i = 0; i < a.cells.length; i++) {
          if (like.cells[i] != null) {
            a.cells[i] =
                newXcspVar(a.cellId(i), like.cells[i].dom, symbolic.containsKey(like.cells[i]));
          }
        }
      } else {
        // another size (pycsp3 writes it for auxiliary arrays): the domain shared by all cells
        FznVar first = null;
        for (FznVar v : like.cells) {
          if (v != null && first == null) {
            first = v;
          } else if (v != null && !v.dom.equals(first.dom)) {
            throw new XcspException(
                "array " + id + " as " + as + " of another size with several domains");
          }
        }
        if (first == null) {
          throw new XcspException("array " + id + " as an empty array");
        }
        for (int i = 0; i < a.cells.length; i++) {
          a.cells[i] = newXcspVar(a.cellId(i), first.dom, symbolic.containsKey(first));
        }
      }
      arrays.put(id, a);
      declared.add(new Declared(id, a, null));
      return;
    }
    ArrayOfVars a = new ArrayOfVars(id, dims(e.attr("size")));
    arrays.put(id, a);
    boolean sym = isSymbolic(e);
    Dom[] doms = new Dom[a.cells.length];
    List<Elem> parts = e.all("domain");
    if (parts.isEmpty()) {
      Dom d = domain(e.trimmed(), sym);
      java.util.Arrays.fill(doms, d);
    } else {
      Dom others = null;
      for (Elem p : parts) {
        Dom d = domain(p.trimmed(), sym);
        String forIds = p.attr("for").trim();
        if (forIds.equals("others")) {
          others = d;
          continue;
        }
        for (String ref : forIds.split("\\s+")) {
          for (int cell : cellsOf(a, ref)) {
            doms[cell] = d;
          }
        }
      }
      for (int i = 0; i < doms.length; i++) {
        if (doms[i] == null) {
          doms[i] = others;
        }
      }
    }
    for (int i = 0; i < a.cells.length; i++) {
      if (doms[i] != null) {
        a.cells[i] = newXcspVar(a.cellId(i), doms[i], sym);
      }
    }
    declared.add(new Declared(id, a, null));
  }

  // the flat cells of an array reference such as x[1][] or x[2..4][0]
  private static List<Integer> cellsOf(ArrayOfVars a, String ref) {
    int open = ref.indexOf('[');
    if (open < 0) {
      throw new XcspException("not an array reference: " + ref);
    }
    int[][] ranges = new int[a.dims.length][];
    int d = 0;
    int i = open;
    while (i < ref.length()) {
      if (ref.charAt(i) != '[') {
        throw new XcspException("bad array reference " + ref);
      }
      int close = ref.indexOf(']', i);
      String in = ref.substring(i + 1, close).trim();
      if (d >= a.dims.length) {
        throw new XcspException("too many indexes in " + ref);
      }
      if (in.isEmpty()) {
        ranges[d] = new int[] {0, a.dims[d] - 1};
      } else {
        int dots = in.indexOf("..");
        if (dots >= 0) {
          ranges[d] =
              new int[] {
                Integer.parseInt(in.substring(0, dots)), Integer.parseInt(in.substring(dots + 2))
              };
        } else {
          int v = Integer.parseInt(in);
          ranges[d] = new int[] {v, v};
        }
      }
      d++;
      i = close + 1;
    }
    for (; d < a.dims.length; d++) {
      ranges[d] = new int[] {0, a.dims[d] - 1};
    }
    List<Integer> out = new ArrayList<>();
    collect(a, ranges, 0, 0, out);
    return out;
  }

  private static void collect(ArrayOfVars a, int[][] ranges, int d, int flat, List<Integer> out) {
    if (d == a.dims.length) {
      out.add(flat);
      return;
    }
    for (int v = ranges[d][0]; v <= ranges[d][1]; v++) {
      if (v < 0 || v >= a.dims[d]) {
        throw new XcspException("index " + v + " out of the bounds of " + a.id);
      }
      collect(a, ranges, d + 1, flat * a.dims[d] + v, out);
    }
  }

  /** The variable of an id such as x[2][3]. */
  FznVar variable(String id) {
    FznVar x = singles.get(id);
    if (x != null) {
      return x;
    }
    int open = id.indexOf('[');
    if (open > 0) {
      ArrayOfVars a = arrays.get(id.substring(0, open));
      if (a != null) {
        List<Integer> c = cellsOf(a, id);
        if (c.size() == 1 && a.cells[c.get(0)] != null) {
          return a.cells[c.get(0)];
        }
      }
    }
    Integer s = symbols.get(id);
    if (s != null) {
      throw new SymbolValue(s);
    }
    throw new XcspException("unknown variable " + id);
  }

  // a symbol where the expression parser expected a variable
  private static final class SymbolValue extends RuntimeException {
    private static final long serialVersionUID = 1L;
    final int value;

    SymbolValue(int value) {
      super(null, null, false, false);
      this.value = value;
    }
  }

  // ------------------------------------------------------------------ lists

  /**
   * The items of a list: variables (compact forms expanded), integers, expressions and parameters
   * of a template bound to their arguments.
   */
  List<Expr> items(String text, List<Expr> args, int restFrom) {
    List<Expr> out = new ArrayList<>();
    int i = 0;
    int n = text.length();
    while (i < n) {
      while (i < n && Character.isWhitespace(text.charAt(i))) {
        i++;
      }
      if (i >= n) {
        break;
      }
      int start = i;
      int depth = 0;
      while (i < n) {
        char c = text.charAt(i);
        if (c == '(') {
          depth++;
        } else if (c == ')') {
          depth--;
        } else if (depth == 0 && Character.isWhitespace(c)) {
          break;
        }
        i++;
      }
      item(text.substring(start, i), args, restFrom, out);
    }
    return out;
  }

  private void item(String t, List<Expr> args, int restFrom, List<Expr> out) {
    char c = t.charAt(0);
    if (c == '%') {
      if (args == null) {
        throw new XcspException("parameter " + t + " outside a template");
      }
      if (t.equals("%...")) {
        for (int k = restFrom; k < args.size(); k++) {
          out.add(args.get(k));
        }
        return;
      }
      int k = Integer.parseInt(t.substring(1));
      if (k >= args.size()) {
        throw new XcspException("parameter " + t + " has no argument");
      }
      out.add(args.get(k));
      return;
    }
    if (c == '-' || c == '+' || Character.isDigit(c)) {
      int dots = t.indexOf("..");
      int times = t.indexOf('x');
      if (times > 0 && dots < 0) {
        // the compact form v x k of k copies of v
        Expr v = Expr.of(bound(t.substring(0, times)));
        long k = bound(t.substring(times + 1));
        for (long r = 0; r < k; r++) {
          out.add(v);
        }
        return;
      }
      if (dots > 0) {
        out.add(Expr.range(bound(t.substring(0, dots)), bound(t.substring(dots + 2))));
      } else {
        out.add(Expr.of(bound(t)));
      }
      return;
    }
    if (t.indexOf('(') >= 0) {
      Expr e = parse(t);
      out.add(args == null ? e : e.bind(args, restFrom));
      return;
    }
    FznVar x = singles.get(t);
    if (x != null) {
      out.add(Expr.of(x));
      return;
    }
    int open = t.indexOf('[');
    if (open > 0) {
      ArrayOfVars a = arrays.get(t.substring(0, open));
      if (a != null) {
        for (int cell : cellsOf(a, t)) {
          if (a.cells[cell] != null) {
            out.add(Expr.of(a.cells[cell]));
          }
        }
        return;
      }
    }
    Integer s = symbols.get(t);
    if (s != null) {
      out.add(Expr.of(s));
      return;
    }
    throw new XcspException("unknown variable " + t);
  }

  Expr parse(CharSequence text) {
    try {
      return Expr.Parser.parse(text, names);
    } catch (SymbolValue s) {
      return parseWithSymbols(text.toString());
    }
  }

  // symbols in an expression of symbolic variables: replaced by their numbers
  private Expr parseWithSymbols(String text) {
    StringBuilder s = new StringBuilder();
    int i = 0;
    while (i < text.length()) {
      char c = text.charAt(i);
      if (Character.isLetter(c)) {
        int j = i;
        while (j < text.length()
            && (Character.isLetterOrDigit(text.charAt(j))
                || text.charAt(j) == '_'
                || text.charAt(j) == '['
                || text.charAt(j) == ']')) {
          j++;
        }
        String w = text.substring(i, j);
        boolean call = j < text.length() && text.charAt(j) == '(';
        Integer v = call ? null : symbols.get(w);
        s.append(v != null && !singles.containsKey(w) ? v.toString() : w);
        i = j;
      } else {
        s.append(c);
        i++;
      }
    }
    return Expr.Parser.parse(s, names);
  }

  // ------------------------------------------------------------------ constraints

  private void constraints(XMLStreamReader r) throws XMLStreamException {
    while (true) {
      int ev = r.next();
      if (ev == XMLStreamConstants.END_ELEMENT) {
        return;
      }
      if (ev != XMLStreamConstants.START_ELEMENT) {
        continue;
      }
      switch (r.getLocalName()) {
        case "block" -> constraints(r);
        case "group" -> group(r);
        default -> post(elem(r), null, 0);
      }
    }
  }

  // a group: the template, then each args line posted as it is read
  private void group(XMLStreamReader r) throws XMLStreamException {
    Elem template = null;
    while (true) {
      int ev = r.next();
      if (ev == XMLStreamConstants.END_ELEMENT) {
        return;
      }
      if (ev != XMLStreamConstants.START_ELEMENT) {
        continue;
      }
      if (template == null) {
        template = elem(r);
        continue;
      }
      Elem args = elem(r);
      if (!args.name.equals("args")) {
        throw new XcspException("unexpected " + args.name + " in group");
      }
      List<Expr> actual = items(args.text.toString(), null, 0);
      post(template, actual, maxParameter(template) + 1);
    }
  }

  private static int maxParameter(Elem e) {
    if (e.maxParameter != -2) {
      return e.maxParameter;
    }
    int max = -1;
    CharSequence t = e.text;
    for (int i = 0; i + 1 < t.length(); i++) {
      if (t.charAt(i) == '%' && Character.isDigit(t.charAt(i + 1))) {
        int j = i + 1;
        int v = 0;
        while (j < t.length() && Character.isDigit(t.charAt(j))) {
          v = v * 10 + t.charAt(j) - '0';
          j++;
        }
        max = Math.max(max, v);
      }
    }
    for (Elem c : e.children) {
      max = Math.max(max, maxParameter(c));
    }
    e.maxParameter = max;
    return max;
  }

  // the items of a child element (or of the element's own text when the child is missing)
  private List<Expr> list(Elem c, String child, List<Expr> args, int rest) {
    Elem l = c.child(child);
    if (l == null) {
      return null;
    }
    return items(l.text.toString(), args, rest);
  }

  private List<Expr> mainList(Elem c, List<Expr> args, int rest) {
    List<Expr> l = list(c, "list", args, rest);
    if (l != null) {
      return l;
    }
    return items(c.text.toString(), args, rest);
  }

  private static long constant(Expr e) {
    if (e.kind != Expr.Kind.INT) {
      throw new XcspException("integer expected, found " + e);
    }
    return e.value;
  }

  private static long[] constants(List<Expr> l) {
    long[] r = new long[l.size()];
    for (int i = 0; i < r.length; i++) {
      r[i] = constant(l.get(i));
    }
    return r;
  }

  private static boolean allConstant(List<Expr> l) {
    for (Expr e : l) {
      if (e.kind != Expr.Kind.INT) {
        return false;
      }
    }
    return true;
  }

  /** The FlatZinc array literal of integer arguments. */
  String array(List<Expr> l) {
    StringBuilder s = new StringBuilder("[");
    for (int i = 0; i < l.size(); i++) {
      if (i > 0) {
        s.append(',');
      }
      s.append(ec.atom(l.get(i)));
    }
    return s.append(']').toString();
  }

  static String ints(long[] v) {
    StringBuilder s = new StringBuilder("[");
    for (int i = 0; i < v.length; i++) {
      if (i > 0) {
        s.append(',');
      }
      s.append(v[i]);
    }
    return s.append(']').toString();
  }

  /** A condition (op, operand) of a global constraint. */
  record Condition(String op, Expr operand) {}

  private Condition condition(Elem c, List<Expr> args, int rest) {
    Elem e = c.child("condition");
    if (e == null) {
      return null;
    }
    return condition(e.trimmed(), args, rest);
  }

  private Condition condition(String t, List<Expr> args, int rest) {
    t = t.trim();
    if (!t.startsWith("(") || !t.endsWith(")")) {
      throw new XcspException("bad condition " + t);
    }
    String body = t.substring(1, t.length() - 1);
    int comma = body.indexOf(',');
    String op = body.substring(0, comma).trim();
    String operand = body.substring(comma + 1).trim();
    if (operand.startsWith("{")) {
      String in = operand.substring(1, operand.length() - 1).replace(',', ' ');
      List<Expr> vs = items(in, args, rest);
      return new Condition(op, Expr.op("set", vs.toArray(new Expr[0])));
    }
    List<Expr> v = items(operand, args, rest);
    if (v.size() != 1) {
      throw new XcspException("bad condition operand " + operand);
    }
    return new Condition(op, v.get(0));
  }

  // posts value cond
  private void post(Lin value, Condition c) {
    if (c.op.equals("in") || c.op.equals("notin")) {
      Expr s = c.operand;
      Lit l = ec.lit(Expr.op(c.op, Expr.of(m.var(value)), s));
      if (value.isVariable() && (s.kind == Expr.Kind.RANGE || s.isOp("set"))) {
        ec.post(Expr.op(c.op, Expr.of(value.v[0]), s));
        return;
      }
      m.post(l);
      return;
    }
    Lin d = ExprCompiler.diff(value, ec.lin(c.operand));
    if (c.op.equals("eq") && c.operand.kind == Expr.Kind.VAR && !c.operand.var.bool) {
      m.postDefining(d, c.operand.var);
      return;
    }
    m.post(c.op, d);
  }

  // the bounds an expression with this condition can take, for an introduced variable
  private void post(FznVar x, Condition c) {
    post(Lin.of(x), c);
  }

  /**
   * Posts one constraint.
   *
   * @param c the constraint element
   * @param args the arguments of a group or slide template, or null
   * @param rest the first argument {@code %...} stands for
   */
  void post(Elem c, List<Expr> args, int rest) {
    switch (c.name) {
      case "intension" -> intension(c, args, rest);
      case "extension" -> extension(c, args, rest);
      case "allDifferent" -> allDifferent(c, args, rest);
      case "allEqual" -> allEqual(c, args, rest);
      case "ordered" -> ordered(c, args, rest);
      case "lex" -> lex(c, args, rest);
      case "sum" -> sum(c, args, rest);
      case "count" -> count(c, args, rest);
      case "nValues" -> nValues(c, args, rest);
      case "cardinality" -> cardinality(c, args, rest);
      case "maximum", "minimum" -> extremum(c, args, rest);
      case "element" -> element(c, args, rest);
      case "channel" -> channel(c, args, rest);
      case "noOverlap" -> noOverlap(c, args, rest);
      case "cumulative" -> cumulative(c, args, rest);
      case "circuit" -> circuit(c, args, rest);
      case "mdd" -> mdd(c, args, rest);
      case "regular" -> regular(c, args, rest);
      case "instantiation" -> instantiation(c, args, rest);
      case "precedence" -> precedence(c, args, rest);
      case "binPacking" -> binPacking(c, args, rest);
      case "knapsack" -> knapsack(c, args, rest);
      case "slide" -> slide(c);
      case "block" -> {
        for (Elem e : c.children) {
          post(e, args, rest);
        }
      }
      case "group" -> {
        Elem template = c.children.get(0);
        for (int i = 1; i < c.children.size(); i++) {
          List<Expr> actual = items(c.children.get(i).text.toString(), args, rest);
          post(template, actual, maxParameter(template) + 1);
        }
      }
      default -> throw new XcspException("unsupported constraint " + c.name);
    }
  }

  private void intension(Elem c, List<Expr> args, int rest) {
    Elem f = c.child("function");
    CharSequence text = f != null ? f.text : c.text;
    Expr e;
    if (args == null) {
      e = parse(text);
    } else {
      if (c.parsed == null) {
        c.parsed = parse(text);
      }
      e = c.parsed.bind(args, rest);
    }
    ec.post(e);
  }

  private void extension(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    Elem s = c.child("supports");
    if (s == null) {
      s = c.child("conflicts");
    }
    if (s == null) {
      throw new XcspException("extension without supports or conflicts");
    }
    Table t = s.table;
    if (t.unary || xs.size() == 1) {
      Dom d = t.unary ? t.values() : unaryValues(t);
      Expr x = xs.get(0);
      if (x.kind == Expr.Kind.VAR) {
        FznVar v = x.var;
        m.restrict(v, t.negative ? v.dom.minus(d) : d);
      } else {
        Lit l = m.inLit(ec.lin(x), d);
        m.post(t.negative ? l.not() : l);
      }
      return;
    }
    if (t.rows() == 0) {
      if (!t.negative) {
        m.fail();
      }
      return;
    }
    if (t.arity != xs.size()) {
      throw new XcspException("table of arity " + t.arity + " on " + xs.size() + " variables");
    }
    if (!t.negative) {
      t = supported(xs, t);
      if (t == null) {
        return;
      }
    }
    String vars = array(xs);
    if (t.negative && t.starred) {
      negativeShortTable(xs, t);
      return;
    }
    long star = 0;
    if (t.starred) {
      if (t.minCell == null) {
        long min = Long.MAX_VALUE;
        for (int i = 0; i < t.size; i++) {
          if (t.cells[i] != Table.STAR) {
            min = Math.min(min, t.cells[i]);
          }
        }
        t.minCell = min;
      }
      star = t.minCell == Long.MAX_VALUE ? 0 : t.minCell - 1;
      for (Expr x : xs) {
        star = Math.min(star, ec.lin(x).min() - 1);
      }
      // any value below the table and the domains will do: keep the one already written
      if (t.param != null && t.paramStar <= star) {
        star = t.paramStar;
      }
    }
    String param = tableParam(t, star);
    if (t.negative) {
      m.constraint("jacop_negative_table_int(" + vars + "," + param + ")");
    } else if (t.starred) {
      m.constraint("jacop_short_table_int(" + vars + "," + param + "," + star + ")");
    } else {
      m.constraint("jacop_table_int(" + vars + "," + param + ")");
    }
  }

  /**
   * The rows of a positive table on variables that are supported by their domains, the table itself
   * when all are; narrows each variable to the values of its column. Null when the table is
   * entailed or failed. Inglenook of XCSP 2026 shares a table of 26 million pairs over a path whose
   * first variable is fixed, so few rows are left.
   */
  private Table supported(List<Expr> xs, Table t) {
    int a = t.arity;
    FznVar[] v = new FznVar[a];
    for (int j = 0; j < a; j++) {
      if (xs.get(j).kind != Expr.Kind.VAR) {
        return t;
      }
      v[j] = xs.get(j).var;
    }
    if (t.columns != null) {
      // no row can be dropped when every domain holds the values of its column
      boolean all = true;
      for (int j = 0; j < a && all; j++) {
        all = t.columns[j] == null || v[j].dom.intersect(t.columns[j]).equals(t.columns[j]);
      }
      if (all) {
        return t;
      }
    }
    int rows = t.rows();
    int[] cells = t.cells;
    int[] kept = null;
    int keptSize = 0;
    for (int r = 0; r < rows; r++) {
      boolean ok = true;
      for (int j = 0; j < a && ok; j++) {
        int c = cells[r * a + j];
        ok = c == Table.STAR || v[j].dom.contains(c);
      }
      if (ok) {
        if (kept != null) {
          System.arraycopy(cells, r * a, kept, keptSize, a);
          keptSize += a;
        }
      } else if (kept == null) {
        kept = new int[Math.max(a, r * a)];
        System.arraycopy(cells, 0, kept, 0, r * a);
        keptSize = r * a;
      }
      if (kept != null && keptSize + a > kept.length) {
        kept = java.util.Arrays.copyOf(kept, (int) Math.min(t.size, 2L * kept.length + a));
      }
    }
    Table result = t;
    if (kept != null && keptSize == 0) {
      m.fail();
      return null;
    }
    // a table that loses less than half of its rows stays shared (one parameter for all its uses)
    if (kept != null && 2L * keptSize <= t.size) {
      boolean starred = false;
      for (int i = 0; i < keptSize && !starred; i++) {
        starred = kept[i] == Table.STAR;
      }
      result = Table.of(java.util.Arrays.copyOf(kept, keptSize), keptSize, a, starred);
    }
    // the values of each column
    if (result.columns == null) {
      int n = result.rows();
      long[] values = new long[n];
      result.columns = new Dom[a];
      for (int j = 0; j < a; j++) {
        boolean star = false;
        for (int r = 0; r < n && !star; r++) {
          int c = result.cells[r * a + j];
          star = c == Table.STAR;
          values[r] = c;
        }
        result.columns[j] = star ? null : Dom.of(values, n);
      }
    }
    for (int j = 0; j < a; j++) {
      if (result.columns[j] != null) {
        m.restrict(v[j], v[j].dom.intersect(result.columns[j]));
      }
    }
    return result;
  }

  private static Dom unaryValues(Table t) {
    long[] v = new long[t.size];
    for (int i = 0; i < t.size; i++) {
      if (t.cells[i] == Table.STAR) {
        return Dom.range(FznModel.MIN, FznModel.MAX);
      }
      v[i] = t.cells[i];
    }
    return Dom.of(v, v.length);
  }

  // no row matches: a clause per row on its non-star positions
  private void negativeShortTable(List<Expr> xs, Table t) {
    int a = t.arity;
    for (int r = 0; r < t.rows(); r++) {
      List<Lit> any = new ArrayList<>();
      for (int j = 0; j < a; j++) {
        int v = t.cells[r * a + j];
        if (v != Table.STAR) {
          any.add(m.lit("ne", ExprCompiler.diff(ec.lin(xs.get(j)), Lin.constant(v))));
        }
      }
      m.clause(any);
    }
  }

  // the parameter of a table's cells, written once per table (and per equal content)
  private String tableParam(Table t, long star) {
    if (t.param != null && t.paramStar == star) {
      return t.param;
    }
    String key = t.key() + ":" + star;
    Table same = tableKeys.get(key);
    if (same != null && same.sameCells(t)) {
      t.param = same.param;
      t.paramStar = star;
      return t.param;
    }
    String name = m.paramName("T");
    try {
      Writer w = m.params();
      w.write("array [1..");
      w.write(Integer.toString(t.size));
      w.write("] of int: ");
      w.write(name);
      w.write(" = [");
      String starText = Long.toString(star);
      for (int i = 0; i < t.size; i++) {
        if (i > 0) {
          w.write(',');
        }
        int v = t.cells[i];
        w.write(v == Table.STAR ? starText : Integer.toString(v));
      }
      w.write("];\n");
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    }
    t.param = name;
    t.paramStar = star;
    tableKeys.put(key, t);
    return name;
  }

  private void allDifferent(Elem c, List<Expr> args, int rest) {
    List<Elem> lists = c.all("list");
    Elem matrix = c.child("matrix");
    // the except of several lists holds tuples, read below
    List<Expr> except = lists.size() > 1 ? null : list(c, "except", args, rest);
    if (matrix != null) {
      List<List<Expr>> rows = matrix(matrix, args, rest);
      for (List<Expr> row : rows) {
        allDifferent(row, except);
      }
      for (int j = 0; j < rows.get(0).size(); j++) {
        List<Expr> col = new ArrayList<>();
        for (List<Expr> row : rows) {
          col.add(row.get(j));
        }
        allDifferent(col, except);
      }
      return;
    }
    if (lists.size() > 1) {
      List<Expr> flat = new ArrayList<>();
      int cols = -1;
      for (Elem l : lists) {
        List<Expr> row = items(l.text.toString(), args, rest);
        if (cols >= 0 && row.size() != cols) {
          throw new XcspException("allDifferent lists of different lengths");
        }
        cols = row.size();
        flat.addAll(row);
      }
      if (c.child("except") == null || c.child("except").trimmed().isEmpty()) {
        m.constraint("jacop_all_different_lists(" + array(flat) + "," + lists.size() + ")");
      } else {
        String e = c.child("except").trimmed();
        Table t = new Table(false);
        t.feed(e.toCharArray(), 0, e.length());
        t.end();
        StringBuilder s = new StringBuilder("[");
        for (int i = 0; i < t.size; i++) {
          if (i > 0) {
            s.append(',');
          }
          s.append(t.cells[i]);
        }
        m.constraint(
            "jacop_all_different_lists_except("
                + array(flat)
                + ","
                + lists.size()
                + ","
                + s.append(']')
                + ")");
      }
      return;
    }
    allDifferent(mainList(c, args, rest), except);
  }

  private void allDifferent(List<Expr> xs, List<Expr> except) {
    if (xs.size() <= 1) {
      return;
    }
    if (except == null || except.isEmpty()) {
      if (xs.size() == 2) {
        ec.post(Expr.op("ne", xs.get(0), xs.get(1)));
        return;
      }
      m.constraint("jacop_alldiff(" + array(xs) + ")");
      return;
    }
    long[] e = constants(except);
    if (e.length == 1 && e[0] == 0) {
      m.constraint("jacop_alldifferent_except_0(" + array(xs) + ")");
    } else {
      m.constraint(
          "jacop_alldifferent_except(" + array(xs) + "," + Dom.of(e, e.length).toFzn() + ")");
    }
  }

  private List<List<Expr>> matrix(Elem e, List<Expr> args, int rest) {
    String t = e.trimmed();
    List<List<Expr>> rows = new ArrayList<>();
    if (t.startsWith("(")) {
      int i = 0;
      while (i < t.length()) {
        int open = t.indexOf('(', i);
        if (open < 0) {
          break;
        }
        int close = t.indexOf(')', open);
        rows.add(items(t.substring(open + 1, close).replace(',', ' '), args, rest));
        i = close + 1;
      }
      return rows;
    }
    // a two-dimensional array reference such as x[][]
    String ref = t;
    int open = ref.indexOf('[');
    ArrayOfVars a = arrays.get(ref.substring(0, open));
    if (a == null || a.dims.length < 2) {
      throw new XcspException("bad matrix " + t);
    }
    List<Integer> cells = cellsOf(a, ref);
    // rows of the last dimension of the selection
    int cols = a.dims[a.dims.length - 1];
    String last = ref.substring(ref.lastIndexOf('[') + 1, ref.lastIndexOf(']')).trim();
    if (!last.isEmpty()) {
      int dots = last.indexOf("..");
      cols =
          dots < 0
              ? 1
              : Integer.parseInt(last.substring(dots + 2))
                  - Integer.parseInt(last.substring(0, dots))
                  + 1;
    }
    for (int i = 0; i < cells.size(); i += cols) {
      List<Expr> row = new ArrayList<>();
      for (int j = i; j < i + cols; j++) {
        row.add(Expr.of(a.cells[cells.get(j)]));
      }
      rows.add(row);
    }
    return rows;
  }

  private void allEqual(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    if (xs.size() <= 1) {
      return;
    }
    if (xs.size() == 2) {
      ec.post(Expr.op("eq", xs.get(0), xs.get(1)));
      return;
    }
    m.constraint("jacop_all_equal_int(" + array(xs) + ")");
  }

  private static String operator(Elem c) {
    Elem o = c.child("operator");
    if (o == null) {
      throw new XcspException(c.name + " without operator");
    }
    return o.trimmed();
  }

  private void ordered(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    List<Expr> lengths = list(c, "lengths", args, rest);
    String op = operator(c);
    if (xs.size() <= 1) {
      return;
    }
    if (lengths == null) {
      String name =
          switch (op) {
            case "le" -> "jacop_increasing";
            case "lt" -> "jacop_strictly_increasing";
            case "ge" -> "jacop_decreasing";
            case "gt" -> "jacop_strictly_decreasing";
            default -> throw new XcspException("bad operator " + op);
          };
      if (xs.size() == 2) {
        ec.post(Expr.op(op, xs.get(0), xs.get(1)));
        return;
      }
      m.constraint(name + "(" + array(xs) + ")");
      return;
    }
    for (int i = 0; i + 1 < xs.size(); i++) {
      ec.post(Expr.op(op, Expr.op("add", xs.get(i), lengths.get(i)), xs.get(i + 1)));
    }
  }

  private void lex(Elem c, List<Expr> args, int rest) {
    String op = operator(c);
    List<List<Expr>> lists = new ArrayList<>();
    Elem matrix = c.child("matrix");
    if (matrix != null) {
      List<List<Expr>> rows = matrix(matrix, args, rest);
      lexChain(rows, op);
      List<List<Expr>> cols = new ArrayList<>();
      for (int j = 0; j < rows.get(0).size(); j++) {
        List<Expr> col = new ArrayList<>();
        for (List<Expr> row : rows) {
          col.add(row.get(j));
        }
        cols.add(col);
      }
      lexChain(cols, op);
      return;
    }
    for (Elem l : c.all("list")) {
      lists.add(items(l.text.toString(), args, rest));
    }
    lexChain(lists, op);
  }

  private void lexChain(List<List<Expr>> lists, String op) {
    if (op.equals("gt") || op.equals("ge")) {
      lists = new ArrayList<>(lists);
      java.util.Collections.reverse(lists);
    }
    boolean strict = op.equals("lt") || op.equals("gt");
    if (lists.size() < 2) {
      return;
    }
    if (lists.size() == 2) {
      m.constraint(
          (strict ? "jacop_lex_less_int(" : "jacop_lex_lesseq_int(")
              + array(lists.get(0))
              + ","
              + array(lists.get(1))
              + ")");
      return;
    }
    // the built-in takes the vectors as the columns of a matrix listed row by row
    List<Expr> flat = new ArrayList<>();
    int length = lists.get(0).size();
    for (int i = 0; i < length; i++) {
      for (List<Expr> l : lists) {
        if (l.size() != length) {
          throw new XcspException("lex over lists of different lengths");
        }
        flat.add(l.get(i));
      }
    }
    m.constraint(
        (strict ? "jacop_lex_chain_less_int(" : "jacop_lex_chain_lesseq_int(")
            + array(flat)
            + ","
            + lists.size()
            + ")");
  }

  private Lin sumOf(List<Expr> xs, List<Expr> coeffs) {
    return sumOf(xs, coeffs, 0);
  }

  /**
   * The linear form of a sum; with up 1 (the sum is only bounded below) or -1 (only above), a
   * comparison whose term may only help the bound is half reified, as MiniZinc does.
   */
  private Lin sumOf(List<Expr> xs, List<Expr> coeffs, int up) {
    Lin s = new Lin();
    for (int i = 0; i < xs.size(); i++) {
      long k = coeffs == null ? 1 : coeffs.get(i).kind == Expr.Kind.INT ? coeffs.get(i).value : 0;
      if (k != 0 && up != 0 && Long.signum(k) == up) {
        s.add(ec.halfLin(xs.get(i)), k);
      } else if (coeffs == null) {
        s.add(ec.lin(xs.get(i)), 1);
      } else if (coeffs.get(i).kind == Expr.Kind.INT) {
        s.add(ec.lin(xs.get(i)), coeffs.get(i).value);
      } else {
        s.add(ec.lin(Expr.op("mul", coeffs.get(i), xs.get(i))), 1);
      }
    }
    return s;
  }

  private void sum(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    List<Expr> coeffs = list(c, "coeffs", args, rest);
    if (coeffs != null && coeffs.size() != xs.size()) {
      if (coeffs.size() == 1 && xs.size() > 1) {
        List<Expr> rep = new ArrayList<>();
        for (int i = 0; i < xs.size(); i++) {
          rep.add(coeffs.get(0));
        }
        coeffs = rep;
      } else {
        throw new XcspException(
            "sum with " + xs.size() + " terms and " + coeffs.size() + " coefficients");
      }
    }
    Condition cond = condition(c, args, rest);
    int up = 0;
    if (cond != null) {
      up =
          switch (cond.op) {
            case "ge", "gt" -> 1;
            case "le", "lt" -> -1;
            default -> 0;
          };
    }
    post(sumOf(xs, coeffs, up), cond);
  }

  private void count(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    List<Expr> values = list(c, "values", args, rest);
    Condition cond = condition(c, args, rest);
    post(countOf(xs, values), cond);
  }

  // the number of items of xs that take one of the values
  private Lin countOf(List<Expr> xs, List<Expr> values) {
    FznVar n = m.aux(0, xs.size());
    n.defined = true;
    if (allConstant(values)) {
      long[] v = constants(values);
      if (v.length == 1) {
        m.constraint("jacop_count(" + array(xs) + "," + v[0] + "," + n.name + ")", n);
      } else {
        m.constraint(
            "jacop_among(" + array(xs) + "," + Dom.of(v, v.length).toFzn() + "," + n.name + ")", n);
      }
      return Lin.of(n);
    }
    if (values.size() == 1) {
      m.constraint(
          "jacop_count_var(" + array(xs) + "," + ec.atom(values.get(0)) + "," + n.name + ")", n);
      return Lin.of(n);
    }
    Lin s = new Lin();
    for (Expr x : xs) {
      List<Lit> any = new ArrayList<>();
      for (Expr v : values) {
        any.add(ec.lit(Expr.op("eq", x, v)));
      }
      s.add(m.lin(m.or(any)), 1);
    }
    m.post("eq", ExprCompiler.diff(Lin.of(n), s));
    return Lin.of(n);
  }

  private void nValues(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    List<Expr> except = list(c, "except", args, rest);
    Condition cond = condition(c, args, rest);
    post(nValuesOf(xs, except), cond);
  }

  private Lin nValuesOf(List<Expr> xs, List<Expr> except) {
    if (except == null || except.isEmpty()) {
      FznVar n = m.aux(xs.isEmpty() ? 0 : 1, xs.size());
      n.defined = true;
      m.constraint("jacop_nvalue(" + n.name + "," + array(xs) + ")", n);
      return Lin.of(n);
    }
    // the values taken outside the excepted ones: one literal per candidate value
    long[] e = constants(except);
    Dom ex = Dom.of(e, e.length);
    Dom all = Dom.EMPTY;
    for (Expr x : xs) {
      Lin l = ec.lin(x);
      all = all.union(l.isConstant() ? Dom.value(l.c) : m.var(l).dom);
    }
    all = all.minus(ex);
    if (all.size() > 100_000) {
      throw new XcspException("nValues with except over too many values");
    }
    Lin s = new Lin();
    for (long v : all.values()) {
      List<Lit> any = new ArrayList<>();
      for (Expr x : xs) {
        any.add(ec.lit(Expr.op("eq", x, Expr.of(v))));
      }
      s.add(m.lin(m.or(any)), 1);
    }
    return s;
  }

  private void cardinality(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    Elem valuesElem = c.child("values");
    List<Expr> values = items(valuesElem.text.toString(), args, rest);
    boolean closed = "true".equals(valuesElem.attr("closed"));
    List<Expr> occurs = list(c, "occurs", args, rest);
    if (allConstant(values)) {
      long[] v = constants(values);
      boolean ranges = true;
      for (Expr o : occurs) {
        ranges &= o.kind == Expr.Kind.RANGE || o.kind == Expr.Kind.INT;
      }
      if (closed) {
        Dom d = Dom.of(v, v.length);
        for (Expr x : xs) {
          ec.post(Expr.op("in", x, Expr.op("set", values.toArray(new Expr[0]))));
        }
        if (d.isEmpty()) {
          return;
        }
      }
      if (ranges) {
        long[] lo = new long[v.length];
        long[] hi = new long[v.length];
        for (int i = 0; i < v.length; i++) {
          Expr o = occurs.get(i);
          lo[i] = o.value;
          hi[i] = o.kind == Expr.Kind.RANGE ? o.value2 : o.value;
        }
        m.constraint(
            "jacop_count_values_bounds("
                + array(xs)
                + ","
                + ints(v)
                + ","
                + ints(lo)
                + ","
                + ints(hi)
                + ")");
        return;
      }
      List<String> counts = new ArrayList<>();
      for (Expr o : occurs) {
        if (o.kind == Expr.Kind.RANGE) {
          counts.add(m.aux(o.value, o.value2).name);
        } else {
          counts.add(ec.atom(o));
        }
      }
      m.constraint(
          "jacop_count_values(" + array(xs) + "," + ints(v) + "," + FznModel.list(counts) + ")");
      return;
    }
    // values that are variables: one count per value
    for (int i = 0; i < values.size(); i++) {
      Lin n = countOf(xs, List.of(values.get(i)));
      Expr o = occurs.get(i);
      if (o.kind == Expr.Kind.RANGE) {
        post(n, new Condition("in", o));
      } else {
        m.post("eq", ExprCompiler.diff(n, ec.lin(o)));
      }
    }
    if (closed) {
      for (Expr x : xs) {
        List<Lit> any = new ArrayList<>();
        for (Expr v : values) {
          any.add(ec.lit(Expr.op("eq", x, v)));
        }
        m.clause(any);
      }
    }
  }

  private void extremum(Elem c, List<Expr> args, int rest) {
    boolean max = c.name.equals("maximum");
    List<Expr> xs = mainList(c, args, rest);
    Elem index = c.child("index");
    Condition cond = condition(c, args, rest);
    if (index != null) {
      // the index of an extremum: first by default
      List<Expr> idx = items(index.text.toString(), args, rest);
      int start = Integer.parseInt(c.child("list").attrs.getOrDefault("startIndex", "0"));
      String rank = index.attrs.getOrDefault("rank", "any");
      FznVar i = ec.var(idx.get(0));
      if (rank.equals("any")) {
        FznVar e = m.var(ec.lin(Expr.op(max ? "max" : "min", xs.toArray(new Expr[0]))));
        m.constraint(
            "jacop_array_var_int_element_nonshifted("
                + i.name
                + ","
                + array(xs)
                + ","
                + e.name
                + ","
                + start
                + ")");
        if (cond != null) {
          post(e, cond);
        }
        return;
      }
      if (rank.equals("first")) {
        m.constraint(
            (max ? "jacop_maximum_arg_int(" : "jacop_minimum_arg_int(")
                + array(xs)
                + ","
                + i.name
                + ","
                + start
                + ")");
        if (cond != null) {
          FznVar e = m.var(ec.lin(Expr.op(max ? "max" : "min", xs.toArray(new Expr[0]))));
          post(e, cond);
        }
        return;
      }
      throw new XcspException("extremum with rank " + rank);
    }
    Lin e = ec.lin(Expr.op(max ? "max" : "min", xs.toArray(new Expr[0])));
    if (cond == null) {
      throw new XcspException(c.name + " without condition");
    }
    // max(xs) = v with v a variable: the variable is the result
    if (cond.op.equals("eq")
        && cond.operand.kind == Expr.Kind.VAR
        && !cond.operand.var.bool
        && xs.size() > 1) {
      ec.post(Expr.op("eq", cond.operand, Expr.op(max ? "max" : "min", xs.toArray(new Expr[0]))));
      return;
    }
    post(e, cond);
  }

  private void element(Elem c, List<Expr> args, int rest) {
    Elem value = c.child("value");
    Condition cond = condition(c, args, rest);
    Expr v = null;
    if (value != null) {
      List<Expr> vs = items(value.text.toString(), args, rest);
      v = vs.get(0);
    }
    Elem matrix = c.child("matrix");
    Elem index = c.child("index");
    if (matrix != null) {
      List<List<Expr>> rows = matrix(matrix, args, rest);
      List<Expr> idx = items(index.text.toString(), args, rest);
      int startRow = Integer.parseInt(matrix.attrs.getOrDefault("startRowIndex", "0"));
      int startCol = Integer.parseInt(matrix.attrs.getOrDefault("startColIndex", "0"));
      int cols = rows.get(0).size();
      List<Expr> flat = new ArrayList<>();
      for (List<Expr> row : rows) {
        flat.addAll(row);
      }
      // flat index (i - startRow) * cols + (j - startCol), with each index in its range
      FznVar i = ec.var(idx.get(0));
      FznVar j = ec.var(idx.get(1));
      m.restrict(i, Dom.range(startRow, (long) startRow + rows.size() - 1));
      m.restrict(j, Dom.range(startCol, (long) startCol + cols - 1));
      if (m.inconsistent) {
        // an index has no value in its range, and the domains of i and j were left as they were
        return;
      }
      if (allConstant(flat) && (long) i.dom.size() * j.dom.size() <= TABLE_ELEMENT_LIMIT) {
        // a constant matrix is a table on (i, j, value), domain consistent as MiniZinc posts it
        matrixTable(flat, cols, i, startRow, j, startCol, v, cond);
        return;
      }
      Lin f = new Lin();
      f.add(i, cols);
      f.add(j, 1);
      f.c = -(long) startRow * cols - startCol;
      elementPost(flat, m.var(f), 0, v, cond);
      return;
    }
    List<Expr> xs = mainList(c, args, rest);
    int start =
        Integer.parseInt(
            c.child("list") == null ? "0" : c.child("list").attrs.getOrDefault("startIndex", "0"));
    if (index == null) {
      // member: v is one of the items
      if (v == null) {
        throw new XcspException("element without index and value");
      }
      if (allConstant(xs)) {
        long[] vals = constants(xs);
        ec.post(Expr.op("in", v, Expr.op("set", xs.toArray(new Expr[0]))));
        if (vals.length == 0) {
          m.fail();
        }
        return;
      }
      m.constraint("jacop_member_int(" + array(xs) + "," + ec.atom(v) + ")");
      return;
    }
    String rank = index.attrs.getOrDefault("rank", "any");
    if (!rank.equals("any")) {
      throw new XcspException("element with rank " + rank);
    }
    FznVar i = ec.var(items(index.text.toString(), args, rest).get(0));
    elementPost(xs, i, start, v, cond);
  }

  // the most cells of a constant matrix posted as a table
  private static final long TABLE_ELEMENT_LIMIT = 1_000_000;

  private void matrixTable(
      List<Expr> flat,
      int cols,
      FznVar i,
      int startRow,
      FznVar j,
      int startCol,
      Expr v,
      Condition cond) {
    long[] vals = constants(flat);
    FznVar result;
    if (v != null && v.kind == Expr.Kind.VAR && !v.var.bool) {
      result = v.var;
    } else {
      long lo = Long.MAX_VALUE;
      long hi = Long.MIN_VALUE;
      for (long x : vals) {
        lo = Math.min(lo, x);
        hi = Math.max(hi, x);
      }
      result = m.aux(lo, hi);
    }
    int[] cells = new int[(int) (3 * i.dom.size() * j.dom.size())];
    int n = 0;
    for (long a : i.dom.values()) {
      for (long b : j.dom.values()) {
        long x = vals[(int) ((a - startRow) * cols + (b - startCol))];
        if (result.dom.contains(x)) {
          cells[n++] = (int) a;
          cells[n++] = (int) b;
          cells[n++] = (int) x;
        }
      }
    }
    if (n == 0) {
      m.fail();
      return;
    }
    Table t = Table.of(java.util.Arrays.copyOf(cells, n), n, 3, false);
    List<Expr> scope = List.of(Expr.of(i), Expr.of(j), Expr.of(result));
    t = supported(scope, t);
    if (t == null) {
      return;
    }
    m.constraint("jacop_table_int(" + array(scope) + "," + tableParam(t, 0) + ")");
    if (v != null && result != v.var) {
      m.post("eq", ExprCompiler.diff(Lin.of(result), ec.lin(v)));
    }
    if (cond != null) {
      post(result, cond);
    }
  }

  private void elementPost(List<Expr> xs, FznVar i, int start, Expr v, Condition cond) {
    m.restrict(i, Dom.range(start, (long) start + xs.size() - 1));
    FznVar result;
    if (v != null && v.kind == Expr.Kind.VAR && !v.var.bool) {
      result = v.var;
    } else {
      long lo = Long.MAX_VALUE;
      long hi = Long.MIN_VALUE;
      for (Expr x : xs) {
        Lin l = ec.lin(x);
        lo = Math.min(lo, l.min());
        hi = Math.max(hi, l.max());
      }
      result = m.aux(lo, hi);
      result.defined = true;
    }
    if (allConstant(xs)) {
      // array_int_element is 1-based: the index is shifted
      Lin shifted = Lin.of(i);
      shifted.c = 1L - start;
      FznVar s = m.var(shifted);
      m.constraint(
          "array_int_element(" + s.name + "," + array(xs) + "," + result.name + ")",
          result.introduced ? result : null);
    } else {
      m.constraint(
          "jacop_array_var_int_element_nonshifted("
              + i.name
              + ","
              + array(xs)
              + ","
              + result.name
              + ","
              + start
              + ")",
          result.introduced ? result : null);
    }
    if (v != null && result != v.var) {
      m.post("eq", ExprCompiler.diff(Lin.of(result), ec.lin(v)));
    }
    if (cond != null) {
      post(result, cond);
    }
  }

  private void channel(Elem c, List<Expr> args, int rest) {
    List<Elem> lists = c.all("list");
    if (lists.isEmpty()) {
      List<Expr> xs = mainList(c, args, rest);
      inverse(xs, 0, xs, 0);
      return;
    }
    List<Expr> x = items(lists.get(0).text.toString(), args, rest);
    int sx = Integer.parseInt(lists.get(0).attrs.getOrDefault("startIndex", "0"));
    Elem value = c.child("value");
    if (value != null) {
      // x[i] = 1 iff v = i (x 0/1)
      Expr v = items(value.text.toString(), args, rest).get(0);
      FznVar vv = ec.var(v);
      m.restrict(vv, Dom.range(sx, (long) sx + x.size() - 1));
      List<String> bs = new ArrayList<>();
      for (Expr b : x) {
        bs.add(m.boolAtom(ec.lit(b)));
      }
      m.constraint(
          "jacop_channel("
              + vv.name
              + ","
              + FznModel.list(bs)
              + ","
              + sx
              + ".."
              + (sx + x.size() - 1)
              + ")");
      return;
    }
    if (lists.size() == 1) {
      inverse(x, sx, x, sx);
      return;
    }
    List<Expr> y = items(lists.get(1).text.toString(), args, rest);
    int sy = Integer.parseInt(lists.get(1).attrs.getOrDefault("startIndex", "0"));
    if (x.size() == y.size()) {
      inverse(x, sx, y, sy);
      return;
    }
    // x[i] = j -> y[j] = i, with x shorter than y
    for (int i = 0; i < x.size(); i++) {
      FznVar xi = ec.var(x.get(i));
      elementPost(y, xi, sy, Expr.of((long) i + sx), null);
    }
  }

  private void inverse(List<Expr> x, int sx, List<Expr> y, int sy) {
    for (Expr e : x) {
      m.restrict(ec.var(e), Dom.range(sy, (long) sy + y.size() - 1));
    }
    for (Expr e : y) {
      m.restrict(ec.var(e), Dom.range(sx, (long) sx + x.size() - 1));
    }
    m.constraint("jacop_assignment(" + array(x) + "," + array(y) + "," + sx + "," + sy + ")");
  }

  private List<List<Expr>> tuples(Elem e, List<Expr> args, int rest) {
    String t = e.trimmed();
    List<List<Expr>> rows = new ArrayList<>();
    if (!t.startsWith("(")) {
      for (Expr x : items(t, args, rest)) {
        rows.add(List.of(x));
      }
      return rows;
    }
    int i = 0;
    while (i < t.length()) {
      int open = t.indexOf('(', i);
      if (open < 0) {
        break;
      }
      int depth = 0;
      int close = open;
      for (; close < t.length(); close++) {
        char ch = t.charAt(close);
        if (ch == '(') {
          depth++;
        } else if (ch == ')') {
          depth--;
          if (depth == 0) {
            break;
          }
        }
      }
      rows.add(splitTuple(t.substring(open + 1, close), args, rest));
      i = close + 1;
    }
    return rows;
  }

  private List<Expr> splitTuple(String s, List<Expr> args, int rest) {
    List<Expr> out = new ArrayList<>();
    int depth = 0;
    int start = 0;
    for (int i = 0; i <= s.length(); i++) {
      char ch = i < s.length() ? s.charAt(i) : ',';
      if (ch == '(') {
        depth++;
      } else if (ch == ')') {
        depth--;
      } else if (ch == ',' && depth == 0) {
        out.addAll(items(s.substring(start, i), args, rest));
        start = i + 1;
      }
    }
    return out;
  }

  private void noOverlap(Elem c, List<Expr> args, int rest) {
    boolean zeroIgnored = !"false".equals(c.attrs.getOrDefault("zeroIgnored", "true"));
    List<List<Expr>> origins = tuples(c.child("origins"), args, rest);
    List<List<Expr>> lengths = tuples(c.child("lengths"), args, rest);
    int k = origins.get(0).size();
    int n = origins.size();
    if (k == 1) {
      List<Expr> s = new ArrayList<>();
      List<Expr> d = new ArrayList<>();
      long minLength = Long.MAX_VALUE;
      for (int i = 0; i < n; i++) {
        s.add(origins.get(i).get(0));
        d.add(lengths.get(i).get(0));
        minLength = Math.min(minLength, ec.lin(lengths.get(i).get(0)).min());
      }
      if (minLength < 0) {
        throw new XcspException("noOverlap with negative lengths");
      }
      List<Expr> ones = new ArrayList<>();
      List<Expr> zeros = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        ones.add(Expr.of(1));
        zeros.add(Expr.of(0));
      }
      if (zeroIgnored || minLength > 0) {
        m.constraint("jacop_cumulative(" + array(s) + "," + array(d) + "," + array(ones) + ",1)");
      } else {
        m.constraint(
            "jacop_diff2_strict("
                + array(s)
                + ","
                + array(zeros)
                + ","
                + array(d)
                + ","
                + array(ones)
                + ")");
      }
      return;
    }
    if (k == 2) {
      List<Expr> x = new ArrayList<>();
      List<Expr> y = new ArrayList<>();
      List<Expr> dx = new ArrayList<>();
      List<Expr> dy = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        x.add(origins.get(i).get(0));
        y.add(origins.get(i).get(1));
        dx.add(lengths.get(i).get(0));
        dy.add(lengths.get(i).get(1));
      }
      m.constraint(
          (zeroIgnored ? "jacop_list_diff2(" : "jacop_diff2_strict(")
              + array(x)
              + ","
              + array(y)
              + ","
              + array(dx)
              + ","
              + array(dy)
              + ")");
      return;
    }
    List<Expr> pos = new ArrayList<>();
    List<Expr> size = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      pos.addAll(origins.get(i));
      size.addAll(lengths.get(i));
    }
    m.constraint(
        "jacop_diffn_k(" + array(pos) + "," + array(size) + "," + k + "," + (!zeroIgnored) + ")");
  }

  private void cumulative(Elem c, List<Expr> args, int rest) {
    List<Expr> s = list(c, "origins", args, rest);
    List<Expr> d = list(c, "lengths", args, rest);
    List<Expr> h = list(c, "heights", args, rest);
    List<Expr> ends = list(c, "ends", args, rest);
    Condition cond = condition(c, args, rest);
    if (ends != null) {
      for (int i = 0; i < s.size(); i++) {
        ec.post(Expr.op("eq", Expr.op("add", s.get(i), d.get(i)), ends.get(i)));
      }
    }
    String cap;
    switch (cond.op) {
      case "le" -> cap = ec.atom(cond.operand);
      case "lt" -> cap = m.intAtom(ExprCompiler.diff(ec.lin(cond.operand), Lin.constant(1)));
      default -> throw new XcspException("cumulative with condition " + cond.op);
    }
    m.constraint(
        "jacop_cumulative(" + array(s) + "," + array(d) + "," + array(h) + "," + cap + ")");
  }

  private void circuit(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    Elem l = c.child("list");
    int start = Integer.parseInt(l == null ? "0" : l.attrs.getOrDefault("startIndex", "0"));
    List<Expr> size = list(c, "size", args, rest);
    int n = xs.size();
    List<FznVar> vs = new ArrayList<>();
    for (Expr x : xs) {
      FznVar v = ec.var(x);
      m.restrict(v, Dom.range(start, (long) start + n - 1));
      vs.add(v);
    }
    // subcircuit with 1-based successors
    List<String> shifted = new ArrayList<>();
    for (FznVar v : vs) {
      Lin s = Lin.of(v);
      s.c = 1L - start;
      shifted.add(m.intAtom(s));
    }
    m.constraint("jacop_subcircuit(" + FznModel.list(shifted) + ")");
    // the number of non-loops: at least 2 (XCSP3 circuit has at least one cycle), or the size
    Lin loops = new Lin();
    for (int i = 0; i < n; i++) {
      loops.add(m.lin(m.valueLit(vs.get(i), (long) i + start).not()), 1);
    }
    if (size == null) {
      m.post("ge", ExprCompiler.diff(loops, Lin.constant(2)));
    } else {
      m.post("eq", ExprCompiler.diff(loops, ec.lin(size.get(0))));
    }
  }

  /** A transition (from, value, to) of an automaton or MDD. */
  record Transition(String from, long value, String to) {}

  private List<Transition> transitions(Elem c) {
    String t = c.child("transitions").trimmed();
    List<Transition> out = new ArrayList<>();
    int i = 0;
    while (i < t.length()) {
      int open = t.indexOf('(', i);
      if (open < 0) {
        break;
      }
      int close = t.indexOf(')', open);
      String[] p = t.substring(open + 1, close).split(",");
      String v = p[1].trim();
      Integer sym = symbols.get(v);
      out.add(new Transition(p[0].trim(), sym != null ? sym : bound(v), p[2].trim()));
      i = close + 1;
    }
    return out;
  }

  private void mdd(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    Elem key = c.child("transitions");
    String[] params = mddCache.get(key);
    if (params == null) {
      params = mddParams(cachedTransitions(c));
      mddCache.put(key, params);
      transitionCache.remove(key);
    }
    m.constraint(
        "jacop_mdd("
            + array(xs)
            + ","
            + params[0]
            + ","
            + params[1]
            + ","
            + params[2]
            + ","
            + params[3]
            + ")");
  }

  private String[] mddParams(List<Transition> ts) {
    // nodes: root has no incoming arc, the terminal no outgoing one
    final Map<String, Integer> number = new LinkedHashMap<>();
    Map<String, List<Transition>> out = new HashMap<>();
    Set<String> hasIn = new java.util.HashSet<>();
    for (Transition t : ts) {
      out.computeIfAbsent(t.from, k -> new ArrayList<>()).add(t);
      out.computeIfAbsent(t.to, k -> new ArrayList<>());
      hasIn.add(t.to);
    }
    String root = null;
    String terminal = null;
    for (String s : out.keySet()) {
      if (!hasIn.contains(s)) {
        if (root != null) {
          throw new XcspException("mdd with several roots");
        }
        root = s;
      }
      if (out.get(s).isEmpty()) {
        if (terminal != null) {
          throw new XcspException("mdd with several terminals");
        }
        terminal = s;
      }
    }
    // breadth-first from the root: levels, nodes numbered 1..N, terminal 0
    Map<String, Integer> level = new HashMap<>();
    List<String> order = new ArrayList<>();
    level.put(root, 1);
    order.add(root);
    for (int k = 0; k < order.size(); k++) {
      String s = order.get(k);
      for (Transition t : out.get(s)) {
        if (!level.containsKey(t.to)) {
          level.put(t.to, level.get(s) + 1);
          order.add(t.to);
        }
      }
    }
    order.remove(terminal);
    for (int k = 0; k < order.size(); k++) {
      number.put(order.get(k), k + 1);
    }
    number.put(terminal, 0);
    String[] params;
    {
      // edges grouped by (from, to) with their value sets
      Map<Long, List<Long>> edges = new java.util.TreeMap<>();
      for (Transition t : ts) {
        long k = ((long) number.get(t.from) << 32) | number.get(t.to);
        edges.computeIfAbsent(k, z -> new ArrayList<>()).add(t.value);
      }
      long[] lv = new long[order.size()];
      for (int k = 0; k < order.size(); k++) {
        lv[k] = level.get(order.get(k));
      }
      StringBuilder from = new StringBuilder("[");
      StringBuilder to = new StringBuilder("[");
      StringBuilder label = new StringBuilder("[");
      boolean first = true;
      for (Map.Entry<Long, List<Long>> e : edges.entrySet()) {
        if (!first) {
          from.append(',');
          to.append(',');
          label.append(',');
        }
        first = false;
        from.append(e.getKey() >>> 32);
        to.append(e.getKey() & 0xffffffffL);
        long[] v = e.getValue().stream().mapToLong(Long::longValue).toArray();
        label.append(Dom.of(v, v.length).toFzn());
      }
      params =
          new String[] {
            m.paramName("MDDlevel"),
            m.paramName("MDDfrom"),
            m.paramName("MDDlabel"),
            m.paramName("MDDto")
          };
      try {
        Writer w = m.params();
        w.write("array [1.." + lv.length + "] of int: " + params[0] + " = " + ints(lv) + ";\n");
        w.write("array [1.." + edges.size() + "] of int: " + params[1] + " = " + from + "];\n");
        w.write(
            "array [1.." + edges.size() + "] of set of int: " + params[2] + " = " + label + "];\n");
        w.write("array [1.." + edges.size() + "] of int: " + params[3] + " = " + to + "];\n");
      } catch (IOException e) {
        throw new UncheckedIOException(e);
      }
    }
    return params;
  }

  private final Map<Elem, List<Transition>> transitionCache = new java.util.IdentityHashMap<>();
  private final Map<Elem, String[]> mddCache = new java.util.IdentityHashMap<>();

  private List<Transition> cachedTransitions(Elem c) {
    return transitionCache.computeIfAbsent(c.child("transitions"), k -> transitions(c));
  }

  private void regular(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    List<Transition> ts = cachedTransitions(c);
    String start = c.child("start").trimmed();
    String[] finals = c.child("final").trimmed().split("\\s+");
    Map<String, Integer> states = new LinkedHashMap<>();
    for (Transition t : ts) {
      states.putIfAbsent(t.from, states.size() + 1);
      states.putIfAbsent(t.to, states.size() + 1);
    }
    states.putIfAbsent(start, states.size() + 1);
    for (String f : finals) {
      if (!f.isEmpty()) {
        states.putIfAbsent(f, states.size() + 1);
      }
    }
    long lo = Long.MAX_VALUE;
    long hi = Long.MIN_VALUE;
    for (Transition t : ts) {
      lo = Math.min(lo, t.value);
      hi = Math.max(hi, t.value);
    }
    for (Expr x : xs) {
      Lin l = ec.lin(x);
      lo = Math.min(lo, l.min());
      hi = Math.max(hi, l.max());
    }
    int q = states.size();
    Map<Long, List<Integer>> targets = new HashMap<>();
    boolean nfa = false;
    for (Transition t : ts) {
      long k = (long) states.get(t.from) * (hi - lo + 1) + (t.value - lo);
      List<Integer> l = targets.computeIfAbsent(k, z -> new ArrayList<>());
      int to = states.get(t.to);
      if (!l.contains(to)) {
        l.add(to);
      }
      nfa |= l.size() > 1;
    }
    StringBuilder f = new StringBuilder("{");
    boolean first = true;
    for (String s : finals) {
      if (s.isEmpty()) {
        continue;
      }
      if (!first) {
        f.append(',');
      }
      first = false;
      f.append(states.get(s));
    }
    f.append('}');
    if ((hi - lo + 1) * q > 50_000_000L) {
      throw new XcspException("regular automaton too large");
    }
    StringBuilder d = new StringBuilder("[");
    first = true;
    for (int s = 1; s <= q; s++) {
      for (long v = lo; v <= hi; v++) {
        if (!first) {
          d.append(',');
        }
        first = false;
        List<Integer> l = targets.get((long) s * (hi - lo + 1) + (v - lo));
        if (nfa) {
          d.append('{');
          if (l != null) {
            for (int k = 0; k < l.size(); k++) {
              if (k > 0) {
                d.append(',');
              }
              d.append(l.get(k));
            }
          }
          d.append('}');
        } else {
          d.append(l == null ? 0 : l.get(0));
        }
      }
    }
    d.append(']');
    String name = m.paramName("REG");
    try {
      m.params()
          .write(
              "array [1.."
                  + (q * (hi - lo + 1))
                  + "] of "
                  + (nfa ? "set of int" : "int")
                  + ": "
                  + name
                  + " = "
                  + d
                  + ";\n");
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    }
    if (nfa) {
      m.constraint(
          "jacop_regular_nfa("
              + array(xs)
              + ","
              + q
              + ","
              + lo
              + ".."
              + hi
              + ","
              + name
              + ","
              + states.get(start)
              + ","
              + f
              + ",1,"
              + lo
              + ","
              + (hi - lo + 1)
              + ")");
    } else {
      m.constraint(
          "jacop_regular("
              + array(xs)
              + ","
              + q
              + ","
              + (hi - lo + 1)
              + ","
              + name
              + ","
              + states.get(start)
              + ","
              + f
              + ","
              + lo
              + ")");
    }
  }

  private void instantiation(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    List<Expr> vs = list(c, "values", args, rest);
    for (int i = 0; i < xs.size(); i++) {
      ec.post(Expr.op("eq", xs.get(i), vs.get(i)));
    }
  }

  private void precedence(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    List<Expr> vs = list(c, "values", args, rest);
    boolean covered =
        "true".equals(c.child("values") == null ? null : c.child("values").attr("covered"))
            || "true".equals(c.attr("covered"));
    long[] v;
    if (vs == null) {
      Dom all = Dom.EMPTY;
      for (Expr x : xs) {
        all = all.union(ec.var(x).dom);
      }
      v = all.values();
    } else {
      v = constants(vs);
    }
    m.constraint("jacop_value_precede_chain_int(" + ints(v) + "," + array(xs) + ")");
    if (covered && v.length > 0) {
      List<Lit> any = new ArrayList<>();
      for (Expr x : xs) {
        any.add(ec.lit(Expr.op("eq", x, Expr.of(v[v.length - 1]))));
      }
      m.clause(any);
    }
  }

  private void binPacking(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    long[] sizes = constants(list(c, "sizes", args, rest));
    Condition cond = condition(c, args, rest);
    List<Expr> limits = list(c, "limits", args, rest);
    List<Expr> loads = list(c, "loads", args, rest);
    long lo = Long.MAX_VALUE;
    long hi = Long.MIN_VALUE;
    for (Expr x : xs) {
      FznVar v = ec.var(x);
      lo = Math.min(lo, v.min());
      hi = Math.max(hi, v.max());
    }
    long total = 0;
    for (long s : sizes) {
      total += s;
    }
    if (loads != null) {
      for (Expr x : xs) {
        m.restrict(ec.var(x), Dom.range(0, loads.size() - 1L));
      }
      m.constraint(
          "jacop_bin_packing(" + array(xs) + "," + array(loads) + "," + ints(sizes) + ",0)");
      return;
    }
    if (limits != null) {
      for (Expr x : xs) {
        m.restrict(ec.var(x), Dom.range(0, limits.size() - 1L));
      }
      if (allConstant(limits)) {
        m.constraint(
            "jacop_bin_packing_capacity("
                + array(xs)
                + ","
                + ints(constants(limits))
                + ","
                + ints(sizes)
                + ",0)");
        return;
      }
      List<Expr> load = new ArrayList<>();
      for (int b = 0; b < limits.size(); b++) {
        FznVar l = m.aux(0, total);
        load.add(Expr.of(l));
        m.post("le", ExprCompiler.diff(Lin.of(l), ec.lin(limits.get(b))));
      }
      m.constraint(
          "jacop_bin_packing(" + array(xs) + "," + array(load) + "," + ints(sizes) + ",0)");
      return;
    }
    if (cond.op.equals("le") || cond.op.equals("lt")) {
      if (cond.operand.kind == Expr.Kind.INT) {
        long cap = cond.operand.value - (cond.op.equals("lt") ? 1 : 0);
        long[] caps = new long[(int) (hi - lo + 1)];
        java.util.Arrays.fill(caps, cap);
        m.constraint(
            "jacop_bin_packing_capacity("
                + array(xs)
                + ","
                + ints(caps)
                + ","
                + ints(sizes)
                + ","
                + lo
                + ")");
        return;
      }
    }
    // the condition holds on each bin that receives an item
    List<Expr> load = new ArrayList<>();
    for (long b = lo; b <= hi; b++) {
      load.add(Expr.of(m.aux(0, total)));
    }
    m.constraint(
        "jacop_bin_packing(" + array(xs) + "," + array(load) + "," + ints(sizes) + "," + lo + ")");
    for (long b = lo; b <= hi; b++) {
      List<Lit> used = new ArrayList<>();
      for (Expr x : xs) {
        used.add(ec.lit(Expr.op("eq", x, Expr.of(b))));
      }
      Lit u = m.or(used);
      Lit ok = condLit(ec.lin(load.get((int) (b - lo))), cond);
      m.clause(List.of(u.not(), ok));
    }
  }

  private Lit condLit(Lin value, Condition c) {
    if (c.op.equals("in") || c.op.equals("notin")) {
      return ec.lit(Expr.op(c.op, Expr.of(m.var(value)), c.operand));
    }
    return m.lit(c.op, ExprCompiler.diff(value, ec.lin(c.operand)));
  }

  private void knapsack(Elem c, List<Expr> args, int rest) {
    List<Expr> xs = mainList(c, args, rest);
    long[] w = constants(list(c, "weights", args, rest));
    long[] p = constants(list(c, "profits", args, rest));
    List<Elem> conds = c.all("condition");
    Elem limit = c.child("limit");
    Lin weight = new Lin();
    Lin profit = new Lin();
    for (int i = 0; i < xs.size(); i++) {
      weight.add(ec.lin(xs.get(i)), w[i]);
      profit.add(ec.lin(xs.get(i)), p[i]);
    }
    if (limit != null) {
      // XCSP3-core 3.2: <limit> bounds the weight, the condition is on the profit
      m.post(
          "le", ExprCompiler.diff(weight, ec.lin(items(limit.text.toString(), args, rest).get(0))));
      post(profit, condition(conds.get(0).trimmed(), args, rest));
      return;
    }
    if (conds.size() == 2) {
      post(weight, condition(conds.get(0).trimmed(), args, rest));
      post(profit, condition(conds.get(1).trimmed(), args, rest));
      return;
    }
    throw new XcspException("knapsack without limit or two conditions");
  }

  private void slide(Elem c) {
    boolean circular = "true".equals(c.attr("circular"));
    List<Elem> lists = c.all("list");
    Elem template = null;
    for (Elem e : c.children) {
      if (!e.name.equals("list")) {
        template = e;
      }
    }
    List<List<Expr>> ls = new ArrayList<>();
    int[] offsets = new int[lists.size()];
    int[] collects = new int[lists.size()];
    for (int i = 0; i < lists.size(); i++) {
      ls.add(items(lists.get(i).text.toString(), null, 0));
      offsets[i] = Integer.parseInt(lists.get(i).attrs.getOrDefault("offset", "1"));
      collects[i] = Integer.parseInt(lists.get(i).attrs.getOrDefault("collect", "1"));
    }
    if (lists.size() == 1) {
      collects[0] = maxParameter(template) + 1;
    }
    int[] idx = new int[lists.size()];
    while (true) {
      if (!circular && idx[0] + collects[0] > ls.get(0).size()) {
        break;
      }
      boolean last = idx[0] + offsets[0] >= ls.get(0).size();
      List<Expr> scope = new ArrayList<>();
      for (int i = 0; i < lists.size(); i++) {
        for (int j = 0; j < collects[i]; j++) {
          scope.add(ls.get(i).get((idx[i] + j) % ls.get(i).size()));
        }
        idx[i] += offsets[i];
      }
      post(template, scope, maxParameter(template) + 1);
      if (last) {
        break;
      }
    }
  }

  // ------------------------------------------------------------------ objectives

  private void objectives(XMLStreamReader r) throws XMLStreamException {
    while (true) {
      int ev = r.next();
      if (ev == XMLStreamConstants.END_ELEMENT) {
        return;
      }
      if (ev != XMLStreamConstants.START_ELEMENT) {
        continue;
      }
      Elem e = elem(r);
      if (objective != null) {
        throw new XcspException("several objectives");
      }
      optimization = true;
      minimize = e.name.equals("minimize");
      String t = e.attrs.getOrDefault("type", "expression");
      Lin value;
      if (t.equals("expression")) {
        List<Expr> es = items(e.text.toString(), null, 0);
        if (es.size() != 1) {
          throw new XcspException("objective expression expected");
        }
        value = ec.lin(es.get(0));
      } else {
        List<Expr> xs = mainList(e, null, 0);
        List<Expr> coeffs = list(e, "coeffs", null, 0);
        switch (t) {
          case "sum" -> value = sumOf(xs, coeffs);
          case "maximum", "minimum" -> {
            List<Expr> terms = new ArrayList<>();
            for (int i = 0; i < xs.size(); i++) {
              terms.add(coeffs == null ? xs.get(i) : Expr.op("mul", coeffs.get(i), xs.get(i)));
            }
            value =
                ec.lin(Expr.op(t.equals("maximum") ? "max" : "min", terms.toArray(new Expr[0])));
          }
          case "nValues" -> value = nValuesOf(xs, null);
          case "product" -> {
            List<Expr> terms = new ArrayList<>(xs);
            value = ec.lin(Expr.op("mul", terms.toArray(new Expr[0])));
          }
          default -> throw new XcspException("objective of type " + t);
        }
      }
      objective = m.var(value);
    }
  }
}
