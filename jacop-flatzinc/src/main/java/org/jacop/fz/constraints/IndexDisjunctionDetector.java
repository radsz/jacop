/*
 * IndexDisjunctionDetector.java
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
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import org.jacop.api.VarMap;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Index variables that only pick a position. An index variable {@code k} used only by element
 * constraints {@code r_i = A_i[k]}, whose results {@code r_i} are used only by one linear relation
 * {@code C(r_1, ..., r_m)}, says that C holds at some position: the constraints are the disjunction
 * {@code OR_p C(A_1[p], ..., A_m[p])} over the values p of k, with k and the r_i existentially
 * quantified. They are replaced by a clause over half-reified relations {@code b_p -> C(A_1[p],
 * ...)}, the decomposition MiniZinc writes for {@code exists(p in P)(C(...))}; k and the r_i are
 * left out of the model and get their values when a solution is printed: k the first position where
 * C holds, r_i the elements there.
 *
 * <p>XCSP3 translations write existential quantifiers this way: Antichain2 ("no set dominates
 * another one") has, for every pair of rows i &lt; j, {@code x[i][xmin] < x[j][xmin]} and {@code
 * x[i][xmax] > x[j][xmax]} with free indices xmin and xmax, 40,000 elements in all. Through the
 * element constraints an LCG explanation of a pair names k and the bounds of the 12 elements; over
 * the disjunction it names the six comparisons, and propagation reaches the last open position at
 * once. Antichain2-100-3-10 is proved infeasible in 13 s instead of 156 s.
 *
 * <p>Left as they are: a k or r_i of the solve item or the search annotation, k with a value
 * outside an array, elements over arrays of more than {@code org.jacop.fz.indexDisjunction.max}
 * (default 64) positions, and models searched for all solutions or under --proof or presolve (the
 * caller decides). On by default; {@code -Dorg.jacop.fz.indexDisjunction=false} turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class IndexDisjunctionDetector implements ParserTreeConstants {
  private static final Set<String> KINDS =
      Set.of(
          "array_int_element", "array_var_int_element", "jacop_array_var_int_element_nonshifted");

  private static final int MAX_POSITIONS =
      Integer.getInteger("org.jacop.fz.indexDisjunction.max", 64);

  private final Support support;

  private final ConstraintFncs fncs;

  private final Set<SimpleNode> frozen;

  private final Set<IntVar> solveItem;

  /** An element r = A[k], with A[j] the element at index value first + j. */
  private record Element(ASTConstElem node, IntVar k, IntVar[] a, IntVar r, int first) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Element e
          && node == e.node
          && k == e.k
          && Arrays.equals(a, e.a)
          && r == e.r
          && first == e.first;
    }

    @Override
    public int hashCode() {
      return Objects.hash(
          System.identityHashCode(node),
          System.identityHashCode(k),
          Arrays.hashCode(a),
          System.identityHashCode(r),
          first);
    }

    @Override
    public String toString() {
      return "Element[" + r + " = " + Arrays.toString(a) + "[" + k + "], first " + first + "]";
    }
  }

  /** A linear relation sum(w * x) op c over results of elements, op one of Support.EQ/NE/LE. */
  private record Relation(ASTConstElem node, int op, int[] w, IntVar[] x, int c) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Relation e
          && node == e.node
          && op == e.op
          && Arrays.equals(w, e.w)
          && Arrays.equals(x, e.x)
          && c == e.c;
    }

    @Override
    public int hashCode() {
      return Objects.hash(
          System.identityHashCode(node), op, Arrays.hashCode(w), Arrays.hashCode(x), c);
    }

    @Override
    public String toString() {
      return "Relation["
          + Arrays.toString(w)
          + " * "
          + Arrays.toString(x)
          + " op "
          + op
          + " "
          + c
          + "]";
    }
  }

  private final Map<IntVar, List<Element>> elements = new LinkedHashMap<>();

  private final Map<IntVar, Element> byResult = new IdentityHashMap<>();

  private final Map<IntVar, Relation> relationOf = new IdentityHashMap<>();

  // the number of constraints each variable occurs in
  private final Map<IntVar, Integer> uses = new IdentityHashMap<>();

  private final Set<SimpleNode> replaced = new HashSet<>();

  private final Set<Var> eliminated = Collections.newSetFromMap(new IdentityHashMap<>());

  private final Values values = new Values();

  /**
   * The index variables and results that were left out of the model, with what gives them their
   * values in a solution.
   */
  public static final class Values {

    private final List<IntVar> indices = new ArrayList<>();
    private final List<int[]> positions = new ArrayList<>();
    private final List<IntVar[][]> columns = new ArrayList<>();
    private final List<IntVar[]> results = new ArrayList<>();
    private final List<int[]> weights = new ArrayList<>();
    private final List<int[]> relations = new ArrayList<>();

    void add(IntVar k, int[] p, IntVar[][] a, IntVar[] r, int[] w, int op, int c) {
      indices.add(k);
      positions.add(p);
      columns.add(a);
      results.add(r);
      weights.add(w);
      relations.add(new int[] {op, c});
    }

    /**
     * It tells if nothing was left out.
     *
     * @return true if no index variable was replaced.
     */
    public boolean isEmpty() {
      return indices.isEmpty();
    }

    /**
     * The index variables and results left out.
     *
     * @return the variables.
     */
    public List<IntVar> variables() {
      List<IntVar> all = new ArrayList<>(indices);
      for (IntVar[] r : results) {
        Collections.addAll(all, r);
      }
      return all;
    }

    /**
     * Adds to the map the values of the index variables and results in the current solution: an
     * index takes the first of its values where the relation holds, each result the element there.
     * An element whose variable is in the map takes its value from there; the others are fixed in a
     * solution.
     *
     * @param out the values of variables the model no longer has.
     */
    public void addValues(Map<Var, Integer> out) {
      for (int e = 0; e < indices.size(); e++) {
        int[] p = positions.get(e);
        IntVar[][] a = columns.get(e);
        int[] w = weights.get(e);
        int op = relations.get(e)[0];
        int c = relations.get(e)[1];
        int at = 0;
        for (int j = 0; j < p.length; j++) {
          long sum = 0;
          for (int i = 0; i < w.length; i++) {
            sum += (long) w[i] * value(a[i][j], out);
          }
          if (holds(op, sum, c)) {
            at = j;
            break;
          }
        }
        out.put(indices.get(e), p[at]);
        IntVar[] r = results.get(e);
        for (int i = 0; i < r.length; i++) {
          out.put(r[i], value(a[i][at], out));
        }
      }
    }

    static boolean holds(int op, long sum, long c) {
      return switch (op) {
        case Support.EQ -> sum == c;
        case Support.NE -> sum != c;
        default -> sum <= c;
      };
    }

    private static int value(IntVar x, Map<Var, Integer> out) {
      Integer known = out.get(x);
      return known != null ? known : x.min();
    }

    /**
     * A copy over the variables of a copied store.
     *
     * @param map the variable map of the copy.
     * @return the copy.
     */
    public Values copy(VarMap map) {
      Values v = new Values();
      for (int e = 0; e < indices.size(); e++) {
        IntVar[][] a = columns.get(e);
        IntVar[][] ca = new IntVar[a.length][];
        for (int i = 0; i < a.length; i++) {
          ca[i] = map.get(a[i]);
        }
        int[] rel = relations.get(e);
        v.add(
            map.get(indices.get(e)),
            positions.get(e),
            ca,
            map.get(results.get(e)),
            weights.get(e),
            rel[0],
            rel[1]);
      }
      return v;
    }
  }

  /**
   * It creates the detector.
   *
   * @param support the support of the FlatZinc front end.
   * @param fncs the constraint functions that post the clauses.
   * @param frozen constraint nodes that earlier detectors replaced; their variables count as used.
   * @param solveItem the variables of the solve item and its search annotation.
   */
  public IndexDisjunctionDetector(
      Support support, ConstraintFncs fncs, Set<SimpleNode> frozen, Set<IntVar> solveItem) {
    this.support = support;
    this.fncs = fncs;
    this.frozen = frozen;
    this.solveItem = solveItem;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.indexDisjunction is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.indexDisjunction"));
  }

  /**
   * The constraint nodes that are not posted: the elements and their relations.
   *
   * @return the replaced nodes.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  /**
   * The index variables and results left without constraints.
   *
   * @return the eliminated variables.
   */
  public Set<Var> eliminated() {
    return eliminated;
  }

  /**
   * The eliminated variables with what gives them values when a solution is printed.
   *
   * @return the values, empty if nothing was replaced.
   */
  public Values values() {
    return values;
  }

  /**
   * It scans the model and posts the disjunctions.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    // the index variables are of elements
    if (!support.hasConstraint(astTree, KINDS)) {
      return;
    }
    List<ASTConstElem> relations = new ArrayList<>();
    support.forEachConstraint(
        astTree,
        node -> {
          Set<IntVar> vars = Collections.newSetFromMap(new IdentityHashMap<>());
          for (int k = 0; k < node.jjtGetNumChildren(); k++) {
            variables((SimpleNode) node.jjtGetChild(k), vars);
          }
          for (IntVar v : vars) {
            uses.merge(v, frozen.contains(node) ? 2 : 1, Integer::sum);
          }
          if (frozen.contains(node)) {
            return;
          }
          if (!element(node)) {
            relations.add(node);
          }
        });
    if (elements.isEmpty()) {
      return;
    }
    for (ASTConstElem node : relations) {
      relation(node);
    }
    int disjunctions = 0;
    long literals = 0;
    for (Map.Entry<IntVar, List<Element>> e : elements.entrySet()) {
      int posted = rewrite(e.getKey(), e.getValue());
      if (posted >= 0) {
        disjunctions++;
        literals += posted;
      }
    }
    if ((support.options.debug() || support.options.searchStatistics()) && disjunctions > 0) {
      FzConsole.println(
          "%%%mzn-stat: indexDisjunctions="
              + disjunctions
              + "\n%%%mzn-stat: indexDisjunctionLiterals="
              + literals);
    }
  }

  // the disjunction of index k, or -1 if k is left as it is; the number of literals posted
  private int rewrite(IntVar k, List<Element> es) {
    // a variable declared equal to another one keeps the equality posted for the declaration,
    // which is no constraint item: the other variable would be printed from a k or r left free
    if (solveItem.contains(k)
        || support.dictionary.isDeclaredEqual(k)
        || uses.getOrDefault(k, 0) != es.size()) {
      return -1;
    }
    Relation rel = null;
    for (Element el : es) {
      Relation r = relationOf.get(el.r());
      if (r == null
          || (rel != null && r != rel)
          || solveItem.contains(el.r())
          || support.dictionary.isDeclaredEqual(el.r())
          || uses.getOrDefault(el.r(), 0) != 2) {
        return -1;
      }
      rel = r;
    }
    // every variable of the relation is the result of exactly one element of k
    Map<IntVar, Element> mine = new IdentityHashMap<>();
    for (Element el : es) {
      if (mine.put(el.r(), el) != null) {
        return -1;
      }
    }
    if (mine.size() != rel.x().length) {
      return -1;
    }
    for (IntVar x : rel.x()) {
      if (!mine.containsKey(x)) {
        return -1;
      }
    }
    // the values of k, which must select a position of every array; the element there must lie in
    // the domain of its result, which the disjunction does not state: a position with a constant
    // outside it is no position, and a variable that can leave it keeps the elements
    int[] p = new int[k.getSize()];
    int n = 0;
    values:
    for (ValueEnumeration en = k.dom().valueEnumeration(); en.hasMoreElements(); ) {
      int v = en.nextElement();
      for (Element el : es) {
        if (v < el.first() || v - (long) el.first() >= el.a().length) {
          return -1;
        }
      }
      for (Element el : es) {
        IntVar a = el.a()[v - el.first()];
        if (a.singleton() && !el.r().domain.contains(a.value())) {
          continue values;
        }
        if (!el.r().domain.contains(a.domain)) {
          return -1;
        }
      }
      p[n++] = v;
    }
    if (n == 0 || n > MAX_POSITIONS) {
      return -1;
    }
    int m = rel.x().length;
    IntVar[][] columns = new IntVar[m][n];
    for (int i = 0; i < m; i++) {
      Element el = mine.get(rel.x()[i]);
      for (int j = 0; j < n; j++) {
        columns[i][j] = el.a()[p[j] - el.first()];
      }
    }
    // the relation at each position, constants folded and equal variables joined
    List<int[]> ws = new ArrayList<>();
    List<IntVar[]> xs = new ArrayList<>();
    List<Integer> cs = new ArrayList<>();
    for (int j = 0; j < n; j++) {
      Map<IntVar, Long> terms = new LinkedHashMap<>();
      long c = rel.c();
      for (int i = 0; i < m; i++) {
        IntVar a = columns[i][j];
        if (a.singleton()) {
          c -= (long) rel.w()[i] * a.value();
        } else {
          terms.merge(a, (long) rel.w()[i], Long::sum);
        }
      }
      terms.values().removeIf(w -> w == 0);
      if (terms.isEmpty()) {
        if (Values.holds(rel.op(), 0, c)) {
          // the relation holds at this position whatever the other variables are
          ws = null;
          break;
        }
        continue;
      }
      if (c < Integer.MIN_VALUE || c > Integer.MAX_VALUE) {
        return -1;
      }
      int[] w = new int[terms.size()];
      IntVar[] x = new IntVar[terms.size()];
      int t = 0;
      for (Map.Entry<IntVar, Long> term : terms.entrySet()) {
        if (term.getValue() < Integer.MIN_VALUE || term.getValue() > Integer.MAX_VALUE) {
          return -1;
        }
        x[t] = term.getKey();
        w[t++] = (int) (long) term.getValue();
      }
      ws.add(w);
      xs.add(x);
      cs.add((int) c);
    }
    if (ws != null && ws.isEmpty()) {
      // the relation holds nowhere: the model is infeasible, which its own constraints show
      return -1;
    }
    for (Element el : es) {
      replaced.add(el.node());
    }
    replaced.add(rel.node());
    eliminated.add(k);
    for (IntVar x : rel.x()) {
      eliminated.add(x);
    }
    values.add(k, Arrays.copyOf(p, n), columns, rel.x(), rel.w(), rel.op(), rel.c());
    if (ws == null) {
      return 0;
    }
    IntVar[] literals = new IntVar[ws.size()];
    for (int j = 0; j < ws.size(); j++) {
      literals[j] = new IntVar(support.store, 0, 1);
      fncs.poseLinearImplied(rel.op(), ws.get(j), xs.get(j), cs.get(j), literals[j]);
    }
    fncs.poseClause(literals, new IntVar[0]);
    return literals.length;
  }

  // r = A[k]: array_var_int_element, array_int_element (A[1] first) or
  // jacop_array_var_int_element_nonshifted (A[first] first)
  private boolean element(ASTConstElem node) {
    String name = node.getName();
    boolean shifted = "array_var_int_element".equals(name) || "array_int_element".equals(name);
    boolean nonshifted = "jacop_array_var_int_element_nonshifted".equals(name);
    if (!shifted && !nonshifted || node.jjtGetNumChildren() != (shifted ? 3 : 4)) {
      return false;
    }
    if (!(node.jjtGetChild(0) instanceof ASTScalarFlatExpr ke)
        || !(node.jjtGetChild(2) instanceof ASTScalarFlatExpr re)) {
      return false;
    }
    IntVar k = support.getVariable(ke);
    IntVar r = support.getVariable(re);
    IntVar[] a = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (k.singleton() || r.singleton() || k == r || a == null || a.length > MAX_POSITIONS) {
      return false;
    }
    for (IntVar x : a) {
      if (x == k || x == r) {
        return false;
      }
    }
    int first = 1;
    if (nonshifted) {
      if (!(node.jjtGetChild(3) instanceof ASTScalarFlatExpr fe) || fe.getType() != 0) {
        return false;
      }
      first = support.getInt(fe);
    }
    Element el = new Element(node, k, a, r, first);
    if (byResult.containsKey(r)) {
      return false;
    }
    byResult.put(r, el);
    elements.computeIfAbsent(k, v -> new ArrayList<>()).add(el);
    return true;
  }

  // a linear relation over results of elements: int_lin_le/eq/ne, int_le, int_lt, int_eq, int_ne
  private void relation(ASTConstElem node) {
    String name = node.getName();
    int op;
    int[] w;
    IntVar[] x;
    int c;
    switch (name) {
      case "int_lin_le", "int_lin_eq", "int_lin_ne" -> {
        if (node.jjtGetNumChildren() != 3
            || !(node.jjtGetChild(2) instanceof ASTScalarFlatExpr ce)
            || ce.getType() != 0) {
          return;
        }
        op =
            "int_lin_le".equals(name)
                ? Support.LE
                : "int_lin_eq".equals(name) ? Support.EQ : Support.NE;
        w = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        c = support.getInt(ce);
        if (w == null || x == null || w.length != x.length) {
          return;
        }
      }
      case "int_le", "int_lt", "int_eq", "int_ne" -> {
        if (node.jjtGetNumChildren() != 2
            || !(node.jjtGetChild(0) instanceof ASTScalarFlatExpr xe)
            || !(node.jjtGetChild(1) instanceof ASTScalarFlatExpr ye)) {
          return;
        }
        op =
            switch (name) {
              case "int_eq" -> Support.EQ;
              case "int_ne" -> Support.NE;
              default -> Support.LE;
            };
        w = new int[] {1, -1};
        x = new IntVar[] {support.getVariable(xe), support.getVariable(ye)};
        c = "int_lt".equals(name) ? -1 : 0;
      }
      default -> {
        return;
      }
    }
    // the constants go to the right-hand side; every variable must be a result, once
    List<Integer> ws = new ArrayList<>();
    List<IntVar> xs = new ArrayList<>();
    long rhs = c;
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    for (int i = 0; i < x.length; i++) {
      if (x[i].singleton()) {
        rhs -= (long) w[i] * x[i].value();
      } else if (byResult.containsKey(x[i]) && seen.add(x[i]) && w[i] != 0) {
        ws.add(w[i]);
        xs.add(x[i]);
      } else {
        return;
      }
    }
    if (xs.isEmpty() || rhs < Integer.MIN_VALUE || rhs > Integer.MAX_VALUE) {
      return;
    }
    Relation rel =
        new Relation(
            node,
            op,
            ws.stream().mapToInt(Integer::intValue).toArray(),
            xs.toArray(new IntVar[0]),
            (int) rhs);
    for (IntVar r : rel.x()) {
      if (relationOf.put(r, rel) != null) {
        // a result in two relations is used twice; the use counts rule it out
        relationOf.put(r, rel);
      }
    }
  }

  // the integer variables of an argument, constants left out
  private void variables(SimpleNode arg, Set<IntVar> out) {
    if (arg.getId() == JJTARRAYLITERAL) {
      for (int i = 0; i < arg.jjtGetNumChildren(); i++) {
        variables((SimpleNode) arg.jjtGetChild(i), out);
      }
      return;
    }
    if (arg.getId() != JJTSCALARFLATEXPR) {
      return;
    }
    ASTScalarFlatExpr e = (ASTScalarFlatExpr) arg;
    if (e.getType() == 2) {
      // a name is of a variable or of an array; the variable is kept by the identifier
      IntVar v = support.dictionary.getVariable(e);
      if (v != null) {
        out.add(v);
        return;
      }
      IntVar[] array = support.dictionary.getDeclaredVariableArray(e.getIdent());
      if (array != null) {
        Collections.addAll(out, array);
      }
    } else if (e.getType() == 3
        && support.dictionary.getDeclaredVariableArray(e.getIdent()) != null) {
      out.add(support.getVariable(e));
    }
  }
}
