/*
 * IndexFunctionDetector.java
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * A product of two functions of one index variable becomes a sum over the values of the index.
 *
 * <p>A model that picks one option per item and then uses two attributes of the chosen option, such
 * as the load {@code sum(p)((good[p] = g) * num[p])} of the 2020 MiniZinc Challenge stable-goods
 * model, where {@code good[p]} and {@code num[p]} are both looked up by the chosen preference, is
 * flattened into {@code int_times(bool2int(good[p] = g), num[p])}. The product propagates to
 * bounds, and the linear relaxation and the explanations of lazy clause generation see a product of
 * two variables. Both factors are functions of the preference p, so the product is too: z =
 * &Sigma;<sub>v</sub> f(v) [p = v], linear over the value literals of p, as the model would state
 * it with {@code sum(i)(req[i] * (preference[p] = i))}.
 *
 * <p>A factor is a function of the index when it is the index, a constant, or defined from such
 * functions by an element over a constant array, bool2int, int_eq_reif, int_ne_reif, int_le_reif or
 * int_lt_reif with a constant, int_times or int_plus. A product int_times(a, b, z) whose factors
 * depend on the same index of at most {@value #MAX_VALUES} values, and on nothing else, is replaced
 * by z = &Sigma;<sub>v</sub> f(v) [p = v], with &Sigma;<sub>v</sub> [p = v] = 1 once per index; the
 * constraints that define the factors stay. A value of the index for which an element is out of its
 * array gets the coefficient 0, since that element removes the value anyway.
 *
 * <p>The stability conditions of the same model are clauses of implied comparisons between such
 * functions, for example {@code bool_clause([b1, b2])} with {@code int_lin_le_imp([1, -1], [n, r],
 * 0, b1)} where n is looked up by one preference and r by the good of another one. A clause whose
 * literals are used nowhere else, at least two of them over functions of at most two indexes with
 * at most {@value #MAX_VALUES} combinations of values, is unfolded: for each combination the
 * comparisons are evaluated, and unless one holds, the clause ¬[p = v] ∨ ¬[q = w] ∨ (the
 * comparisons left open) is posted. This is the expansion of element constraints over the value
 * literals of their index done by the presolve of CP-SAT (L. Perron, F. Didier and S. Gay, The
 * CP-SAT-LP Solver, CP 2023, LIPIcs 280, 3:1-3:2) and, offline, the auto-tabling of subproblems
 * over few values (J. J. Dekker, G. Björdal, M. Carlsson, P. Flener and J.-N. Monette, Auto-tabling
 * for subproblem presolving in MiniZinc, Constraints 22(4), 512-529, 2017).
 *
 * <p>On the 2020 MiniZinc Challenge stable-goods instances at 600 s, s-d16 is proved in 57 s with
 * free search and in 283 s with the default search, and not at all without the rewrite.
 *
 * <p>Setting the system property {@code org.jacop.fz.indexFunctions} to false turns it off, and
 * {@code org.jacop.fz.indexFunctions.clauses} to false turns off only the clause unfolding.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class IndexFunctionDetector implements ParserTreeConstants {

  /** The largest domain of an index whose functions are expanded. */
  static final int MAX_VALUES = 64;

  private static final int DEPTH = 16;

  private static final String BOOL2INT = "bool2int";
  private static final String INT_TIMES = "int_times";
  private static final String INT_PLUS = "int_plus";

  private final Support support;

  private final Set<SimpleNode> replaced = new HashSet<>();

  // the definition of a variable from others; op names the FlatZinc constraint. Records of one
  // model node each, compared by identity
  private record Definition(String op, IntVar[] args, int[] array, int first, int constant) {
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
      return op + Arrays.toString(args);
    }
  }

  private final Map<IntVar, Definition> definitions = new IdentityHashMap<>();

  private final List<ASTConstElem> products = new ArrayList<>();

  // y = array[index - first] over an array with variables
  private record VarElement(IntVar index, IntVar[] array, int first) {
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
      return index + " in " + Arrays.toString(array);
    }
  }

  private final Map<IntVar, VarElement> varElements = new IdentityHashMap<>();

  // b -> (sum coeffs * vars) op rhs, op LE, EQ or NE
  private record Implied(String op, int[] coeffs, IntVar[] vars, int rhs, SimpleNode node) {
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
      return Arrays.toString(coeffs) + Arrays.toString(vars) + " " + op + " " + rhs;
    }
  }

  private final Map<IntVar, Implied> implied = new IdentityHashMap<>();

  private final List<ASTConstElem> clauses = new ArrayList<>();

  private final Map<IntVar, Integer> occurrences = new IdentityHashMap<>();

  private final Map<String, IntVar> conditions = new HashMap<>();

  private int unfolded;

  private int unfoldedClauses;

  // [x = v] literals made here, by x
  private final Map<IntVar, Map<Integer, IntVar>> valueLiterals = new IdentityHashMap<>();

  private final Map<IntVar, Map<Integer, IntVar>> made = new LinkedHashMap<>();

  private int rewritten;

  /**
   * It creates a detector posting through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public IndexFunctionDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.indexFunctions is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.indexFunctions"));
  }

  /**
   * It replaces each product of two functions of one index variable by a linear sum over the value
   * literals of the index.
   *
   * @param astTree the root of the parsed model.
   * @return the int_times constraint nodes it replaces, which must not be posted.
   */
  public Set<SimpleNode> detect(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      switch (node.getId()) {
        case JJTCONSTRAINTITEMS -> readConstraints(node);
        case JJTSOLVEITEM, JJTMODELEND -> countAll(node);
        default -> {
          // other items define no constraint and use no variable of interest
        }
      }
    }
    if (unfoldEnabled()) {
      for (ASTConstElem clause : clauses) {
        support.checkTimeOut();
        unfold(clause);
      }
    }
    Set<IntVar> partitioned = new HashSet<>();
    for (ASTConstElem node : products) {
      IntVar a = variable(node, 0);
      IntVar b = variable(node, 1);
      IntVar z = variable(node, 2);
      IntVar index = a.singleton() || b.singleton() || z.singleton() ? null : index(a, b);
      if (index != null) {
        rewrite(index, a, b, z, partitioned);
        replaced.add(node);
      }
    }
    poseLiterals();
    if (support.options.debug()) {
      FzConsole.println(
          "% index function products: "
              + rewritten
              + ", unfolded clauses: "
              + unfolded
              + " into "
              + unfoldedClauses);
    }
    return replaced;
  }

  /**
   * It tells if clauses over functions of small indexes are unfolded.
   *
   * @return false if the system property org.jacop.fz.indexFunctions.clauses is false.
   */
  public static boolean unfoldEnabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.indexFunctions.clauses"));
  }

  private void readConstraints(SimpleNode items) {
    for (int j = 0; j < items.jjtGetNumChildren(); j++) {
      support.checkTimeOut();
      if (((SimpleNode) items.jjtGetChild(j)).jjtGetChild(0) instanceof ASTConstElem constraint) {
        collect(constraint);
      }
    }
  }

  private void countAll(SimpleNode node) {
    PartialCopyDetector.countVariables(support, node, occurrences);
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      countAll((SimpleNode) node.jjtGetChild(i));
    }
  }

  // a clause of implied comparisons over functions of at most two small indexes: one clause per
  // assignment of the indexes, [i = v] -> the comparisons with the functions evaluated
  private void unfold(ASTConstElem clause) {
    IntVar[] literals = support.getVarArray((SimpleNode) clause.jjtGetChild(0));
    Set<IntVar> roots = Collections.newSetFromMap(new IdentityHashMap<>());
    int defined = 0;
    for (IntVar b : literals) {
      Implied c = implied.get(b);
      if (b.singleton()
          || c == null
          || occurrences.getOrDefault(b, 0) != 2
          || support.dictionary.isOutput(b)
          || replaced.contains(c.node())) {
        return;
      }
      boolean depends = false;
      for (IntVar x : c.vars()) {
        if (definitions.containsKey(x) || varElements.containsKey(x)) {
          depends = true;
          if (!indexRoots(x, roots, 0)) {
            return;
          }
        }
      }
      defined += depends ? 1 : 0;
    }
    // one comparison over a function of the index is the same clause with another literal
    if (defined < 2 || roots.isEmpty() || roots.size() > 2) {
      return;
    }
    List<IntVar> index = new ArrayList<>(roots);
    long combinations = 1;
    for (IntVar r : index) {
      combinations *= r.getSize();
    }
    if (combinations > MAX_VALUES) {
      return;
    }
    List<IntVar[]> posted = new ArrayList<>();
    List<IntVar[]> negated = new ArrayList<>();
    int[] values = new int[index.size()];
    if (!combine(index, 0, values, literals, posted, negated)) {
      return;
    }
    for (int i = 0; i < posted.size(); i++) {
      support.pose(new BoolClause(posted.get(i), negated.get(i)));
    }
    replaced.add(clause);
    for (IntVar b : literals) {
      replaced.add(implied.get(b).node());
    }
    unfolded++;
    unfoldedClauses += posted.size();
  }

  private boolean combine(
      List<IntVar> index,
      int k,
      int[] values,
      IntVar[] literals,
      List<IntVar[]> posted,
      List<IntVar[]> negated) {
    if (k == index.size()) {
      Map<IntVar, Integer> assignment = new IdentityHashMap<>();
      for (int i = 0; i < values.length; i++) {
        assignment.put(index.get(i), values[i]);
      }
      List<IntVar> or = new ArrayList<>();
      for (IntVar b : literals) {
        Implied c = implied.get(b);
        IntVar l = condition(c, assignment);
        if (l == null) {
          return false;
        }
        if (l == OUT_OF_RANGE) {
          // an element of this assignment is out of its array: the element excludes it
          return true;
        }
        if (l == TRUE) {
          return true;
        }
        if (l != FALSE) {
          or.add(l);
        }
      }
      IntVar[] neg = new IntVar[index.size()];
      for (int i = 0; i < neg.length; i++) {
        neg[i] = literal(index.get(i), values[i]);
      }
      posted.add(or.toArray(new IntVar[0]));
      negated.add(neg);
      return true;
    }
    for (ValueEnumeration e = index.get(k).dom().valueEnumeration(); e.hasMoreElements(); ) {
      values[k] = e.nextElement();
      if (!combine(index, k + 1, values, literals, posted, negated)) {
        return false;
      }
    }
    return true;
  }

  private static final IntVar TRUE = new IntVar();

  private static final IntVar FALSE = new IntVar();

  private static final IntVar OUT_OF_RANGE = new IntVar();

  // the comparison of c under the assignment: TRUE, FALSE, OUT_OF_RANGE or a literal for it
  private IntVar condition(Implied c, Map<IntVar, Integer> assignment) {
    Map<IntVar, Long> terms = new LinkedHashMap<>();
    long rhs = c.rhs();
    for (int i = 0; i < c.vars().length; i++) {
      IntVar x = c.vars()[i];
      IntVar leaf = x;
      Long constant = null;
      VarElement ve = varElements.get(x);
      if (ve != null) {
        Long k = value(ve.index(), assignment, 0);
        if (k == null) {
          return OUT_OF_RANGE;
        }
        long pos = k - ve.first();
        if (pos < 0 || pos >= ve.array().length) {
          return OUT_OF_RANGE;
        }
        leaf = ve.array()[(int) pos];
        if (!leaf.singleton() && (definitions.containsKey(leaf) || assignment.containsKey(leaf))) {
          return null;
        }
      }
      if (leaf.singleton()) {
        constant = (long) leaf.value();
      } else if (assignment.containsKey(leaf) || definitions.containsKey(leaf)) {
        constant = value(leaf, assignment, 0);
        if (constant == null) {
          return OUT_OF_RANGE;
        }
      }
      if (constant != null) {
        rhs -= c.coeffs()[i] * constant;
      } else if (varElements.containsKey(leaf)) {
        // an element of an element: not unfolded
        return null;
      } else {
        terms.merge(leaf, (long) c.coeffs()[i], Long::sum);
      }
    }
    terms.values().removeIf(w -> w == 0);
    if (terms.isEmpty()) {
      boolean holds =
          switch (c.op()) {
            case "LE" -> 0 <= rhs;
            case "EQ" -> 0 == rhs;
            default -> 0 != rhs;
          };
      return holds ? TRUE : FALSE;
    }
    if (rhs < IntDomain.MIN_INT || rhs > IntDomain.MAX_INT) {
      return null;
    }
    IntVar[] vs = terms.keySet().toArray(new IntVar[0]);
    int[] ws = new int[vs.length];
    int i = 0;
    StringBuilder key = new StringBuilder(c.op()).append(':').append(rhs);
    for (Map.Entry<IntVar, Long> t : terms.entrySet()) {
      ws[i++] = (int) (long) t.getValue();
      key.append(':').append(System.identityHashCode(t.getKey())).append('*').append(t.getValue());
    }
    IntVar l = conditions.get(key.toString());
    if (l == null) {
      l = new IntVar(support.store, 0, 1);
      String rel =
          switch (c.op()) {
            case "LE" -> "<=";
            case "EQ" -> "==";
            default -> "!=";
          };
      support.pose(new Reified(new LinearInt(vs, ws, rel, (int) rhs), l));
      conditions.put(key.toString(), l);
    }
    return l;
  }

  // adds the index variables x depends on through functions and elements; false when too deep
  private boolean indexRoots(IntVar x, Set<IntVar> roots, int depth) {
    if (x.singleton()) {
      return true;
    }
    if (depth > DEPTH) {
      return false;
    }
    VarElement ve = varElements.get(x);
    if (ve != null) {
      return roots(ve.index(), roots, depth + 1);
    }
    return roots(x, roots, depth);
  }

  // the one variable both factors depend on, or null
  private IntVar index(IntVar a, IntVar b) {
    Set<IntVar> roots = Collections.newSetFromMap(new IdentityHashMap<>());
    if (!roots(a, roots, 0) || !roots(b, roots, 0) || roots.size() != 1) {
      return null;
    }
    IntVar index = roots.iterator().next();
    if (index.getSize() > MAX_VALUES || a == index && b == index) {
      return null;
    }
    return index;
  }

  // adds the free variables x is a function of; false when too deep
  private boolean roots(IntVar x, Set<IntVar> roots, int depth) {
    if (x.singleton()) {
      return true;
    }
    Definition d = definitions.get(x);
    if (d == null) {
      roots.add(x);
      return true;
    }
    if (depth > DEPTH) {
      return false;
    }
    for (IntVar y : d.args()) {
      if (!roots(y, roots, depth + 1)) {
        return false;
      }
    }
    return true;
  }

  // the value of x when the index is v, or null when an element is out of its array
  private Long value(IntVar x, IntVar index, int v, int depth) {
    return value(x, Map.of(index, v), depth);
  }

  // the value of x under an assignment of its roots, or null when an element is out of its array
  private Long value(IntVar x, Map<IntVar, Integer> assignment, int depth) {
    Integer fixed = assignment.get(x);
    if (fixed != null) {
      return (long) fixed;
    }
    if (x.singleton()) {
      return (long) x.value();
    }
    Definition d = definitions.get(x);
    if (d == null || depth > DEPTH) {
      return null;
    }
    Long[] args = new Long[d.args().length];
    for (int i = 0; i < args.length; i++) {
      args[i] = value(d.args()[i], assignment, depth + 1);
      if (args[i] == null) {
        return null;
      }
    }
    return switch (d.op()) {
      case "element" -> {
        long k = args[0] - d.first();
        yield k < 0 || k >= d.array().length ? null : (long) d.array()[(int) k];
      }
      case BOOL2INT -> args[0];
      case "int_eq_reif" -> args[0] == d.constant() ? 1L : 0L;
      case "int_ne_reif" -> args[0] == d.constant() ? 0L : 1L;
      case "int_le_reif" -> args[0] <= d.constant() ? 1L : 0L;
      case "int_lt_reif" -> args[0] < d.constant() ? 1L : 0L;
      case INT_TIMES -> args[0] * args[1];
      case INT_PLUS -> args[0] + args[1];
      default -> null;
    };
  }

  private void rewrite(IntVar index, IntVar a, IntVar b, IntVar z, Set<IntVar> partitioned) {
    List<IntVar> vars = new ArrayList<>();
    List<Integer> weights = new ArrayList<>();
    List<IntVar> all = new ArrayList<>();
    for (ValueEnumeration e = index.dom().valueEnumeration(); e.hasMoreElements(); ) {
      int v = e.nextElement();
      IntVar literal = literal(index, v);
      all.add(literal);
      Long p = value(a, index, v, 0);
      Long q = value(b, index, v, 0);
      long f = p == null || q == null ? 0 : p * q;
      if (f != 0 && f >= IntDomain.MIN_INT && f <= IntDomain.MAX_INT) {
        vars.add(literal);
        weights.add((int) f);
      } else if (f != 0) {
        // out of the integer range: the value cannot be taken
        support.pose(new LinearInt(new IntVar[] {literal}, new int[] {1}, "==", 0));
      }
    }
    vars.add(z);
    weights.add(-1);
    support.pose(
        new LinearInt(
            vars.toArray(new IntVar[0]),
            weights.stream().mapToInt(Integer::intValue).toArray(),
            "==",
            0));
    if (partitioned.add(index)) {
      int[] ones = new int[all.size()];
      Arrays.fill(ones, 1);
      support.pose(new LinearInt(all.toArray(new IntVar[0]), ones, "==", 1));
    }
    rewritten++;
  }

  // the literal [x = v]: the one the model reifies, or a new one channelled to x
  private IntVar literal(IntVar x, int v) {
    Map<Integer, IntVar> byValue = valueLiterals.computeIfAbsent(x, k -> new HashMap<>());
    IntVar b = byValue.get(v);
    if (b == null) {
      Map<Integer, IntVar> reified = support.reif.cs.get(x);
      if (reified != null && reified.get(v) != null) {
        b = reified.get(v);
      } else {
        b = new IntVar(support.store, 0, 1);
        made.computeIfAbsent(x, k -> new HashMap<>()).put(v, b);
      }
      byValue.put(v, b);
    }
    return b;
  }

  private void poseLiterals() {
    SetUnionDetector.poseLiterals(support, made);
  }

  private void collect(ASTConstElem node) {
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      PartialCopyDetector.countVariables(support, (SimpleNode) node.jjtGetChild(i), occurrences);
    }
    String name = node.getName();
    switch (name) {
      case "bool_clause" -> {
        if (support.getVarArray((SimpleNode) node.jjtGetChild(1)).length == 0) {
          clauses.add(node);
        }
      }
      case "int_lin_le_imp" ->
          implied.putIfAbsent(
              variable(node, 3),
              new Implied(
                  "LE",
                  support.getIntArray((SimpleNode) node.jjtGetChild(0)),
                  support.getVarArray((SimpleNode) node.jjtGetChild(1)),
                  support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)),
                  node));
      case "int_le_imp", "int_lt_imp", "int_eq_imp", "int_ne_imp" -> {
        String op =
            switch (name) {
              case "int_eq_imp" -> "EQ";
              case "int_ne_imp" -> "NE";
              default -> "LE";
            };
        int rhs = name.equals("int_lt_imp") ? -1 : 0;
        implied.putIfAbsent(
            variable(node, 2),
            new Implied(
                op,
                new int[] {1, -1},
                new IntVar[] {variable(node, 0), variable(node, 1)},
                rhs,
                node));
      }
      case "array_int_element", "array_var_int_element" -> element(node, 1);
      case "jacop_array_var_int_element_nonshifted", "jacop_array_int_element_nonshifted" ->
          element(node, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
      case BOOL2INT -> define(variable(node, 1), BOOL2INT, variable(node, 0));
      case "int_eq_reif", "int_ne_reif", "int_le_reif", "int_lt_reif" -> {
        IntVar x = variable(node, 0);
        IntVar c = variable(node, 1);
        IntVar r = variable(node, 2);
        if (c.singleton() && !x.singleton()) {
          definitions.putIfAbsent(r, new Definition(name, new IntVar[] {x}, null, 0, c.value()));
        }
      }
      case INT_TIMES -> {
        define(variable(node, 2), INT_TIMES, variable(node, 0), variable(node, 1));
        products.add(node);
      }
      case INT_PLUS -> define(variable(node, 2), INT_PLUS, variable(node, 0), variable(node, 1));
      default -> {
        // not a function step
      }
    }
  }

  private void define(IntVar x, String op, IntVar... args) {
    if (!x.singleton()) {
      definitions.putIfAbsent(x, new Definition(op, args, null, 0, 0));
    }
  }

  private void element(ASTConstElem node, int first) {
    IntVar index = variable(node, 0);
    IntVar value = variable(node, 2);
    if (index.singleton() || value.singleton()) {
      return;
    }
    IntVar[] vars = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int[] array = new int[vars.length];
    for (int k = 0; k < vars.length; k++) {
      if (!vars[k].singleton()) {
        return;
      }
      array[k] = vars[k].value();
    }
    definitions.putIfAbsent(
        value, new Definition("element", new IntVar[] {index}, array, first, 0));
  }

  private IntVar variable(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }
}
