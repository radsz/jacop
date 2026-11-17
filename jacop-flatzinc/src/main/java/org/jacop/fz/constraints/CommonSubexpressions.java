/*
 * CommonSubexpressions.java
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It merges constraints that compute the same function of the same inputs and removes duplicate
 * constraints, as the presolve of CP-SAT does ({@code DetectDuplicateConstraints}; Perron, Didier
 * and Gay, "The CP-SAT-LP solver", CP 2023) and the duplicate-row presolver of MIP solvers
 * (Achterberg, Bixby, Gu, Rothberg and Weninger, "Presolve reductions in mixed integer
 * programming", INFORMS Journal on Computing 32(2), 2020). Two constraints {@code r1 = f(x)} and
 * {@code r2 = f(x)} make r2 an alias of r1 and the second one is not posted; two equal constraints
 * without an output are posted once. Inputs are compared after aliasing, so the merging is repeated
 * while it finds merges. MiniZinc's own common subexpression elimination misses these when the
 * inputs become equal only through its later aliasing. Equalities left in the model ({@code
 * int_eq}, {@code bool_eq}, {@code x - y = 0} and a conjunction or disjunction of one literal) make
 * one variable an alias of the other in the same way.
 *
 * <p>The functions are the full reifications of comparisons and linear constraints, the Boolean
 * connectives, element constraints and the arithmetic functions; arguments are compared by value
 * for constants and by variable otherwise, with the inputs of commutative functions and the terms
 * of linear constraints in a fixed order. A merge is skipped when it would put both outputs in one
 * constraint other than a plain linear one, when an output is a constant, a variable of the solve
 * item, or a variable of an {@code int_eq_reif} or {@code int_eq_imp} with a constant, which are
 * collected for channelling before this pass, and when the outputs are of different variable
 * classes. Merged outputs keep every solution, since they are equal in all of them; aliased output
 * variables are printed through an equality.
 *
 * <p>Off under {@code --proof}; the system property {@code org.jacop.fz.cse} set to false turns it
 * off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class CommonSubexpressions implements ParserTreeConstants {

  private static final int ROUNDS = 6;

  private static final Set<String> COMMUTATIVE =
      Set.of(
          "int_eq_reif",
          "int_ne_reif",
          "bool_eq_reif",
          "bool_and",
          "bool_or",
          "bool_xor",
          "int_times",
          "int_plus",
          "int_min",
          "int_max");

  private static final Set<String> ORDERED =
      Set.of(
          "int_le_reif",
          "int_lt_reif",
          "bool_le_reif",
          "bool_lt_reif",
          "int_div",
          "int_mod",
          "int_pow",
          "int_abs",
          "bool_not");

  private static final Set<String> LINEAR_REIF =
      Set.of("int_lin_eq_reif", "int_lin_ne_reif", "int_lin_le_reif");

  private static final Set<String> LINEAR = Set.of("int_lin_eq", "int_lin_ne", "int_lin_le");

  private static final Set<String> CONNECTIVES = Set.of("array_bool_and", "array_bool_or");

  private static final Set<String> ELEMENTS =
      Set.of(
          "array_int_element",
          "array_var_int_element",
          "array_bool_element",
          "array_var_bool_element");

  private static final Set<String> BINARY = Set.of("int_le", "int_lt", "int_ne", "bool_le");

  private final Support support;

  private final Set<IntVar> pinned;

  private final List<ASTConstElem> nodes = new ArrayList<>();

  // the constraints, by index into nodes, in which each variable occurs
  private final Map<IntVar, Set<Integer>> occurrences = new IdentityHashMap<>();

  // a number for each variable, in the order of first occurrence, so keys do not depend on hashes
  private final Map<IntVar, Integer> numbers = new IdentityHashMap<>();

  private final Set<SimpleNode> replaced = new HashSet<>();

  // the constraints, by index, that are linear: they accept a variable twice
  private final Set<Integer> linear = new HashSet<>();

  // the variables that are aliases of each variable, as bool2int makes them
  private final Map<IntVar, List<IntVar>> aliasesOf = new IdentityHashMap<>();

  private int merged;

  private int duplicates;

  private int aliases;

  /** A key and the output of a constraint, null when it has no output. */
  private record Keyed(List<Object> key, IntVar out) {}

  /**
   * It creates the merging.
   *
   * @param support the support of the FlatZinc front end.
   * @param pinned variables that must not become aliases: those of the solve item.
   */
  public CommonSubexpressions(Support support, Set<IntVar> pinned) {
    this.support = support;
    this.pinned = pinned;
  }

  /**
   * It tells if the merging is on.
   *
   * @return false if the system property org.jacop.fz.cse is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.cse"));
  }

  /**
   * The constraint nodes that are not posted.
   *
   * @return the merged and duplicate constraint nodes.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  /**
   * It returns the number of outputs that became aliases.
   *
   * @return the number of merged outputs.
   */
  public int merged() {
    return merged;
  }

  /**
   * It returns the number of duplicate constraints removed.
   *
   * @return the number of duplicates.
   */
  public int duplicates() {
    return duplicates;
  }

  /**
   * It merges the constraints of the model.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM && relevant(((ASTConstElem) item).getName())) {
            nodes.add((ASTConstElem) item);
          }
        }
      }
    }
    if (nodes.size() < 2) {
      return;
    }
    // the occurrences in every constraint, not only the merged kinds, guard against repeats
    countAll(astTree);
    support.dictionary.aliasTable.forEach(
        (alias, target) -> aliasesOf.computeIfAbsent(target, v -> new ArrayList<>()).add(alias));
    for (int round = 0; round < ROUNDS; round++) {
      support.checkTimeOut();
      if (!round()) {
        break;
      }
    }
    if (merged > 0 || aliases > 0) {
      support.dictionary.removeAliasFromSearch();
    }
    if (support.options.debug() && (merged > 0 || aliases > 0 || duplicates > 0)) {
      FzConsole.println(
          "% common subexpressions: "
              + merged
              + " outputs merged, "
              + aliases
              + " equalities aliased, "
              + duplicates
              + " duplicate constraints removed");
    }
  }

  private static boolean relevant(String name) {
    return COMMUTATIVE.contains(name)
        || ORDERED.contains(name)
        || LINEAR_REIF.contains(name)
        || LINEAR.contains(name)
        || CONNECTIVES.contains(name)
        || ELEMENTS.contains(name)
        || BINARY.contains(name)
        || name.equals("bool_clause")
        || name.equals("int_eq")
        || name.equals("bool_eq");
  }

  // one pass over the live constraints; true if an output became an alias
  private boolean round() {
    Map<List<Object>, Integer> first = new HashMap<>();
    boolean aliased = false;
    for (int i = 0; i < nodes.size(); i++) {
      ASTConstElem node = nodes.get(i);
      if (replaced.contains(node)) {
        continue;
      }
      IntVar[] eq = equality(node);
      if (eq != null) {
        if (eq[0] == eq[1]) {
          replaced.add(node);
          duplicates++;
        } else if (merge(eq[0], eq[1], i) || merge(eq[1], eq[0], i)) {
          aliases++;
          aliased = true;
        }
        continue;
      }
      Keyed k = key(node);
      if (k == null) {
        continue;
      }
      Integer j = first.putIfAbsent(k.key(), i);
      if (j == null) {
        continue;
      }
      IntVar out1 = k.out() == null ? null : key(nodes.get(j)).out();
      IntVar out2 = k.out();
      if (out2 == null || out1 == out2) {
        replaced.add(node);
        duplicates++;
        continue;
      }
      if (merge(out1, out2, i)) {
        merged++;
        aliased = true;
      } else if (merge(out2, out1, j)) {
        // the first output is the one that cannot go: the second constraint stays as the first
        first.put(k.key(), i);
        merged++;
        aliased = true;
      }
    }
    return aliased;
  }

  // makes out2 an alias of out1 and drops the constraint `drop` defining out2
  private boolean merge(IntVar out1, IntVar out2, int drop) {
    if (out1.singleton()
        || out2.singleton()
        || (out1 instanceof BooleanVar) != (out2 instanceof BooleanVar)
        || pinned.contains(out2)
        || !support.reif.variablesOf(out2).isEmpty()
        || !support.imply.variablesOf(out2).isEmpty()
        || support.reif.size(out2) > 0
        || support.imply.size(out2) > 0) {
      return false;
    }
    Set<Integer> o1 = occurrences.getOrDefault(out1, Set.of());
    for (Integer c : occurrences.getOrDefault(out2, Set.of())) {
      if (c != drop && o1.contains(c) && !linear.contains(c)) {
        // the two would occur in one constraint; linear constraints add up repeated variables
        return false;
      }
    }
    out1.domain.in(support.store.level, out1, out2.domain);
    List<IntVar> aliases = aliasesOf.getOrDefault(out2, List.of());
    support.dictionary.mergeAlias(out1, out2, aliases);
    List<IntVar> ofOut1 = aliasesOf.computeIfAbsent(out1, v -> new ArrayList<>());
    ofOut1.addAll(aliases);
    ofOut1.add(out2);
    aliasesOf.remove(out2);
    replaced.add(nodes.get(drop));
    Set<Integer> moved = occurrences.remove(out2);
    if (moved != null) {
      moved.remove(drop);
      occurrences.computeIfAbsent(out1, v -> new HashSet<>()).addAll(moved);
    }
    occurrences.getOrDefault(out1, new HashSet<>()).remove(drop);
    return true;
  }

  // the two variables of x = y (int_eq, bool_eq, x - y = 0, a one-literal conjunction or
  // disjunction), or null
  private IntVar[] equality(ASTConstElem node) {
    String name = node.getName();
    if (name.equals("int_eq") || name.equals("bool_eq")) {
      if (!(node.jjtGetChild(0) instanceof ASTScalarFlatExpr a)
          || !(node.jjtGetChild(1) instanceof ASTScalarFlatExpr b)
          || a.getType() == 0
          || b.getType() == 0) {
        return null;
      }
      return variables(support.getVariable(a), support.getVariable(b));
    }
    if (name.equals("int_lin_eq")) {
      int[] c = support.getIntArray(child(node, 0));
      if (c == null
          || c.length != 2
          || c[0] != -c[1]
          || Math.abs(c[0]) != 1
          || support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)) != 0) {
        return null;
      }
      IntVar[] x = support.getVarArray(child(node, 1));
      return variables(x[0], x[1]);
    }
    if (CONNECTIVES.contains(name)) {
      IntVar[] a = support.getVarArray(child(node, 0));
      if (a.length != 1 || !(node.jjtGetChild(1) instanceof ASTScalarFlatExpr r)) {
        return null;
      }
      return variables(a[0], support.getVariable(r));
    }
    return null;
  }

  private static IntVar[] variables(IntVar x, IntVar y) {
    if (x.singleton() || y.singleton()) {
      return null;
    }
    return new IntVar[] {x, y};
  }

  private Keyed key(ASTConstElem node) {
    String name = node.getName();
    List<Object> key = new ArrayList<>();
    key.add(name);
    if (COMMUTATIVE.contains(name) || ORDERED.contains(name)) {
      int n = node.jjtGetNumChildren();
      Object[] in = new Object[n - 1];
      for (int a = 0; a < n - 1; a++) {
        in[a] = scalar(node, a);
        if (in[a] == null) {
          return null;
        }
      }
      if (name.equals("int_eq_reif") && (constant(in[0]) || constant(in[1]))) {
        // collected for channelling with the other literals of the variable
        return null;
      }
      if (COMMUTATIVE.contains(name)) {
        Arrays.sort(in, CommonSubexpressions::compare);
      }
      key.addAll(Arrays.asList(in));
      return output(node, n - 1, key);
    }
    if (LINEAR_REIF.contains(name) || LINEAR.contains(name)) {
      int[] c = support.getIntArray(child(node, 0));
      IntVar[] x = support.getVarArray(child(node, 1));
      if (c == null || x == null || c.length != x.length) {
        return null;
      }
      key.add(linear(c, x));
      key.add(support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)));
      return LINEAR.contains(name) ? new Keyed(key, null) : output(node, 3, key);
    }
    if (CONNECTIVES.contains(name)) {
      key.add(sorted(tokens(support.getVarArray(child(node, 0)))));
      return output(node, 1, key);
    }
    if (ELEMENTS.contains(name)) {
      Object index = scalar(node, 0);
      if (index == null) {
        return null;
      }
      key.add(index);
      key.add(tokens(support.getVarArray(child(node, 1))));
      return output(node, 2, key);
    }
    if (BINARY.contains(name)) {
      for (int a = 0; a < 2; a++) {
        Object t = scalar(node, a);
        if (t == null) {
          return null;
        }
        key.add(t);
      }
      return new Keyed(key, null);
    }
    if (!name.equals("bool_clause")) {
      // an int_eq or bool_eq with a constant, which equality() leaves
      return null;
    }
    key.add(sorted(tokens(support.getVarArray(child(node, 0)))));
    key.add(sorted(tokens(support.getVarArray(child(node, 1)))));
    return new Keyed(key, null);
  }

  private Keyed output(ASTConstElem node, int index, List<Object> key) {
    if (!(node.jjtGetChild(index) instanceof ASTScalarFlatExpr e)
        || e.getType() != 2 && e.getType() != 3) {
      // a constant output: the constraint is only compared as a whole
      Object t = scalar(node, index);
      if (t == null) {
        return null;
      }
      key.add(t);
      return new Keyed(key, null);
    }
    return new Keyed(key, support.getVariable(e));
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  // a variable as its number (a Long) and a constant as its value (an Integer); null otherwise
  private Object scalar(ASTConstElem node, int i) {
    if (!(node.jjtGetChild(i) instanceof ASTScalarFlatExpr e)) {
      return null;
    }
    if (e.getType() == 0) {
      return support.getInt(e);
    }
    if (e.getType() != 1 && e.getType() != 2 && e.getType() != 3) {
      return null;
    }
    return token(support.getVariable(e));
  }

  private Object token(IntVar v) {
    if (v.singleton()) {
      return v.value();
    }
    return (long) numbers.computeIfAbsent(v, x -> numbers.size());
  }

  private List<Object> tokens(IntVar[] vars) {
    List<Object> t = new ArrayList<>(vars.length);
    for (IntVar v : vars) {
      t.add(token(v));
    }
    return t;
  }

  // the tokens as a sorted list without repetitions, constants (Integer) before variables (Long);
  // a list since the hash code of a set adds up its elements and collides for most sets
  private static List<Object> sorted(List<Object> tokens) {
    SortedSet<Object> set = new TreeSet<>(CommonSubexpressions::compare);
    set.addAll(tokens);
    return new ArrayList<>(set);
  }

  private static boolean constant(Object t) {
    return t instanceof Integer;
  }

  private static int compare(Object a, Object b) {
    if (a instanceof Integer x) {
      return b instanceof Integer y ? Integer.compare(x, y) : -1;
    }
    if (b instanceof Integer) {
      return 1;
    }
    return Long.compare((Long) a, (Long) b);
  }

  // the terms of a linear constraint with repeated variables added up, constants as a sum
  private Object linear(int[] c, IntVar[] x) {
    Map<Long, Long> terms = new TreeMap<>();
    long constant = 0;
    for (int i = 0; i < c.length; i++) {
      if (x[i].singleton()) {
        constant += (long) c[i] * x[i].value();
      } else {
        terms.merge((Long) token(x[i]), (long) c[i], Long::sum);
      }
    }
    terms.values().removeIf(v -> v == 0);
    // a flat list: the hash code of a map adds up its entries and collides for most sums
    List<Long> key = new ArrayList<>(2 * terms.size() + 1);
    for (Map.Entry<Long, Long> t : terms.entrySet()) {
      key.add(t.getKey());
      key.add(t.getValue());
    }
    key.add(constant);
    return key;
  }

  // the constraints in which each variable occurs, over every constraint of the model
  private void countAll(SimpleNode astTree) {
    Map<SimpleNode, Integer> index = new IdentityHashMap<>();
    for (int i = 0; i < nodes.size(); i++) {
      index.put(nodes.get(i), i);
    }
    int other = nodes.size();
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() != JJTCONSTRAINTITEMS) {
        continue;
      }
      for (int j = 0; j < node.jjtGetNumChildren(); j++) {
        SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
        if (item.getId() != JJTCONSTELEM) {
          continue;
        }
        Integer c = index.get(item);
        int id = c == null ? other++ : c;
        if (LINEAR.contains(((ASTConstElem) item).getName())) {
          linear.add(id);
        }
        for (int k = 0; k < item.jjtGetNumChildren(); k++) {
          occur(child(item, k), id);
        }
      }
    }
  }

  private void occur(SimpleNode arg, int id) {
    if (arg.getId() == JJTARRAYLITERAL) {
      for (int i = 0; i < arg.jjtGetNumChildren(); i++) {
        occur(child(arg, i), id);
      }
      return;
    }
    if (!(arg instanceof ASTScalarFlatExpr e)) {
      return;
    }
    IntVar[] vars;
    if (e.getType() == 2) {
      // an identifier: a variable or an array of variables
      IntVar[] a = support.dictionary.getDeclaredVariableArray(e.getIdent());
      vars = a != null ? a : identVariable(e);
    } else if (e.getType() == 3
        && support.dictionary.getDeclaredVariableArray(e.getIdent()) != null) {
      // an element of an array of integer variables; float and set arrays are not merged
      vars = new IntVar[] {support.getVariable(e)};
    } else {
      return;
    }
    for (IntVar v : vars) {
      if (v != null && !v.singleton()) {
        occurrences.computeIfAbsent(v, x -> new HashSet<>()).add(id);
      }
    }
  }

  private IntVar[] identVariable(ASTScalarFlatExpr e) {
    IntVar v = support.dictionary.getVariable(e.getIdent());
    return v == null ? new IntVar[0] : new IntVar[] {v};
  }
}
