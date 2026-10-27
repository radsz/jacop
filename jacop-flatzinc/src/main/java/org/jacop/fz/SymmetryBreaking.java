/*
 * SymmetryBreaking.java
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

package org.jacop.fz;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import org.jacop.constraints.LexOrder;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.presolve.GraphAutomorphisms;

/**
 * Detects variable symmetries of a FlatZinc model and breaks them with lex-leader constraints.
 *
 * <p>The model becomes a coloured graph (Puget, CP 2005; CP-SAT does the same on its model): a
 * vertex per integer variable, coloured by its domain, a vertex per constraint, coloured by its
 * name and the constants among its arguments, and vertices for the argument positions that hold
 * variables, coloured by the position. Any automorphism of the graph maps every constraint to a
 * constraint of the model with the same name and constants, and every variable to one with the same
 * domain, so the permutation it makes of the variables maps solutions to solutions. Arguments of a
 * constraint whose order does not matter are positions of one colour: the arrays of {@code
 * all_different}, {@code bool_clause} or {@code nvalue}, the terms of a linear constraint, the
 * tasks of a cumulative, the items of a bin packing, the two sides of {@code int_eq} or {@code
 * int_plus}. Every other argument keeps its position. Variables fixed at the root are constants; a
 * constraint that is then the same as another is left out, and equal items of one array are one
 * vertex with their number in its colour. Float and set variables get a colour each, so no symmetry
 * moves them.
 *
 * <p>For each generator {@code g} found by {@link GraphAutomorphisms} the constraint {@code X <=lex
 * g(X)} is posted, with {@code X} the variables in one fixed order: those of the search annotation
 * first, in its order, then the others as the model first uses them. The lexicographically smallest
 * solution of every orbit satisfies all of them, so a satisfiable model stays satisfiable. The
 * objective variable has a colour of its own, so every symmetry keeps the objective and the optimum
 * is kept. Solutions are lost, so the caller does not use this to enumerate solutions. Positions
 * that a generator does not move are left out, and so are those where the earlier positions, when
 * equal, already make the two variables equal.
 *
 * <p>A model with an argument that is not understood is left as it is.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class SymmetryBreaking implements ParserTreeConstants {

  /** Graphs with more vertices are not searched. */
  static final int MAX_VERTICES = 2_000_000;

  /** The largest number of adjacency entries the automorphism search reads. */
  static final long MAX_WORK = 200_000_000L;

  /**
   * What was done.
   *
   * @param vertices vertices of the model graph, 0 if no graph was built.
   * @param generators generators found that move variables.
   * @param constraints lex-leader constraints posted.
   * @param complete true if the automorphism search ran to the end.
   * @param skipped why no graph was built, or null.
   */
  record Outcome(int vertices, int generators, int constraints, boolean complete, String skipped) {}

  private static final class Unsupported extends RuntimeException {
    Unsupported(String reason) {
      super(reason, null, false, false);
    }
  }

  /**
   * An argument value: an integer variable that is not fixed, a float or set variable, which no
   * symmetry moves, or a constant written as a string.
   */
  private record Atom(IntVar var, Var other, String constant) {
    boolean isConstant() {
      return constant != null;
    }
  }

  /** How the arguments of a constraint are grouped; arguments in no group keep their position. */
  private record Spec(int[] symmetric, int[][] bags) {
    static Spec sym(int... args) {
      return new Spec(args, new int[0][]);
    }

    static Spec bags(int[]... bags) {
      return new Spec(new int[0], bags);
    }
  }

  private static final Map<String, Spec> SPECS = new HashMap<>();

  static {
    for (String s :
        new String[] {
          "int_eq",
          "int_ne",
          "int_eq_reif",
          "int_ne_reif",
          "int_eq_imp",
          "int_ne_imp",
          "bool_eq",
          "bool_eq_reif",
          "bool_eq_imp",
          "bool_xor",
          "bool_xor_reif",
          "bool_xor_imp",
          "bool_not",
          "int_plus",
          "int_times",
          "int_max",
          "int_min",
          "bool_and",
          "bool_or",
          "bool_and_reif",
          "bool_or_reif",
          "bool_and_imp",
          "bool_or_imp"
        }) {
      SPECS.put(s, Spec.sym(0, 1));
    }
    for (String s : new String[] {"int_lin_eq", "int_lin_le", "int_lin_ne", "bool_lin_eq"}) {
      SPECS.put(s, Spec.bags(new int[] {0, 1}));
      SPECS.put(s + "_reif", Spec.bags(new int[] {0, 1}));
      SPECS.put(s + "_imp", Spec.bags(new int[] {0, 1}));
    }
    SPECS.put("bool_lin_le", Spec.bags(new int[] {0, 1}));
    for (String s :
        new String[] {
          "array_bool_and",
          "array_bool_or",
          "array_bool_xor",
          "array_bool_and_imp",
          "array_bool_or_imp",
          "array_bool_and_reif",
          "array_bool_or_reif",
          "jacop_alldiff",
          "jacop_alldistinct",
          "jacop_alldistinct_reif",
          "jacop_alldifferent_except",
          "jacop_alldifferent_except_0",
          "jacop_all_equal_int",
          "jacop_all_equal_int_reif",
          "jacop_among",
          "jacop_atleast",
          "jacop_atmost",
          "jacop_atleast_reif",
          "jacop_atmost_reif",
          "jacop_count",
          "jacop_count_reif",
          "jacop_count_var",
          "jacop_count_var_ge",
          "jacop_count_var_le",
          "jacop_count_var_reif",
          "jacop_member_int",
          "jacop_member_bool",
          "jacop_member_int_reif",
          "jacop_member_bool_reif",
          "jacop_count_values"
        }) {
      SPECS.put(s, Spec.bags(new int[] {0}));
    }
    for (String s :
        new String[] {
          "array_int_maximum", "array_int_minimum", "jacop_nvalue", "jacop_maximum", "jacop_minimum"
        }) {
      SPECS.put(s, Spec.bags(new int[] {1}));
    }
    SPECS.put("bool_clause", Spec.bags(new int[] {0}, new int[] {1}));
    SPECS.put("bool_clause_reif", Spec.bags(new int[] {0}, new int[] {1}));
    SPECS.put("bool_clause_imp", Spec.bags(new int[] {0}, new int[] {1}));
    SPECS.put("jacop_cumulative", Spec.bags(new int[] {0, 1, 2}));
    SPECS.put("jacop_diff2_strict", Spec.bags(new int[] {0, 1, 2, 3}));
    SPECS.put("jacop_bin_packing", Spec.bags(new int[] {0, 2}));
    SPECS.put("jacop_bin_packing_capacity", Spec.bags(new int[] {0, 2}));
  }

  private final Store store;
  private final Tables dictionary;

  // the graph
  private final List<String> colorKeys = new ArrayList<>();
  private int[][] adjacency = new int[64][];
  private int[] degree = new int[64];
  private final Map<IntVar, Integer> varVertex = new IdentityHashMap<>();
  private final Map<Var, Integer> otherVertex = new IdentityHashMap<>();
  private final Set<String> distinct = new HashSet<>();
  private final List<IntVar> vars = new ArrayList<>();
  private IntVar objective;

  SymmetryBreaking(Store store, Tables dictionary) {
    this.store = store;
    this.dictionary = dictionary;
  }

  /**
   * Finds the symmetries of the model and posts the constraints that break them.
   *
   * @param astTree the parsed model.
   * @param objective the objective variable, or null for a satisfaction problem.
   * @param order variables in the order their lex-leader constraints compare them first, for
   *     example those of the search annotation.
   * @param maxNanos the longest time the automorphism search runs.
   * @return what was done.
   */
  Outcome run(SimpleNode astTree, IntVar objective, List<Var> order, long maxNanos) {
    this.objective = objective != null && !objective.singleton() ? objective : null;
    try {
      buildGraph(astTree);
    } catch (Unsupported e) {
      return new Outcome(0, 0, 0, true, e.getMessage());
    } catch (IllegalArgumentException | ClassCastException e) {
      // a form of argument the front end reads elsewhere; the model is left as it is
      return new Outcome(0, 0, 0, true, String.valueOf(e.getMessage()));
    }
    int n = colorKeys.size();
    if (n > MAX_VERTICES) {
      return new Outcome(n, 0, 0, true, "graph too large");
    }

    TreeMap<String, Integer> sorted = new TreeMap<>();
    for (String k : colorKeys) {
      sorted.put(k, 0);
    }
    int c = 0;
    for (Map.Entry<String, Integer> e : sorted.entrySet()) {
      e.setValue(c++);
    }
    int[] colors = new int[n];
    int[][] adj = new int[n][];
    for (int v = 0; v < n; v++) {
      colors[v] = sorted.getOrDefault(colorKeys.get(v), 0);
      adj[v] = Arrays.copyOf(adjacency[v], degree[v]);
    }
    adjacency = null;

    // the position of each variable in the lex-leader order
    Map<IntVar, Integer> rank = new IdentityHashMap<>();
    for (Var v : order) {
      if (v instanceof IntVar iv && varVertex.containsKey(iv)) {
        rank.putIfAbsent(iv, rank.size());
      }
    }
    for (IntVar v : vars) {
      rank.putIfAbsent(v, rank.size());
    }
    // the variables are the base of the search, in the lex-leader order
    int[] base = new int[rank.size()];
    rank.forEach((x, r) -> base[r] = varVertex.getOrDefault(x, 0));
    GraphAutomorphisms.Result result =
        new GraphAutomorphisms(colors, adj, base).generators(MAX_WORK, maxNanos);

    IntVar[] varAt = new IntVar[n];
    int[] rankAt = new int[n];
    varVertex.forEach(
        (x, v) -> {
          varAt[v] = x;
          rankAt[v] = rank.getOrDefault(x, 0);
        });
    int moving = 0;
    int posted = 0;
    for (GraphAutomorphisms.Permutation g : result.generators()) {
      // the variables the generator moves, in the lex-leader order; the others compare equal
      List<Integer> moved = new ArrayList<>();
      for (int v : g.points()) {
        if (varAt[v] != null) {
          moved.add(v);
        }
      }
      moved.sort((a, b) -> Integer.compare(rankAt[a], rankAt[b]));
      List<IntVar> xs = new ArrayList<>();
      List<IntVar> ys = new ArrayList<>();
      Map<IntVar, IntVar> equal = new IdentityHashMap<>();
      for (int v : moved) {
        IntVar x = varAt[v];
        IntVar y = varAt[g.image(v)];
        IntVar rx = find(equal, x);
        IntVar ry = find(equal, y);
        if (rx != ry) {
          xs.add(x);
          ys.add(y);
          equal.put(rx, ry);
        }
      }
      if (xs.isEmpty()) {
        continue;
      }
      moving++;
      LexOrder lex = new LexOrder(xs.toArray(new IntVar[0]), ys.toArray(new IntVar[0]), false);
      // added constraints do not change the static degrees that variable selections read
      lex.setDegreeWeight(0);
      store.impose(lex);
      posted++;
    }
    return new Outcome(n, moving, posted, result.complete(), null);
  }

  private static IntVar find(Map<IntVar, IntVar> parent, IntVar v) {
    IntVar p = parent.get(v);
    while (p != null) {
      v = p;
      p = parent.get(v);
    }
    return v;
  }

  private void buildGraph(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            addConstraint((ASTConstElem) item);
          }
        }
      }
    }
    if (objective != null) {
      varVertex(objective);
    }
  }

  private void addConstraint(ASTConstElem item) {
    String name = item.getName();
    int arity = item.jjtGetNumChildren();
    Atom[][] args = new Atom[arity][];
    boolean[] array = new boolean[arity];
    for (int i = 0; i < arity; i++) {
      SimpleNode arg = (SimpleNode) item.jjtGetChild(i);
      if (arg.getId() == JJTARRAYLITERAL) {
        array[i] = true;
        args[i] = arrayAtoms(arg);
      } else if (isArrayName(arg)) {
        array[i] = true;
        args[i] = namedArray(((ASTScalarFlatExpr) arg).getIdent());
      } else {
        args[i] = new Atom[] {scalarAtom(arg)};
      }
    }
    String prefix = name + "/" + arity + "|";
    Spec spec = SPECS.get(name);
    if (!distinct.add(prefix + canonical(spec, args, array))) {
      // the same constraint again, once variables fixed at the root are replaced by their values
      return;
    }
    // the constants become part of the constraint's colour, so they need no vertices
    int constraint = vertex(null);
    List<String> constants = new ArrayList<>();

    boolean[] grouped = new boolean[arity];
    if (spec != null) {
      for (int a : spec.symmetric()) {
        if (a >= arity || array[a]) {
          throw new Unsupported("unexpected arguments of " + name);
        }
        grouped[a] = true;
        position(constraint, "y|" + prefix, args[a][0], constants);
      }
      for (int b = 0; b < spec.bags().length; b++) {
        int[] bag = spec.bags()[b];
        for (int a : bag) {
          if (a >= arity || !array[a] || args[a].length != args[bag[0]].length) {
            throw new Unsupported("unexpected arguments of " + name);
          }
          grouped[a] = true;
        }
        addBag(constraint, prefix + "b" + b + "|", bag, args, constants);
      }
    }
    for (int a = 0; a < arity; a++) {
      if (grouped[a]) {
        continue;
      }
      if (array[a]) {
        constants.add(a + "#" + args[a].length);
        for (int j = 0; j < args[a].length; j++) {
          position(constraint, "o|" + prefix + a + "[" + j + "]", args[a][j], constants);
        }
      } else {
        position(constraint, "o|" + prefix + a, args[a][0], constants);
      }
    }
    constants.sort(null);
    colorKeys.set(constraint, "c|" + prefix + String.join(";", constants));
  }

  /**
   * A text that is the same for two constraints exactly when they are the same constraint up to the
   * order of the arguments that the spec groups.
   */
  private String canonical(Spec spec, Atom[][] args, boolean[] array) {
    int arity = args.length;
    boolean[] grouped = new boolean[arity];
    StringBuilder key = new StringBuilder();
    if (spec != null) {
      List<String> sym = new ArrayList<>();
      for (int a : spec.symmetric()) {
        if (a < arity) {
          grouped[a] = true;
          sym.add(id(args[a][0]));
        }
      }
      sym.sort(null);
      key.append(sym);
      for (int[] bag : spec.bags()) {
        List<String> items = new ArrayList<>();
        for (int a : bag) {
          if (a >= arity || args[a].length != args[bag[0]].length) {
            throw new Unsupported("unexpected arguments");
          }
          grouped[a] = true;
        }
        for (int j = 0; j < args[bag[0]].length; j++) {
          items.add(item(bag, args, j));
        }
        items.sort(null);
        key.append(items);
      }
    }
    for (int a = 0; a < arity; a++) {
      if (!grouped[a]) {
        key.append(array[a] ? "[" : "(");
        for (Atom atom : args[a]) {
          key.append(id(atom)).append(',');
        }
      }
    }
    return key.toString();
  }

  private String item(int[] bag, Atom[][] args, int j) {
    StringBuilder item = new StringBuilder();
    for (int a : bag) {
      item.append(id(args[a][j])).append(',');
    }
    return item.toString();
  }

  private String id(Atom atom) {
    return atom.isConstant() ? atom.constant() : "#" + atomVertex(atom);
  }

  /**
   * The items of a bag: the elements at one index of the bag's arrays, interchangeable with the
   * items at other indices. An item of constants only is part of the constraint's colour, and equal
   * items are one vertex with their number in its colour.
   */
  private void addBag(
      int constraint, String prefix, int[] bag, Atom[][] args, List<String> constants) {
    Map<String, Integer> multiplicity = new HashMap<>();
    List<Integer> firsts = new ArrayList<>();
    for (int j = 0; j < args[bag[0]].length; j++) {
      if (multiplicity.merge(item(bag, args, j), 1, Integer::sum) == 1) {
        firsts.add(j);
      }
    }
    for (int j : firsts) {
      StringBuilder key = new StringBuilder("b|").append(prefix);
      int variables = 0;
      for (int a : bag) {
        Atom atom = args[a][j];
        key.append(atom.isConstant() ? atom.constant() : "_").append(',');
        if (!atom.isConstant()) {
          variables++;
        }
      }
      key.append('x').append(multiplicity.get(item(bag, args, j)));
      if (variables == 0) {
        constants.add(key.toString());
        continue;
      }
      int item = vertex(key.toString());
      edge(constraint, item);
      for (int k = 0; k < bag.length; k++) {
        Atom atom = args[bag[k]][j];
        if (atom.isConstant()) {
          continue;
        }
        if (variables == 1) {
          edge(item, atomVertex(atom));
        } else {
          int part = vertex("p|" + prefix + k);
          edge(item, part);
          edge(part, atomVertex(atom));
        }
      }
    }
  }

  private void position(int constraint, String key, Atom atom, List<String> constants) {
    if (atom.isConstant()) {
      constants.add(key + "=" + atom.constant());
      return;
    }
    int p = vertex(key);
    edge(constraint, p);
    edge(p, atomVertex(atom));
  }

  private int atomVertex(Atom atom) {
    if (atom.var() != null) {
      return varVertex(atom.var());
    }
    // a float or set variable is kept in place: a colour of its own
    return otherVertex.computeIfAbsent(atom.other(), v -> vertex("u|" + otherVertex.size()));
  }

  private int varVertex(IntVar x) {
    Integer v = varVertex.get(x);
    if (v == null) {
      String key =
          x == objective
              ? "v|objective"
              : "v|" + x.getClass().getName() + "|" + x.dom().getClass().getName() + "|" + x.dom();
      v = vertex(key);
      varVertex.put(x, v);
      vars.add(x);
    }
    return v;
  }

  private int vertex(String key) {
    int v = colorKeys.size();
    colorKeys.add(key);
    if (v == adjacency.length) {
      adjacency = Arrays.copyOf(adjacency, 2 * v);
      degree = Arrays.copyOf(degree, 2 * v);
    }
    adjacency[v] = new int[2];
    return v;
  }

  private void edge(int a, int b) {
    add(a, b);
    add(b, a);
  }

  private void add(int a, int b) {
    if (degree[a] == adjacency[a].length) {
      adjacency[a] = Arrays.copyOf(adjacency[a], 2 * degree[a]);
    }
    adjacency[a][degree[a]++] = b;
  }

  private boolean isArrayName(SimpleNode arg) {
    if (arg.getId() != JJTSCALARFLATEXPR || ((ASTScalarFlatExpr) arg).getType() != 2) {
      return false;
    }
    String ident = ((ASTScalarFlatExpr) arg).getIdent();
    return dictionary.getVariableArray(ident) != null
        || dictionary.getSetArray(ident) != null
        || dictionary.getFloatArray(ident) != null
        || dictionary.variableFloatArrayTable.containsKey(ident)
        || dictionary.setVariableArrayTable.containsKey(ident);
  }

  private Atom[] arrayAtoms(SimpleNode arg) {
    Atom[] atoms = new Atom[arg.jjtGetNumChildren()];
    for (int i = 0; i < atoms.length; i++) {
      atoms[i] = scalarAtom((SimpleNode) arg.jjtGetChild(i));
    }
    return atoms;
  }

  private Atom scalarAtom(SimpleNode arg) {
    if (arg.getId() == JJTSETLITERAL) {
      return constant("s" + dump(arg));
    }
    if (arg.getId() != JJTSCALARFLATEXPR) {
      throw new Unsupported("argument " + arg);
    }
    ASTScalarFlatExpr e = (ASTScalarFlatExpr) arg;
    return switch (e.getType()) {
      case 0, 1 -> constant("i" + e.getInt());
      case 4 -> constant("t" + e.getString());
      case 5 -> constant("f" + e.getFloat());
      case 2 -> identAtom(e.getIdent());
      case 3 -> {
        IntVar[] a = dictionary.getVariableArray(e.getIdent());
        if (a == null || e.getInt() < 0 || e.getInt() >= a.length) {
          throw new Unsupported("array access " + e.getIdent());
        }
        yield variable(a[e.getInt()]);
      }
      default -> throw new Unsupported("argument " + e);
    };
  }

  private Atom identAtom(String ident) {
    IntVar v = dictionary.getVariable(ident);
    if (v != null) {
      return variable(v);
    }
    Integer i = dictionary.checkInt(ident);
    if (i != null) {
      return constant("i" + i);
    }
    if (dictionary.getSet(ident) != null) {
      return constant("s" + dictionary.getSet(ident));
    }
    Double f = dictionary.checkFloat(ident);
    if (f != null) {
      return constant("f" + f);
    }
    Var other = dictionary.getFloatVariable(ident);
    if (other == null) {
      other = dictionary.getSetVariable(ident);
    }
    if (other != null) {
      return new Atom(null, other, null);
    }
    throw new Unsupported("identifier " + ident);
  }

  /**
   * The atoms of an array given by name; arrays of parameters are constants, arrays of float or set
   * variables are not supported.
   */
  private Atom[] namedArray(String ident) {
    IntVar[] a = dictionary.getVariableArray(ident);
    if (a != null) {
      Atom[] atoms = new Atom[a.length];
      for (int i = 0; i < a.length; i++) {
        atoms[i] = variable(a[i]);
      }
      return atoms;
    }
    if (dictionary.getSetArray(ident) != null) {
      return Arrays.stream(dictionary.getSetArray(ident))
          .map(s -> constant("s" + s))
          .toArray(Atom[]::new);
    }
    Var[] others = dictionary.variableFloatArrayTable.get(ident);
    if (others == null) {
      others = dictionary.setVariableArrayTable.get(ident);
    }
    if (others != null) {
      return Arrays.stream(others).map(v -> new Atom(null, v, null)).toArray(Atom[]::new);
    }
    if (dictionary.getFloatArray(ident) != null) {
      return Arrays.stream(dictionary.getFloatArray(ident))
          .mapToObj(f -> constant("f" + f))
          .toArray(Atom[]::new);
    }
    throw new Unsupported("array " + ident);
  }

  private static Atom variable(IntVar v) {
    return v.singleton() ? constant("i" + v.value()) : new Atom(v, null, null);
  }

  private static Atom constant(String c) {
    return new Atom(null, null, c);
  }

  private static String dump(SimpleNode node) {
    StringBuilder s = new StringBuilder(node.toString());
    s.append('(');
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      s.append(dump((SimpleNode) node.jjtGetChild(i))).append(',');
    }
    return s.append(')').toString();
  }
}
