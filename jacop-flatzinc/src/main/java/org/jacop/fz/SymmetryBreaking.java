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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.Function;
import java.util.function.LongSupplier;
import org.jacop.constraints.LexChain;
import org.jacop.constraints.LexOrder;
import org.jacop.constraints.SeqPrecedeChain;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqY;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.presolve.GraphAutomorphisms;
import org.jacop.set.constraints.ChannelBoolSet;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

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
 * vertex with their number in its colour. Float variables get a colour each, so no symmetry moves
 * them. A set variable is a vertex coloured by its domain, joined to one vertex for each element of
 * its upper bound that is not in its lower bound, coloured by the element; a symmetry that maps one
 * set variable to another maps the element vertices of the same element onto each other, so the
 * Booleans {@code e in s} (posted by {@link ChannelBoolSet} for the set variables a symmetry moves)
 * take part in the lex-leader constraints like integer variables.
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
 * <p>The generators alone leave orbits of the whole group unordered (the lex-leader constraint of
 * the 3-cycle (x0 x1 x2) keeps x0 <= x1 but not x0 <= x2), so Schreier-Sims cuts {@code x_b <= x_j}
 * over the orbits of the stabilizer chain are posted as well where the other constraints do not
 * already imply them (Liberti and Ostrowski, J. Global Optim. 60, 2014; Salvagnin, CPAIOR 2018),
 * see {@link #schreierSims}.
 *
 * <p>A model with an argument that is not understood is left as it is.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class SymmetryBreaking implements ParserTreeConstants {

  /** The most Schreier-Sims cuts posted. */
  static final int MAX_CUTS = 100_000;

  /** The largest orbit size times generators walked to find the symmetry of a cut. */
  static final long MAX_TREE_WORK = 10_000_000L;

  /**
   * Whether set variables may be moved by symmetries (org.jacop.fz.symmetrySets, default true), in
   * models whose search annotation branches on set variables. Without it every set variable has a
   * colour of its own.
   */
  static final boolean SETS = !"false".equals(System.getProperty("org.jacop.fz.symmetrySets"));

  /**
   * The most element vertices that set variables add to the graph; the set variables met after that
   * keep a colour of their own.
   */
  static final int MAX_SET_ELEMENTS = 200_000;

  /**
   * Whether value symmetries are also looked for in spaces joined through set variables and shared
   * values, when the plain value spaces give none (org.jacop.fz.symmetryEncoded, default true).
   */
  static final boolean ENCODED =
      !"false".equals(System.getProperty("org.jacop.fz.symmetryEncoded"));

  /** The n-ary union that a chain of binary unions stands for: {@code s = union(xs)}. */
  static final String UNION_N = "jacop_symmetry_union";

  /** Graphs with more vertices are not searched. */
  static final int MAX_VERTICES = 2_000_000;

  /** The largest number of adjacency entries the automorphism search reads. */
  static final long MAX_WORK = 200_000_000L;

  /**
   * What was done.
   *
   * @param vertices vertices of the model graph, 0 if no graph was built.
   * @param generators generators found that move variables.
   * @param constraints lex-leader constraints posted, value precedences and lex chains included.
   * @param complete true if the automorphism search ran to the end.
   * @param skipped why no graph was built, or null.
   * @param precedences value precedence chains posted, one per class of interchangeable values.
   * @param orbitopes lex chains posted over interchangeable columns of variables.
   */
  record Outcome(
      int vertices,
      int generators,
      int constraints,
      boolean complete,
      String skipped,
      int precedences,
      int orbitopes,
      int cuts,
      int impliedCuts) {

    Outcome(int vertices, int generators, int constraints, boolean complete, String skipped) {
      this(vertices, generators, constraints, complete, skipped, 0, 0);
    }

    Outcome(
        int vertices,
        int generators,
        int constraints,
        boolean complete,
        String skipped,
        int precedences,
        int orbitopes) {
      this(vertices, generators, constraints, complete, skipped, precedences, orbitopes, 0, 0);
    }
  }

  private static class Unsupported extends RuntimeException {
    Unsupported(String reason) {
      super(reason, null, false, false);
    }
  }

  /** The time given ran out before the graph was built. */
  private static final class OutOfTime extends Unsupported {
    OutOfTime() {
      super("time limit reached while building the graph");
    }
  }

  /**
   * An argument value: an integer variable that is not fixed, a float or set variable, which no
   * symmetry moves, or a constant written as a string. An integer constant has its value; when it
   * stands for a value of a value space ({@code space >= 0}) it is a vertex, not a constant.
   */
  private record Atom(IntVar aVar, Var other, String constant, int space, int value) {
    boolean isConstant() {
      return constant != null && space < 0;
    }

    boolean isInt() {
      return constant != null && constant.charAt(0) == 'i';
    }
  }

  /** How the arguments of a constraint are grouped; arguments in no group keep their position. */
  private static final class Spec {
    final int[] symmetric;
    final int[][] bags;

    Spec(int[] symmetric, int[][] bags) {
      this.symmetric = symmetric;
      this.bags = bags;
    }

    static Spec sym(int... args) {
      return new Spec(args, new int[0][]);
    }

    static Spec grouped(int[]... bags) {
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
      SPECS.put(s, Spec.grouped(new int[] {0, 1}));
      SPECS.put(s + "_reif", Spec.grouped(new int[] {0, 1}));
      SPECS.put(s + "_imp", Spec.grouped(new int[] {0, 1}));
    }
    SPECS.put("bool_lin_le", Spec.grouped(new int[] {0, 1}));
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
      SPECS.put(s, Spec.grouped(new int[] {0}));
    }
    for (String s :
        new String[] {
          "array_int_maximum", "array_int_minimum", "jacop_nvalue", "jacop_maximum", "jacop_minimum"
        }) {
      SPECS.put(s, Spec.grouped(new int[] {1}));
    }
    SPECS.put("bool_clause", Spec.grouped(new int[] {0}, new int[] {1}));
    SPECS.put("bool_clause_reif", Spec.grouped(new int[] {0}, new int[] {1}));
    SPECS.put("bool_clause_imp", Spec.grouped(new int[] {0}, new int[] {1}));
    // set operations whose two operands can be exchanged
    for (String s :
        new String[] {
          "set_union",
          "set_intersect",
          "set_symdiff",
          "set_eq",
          "set_ne",
          "set_eq_reif",
          "set_ne_reif",
          "set_eq_imp",
          "set_ne_imp",
          "jacop_disjoint"
        }) {
      SPECS.put(s, Spec.sym(0, 1));
    }
    SPECS.put(UNION_N, Spec.grouped(new int[] {0}));
    SPECS.put("jacop_cumulative", Spec.grouped(new int[] {0, 1, 2}));
    SPECS.put("jacop_diff2_strict", Spec.grouped(new int[] {0, 1, 2, 3}));
    SPECS.put("jacop_bin_packing", Spec.grouped(new int[] {0, 2}));
    SPECS.put("jacop_bin_packing_capacity", Spec.grouped(new int[] {0, 2}));
  }

  /**
   * How the values of a constraint's variables are used, for value symmetries: the arguments in
   * {@code shared} hold variables and constants of one value space, and the constraint holds for an
   * assignment exactly when it holds after the same permutation of that space is applied to them
   * all; the argument {@code indexed}, if not -1, is an array whose element {@code j} belongs to
   * the value {@code offset + j}, with {@code offset} the integer constant of argument {@code
   * offsetArg}. Every other argument uses its values as numbers.
   */
  private record ValueSpec(int[] shared, int indexed, int offsetArg) {
    static ValueSpec of(int... shared) {
      return new ValueSpec(shared, -1, -1);
    }

    @Override
    public boolean equals(Object o) {
      return o instanceof ValueSpec v
          && Arrays.equals(shared, v.shared)
          && indexed == v.indexed
          && offsetArg == v.offsetArg;
    }

    @Override
    public int hashCode() {
      return 31 * (31 * Arrays.hashCode(shared) + indexed) + offsetArg;
    }

    @Override
    public String toString() {
      return "ValueSpec" + Arrays.toString(shared) + "/" + indexed + "/" + offsetArg;
    }
  }

  private static final Map<String, ValueSpec> VALUE_SPECS = new HashMap<>();

  static {
    for (String s :
        new String[] {
          "int_eq", "int_ne", "int_eq_reif", "int_ne_reif", "int_eq_imp", "int_ne_imp",
        }) {
      VALUE_SPECS.put(s, ValueSpec.of(0, 1));
    }
    VALUE_SPECS.put("array_int_element", ValueSpec.of(1, 2));
    VALUE_SPECS.put("array_var_int_element", ValueSpec.of(1, 2));
    for (String s :
        new String[] {
          "jacop_alldiff",
          "jacop_alldistinct",
          "jacop_alldistinct_reif",
          "jacop_all_equal_int",
          "jacop_all_equal_int_reif"
        }) {
      VALUE_SPECS.put(s, ValueSpec.of(0));
    }
    for (String s :
        new String[] {
          "jacop_count",
          "jacop_count_reif",
          "jacop_count_var",
          "jacop_count_var_reif",
          "jacop_count_var_ge",
          "jacop_count_var_le",
          "jacop_atleast",
          "jacop_atleast_reif",
          "jacop_atmost",
          "jacop_atmost_reif",
          "jacop_member_int",
          "jacop_member_int_reif"
        }) {
      VALUE_SPECS.put(s, ValueSpec.of(0, 1));
    }
    VALUE_SPECS.put("jacop_nvalue", ValueSpec.of(1));
    VALUE_SPECS.put("jacop_gcc", new ValueSpec(new int[] {0}, 1, 2));
    VALUE_SPECS.put("jacop_bin_packing", new ValueSpec(new int[] {0}, 1, 3));
    VALUE_SPECS.put("jacop_bin_packing_capacity", new ValueSpec(new int[] {0}, 1, 3));
  }

  /** Value spaces with more values are not searched for value symmetries. */
  static final int MAX_VALUES = 10_000;

  /** The largest number of variable-value pairs of a value space with different domains. */
  static final int MAX_DOMAIN_EDGES = 1_000_000;

  /** The most values of a space whose permutation group is computed beyond transpositions. */
  static final int MAX_SCHREIER_SIMS = 40;

  /** A constraint of the model with its arguments. */
  private record Item(String name, Atom[][] args, boolean[] array) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Item i
          && name.equals(i.name)
          && Arrays.deepEquals(args, i.args)
          && Arrays.equals(array, i.array);
    }

    @Override
    public int hashCode() {
      return 31 * (31 * name.hashCode() + Arrays.deepHashCode(args)) + Arrays.hashCode(array);
    }

    @Override
    public String toString() {
      return name + Arrays.deepToString(args);
    }
  }

  private final Store store;
  private final Tables dictionary;
  // the clock of the time given, in nanoseconds; tests replace it to end the time at every check
  static LongSupplier clock = System::nanoTime;
  // when the time given to run ends (clock)
  private long deadline = Long.MAX_VALUE;
  // whether the lex-leader keeps the largest solution of an orbit instead of the smallest
  private boolean largest;
  // whether the search is free search (-f), which does not follow the search annotation
  private boolean free;
  // whether set variables are vertices of the variable graph that symmetries may move
  private boolean setsMove;
  // the constraints posted, as their kind and variables, for added()
  private final List<String> postedKinds = new ArrayList<>();
  private final List<IntVar[][]> postedVariables = new ArrayList<>();
  // the constraints posted with their symmetries, for local search
  private final SymmetryCanonicalizer canonicalizer = new SymmetryCanonicalizer();
  // the atoms of each named array, read once: a table of a hundred thousand tuples is often an
  // argument of many constraints
  private final Map<String, Atom[]> namedArrays = new HashMap<>();
  // one atom for each integer constant
  private final Map<Integer, Atom> intAtoms = new HashMap<>();
  // the key of each array of constants, the same for arrays with the same elements
  private final Map<Atom[], String> constantArrays = new IdentityHashMap<>();
  private final Map<Contents, String> contentKeys = new HashMap<>();

  // Schreier-Sims cuts: "on" posts them, "count" only counts them, "off" skips them
  private final String schreierSims =
      System.getProperty("org.jacop.fz.symmetry.schreierSims", "on");

  SymmetryBreaking(Store store, Tables dictionary) {
    this.store = store;
    this.dictionary = dictionary;
  }

  private void note(String kind, IntVar[]... rows) {
    postedKinds.add(kind);
    postedVariables.add(rows);
  }

  /**
   * Describes the constraints posted by {@link #run}, so that two stores of the same model can tell
   * whether they added the same ones: the same text means the same constraints.
   *
   * @param name the name of a variable of the model, null for any other variable
   * @return the text, empty when nothing was posted, or null when a constraint has a variable with
   *     no name
   */
  String added(Function<IntVar, String> name) {
    StringBuilder s = new StringBuilder();
    for (int k = 0; k < postedKinds.size(); k++) {
      s.append(postedKinds.get(k));
      for (IntVar[] row : postedVariables.get(k)) {
        s.append('[');
        for (IntVar x : row) {
          String n = name.apply(x);
          if (n == null) {
            return null;
          }
          s.append(n).append(',');
        }
        s.append(']');
      }
      s.append(';');
    }
    return s.toString();
  }

  /**
   * Lets the symmetries of the variable graph move set variables, with {@link #SETS}, when the
   * search annotation branches on set variables. In a search on integers alone the symmetries they
   * reveal slowed the search down (2023 valve-network), so every set variable then keeps a colour
   * of its own.
   *
   * @param sets true when the search annotation branches on set variables.
   * @return this.
   */
  SymmetryBreaking branchesOnSets(boolean sets) {
    this.setsMove = SETS && sets;
    return this;
  }

  /**
   * Keeps the lexicographically largest solution of each orbit of the variable symmetries, for a
   * search that tries the largest values first; with the smallest one kept, such a search would
   * first meet the solutions the lex-leader constraints remove. Value precedence keeps the values
   * in order of first use, which goes with the smallest solution only, so the variable symmetries
   * are then broken towards the smallest one all the same.
   *
   * @param largest true for the largest solution.
   * @return this.
   */
  SymmetryBreaking keepLargest(boolean largest) {
    this.largest = largest;
    return this;
  }

  /**
   * Tells that the search is free search. Value precedence is then left out of a model that
   * minimizes the largest load of a bin packing (identical parallel machines, P||Cmax): under
   * {@code --lcg -f} it multiplies the failures there (n41-m7-s18: 214 without it, 2,000-30,000
   * with it), while it helps bin packing that minimizes the bins used.
   *
   * @param free true for free search.
   * @return this.
   */
  SymmetryBreaking freeSearch(boolean free) {
    this.free = free;
    return this;
  }

  /** Whether the objective is the largest load of a bin packing of the model. */
  private static boolean largestLoad(List<Item> items, IntVar objective) {
    if (objective == null) {
      return false;
    }
    Set<IntVar> loads = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Item item : items) {
      if (item.name().startsWith("jacop_bin_packing") && item.args().length > 1) {
        for (Atom a : item.args()[1]) {
          if (a.aVar() != null) {
            loads.add(a.aVar());
          }
        }
      }
    }
    for (Item item : items) {
      Atom[][] args = item.args();
      if ((item.name().equals("jacop_maximum") || item.name().equals("array_int_maximum"))
          && args.length == 2
          && args[0].length == 1
          && args[0][0].aVar() == objective
          && args[1].length > 0) {
        boolean all = true;
        for (Atom a : args[1]) {
          all &= a.aVar() != null && loads.contains(a.aVar());
        }
        if (all) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Finds the symmetries of the model and posts the constraints that break them.
   *
   * <p>Value symmetries are searched first, on a graph where the variables whose values are only
   * compared for equality (a value space, see {@link ValueSpec}) are joined to vertices for their
   * values. An automorphism of that graph that fixes the variables of a space permutes its values,
   * and when the automorphisms permute a set of values of the space in every way while fixing its
   * other values, the values are interchangeable: a value precedence chain over the variables of
   * the space, in increasing order of the values, keeps the lexicographically smallest solution of
   * every orbit (Law and Lee, CP 2004). The variables of those spaces then come first in the
   * lex-leader order of the variable symmetries, so that both kinds of constraints keep the same
   * solution of each orbit.
   *
   * <p>A minimized objective that only bounds the variables of one value space from above ({@code x
   * <= z}, {@code z = max(xs)}), as the number of colours of a graph colouring, breaks the value
   * symmetry. The constraints on it are then left out of the value graph: relabelling the values of
   * a solution in the order of their first use never raises the largest one, so the
   * lexicographically smallest optimal solution satisfies the precedence chains (a dominance, not a
   * symmetry), and the optimum is kept.
   *
   * @param astTree the parsed model.
   * @param objective the objective variable, or null for a satisfaction problem.
   * @param minimize true if the objective is minimized.
   * @param order variables in the order their lex-leader constraints compare them first, for
   *     example those of the search annotation.
   * @param maxNanos the longest time the automorphism search runs.
   * @return what was done.
   */
  Outcome run(
      SimpleNode astTree, IntVar objective, boolean minimize, List<Var> order, long maxNanos) {
    IntVar goal = objective != null && !objective.singleton() ? objective : null;
    // reading the model and building its graphs count in the time given, as the search does
    deadline = clock.getAsLong() + maxNanos;
    List<Item> items;
    try {
      items = parse(astTree);
    } catch (Unsupported e) {
      return new Outcome(0, 0, 0, !(e instanceof OutOfTime), e.getMessage());
    } catch (IllegalArgumentException | ClassCastException e) {
      // a form of argument the front end reads elsewhere; the model is left as it is
      return new Outcome(0, 0, 0, true, String.valueOf(e.getMessage()));
    }

    // the lex-leader order: the variables of the search annotation, then the others as the model
    // first uses them
    List<IntVar> ranked = new ArrayList<>();
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Var v : order) {
      if (v instanceof IntVar iv && !iv.singleton() && seen.add(iv)) {
        ranked.add(iv);
      }
    }
    for (Item item : items) {
      for (Atom[] arg : item.args()) {
        for (Atom a : arg) {
          if (a.aVar() != null && seen.add(a.aVar())) {
            ranked.add(a.aVar());
          }
        }
      }
    }

    ValueOutcome values = breakValueSymmetries(items, goal, minimize, ranked, maxNanos / 2);
    if (values.posted() == 0 && ENCODED && !(free && minimize && largestLoad(items, goal))) {
      Set<IntVar> annotated = Collections.newSetFromMap(new IdentityHashMap<>());
      for (Var v : order) {
        if (v instanceof IntVar iv) {
          annotated.add(iv);
        }
      }
      values = breakEncodedValueSymmetries(items, goal, ranked, annotated, maxNanos / 2);
    }
    if (!values.first().isEmpty()) {
      List<IntVar> reordered = new ArrayList<>(values.first());
      Set<IntVar> front = Collections.newSetFromMap(new IdentityHashMap<>());
      front.addAll(values.first());
      for (IntVar v : ranked) {
        if (!front.contains(v)) {
          reordered.add(v);
        }
      }
      ranked = reordered;
    }

    Graph graph = new Graph(goal, null);
    try {
      // a chain of set unions is one n-ary union, whose operands can be exchanged
      for (Item item : setsMove ? flattenUnions(items) : items) {
        checkTime();
        graph.addConstraint(item);
      }
      graph.finish();
    } catch (Unsupported e) {
      return new Outcome(
          0, 0, values.posted(), !(e instanceof OutOfTime), e.getMessage(), values.posted(), 0);
    }
    int n = graph.size();
    if (n > MAX_VERTICES) {
      return new Outcome(n, 0, values.posted(), true, "graph too large", values.posted(), 0);
    }

    // the vertices of the variables, and of the elements of set variables, in the lex-leader
    // order: those of the search annotation first, then the integer variables as the model first
    // uses them, then the elements of the other set variables
    List<Integer> rankedVertices = new ArrayList<>();
    boolean[] isRanked = new boolean[n];
    for (Var v : order) {
      if (v instanceof IntVar iv) {
        rankVertex(graph.varVertices.get(iv), rankedVertices, isRanked);
      } else if (v instanceof SetVar sv && graph.elementVertices.containsKey(sv)) {
        for (int e : graph.elementVertices.get(sv)) {
          rankVertex(e, rankedVertices, isRanked);
        }
      }
    }
    for (IntVar v : ranked) {
      rankVertex(graph.varVertices.get(v), rankedVertices, isRanked);
    }
    for (IntVar v : graph.vars) {
      rankVertex(graph.varVertices.get(v), rankedVertices, isRanked);
    }
    for (SetVar sv : graph.sets) {
      for (int e : graph.elementVertices.get(sv)) {
        rankVertex(e, rankedVertices, isRanked);
      }
    }
    // the variables are the base of the search, in the lex-leader order
    int[] base = rankedVertices.stream().mapToInt(Integer::intValue).toArray();
    long left = Math.max(0, deadline - clock.getAsLong());
    GraphAutomorphisms.Result result =
        new GraphAutomorphisms(graph.colors(), graph.adjacency(), base).generators(MAX_WORK, left);

    IntVar[] varAt = new IntVar[n];
    int[] rankAt = new int[n];
    for (int r = 0; r < base.length; r++) {
      rankAt[base[r]] = r;
    }
    graph.varVertices.forEach((x, v) -> varAt[v] = x);
    // the set variables that a generator moves get their Booleans
    for (GraphAutomorphisms.Permutation g : result.generators()) {
      for (int v : g.points()) {
        SetVar s = graph.setOfElement.get(v);
        if (s != null && varAt[v] == null) {
          channel(s, graph.elementVertices.get(s), varAt);
        }
      }
    }

    // interchangeable columns of variables are ordered by one lex chain
    List<GraphAutomorphisms.Permutation> generators = new ArrayList<>(result.generators());
    int orbitopes = 0;
    int posted = values.posted();
    boolean descending = largest && values.posted() == 0;
    // x <= y pairs the posted constraints compare first, which Schreier-Sims cuts need not repeat
    List<IntVar[]> implied = new ArrayList<>();
    for (IntVar[][] columns : interchangeableSets(result.generators(), base, graph, varAt)) {
      if (descending) {
        Collections.reverse(Arrays.asList(columns));
      }
      for (int c = 0; c + 1 < columns.length; c++) {
        implied.add(new IntVar[] {columns[c][0], columns[c + 1][0]});
      }
      LexChain chain = new LexChain(columns);
      chain.setDegreeWeight(0);
      store.impose(chain);
      canonicalizer.chain(chain, columns);
      note("chain", columns);
      orbitopes++;
      posted++;
    }
    for (IntVar[][] columns : orbitopes(generators, varAt, rankAt)) {
      if (descending) {
        Collections.reverse(Arrays.asList(columns));
      }
      for (int c = 0; c + 1 < columns.length; c++) {
        implied.add(new IntVar[] {columns[c][0], columns[c + 1][0]});
      }
      LexChain chain = new LexChain(columns);
      chain.setDegreeWeight(0);
      store.impose(chain);
      canonicalizer.chain(chain, columns);
      note("chain", columns);
      orbitopes++;
      posted++;
    }
    Set<GraphAutomorphisms.Permutation> unchained =
        Collections.newSetFromMap(new IdentityHashMap<>());
    unchained.addAll(generators);

    int moving = 0;
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
      if (!unchained.contains(g)) {
        // ordered by the lex chain of its orbitope
        continue;
      }
      IntVar[] x = xs.toArray(new IntVar[0]);
      IntVar[] y = ys.toArray(new IntVar[0]);
      implied.add(descending ? new IntVar[] {y[0], x[0]} : new IntVar[] {x[0], y[0]});
      LexOrder lex = descending ? new LexOrder(y, x, false) : new LexOrder(x, y, false);
      // added constraints do not change the static degrees that variable selections read
      lex.setDegreeWeight(0);
      store.impose(lex);
      canonicalizer.lex(
          lex,
          x,
          y,
          descending,
          moves(g, varAt, true).orElse(null),
          moves(g, varAt, false).orElse(null));
      note(descending ? "lex>" : "lex<", x, y);
      posted++;
    }
    int[] cuts =
        schreierSims.equals("off")
            ? new int[2]
            : schreierSims(
                result.generators(), varAt, rankAt, descending, implied, schreierSims.equals("on"));
    posted += cuts[0] > 0 && schreierSims.equals("on") ? cuts[0] : 0;
    return new Outcome(
        n,
        moving,
        posted,
        result.complete() && values.complete(),
        null,
        values.posted(),
        orbitopes,
        cuts[0],
        cuts[1]);
  }

  /**
   * Posts the Schreier-Sims cuts of the variable symmetries (Liberti and Ostrowski,
   * "Stabilizer-based symmetry breaking constraints for mathematical programs", J. Global Optim.
   * 60, 2014; Salvagnin, "Symmetry breaking inequalities from the Schreier-Sims table", CPAIOR
   * 2018, LNCS 10848). Each generator fixes every variable ranked before the first variable b it
   * moves, so the generators whose first moved variable is ranked at or after b generate a group
   * H_b that fixes them all. The lexicographically smallest solution x of its orbit then has x_b <=
   * x_j for every j of the orbit of b under H_b: the symmetric solution that brings x_j to b is
   * equal to x before b. The same solution satisfies every lex-leader constraint, lex chain and
   * value precedence posted, so the cuts keep it. Cuts the posted constraints already imply through
   * their first positions are left out.
   *
   * @return the cuts posted (or counted when post is false) and those left out as implied.
   */
  private int[] schreierSims(
      List<GraphAutomorphisms.Permutation> generators,
      IntVar[] varAt,
      int[] rankAt,
      boolean descending,
      List<IntVar[]> implied,
      boolean post) {
    // the generators by the rank of the first variable they move
    TreeMap<Integer, List<GraphAutomorphisms.Permutation>> byFirst = new TreeMap<>();
    Map<Integer, Integer> baseAt = new HashMap<>();
    for (GraphAutomorphisms.Permutation g : generators) {
      int first = -1;
      for (int v : g.points()) {
        if (varAt[v] != null
            && varAt[g.image(v)] != null
            && (first < 0 || rankAt[v] < rankAt[first])) {
          first = v;
        }
      }
      if (first >= 0) {
        byFirst.computeIfAbsent(rankAt[first], r -> new ArrayList<>()).add(g);
        baseAt.put(rankAt[first], first);
      }
    }
    if (byFirst.isEmpty()) {
      return new int[2];
    }
    // the edges from a variable to those the posted constraints keep at least as large (at most as
    // large when descending), through the first positions they compare
    Map<IntVar, List<IntVar>> above = new IdentityHashMap<>();
    for (IntVar[] e : implied) {
      IntVar from = descending ? e[1] : e[0];
      above.computeIfAbsent(from, k -> new ArrayList<>()).add(descending ? e[0] : e[1]);
    }
    // orbits by union-find over the variable vertices, from the deepest level up
    Map<Integer, Integer> parent = new HashMap<>();
    Map<Integer, List<Integer>> members = new HashMap<>();
    int posted = 0;
    int skipped = 0;
    // the generators of the levels seen, which fix every variable ranked before the current one
    List<GraphAutomorphisms.Permutation> below = new ArrayList<>();
    Map<GraphAutomorphisms.Permutation, IntVar[][]> moveOf = new IdentityHashMap<>();
    for (Map.Entry<Integer, List<GraphAutomorphisms.Permutation>> level :
        byFirst.descendingMap().entrySet()) {
      below.addAll(level.getValue());
      for (GraphAutomorphisms.Permutation g : level.getValue()) {
        int[] points = g.points();
        for (int i = 0; i < points.length; i++) {
          if (varAt[points[i]] != null && varAt[g.images()[i]] != null) {
            join(parent, members, points[i], g.images()[i]);
          }
        }
      }
      int b = baseAt.get(level.getKey());
      List<Integer> orbit = members.get(rootOf(parent, b));
      if (orbit == null) {
        continue;
      }
      Set<IntVar> reach = reachable(above, varAt[b]);
      Map<Integer, Object[]> tree = null;
      for (int j : orbit) {
        if (j == b) {
          continue;
        }
        if (outOfTime()) {
          // the cuts posted so far are each implied by the lex-leader order, as with MAX_CUTS
          return new int[] {posted, skipped};
        }
        if (reach.contains(varAt[j])) {
          skipped++;
          continue;
        }
        if (posted >= MAX_CUTS) {
          return new int[] {posted, skipped};
        }
        posted++;
        above.computeIfAbsent(varAt[b], k -> new ArrayList<>()).add(varAt[j]);
        if (post) {
          IntVar lo = descending ? varAt[j] : varAt[b];
          IntVar hi = descending ? varAt[b] : varAt[j];
          XlteqY cut = new XlteqY(lo, hi);
          store.impose(cut);
          if (tree == null) {
            tree = schreierTree(b, below, varAt, orbit.size());
          }
          canonicalizer.cut(cut, lo, hi, word(tree, j, varAt, moveOf));
          note("ss", new IntVar[] {lo, hi});
        }
      }
    }
    return new int[] {posted, skipped};
  }

  /**
   * The Schreier tree of b: each variable vertex of its orbit with the vertex it is reached from
   * and the generator that maps that vertex onto it; null when the orbit is too large to walk.
   */
  private Map<Integer, Object[]> schreierTree(
      int b, List<GraphAutomorphisms.Permutation> generators, IntVar[] varAt, int size) {
    if ((long) size * generators.size() > MAX_TREE_WORK) {
      return null;
    }
    Map<Integer, Object[]> tree = new HashMap<>();
    tree.put(b, new Object[] {b, null});
    List<Integer> queue = new ArrayList<>(List.of(b));
    for (int head = 0; head < queue.size(); head++) {
      int w = queue.get(head);
      for (GraphAutomorphisms.Permutation g : generators) {
        int u = g.image(w);
        if (u != w && varAt[u] != null && !tree.containsKey(u)) {
          tree.put(u, new Object[] {w, g});
          queue.add(u);
        }
      }
    }
    return tree;
  }

  /**
   * The symmetry that brings the value of j onto b, as the moves of generators in the order the
   * canonicalizer applies them; null when one of them is not known.
   */
  private static List<IntVar[][]> word(
      Map<Integer, Object[]> tree,
      int j,
      IntVar[] varAt,
      Map<GraphAutomorphisms.Permutation, IntVar[][]> moveOf) {
    if (tree == null || !tree.containsKey(j)) {
      return null;
    }
    List<IntVar[][]> moves = new ArrayList<>();
    int v = j;
    while (tree.get(v)[1] != null) {
      GraphAutomorphisms.Permutation g = (GraphAutomorphisms.Permutation) tree.get(v)[1];
      IntVar[][] m =
          moveOf.computeIfAbsent(
              g,
              k -> {
                Optional<IntVar[]> from = moves(k, varAt, true);
                Optional<IntVar[]> to = moves(k, varAt, false);
                return from.isPresent() && to.isPresent()
                    ? new IntVar[][] {from.get(), to.get()}
                    : new IntVar[0][];
              });
      if (m.length == 0) {
        return null;
      }
      moves.add(m);
      v = (Integer) tree.get(v)[0];
    }
    return moves;
  }

  /** The vertices reached from x along the edges. */
  private static Set<IntVar> reachable(Map<IntVar, List<IntVar>> edges, IntVar x) {
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    List<IntVar> stack = new ArrayList<>(List.of(x));
    while (!stack.isEmpty()) {
      IntVar v = stack.remove(stack.size() - 1);
      for (IntVar w : edges.getOrDefault(v, List.of())) {
        if (seen.add(w)) {
          stack.add(w);
        }
      }
    }
    return seen;
  }

  private static int rootOf(Map<Integer, Integer> parent, int v) {
    Integer p = parent.get(v);
    while (p != null && p != v) {
      v = p;
      p = parent.get(v);
    }
    return v;
  }

  private static void join(
      Map<Integer, Integer> parent, Map<Integer, List<Integer>> members, int a, int b) {
    int ra = rootOf(parent, a);
    int rb = rootOf(parent, b);
    if (ra == rb) {
      return;
    }
    List<Integer> ma = members.computeIfAbsent(ra, k -> new ArrayList<>(List.of(k)));
    List<Integer> mb = members.computeIfAbsent(rb, k -> new ArrayList<>(List.of(k)));
    if (ma.size() < mb.size()) {
      int t = ra;
      ra = rb;
      rb = t;
      List<Integer> mt = ma;
      ma = mb;
      mb = mt;
    }
    ma.addAll(mb);
    members.remove(rb);
    parent.put(rb, ra);
  }

  /** The most variables at the front of the lex-leader order whose permutations are examined. */
  static final int MAX_PREFIX = 64;

  /**
   * Set variables at the front of the lex-leader order that the symmetries permute in every way, as
   * columns of a lex chain in that order: each column is the Booleans of one set variable.
   *
   * <p>The variables are the blocks of the order (a set variable is the block of its element
   * vertices). The shortest prefix of blocks that every generator maps onto itself is found; if it
   * starts with a set variable and the group permutes a class of its blocks in every way while
   * fixing the other blocks of the prefix (checked on the permutations the generators make of the
   * prefix's blocks), then for two blocks {@code a} before {@code b} of the class the group holds a
   * symmetry that exchanges them and fixes the rest of the prefix, whose lex-leader constraint on
   * the prefix is {@code a <=lex b}. These are lex-leader constraints of the same order as those of
   * the generators, so they may be posted together.
   */
  private static List<IntVar[][]> interchangeableSets(
      List<GraphAutomorphisms.Permutation> generators, int[] base, Graph graph, IntVar[] varAt) {
    if (generators.isEmpty() || base.length == 0) {
      return List.of();
    }
    // the blocks of the order and the block of each vertex
    Map<Integer, Integer> blockOf = new HashMap<>();
    List<int[]> blocks = new ArrayList<>();
    for (int v : base) {
      if (blockOf.containsKey(v)) {
        continue;
      }
      SetVar s = graph.setOfElement.get(v);
      int[] block = s == null ? new int[] {v} : graph.elementVertices.get(s);
      for (int w : block) {
        blockOf.put(w, blocks.size());
      }
      blocks.add(block);
      if (blocks.size() > 4 * MAX_PREFIX) {
        break;
      }
    }
    if (graph.setOfElement.get(blocks.get(0)[0]) == null) {
      return List.of();
    }
    // the shortest prefix that every generator maps onto itself
    int end = 1;
    boolean grown = true;
    while (grown) {
      grown = false;
      for (GraphAutomorphisms.Permutation g : generators) {
        for (int b = 0; b < end; b++) {
          Integer image = blockOf.get(g.image(blocks.get(b)[0]));
          if (image == null || image >= MAX_PREFIX) {
            return List.of();
          }
          if (image >= end) {
            end = image + 1;
            grown = true;
          }
        }
      }
    }
    List<int[]> perms = new ArrayList<>();
    for (GraphAutomorphisms.Permutation g : generators) {
      int[] p = new int[end];
      for (int b = 0; b < end; b++) {
        p[b] = blockOf.get(g.image(blocks.get(b)[0]));
      }
      perms.add(p);
    }
    List<IntVar[][]> found = new ArrayList<>();
    for (int[] c : symmetricClasses(perms, end)) {
      IntVar[][] columns = new IntVar[c.length][];
      for (int i = 0; i < c.length; i++) {
        int[] block = blocks.get(c[i]);
        if (graph.setOfElement.get(block[0]) == null) {
          columns = null;
          break;
        }
        columns[i] = new IntVar[block.length];
        for (int k = 0; k < block.length; k++) {
          columns[i][k] = varAt[block[k]];
        }
      }
      if (columns != null && columns.length > 1 && columns[0].length > 0) {
        found.add(columns);
      }
    }
    return found;
  }

  private static void rankVertex(Integer v, List<Integer> ranked, boolean[] isRanked) {
    if (v != null && !isRanked[v]) {
      isRanked[v] = true;
      ranked.add(v);
    }
  }

  /**
   * Posts {@code e in s <-> b} for the elements {@code e} of the upper bound of {@code s} and
   * records {@code not b} as the variable of the element's vertex.
   */
  private void channel(SetVar s, int[] elementVertices, IntVar[] varAt) {
    SetDomain d = s.dom();
    int min = d.lub().min();
    int max = d.lub().max();
    IntVar[] b = new IntVar[max - min + 1];
    int k = 0;
    for (int e = min; e <= max; e++) {
      if (d.glb().contains(e)) {
        b[e - min] = new BooleanVar(store, 1, 1);
      } else if (!d.lub().contains(e)) {
        b[e - min] = new BooleanVar(store, 0, 0);
      } else {
        b[e - min] = new BooleanVar(store);
        // the lex-leader order takes e not in s before e in s, so that the sets with the
        // smallest elements come first, as the set searches that include the smallest element
        // first meet them
        BooleanVar out = new BooleanVar(store);
        store.impose(new XneqY(b[e - min], out));
        varAt[elementVertices[k++]] = out;
      }
    }
    store.impose(new ChannelBoolSet(b, s, min));
  }

  /**
   * The variables a generator moves (from) or their images (to); the other vertices it moves stand
   * for constraints and constants. Empty when it maps a variable onto a vertex that is not one.
   */
  private static Optional<IntVar[]> moves(
      GraphAutomorphisms.Permutation g, IntVar[] varAt, boolean from) {
    int[] points = g.points();
    List<IntVar> out = new ArrayList<>();
    for (int i = 0; i < points.length; i++) {
      IntVar x = varAt[points[i]];
      if (x == null) {
        continue;
      }
      IntVar y = varAt[g.images()[i]];
      if (y == null) {
        return Optional.empty();
      }
      out.add(from ? x : y);
    }
    return Optional.of(out.toArray(new IntVar[0]));
  }

  /**
   * Returns the canonicalizer of the symmetry breaking constraints posted, for local search.
   *
   * @return the canonicalizer.
   */
  SymmetryCanonicalizer canonicalizer() {
    return canonicalizer;
  }

  private static IntVar find(Map<IntVar, IntVar> parent, IntVar v) {
    IntVar p = parent.get(v);
    while (p != null) {
      v = p;
      p = parent.get(v);
    }
    return v;
  }

  private boolean outOfTime() {
    return clock.getAsLong() > deadline;
  }

  private void checkTime() {
    if (outOfTime()) {
      throw new OutOfTime();
    }
  }

  private List<Item> parse(SimpleNode astTree) {
    List<Item> items = new ArrayList<>();
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTVARDECLITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          checkTime();
          Item alias = alias((SimpleNode) node.jjtGetChild(j));
          if (alias != null) {
            items.add(alias);
          }
        }
      }
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            checkTime();
            items.add(parse((ASTConstElem) item));
          }
        }
      }
    }
    return items;
  }

  /**
   * The equality that a variable declared as another variable ({@code var bool: x = y}) stands for:
   * the front end makes x a variable of its own and posts x = y, so the graph needs the equality as
   * well, or it would take x and y for unrelated variables. Null for any other declaration.
   */
  private Item alias(SimpleNode node) {
    if (!(node instanceof ASTVarDeclItem decl) || node.jjtGetNumChildren() < 2) {
      return null;
    }
    IntVar x = dictionary.getVariable(decl.getIdent());
    SimpleNode init = (SimpleNode) node.jjtGetChild(node.jjtGetNumChildren() - 1);
    if (x == null
        || init.getId() != JJTSCALARFLATEXPR
        || ((ASTScalarFlatExpr) init).getType() != 2 && ((ASTScalarFlatExpr) init).getType() != 3) {
      return null;
    }
    Atom y = scalarAtom(init);
    if (y.aVar() == null || y.aVar() == x) {
      return null;
    }
    return new Item("int_eq", new Atom[][] {{variable(x)}, {y}}, new boolean[2]);
  }

  private Item parse(ASTConstElem item) {
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
    return new Item(item.getName(), args, array);
  }

  // ---------------------------------------------------------------------------------------------
  // value symmetries

  /**
   * What value symmetry breaking did.
   *
   * @param first the variables of the value spaces that got precedence chains, in the order the
   *     chains compare them.
   * @param posted precedence chains posted.
   * @param complete true if the automorphism search ran to the end.
   */
  private record ValueOutcome(List<IntVar> first, int posted, boolean complete) {}

  /**
   * A value space: the variables whose values it holds, in the lex-leader order, and its values.
   */
  private static final class Space {
    final List<IntVar> vars = new ArrayList<>();
    IntDomain values;
    boolean sameDomain = true;
    long pairs;
    // the variables whose values the precedence chains order, null for all of them
    List<IntVar> anchors;

    List<IntVar> anchors() {
      return anchors == null ? vars : anchors;
    }
  }

  /**
   * Value specs of set constraints, used only for the encoded spaces, where a set variable belongs
   * to the space of its elements: membership, the set operations and the comparisons other than the
   * lexicographic ones hold after a permutation of the values is applied to the elements of every
   * set. {@code set_card} keeps its set in place and uses the cardinality as a number.
   */
  private static final Map<String, ValueSpec> SET_VALUE_SPECS = new HashMap<>();

  static {
    for (String s : new String[] {"set_in", "set_in_reif", "set_in_imp"}) {
      SET_VALUE_SPECS.put(s, ValueSpec.of(0, 1));
    }
    for (String s : new String[] {"set_union", "set_intersect", "set_diff", "set_symdiff"}) {
      SET_VALUE_SPECS.put(s, ValueSpec.of(0, 1, 2));
    }
    for (String s : new String[] {"set_eq", "set_ne", "set_subset", "set_superset"}) {
      SET_VALUE_SPECS.put(s, ValueSpec.of(0, 1));
      SET_VALUE_SPECS.put(s + "_reif", ValueSpec.of(0, 1));
      SET_VALUE_SPECS.put(s + "_imp", ValueSpec.of(0, 1));
    }
    SET_VALUE_SPECS.put("jacop_disjoint", ValueSpec.of(0, 1));
    SET_VALUE_SPECS.put(UNION_N, ValueSpec.of(0, 1));
  }

  /** The value spec of a constraint, with the set specs in the encoded spaces. */
  private static ValueSpec valueSpec(Item item, boolean encoded) {
    if (encoded) {
      ValueSpec spec = SET_VALUE_SPECS.get(item.name());
      if (spec != null) {
        return spec.shared()[spec.shared().length - 1] < item.args().length ? spec : null;
      }
    }
    return valueSpec(item);
  }

  /**
   * The value spec of a constraint, or null. A linear constraint {@code x - y = 0} or {@code x - y
   * != 0}, as MiniZinc writes {@code x = y} and {@code x != y}, compares values.
   */
  private static ValueSpec valueSpec(Item item) {
    ValueSpec spec = VALUE_SPECS.get(item.name());
    if (spec != null) {
      return spec.shared()[spec.shared().length - 1] < item.args().length
              && (spec.indexed() < 0 || isIndexArray(item, spec))
          ? spec
          : null;
    }
    String name = item.name();
    if ((name.startsWith("int_lin_eq") || name.startsWith("int_lin_ne"))
        && item.args().length >= 3
        && item.args()[0].length == 2
        && item.args()[2].length == 1
        && item.args()[2][0].isInt()
        && item.args()[2][0].value() == 0
        && item.args()[0][0].isInt()
        && item.args()[0][1].isInt()
        && Math.abs(item.args()[0][0].value()) == 1
        && item.args()[0][0].value() == -item.args()[0][1].value()) {
      return ValueSpec.of(1);
    }
    return null;
  }

  private static boolean isIndexArray(Item item, ValueSpec spec) {
    Atom[][] args = item.args();
    return spec.indexed() < args.length
        && spec.offsetArg() < args.length
        && item.array()[spec.indexed()]
        && args[spec.offsetArg()].length == 1
        && args[spec.offsetArg()][0].isInt();
  }

  /**
   * Finds the value spaces of the model: the integer variables joined by constraints that only
   * compare their values. A space with a variable that is used as a number anywhere, or that is the
   * objective or a Boolean, is not one.
   */
  private static Map<IntVar, Integer> valueSpaces(
      List<Item> items, IntVar objective, List<IntVar> ranked, List<Space> spaces) {
    Map<IntVar, IntVar> parent = new IdentityHashMap<>();
    Set<IntVar> numeric = Collections.newSetFromMap(new IdentityHashMap<>());
    if (objective != null) {
      numeric.add(objective);
    }
    for (Item item : items) {
      ValueSpec spec = valueSpec(item);
      boolean[] shared = new boolean[item.args().length];
      if (spec != null) {
        for (int a : spec.shared()) {
          shared[a] = true;
        }
      }
      IntVar first = null;
      for (int a = 0; a < item.args().length; a++) {
        for (Atom atom : item.args()[a]) {
          IntVar x = atom.aVar();
          if (x == null) {
            continue;
          }
          parent.putIfAbsent(x, x);
          if (!shared[a] || x instanceof BooleanVar) {
            numeric.add(x);
          }
          if (!shared[a]) {
            continue;
          }
          if (first == null) {
            first = x;
          } else {
            union(parent, first, x);
          }
        }
      }
    }
    Map<IntVar, Boolean> rootNumeric = new IdentityHashMap<>();
    parent
        .keySet()
        .forEach(x -> rootNumeric.merge(root(parent, x), numeric.contains(x), Boolean::logicalOr));

    Map<IntVar, Integer> spaceOf = new IdentityHashMap<>();
    // the values of each group of joined variables
    Map<IntVar, IntDomain> rootValues = new IdentityHashMap<>();
    for (IntVar x : ranked) {
      if (parent.containsKey(x) && Boolean.FALSE.equals(rootNumeric.get(root(parent, x)))) {
        rootValues.merge(root(parent, x), x.dom(), IntDomain::union);
      }
    }
    // groups with the same values are one space: a permutation of the values then applies to all
    // of them, as when variables that no constraint joins choose among identical machines
    Map<String, Space> byValues = new HashMap<>();
    List<Space> created = new ArrayList<>();
    for (IntVar x : ranked) {
      IntDomain values = parent.containsKey(x) ? rootValues.get(root(parent, x)) : null;
      if (values == null) {
        continue;
      }
      Space s =
          byValues.computeIfAbsent(
              values.toString(),
              k -> {
                Space space = new Space();
                space.values = values;
                created.add(space);
                return space;
              });
      if (!s.vars.isEmpty() && !s.vars.get(0).dom().eq(x.dom())) {
        s.sameDomain = false;
      }
      s.vars.add(x);
      s.pairs += x.getSize();
    }
    for (Space s : created) {
      if (s.values.getSize() < 2
          || s.values.getSize() > MAX_VALUES
          || (!s.sameDomain && s.pairs > MAX_DOMAIN_EDGES)) {
        continue;
      }
      for (IntVar x : s.vars) {
        spaceOf.put(x, spaces.size());
      }
      spaces.add(s);
    }
    return spaceOf;
  }

  private static IntVar root(Map<IntVar, IntVar> parent, IntVar x) {
    IntVar p = parent.get(x);
    while (p != x) {
      x = p;
      p = parent.get(x);
    }
    return x;
  }

  private static void union(Map<IntVar, IntVar> parent, IntVar a, IntVar b) {
    IntVar ra = root(parent, a);
    IntVar rb = root(parent, b);
    if (ra != rb) {
      parent.put(rb, ra);
    }
  }

  /**
   * Breaks the value symmetries of the value spaces with value precedence chains.
   *
   * <p>The graph is the model graph of the variable symmetries with two changes: a variable of a
   * value space is coloured by its space, not by its domain, and is joined to a vertex for each
   * value of its domain (unless all variables of the space have the same domain); a constant at an
   * argument that holds values of a space is the vertex of that value. The search individualizes
   * the variables of the spaces first, then the values of each space in turn, so the generators
   * found at the levels of a space's values fix all those variables and the values of the earlier
   * spaces. They make a group of permutations of the space's values; a set of values that the group
   * permutes in every way while fixing the other values is a class of interchangeable values.
   */
  private ValueOutcome breakValueSymmetries(
      List<Item> items, IntVar objective, boolean minimize, List<IntVar> ranked, long maxNanos) {
    if (free && minimize && largestLoad(items, objective)) {
      return new ValueOutcome(List.of(), 0, true);
    }
    List<Space> spaces = new ArrayList<>();
    // a minimized objective that only bounds the variables of one space from above
    Set<IntVar> bounded = minimize && objective != null ? upperBounded(items, objective) : null;
    if (bounded != null) {
      List<Item> kept = new ArrayList<>();
      for (Item item : items) {
        if (!bounds(item, objective, new ArrayList<>())) {
          kept.add(item);
        }
      }
      Map<IntVar, Integer> spaceOf = valueSpaces(kept, objective, ranked, spaces);
      Space space = null;
      for (Space s : spaces) {
        if (s.vars.size() == bounded.size() && bounded.containsAll(s.vars)) {
          space = s;
        }
      }
      if (space != null) {
        spaceOf.keySet().retainAll(space.vars);
        spaceOf.replaceAll((x, k) -> 0);
        spaces = new ArrayList<>(List.of(space));
        return breakValueSymmetries(kept, objective, spaces, spaceOf, null, maxNanos);
      }
      spaces = new ArrayList<>();
    }
    Map<IntVar, Integer> spaceOf = valueSpaces(items, objective, ranked, spaces);
    return breakValueSymmetries(items, objective, spaces, spaceOf, null, maxNanos);
  }

  /**
   * The variables that the objective bounds from above, when it appears only in constraints {@code
   * x <= objective} or {@code objective = max(xs)}, or null.
   */
  private static Set<IntVar> upperBounded(List<Item> items, IntVar objective) {
    Set<IntVar> bounded = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Item item : items) {
      List<IntVar> xs = new ArrayList<>();
      if (bounds(item, objective, xs)) {
        bounded.addAll(xs);
        continue;
      }
      for (Atom[] arg : item.args()) {
        for (Atom a : arg) {
          if (a.aVar() == objective) {
            return null;
          }
        }
      }
    }
    return bounded.isEmpty() ? null : bounded;
  }

  /**
   * Tells whether a constraint bounds variables by the objective from above, and adds them to xs:
   * {@code int_le(x, z)}, {@code int_lin_le([1, -1], [x, z], 0)}, {@code int_max(x, y, z)} or
   * {@code z = max(xs)}.
   */
  private static boolean bounds(Item item, IntVar z, List<IntVar> xs) {
    Atom[][] args = item.args();
    switch (item.name()) {
      case "int_le" -> {
        return args.length == 2 && args[1][0].aVar() == z && single(args[0][0], z, xs);
      }
      case "int_lin_le" -> {
        if (args.length != 3
            || args[0].length != 2
            || !args[2][0].isInt()
            || args[2][0].value() != 0
            || !args[0][0].isInt()
            || !args[0][1].isInt()) {
          return false;
        }
        int a = args[0][0].value();
        int b = args[0][1].value();
        if (a == 1 && b == -1 && args[1][1].aVar() == z) {
          return single(args[1][0], z, xs);
        }
        return a == -1 && b == 1 && args[1][0].aVar() == z && single(args[1][1], z, xs);
      }
      case "int_max" -> {
        return args.length == 3
            && args[2][0].aVar() == z
            && single(args[0][0], z, xs)
            && single(args[1][0], z, xs);
      }
      case "array_int_maximum", "jacop_maximum" -> {
        if (args.length != 2 || args[0].length != 1 || args[0][0].aVar() != z) {
          return false;
        }
        for (Atom a : args[1]) {
          if (!single(a, z, xs)) {
            return false;
          }
        }
        return true;
      }
      default -> {
        return false;
      }
    }
  }

  /** Adds the variable of an atom; a constant bounds nothing, and the objective cannot be bound. */
  private static boolean single(Atom a, IntVar z, List<IntVar> xs) {
    if (a.aVar() == z || a.other() != null) {
      return false;
    }
    if (a.aVar() != null) {
      xs.add(a.aVar());
      return true;
    }
    return a.isInt();
  }

  private ValueOutcome breakValueSymmetries(
      List<Item> items,
      IntVar objective,
      List<Space> spaces,
      Map<IntVar, Integer> spaceOf,
      Map<SetVar, Integer> setSpaceOf,
      long maxNanos) {
    if (spaces.isEmpty()) {
      return new ValueOutcome(List.of(), 0, true);
    }
    Graph graph = new Graph(objective, spaceOf);
    graph.spaces = spaces;
    graph.setSpaceOf = setSpaceOf;
    try {
      for (Item item : items) {
        checkTime();
        graph.addConstraint(item);
      }
      graph.finish();
    } catch (Unsupported e) {
      return new ValueOutcome(List.of(), 0, !(e instanceof OutOfTime));
    }
    if (graph.size() > MAX_VERTICES) {
      return new ValueOutcome(List.of(), 0, true);
    }
    // the base: the variables of the spaces, then the values of each space
    List<Integer> base = new ArrayList<>();
    for (Space s : spaces) {
      for (IntVar x : s.anchors()) {
        base.add(graph.varVertex(x));
      }
    }
    int[][] valueVertices = new int[spaces.size()][];
    for (int k = 0; k < spaces.size(); k++) {
      int[] values = spaces.get(k).values.toIntArray();
      valueVertices[k] = new int[values.length];
      for (int i = 0; i < values.length; i++) {
        valueVertices[k][i] = graph.valueVertex(k, values[i]);
        base.add(valueVertices[k][i]);
      }
    }
    GraphAutomorphisms.Result result =
        new GraphAutomorphisms(
                graph.colors(),
                graph.adjacency(),
                base.stream().mapToInt(Integer::intValue).toArray())
            .generators(MAX_WORK, Math.min(maxNanos, Math.max(0, deadline - clock.getAsLong())));

    boolean[] fixedVertex = new boolean[graph.size()];
    for (Space s : spaces) {
      for (IntVar x : s.anchors()) {
        fixedVertex[graph.varVertex(x)] = true;
      }
    }
    List<IntVar> first = new ArrayList<>();
    int posted = 0;
    for (int k = 0; k < spaces.size(); k++) {
      int[] vertices = valueVertices[k];
      int[] values = spaces.get(k).values.toIntArray();
      Map<Integer, Integer> index = new HashMap<>();
      for (int i = 0; i < vertices.length; i++) {
        index.put(vertices[i], i);
      }
      // the generators that fix the variables and the values of the earlier spaces, as
      // permutations of this space's values
      List<int[]> perms = new ArrayList<>();
      for (GraphAutomorphisms.Permutation g : result.generators()) {
        int[] perm = null;
        boolean fixes = true;
        for (int i = 0; i < g.points().length && fixes; i++) {
          int v = g.points()[i];
          Integer at = index.get(v);
          if (fixedVertex[v]) {
            fixes = false;
          } else if (at != null) {
            if (perm == null) {
              perm = identity(vertices.length);
            }
            perm[at] = index.get(g.images()[i]);
          }
        }
        if (fixes && perm != null) {
          perms.add(perm);
        }
      }
      for (int v : vertices) {
        fixedVertex[v] = true;
      }
      List<int[]> classes = symmetricClasses(perms, vertices.length);
      if (classes.isEmpty()) {
        continue;
      }
      IntVar[] xs = spaces.get(k).anchors().toArray(new IntVar[0]);
      for (int[] c : classes) {
        int[] chain = Arrays.stream(c).map(i -> values[i]).sorted().toArray();
        SeqPrecedeChain precede = new SeqPrecedeChain(xs, chain);
        precede.setDegreeWeight(0);
        store.impose(precede);
        canonicalizer.precedence(precede, xs, chain);
        note("precede" + Arrays.toString(chain), xs);
        posted++;
      }
      first.addAll(spaces.get(k).anchors());
    }
    return new ValueOutcome(first, posted, result.complete());
  }

  /**
   * Value symmetries of encoded models, tried when the plain value spaces give none.
   *
   * <p>A MiniZinc model that collects values in a set, such as {@code {t | t in T where
   * exists(...)}}, is flattened into one variable per value {@code t} with domain {@code {0, t}}, a
   * set variable per value and a chain of binary unions; the value {@code t} then sits in a
   * different variable for each value, so no plain value space holds them all. Here a set variable
   * belongs to the space of its elements (through membership and the set operations, {@link
   * #SET_VALUE_SPECS}), groups of variables whose values overlap are one space, and a chain of
   * unions is one n-ary union. Generators may now move the other variables of a space with its
   * values: the base lists only the anchors, the space's variables of the search annotation (all
   * its variables if none is), then the values, so the generators found at the values' levels fix
   * the anchors and permute the values, and the precedence chains order the anchors only. A value
   * permutation that such a generator makes, with the variables it moves, maps solutions to
   * solutions, so the chain keeps a solution of every orbit.
   */
  private ValueOutcome breakEncodedValueSymmetries(
      List<Item> items,
      IntVar objective,
      List<IntVar> ranked,
      Set<IntVar> annotated,
      long maxNanos) {
    boolean anySet = false;
    for (Item item : items) {
      if (SET_VALUE_SPECS.containsKey(item.name())) {
        anySet = true;
        break;
      }
    }
    if (!anySet) {
      return new ValueOutcome(List.of(), 0, true);
    }
    List<Item> flat = flattenUnions(items);
    List<Space> spaces = new ArrayList<>();
    Map<SetVar, Integer> setSpaceOf = new IdentityHashMap<>();
    Map<IntVar, Integer> spaceOf = encodedSpaces(flat, objective, ranked, spaces, setSpaceOf);
    if (spaces.isEmpty() || setSpaceOf.isEmpty()) {
      return new ValueOutcome(List.of(), 0, true);
    }
    for (Space space : spaces) {
      List<IntVar> anchors = new ArrayList<>();
      for (IntVar x : space.vars) {
        if (annotated.contains(x)) {
          anchors.add(x);
        }
      }
      space.anchors = anchors.isEmpty() ? null : anchors;
    }
    return breakValueSymmetries(flat, objective, spaces, spaceOf, setSpaceOf, maxNanos);
  }

  /**
   * The items with each chain of binary set unions {@code u1 = x1 union x2, u2 = u1 union x3, ...}
   * whose intermediate results are used nowhere else replaced by one n-ary union.
   */
  private static List<Item> flattenUnions(List<Item> items) {
    Map<Var, Integer> uses = new IdentityHashMap<>();
    Map<Var, Item> unionOf = new IdentityHashMap<>();
    Set<Var> unionOperands = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Item item : items) {
      for (Atom[] arg : item.args()) {
        for (Atom a : arg) {
          Var v = a.aVar() != null ? a.aVar() : a.other();
          if (v != null) {
            uses.merge(v, 1, Integer::sum);
          }
        }
      }
      if (item.name().equals("set_union") && item.args().length == 3) {
        Var r = item.args()[2][0].other();
        if (r != null) {
          unionOf.put(r, item);
        }
        for (int a = 0; a < 2; a++) {
          if (item.args()[a][0].other() != null) {
            unionOperands.add(item.args()[a][0].other());
          }
        }
      }
    }
    // a union whose result is only an operand of one other union is inlined there
    Set<Item> inlined = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Map.Entry<Var, Item> e : unionOf.entrySet()) {
      if (uses.getOrDefault(e.getKey(), 0) == 2 && unionOperands.contains(e.getKey())) {
        inlined.add(e.getValue());
      }
    }
    if (inlined.isEmpty()) {
      return items;
    }
    List<Item> out = new ArrayList<>();
    for (Item item : items) {
      if (inlined.contains(item)) {
        continue;
      }
      if (!item.name().equals("set_union")
          || item.args().length != 3
          || item.args()[2][0].other() == null
          || unionOf.get(item.args()[2][0].other()) != item) {
        out.add(item);
        continue;
      }
      List<Atom> operands = new ArrayList<>();
      collect(item.args()[0][0], unionOf, inlined, operands);
      collect(item.args()[1][0], unionOf, inlined, operands);
      out.add(
          new Item(
              UNION_N,
              new Atom[][] {operands.toArray(new Atom[0]), item.args()[2]},
              new boolean[] {true, false}));
    }
    return out;
  }

  private static void collect(Atom a, Map<Var, Item> unionOf, Set<Item> inlined, List<Atom> out) {
    Item u = a.other() == null ? null : unionOf.get(a.other());
    if (u != null && inlined.contains(u)) {
      collect(u.args()[0][0], unionOf, inlined, out);
      collect(u.args()[1][0], unionOf, inlined, out);
    } else {
      out.add(a);
    }
  }

  /**
   * The encoded value spaces: integer and set variables joined by constraints that only compare
   * their values (set constraints by {@link #SET_VALUE_SPECS}), then groups whose values overlap
   * joined into one space. A group with a variable used as a number, a Boolean, the objective, or a
   * constant other than an integer among the values, is not a space.
   */
  private static Map<IntVar, Integer> encodedSpaces(
      List<Item> items,
      IntVar objective,
      List<IntVar> ranked,
      List<Space> spaces,
      Map<SetVar, Integer> setSpaceOf) {
    Map<Var, Var> parent = new IdentityHashMap<>();
    Set<Var> numeric = Collections.newSetFromMap(new IdentityHashMap<>());
    if (objective != null) {
      numeric.add(objective);
    }
    List<SetVar> setOrder = new ArrayList<>();
    for (Item item : items) {
      ValueSpec spec = valueSpec(item, true);
      boolean card = item.name().equals("set_card") && item.args().length == 2;
      boolean[] shared = new boolean[item.args().length];
      if (spec != null) {
        for (int a : spec.shared()) {
          shared[a] = true;
        }
      }
      Var first = null;
      boolean foreign = false;
      for (int a = 0; a < item.args().length; a++) {
        for (Atom atom : item.args()[a]) {
          Var x = atom.aVar() != null ? atom.aVar() : atom.other();
          if (x == null) {
            foreign |= shared[a] && !atom.isInt();
            continue;
          }
          if (parent.putIfAbsent(x, x) == null && x instanceof SetVar sv) {
            setOrder.add(sv);
          }
          if (card && a == 0) {
            // the cardinality of a set does not change when its elements are renamed
            continue;
          }
          if (!shared[a]
              || x instanceof BooleanVar
              || !(x instanceof IntVar || x instanceof SetVar)) {
            numeric.add(x);
          }
          if (!shared[a]) {
            continue;
          }
          if (first == null) {
            first = x;
          } else {
            unionVar(parent, first, x);
          }
        }
      }
      if (foreign && first != null) {
        numeric.add(first);
      }
    }
    Map<Var, Boolean> rootNumeric = new IdentityHashMap<>();
    parent
        .keySet()
        .forEach(
            x -> rootNumeric.merge(rootVar(parent, x), numeric.contains(x), Boolean::logicalOr));
    // the values of each group, and groups that share a value joined
    Map<Var, IntDomain> rootValues = new IdentityHashMap<>();
    List<Var> members = new ArrayList<>(ranked);
    members.addAll(setOrder);
    for (Var x : members) {
      if (!parent.containsKey(x) || !Boolean.FALSE.equals(rootNumeric.get(rootVar(parent, x)))) {
        continue;
      }
      IntDomain d = x instanceof SetVar sv ? sv.dom().lub() : ((IntVar) x).dom();
      if (d.getSize() > MAX_VALUES) {
        rootNumeric.put(rootVar(parent, x), true);
        continue;
      }
      rootValues.merge(rootVar(parent, x), d, IntDomain::union);
    }
    Map<Integer, Var> owner = new HashMap<>();
    for (Map.Entry<Var, IntDomain> e : new ArrayList<>(rootValues.entrySet())) {
      if (Boolean.TRUE.equals(rootNumeric.get(e.getKey()))) {
        continue;
      }
      for (ValueEnumeration en = e.getValue().valueEnumeration(); en.hasMoreElements(); ) {
        Var other = owner.putIfAbsent(en.nextElement(), e.getKey());
        if (other != null) {
          unionVar(parent, other, e.getKey());
        }
      }
    }
    // the spaces, with their variables in the lex-leader order
    Map<Var, Space> spaceOfRoot = new IdentityHashMap<>();
    List<Space> created = new ArrayList<>();
    Map<Space, List<SetVar>> setsOf = new IdentityHashMap<>();
    for (Var x : members) {
      if (!parent.containsKey(x) || !Boolean.FALSE.equals(rootNumeric.get(rootVar(parent, x)))) {
        continue;
      }
      // a group joined by shared values: numeric if any part of it is
      Var root = rootVar(parent, x);
      Space space =
          spaceOfRoot.computeIfAbsent(
              root,
              r -> {
                Space sp = new Space();
                created.add(sp);
                return sp;
              });
      IntDomain d = x instanceof SetVar sv ? sv.dom().lub() : ((IntVar) x).dom();
      space.values = space.values == null ? d : space.values.union(d);
      if (x instanceof IntVar iv) {
        if (!space.vars.isEmpty() && !space.vars.get(0).dom().eq(iv.dom())) {
          space.sameDomain = false;
        }
        space.vars.add(iv);
        space.pairs += iv.getSize();
      } else {
        setsOf.computeIfAbsent(space, k -> new ArrayList<>()).add((SetVar) x);
      }
    }
    Map<IntVar, Integer> spaceOf = new IdentityHashMap<>();
    for (Space s : created) {
      if (s.vars.isEmpty()
          || !setsOf.containsKey(s)
          || anyNumeric(s, setsOf.get(s), parent, rootNumeric)
          || s.values.getSize() < 2
          || s.values.getSize() > MAX_VALUES
          || (!s.sameDomain && s.pairs > MAX_DOMAIN_EDGES)) {
        continue;
      }
      // the domains of the set variables differ from those of the integers: edges, not colours
      s.sameDomain = false;
      for (IntVar x : s.vars) {
        spaceOf.put(x, spaces.size());
      }
      for (SetVar x : setsOf.get(s)) {
        setSpaceOf.put(x, spaces.size());
      }
      spaces.add(s);
    }
    return spaceOf;
  }

  private static boolean anyNumeric(
      Space s, List<SetVar> sets, Map<Var, Var> parent, Map<Var, Boolean> rootNumeric) {
    for (IntVar x : s.vars) {
      if (!Boolean.FALSE.equals(rootNumeric.get(rootVar(parent, x)))) {
        return true;
      }
    }
    for (SetVar x : sets) {
      if (!Boolean.FALSE.equals(rootNumeric.get(rootVar(parent, x)))) {
        return true;
      }
    }
    return false;
  }

  private static Var rootVar(Map<Var, Var> parent, Var x) {
    Var p = parent.get(x);
    while (p != x) {
      x = p;
      p = parent.get(x);
    }
    return x;
  }

  private static void unionVar(Map<Var, Var> parent, Var a, Var b) {
    Var ra = rootVar(parent, a);
    Var rb = rootVar(parent, b);
    if (ra != rb) {
      parent.put(rb, ra);
    }
  }

  private static int[] identity(int n) {
    int[] p = new int[n];
    for (int i = 0; i < n; i++) {
      p[i] = i;
    }
    return p;
  }

  /**
   * Finds sets of points that a group permutes in every way while fixing the other points.
   *
   * <p>Transpositions among the generators join their two points: the transpositions of a connected
   * set of points generate all its permutations. For few points, each orbit of the group is also
   * checked with a Schreier-Sims stabilizer chain whose base lists the other points first: the
   * stabilizer of the other points permutes the orbit in every way exactly when the fundamental
   * orbits along the orbit's points have sizes {@code m, m - 1, ..., 1}.
   *
   * @param generators permutations of the points {@code 0..n-1}.
   * @param n the number of points.
   * @return the sets found, each of at least two points.
   */
  static List<int[]> symmetricClasses(List<int[]> generators, int n) {
    int[] orbit = identity(n);
    int[] joined = identity(n);
    for (int[] g : generators) {
      int moved = 0;
      int a = -1;
      int b = -1;
      for (int i = 0; i < n; i++) {
        if (g[i] != i) {
          moved++;
          a = b;
          b = i;
          link(orbit, i, g[i]);
        }
      }
      if (moved == 2) {
        link(joined, a, b);
      }
    }
    Map<Integer, List<Integer>> orbits = new TreeMap<>();
    Map<Integer, List<Integer>> components = new TreeMap<>();
    for (int i = 0; i < n; i++) {
      orbits.computeIfAbsent(top(orbit, i), k -> new ArrayList<>()).add(i);
      components.computeIfAbsent(top(joined, i), k -> new ArrayList<>()).add(i);
    }
    List<int[]> classes = new ArrayList<>();
    for (List<Integer> o : orbits.values()) {
      if (o.size() < 2) {
        continue;
      }
      List<Integer> component = components.get(top(joined, o.get(0)));
      if (component.size() < o.size() && n <= MAX_SCHREIER_SIMS && isSymmetric(generators, n, o)) {
        component = o;
      }
      if (component.size() == o.size()) {
        classes.add(o.stream().mapToInt(Integer::intValue).toArray());
        continue;
      }
      // the transpositions join parts of the orbit
      for (int i : o) {
        List<Integer> c = components.get(i);
        if (c != null && c.size() > 1) {
          classes.add(c.stream().mapToInt(Integer::intValue).toArray());
        }
      }
    }
    return classes;
  }

  /**
   * Tells whether the stabilizer of the points outside an orbit permutes the orbit in every way.
   */
  private static boolean isSymmetric(List<int[]> generators, int n, List<Integer> o) {
    int[] base = new int[n];
    int at = 0;
    Set<Integer> in = new HashSet<>(o);
    for (int i = 0; i < n; i++) {
      if (!in.contains(i)) {
        base[at++] = i;
      }
    }
    int from = at;
    for (int i : o) {
      base[at++] = i;
    }
    int[] sizes = new StabilizerChain(n, base, generators).orbitSizes();
    for (int l = from; l < n; l++) {
      if (sizes[l] != n - l) {
        return false;
      }
    }
    return true;
  }

  private static int top(int[] parent, int i) {
    while (parent[i] != i) {
      i = parent[i];
    }
    return i;
  }

  private static void link(int[] parent, int a, int b) {
    int ra = top(parent, a);
    int rb = top(parent, b);
    if (ra != rb) {
      parent[Math.max(ra, rb)] = Math.min(ra, rb);
    }
  }

  /**
   * A Schreier-Sims stabilizer chain of a permutation group on few points, with a base that lists
   * every point (Holt, Handbook of Computational Group Theory, SCHREIERSIMS). A permutation {@code
   * p} maps {@code i} to {@code p[i]}.
   */
  static final class StabilizerChain {
    private final int n;
    private final int[] base;
    private final List<int[]> strong = new ArrayList<>();
    // transversal[l][q] maps base[l] to q, or is null when q is not in the orbit
    private final int[][][] transversal;

    StabilizerChain(int n, int[] base, List<int[]> generators) {
      this.n = n;
      this.base = base;
      transversal = new int[n][][];
      for (int[] g : generators) {
        if (!Arrays.equals(g, identity(n))) {
          strong.add(g);
        }
      }
      for (int l = 0; l < n; l++) {
        transversal(l);
      }
      int l = n - 1;
      while (l >= 0) {
        int added = completeLevel(l);
        if (added < 0) {
          l--;
        } else {
          for (int k = 0; k <= added && k < n; k++) {
            transversal(k);
          }
          l = Math.min(added, n - 1);
        }
      }
    }

    /** The fundamental orbit size of each level. */
    int[] orbitSizes() {
      int[] sizes = new int[n];
      for (int l = 0; l < n; l++) {
        for (int[] t : transversal[l]) {
          if (t != null) {
            sizes[l]++;
          }
        }
      }
      return sizes;
    }

    /**
     * Sifts the Schreier generators of a level; the first one that is not in the chain is added to
     * the strong generators.
     *
     * @return the deepest level the added generator belongs to, or -1 if none was added.
     */
    private int completeLevel(int l) {
      List<int[]> level = level(l);
      for (int q = 0; q < n; q++) {
        int[] tq = transversal[l][q];
        if (tq == null) {
          continue;
        }
        for (int[] s : level) {
          int[] h = multiply(multiply(tq, s), inverse(transversal[l][s[q]]));
          int stop = sift(h, l + 1);
          if (stop < n) {
            strong.add(h);
            return stop;
          }
        }
      }
      return -1;
    }

    /** Sifts h through the levels from l on; h is left as the residue. */
    private int sift(int[] h, int l) {
      for (int k = l; k < n; k++) {
        int q = h[base[k]];
        int[] t = transversal[k][q];
        if (t == null) {
          return k;
        }
        int[] r = multiply(h, inverse(t));
        System.arraycopy(r, 0, h, 0, n);
      }
      return n;
    }

    private List<int[]> level(int l) {
      List<int[]> level = new ArrayList<>();
      for (int[] s : strong) {
        boolean fixes = true;
        for (int k = 0; k < l && fixes; k++) {
          fixes = s[base[k]] == base[k];
        }
        if (fixes) {
          level.add(s);
        }
      }
      return level;
    }

    private void transversal(int l) {
      int[][] t = new int[n][];
      t[base[l]] = identity(n);
      List<int[]> level = level(l);
      int[] queue = new int[n];
      int head = 0;
      int tail = 0;
      queue[tail++] = base[l];
      while (head < tail) {
        int q = queue[head++];
        for (int[] s : level) {
          int r = s[q];
          if (t[r] == null) {
            t[r] = multiply(t[q], s);
            queue[tail++] = r;
          }
        }
      }
      transversal[l] = t;
    }

    /** The permutation that applies a, then b. */
    private static int[] multiply(int[] a, int[] b) {
      int[] c = new int[a.length];
      for (int i = 0; i < a.length; i++) {
        c[i] = b[a[i]];
      }
      return c;
    }

    private static int[] inverse(int[] a) {
      int[] c = new int[a.length];
      for (int i = 0; i < a.length; i++) {
        c[a[i]] = i;
      }
      return c;
    }
  }

  // ---------------------------------------------------------------------------------------------
  // orbitopes

  /**
   * Finds interchangeable columns of variables among the generators, the way CP-SAT extracts
   * orbitopes: a generator that swaps two columns of variables, element by element, starts an
   * orbitope, and a generator that swaps one of its columns with new variables adds a column. The
   * swaps of a connected set of columns generate all permutations of the columns, so with the
   * columns ordered and their elements in one row order consistent with the lex-leader order, the
   * lex-leader constraints of all those permutations are the lex chain of the columns. The
   * generators used are removed from the list; an orbitope whose columns do not fit the lex-leader
   * order, or with only two columns, is left to its generators.
   */
  private static List<IntVar[][]> orbitopes(
      List<GraphAutomorphisms.Permutation> generators, IntVar[] varAt, int[] rankAt) {
    // the swaps: generators whose variable part is made of 2-cycles only
    List<GraphAutomorphisms.Permutation> swaps = new ArrayList<>();
    List<int[][]> pairs = new ArrayList<>();
    for (GraphAutomorphisms.Permutation g : generators) {
      List<int[]> cycles = new ArrayList<>();
      boolean swap = true;
      for (int v : g.points()) {
        if (varAt[v] == null) {
          continue;
        }
        int w = g.image(v);
        if (varAt[w] == null || g.image(w) != v) {
          swap = false;
          break;
        }
        if (v < w) {
          cycles.add(new int[] {v, w});
        }
      }
      if (swap && !cycles.isEmpty()) {
        swaps.add(g);
        pairs.add(cycles.toArray(new int[0][]));
      }
    }
    List<IntVar[][]> found = new ArrayList<>();
    boolean[] used = new boolean[swaps.size()];
    // member[t] == s + 1 when swap t is in the orbitope started at s: a list scan per swap and
    // pass was quadratic in the number of swaps
    int[] member = new int[swaps.size()];
    for (int s = 0; s < swaps.size(); s++) {
      if (used[s]) {
        continue;
      }
      int rows = pairs.get(s).length;
      // column and row of each vertex in the orbitope
      Map<Integer, int[]> cell = new HashMap<>();
      List<int[]> columns = new ArrayList<>();
      int[] c0 = new int[rows];
      int[] c1 = new int[rows];
      for (int r = 0; r < rows; r++) {
        c0[r] = pairs.get(s)[r][0];
        c1[r] = pairs.get(s)[r][1];
        cell.put(c0[r], new int[] {0, r});
        cell.put(c1[r], new int[] {1, r});
      }
      columns.add(c0);
      columns.add(c1);
      List<Integer> members = new ArrayList<>(List.of(s));
      member[s] = s + 1;
      boolean grown = true;
      while (grown) {
        grown = false;
        for (int t = 0; t < swaps.size(); t++) {
          if (used[t] || member[t] == s + 1 || pairs.get(t).length != rows) {
            continue;
          }
          int[] added = extend(pairs.get(t), cell, columns.size(), rows);
          if (added != null) {
            for (int r = 0; r < rows; r++) {
              cell.put(added[r], new int[] {columns.size(), r});
            }
            columns.add(added);
            members.add(t);
            member[t] = s + 1;
            grown = true;
          } else if (swapsColumns(pairs.get(t), cell)) {
            members.add(t);
            member[t] = s + 1;
          }
        }
      }
      IntVar[][] chain = columns.size() > 2 ? ordered(columns, varAt, rankAt) : null;
      if (chain == null) {
        continue;
      }
      for (int t : members) {
        used[t] = true;
      }
      found.add(chain);
    }
    Set<GraphAutomorphisms.Permutation> remove = Collections.newSetFromMap(new IdentityHashMap<>());
    for (int t = 0; t < swaps.size(); t++) {
      if (used[t]) {
        remove.add(swaps.get(t));
      }
    }
    if (!remove.isEmpty()) {
      generators.removeIf(remove::contains);
    }
    return found;
  }

  /**
   * The new column that a swap adds: each of its 2-cycles has one vertex in the same column of the
   * orbitope, one per row, and one vertex outside it. Null if the swap is not of that form.
   */
  private static int[] extend(int[][] cycles, Map<Integer, int[]> cell, int columns, int rows) {
    int column = -1;
    int[] added = new int[rows];
    boolean[] row = new boolean[rows];
    for (int[] c : cycles) {
      int[] in = cell.get(c[0]);
      int out = c[1];
      if (in == null) {
        in = cell.get(c[1]);
        out = c[0];
      } else if (cell.containsKey(c[1])) {
        return null;
      }
      if (in == null || (column >= 0 && in[0] != column) || row[in[1]]) {
        return null;
      }
      column = in[0];
      row[in[1]] = true;
      added[in[1]] = out;
    }
    return column >= 0 && column < columns ? added : null;
  }

  /** Tells whether a swap exchanges two columns of the orbitope, row by row. */
  private static boolean swapsColumns(int[][] cycles, Map<Integer, int[]> cell) {
    int a = -1;
    int b = -1;
    for (int[] c : cycles) {
      int[] x = cell.get(c[0]);
      int[] y = cell.get(c[1]);
      if (x == null || y == null || x[1] != y[1]) {
        return false;
      }
      int lo = Math.min(x[0], y[0]);
      int hi = Math.max(x[0], y[0]);
      if (a >= 0 && (lo != a || hi != b)) {
        return false;
      }
      a = lo;
      b = hi;
    }
    return a >= 0 && a != b;
  }

  /**
   * The columns as lex chain arguments: columns ordered by the rank of their first row, rows
   * ordered by their rank in the first column. Null unless every row then increases in rank along
   * the columns and every column has its rows in the same order, the conditions under which the
   * lex-leader constraint of swapping two columns compares them as the lex chain does.
   */
  private static IntVar[][] ordered(List<int[]> columns, IntVar[] varAt, int[] rankAt) {
    int rows = columns.get(0).length;
    Integer[] rowOrder = new Integer[rows];
    for (int r = 0; r < rows; r++) {
      rowOrder[r] = r;
    }
    int[] c0 = columns.get(0);
    Arrays.sort(rowOrder, (a, b) -> Integer.compare(rankAt[c0[a]], rankAt[c0[b]]));
    List<int[]> sorted = new ArrayList<>(columns);
    int firstRow = rowOrder[0];
    sorted.sort((a, b) -> Integer.compare(rankAt[a[firstRow]], rankAt[b[firstRow]]));
    IntVar[][] chain = new IntVar[sorted.size()][rows];
    for (int c = 0; c < sorted.size(); c++) {
      int[] col = sorted.get(c);
      for (int i = 0; i < rows; i++) {
        int r = rowOrder[i];
        if (i > 0 && rankAt[col[rowOrder[i - 1]]] > rankAt[col[r]]) {
          return null;
        }
        if (c > 0 && rankAt[sorted.get(c - 1)[r]] > rankAt[col[r]]) {
          return null;
        }
        chain[c][i] = varAt[col[r]];
      }
    }
    return chain;
  }

  // ---------------------------------------------------------------------------------------------
  // the model graph

  /**
   * The coloured graph of the model. With value spaces, their variables are coloured by space and
   * their values are vertices.
   */
  private final class Graph {
    private final IntVar objective;
    private final Map<IntVar, Integer> spaceOf;
    private List<Space> spaces;

    private final List<String> colorKeys = new ArrayList<>();
    private int[][] adjacency = new int[64][];
    private int[] degree = new int[64];
    final Map<IntVar, Integer> varVertices = new IdentityHashMap<>();
    // the encoded spaces: the space of each set variable in one, and set constraints have specs
    Map<SetVar, Integer> setSpaceOf;
    private final Map<Var, Integer> otherVertex = new IdentityHashMap<>();
    private final Map<Long, Integer> valueVertex = new HashMap<>();
    private final Set<String> distinct = new HashSet<>();
    final List<IntVar> vars = new ArrayList<>();
    // the element vertices of each set variable, in increasing order of the elements
    final Map<SetVar, int[]> elementVertices = new IdentityHashMap<>();
    final Map<Integer, SetVar> setOfElement = new HashMap<>();
    // the set variables with element vertices, in the order the graph met them
    final List<SetVar> sets = new ArrayList<>();
    private int setElements;

    Graph(IntVar objective, Map<IntVar, Integer> spaceOf) {
      this.objective = objective;
      this.spaceOf = spaceOf;
    }

    int size() {
      return colorKeys.size();
    }

    void finish() {
      if (objective != null) {
        varVertex(objective);
      }
    }

    int[] colors() {
      int n = colorKeys.size();
      TreeMap<String, Integer> sorted = new TreeMap<>();
      for (String k : colorKeys) {
        sorted.put(k, 0);
      }
      int c = 0;
      for (Map.Entry<String, Integer> e : sorted.entrySet()) {
        e.setValue(c++);
      }
      int[] colors = new int[n];
      for (int v = 0; v < n; v++) {
        colors[v] = sorted.getOrDefault(colorKeys.get(v), 0);
      }
      return colors;
    }

    int[][] adjacency() {
      int n = colorKeys.size();
      int[][] adj = new int[n][];
      for (int v = 0; v < n; v++) {
        adj[v] = Arrays.copyOf(adjacency[v], degree[v]);
      }
      return adj;
    }

    /** The value space of the shared arguments of a constraint, or -1. */
    private int space(Item item, ValueSpec spec) {
      if (spaceOf == null || spec == null) {
        return -1;
      }
      for (int a : spec.shared()) {
        for (Atom atom : item.args()[a]) {
          if (atom.aVar() != null) {
            Integer s = spaceOf.get(atom.aVar());
            return s == null ? -1 : s;
          }
          if (setSpaceOf != null && atom.other() instanceof SetVar sv) {
            Integer s = setSpaceOf.get(sv);
            return s == null ? -1 : s;
          }
        }
      }
      return -1;
    }

    void addConstraint(Item item) {
      String name = item.name();
      Atom[][] args = item.args();
      boolean[] array = item.array();
      int arity = args.length;
      ValueSpec valueSpec = spaceOf == null ? null : valueSpec(item, setSpaceOf != null);
      int space = space(item, valueSpec);
      int indexed = -1;
      int offset = 0;
      if (space >= 0) {
        // the constants of the shared arguments are values of the space
        args = args.clone();
        for (int a : valueSpec.shared()) {
          Atom[] arg = args[a].clone();
          for (int j = 0; j < arg.length; j++) {
            if (arg[j].isInt()) {
              arg[j] = new Atom(null, null, arg[j].constant(), space, arg[j].value());
            } else if (arg[j].isConstant()) {
              throw new Unsupported("value " + arg[j].constant() + " of " + name);
            }
          }
          args[a] = arg;
        }
        indexed = valueSpec.indexed();
        if (indexed >= 0) {
          offset = args[valueSpec.offsetArg()][0].value();
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
        for (int a : spec.symmetric) {
          if (a >= arity || array[a]) {
            throw new Unsupported("unexpected arguments of " + name);
          }
          grouped[a] = true;
          position(constraint, "y|" + prefix, args[a][0], constants);
        }
        for (int b = 0; b < spec.bags.length; b++) {
          int[] bag = spec.bags[b];
          for (int a : bag) {
            if (a >= arity || !array[a] || args[a].length != args[bag[0]].length) {
              throw new Unsupported("unexpected arguments of " + name);
            }
            grouped[a] = true;
          }
          addBag(constraint, prefix + "b" + b + "|", bag, args, constants);
        }
      }
      if (indexed >= 0) {
        // element j belongs to the value offset + j, wherever the value goes
        grouped[indexed] = true;
        constants.add(indexed + "#" + args[indexed].length);
        for (int j = 0; j < args[indexed].length; j++) {
          Atom atom = args[indexed][j];
          int p =
              vertex("x|" + prefix + indexed + (atom.isConstant() ? "=" + atom.constant() : "|_"));
          edge(constraint, p);
          edge(p, valueVertex(space, offset + j));
          if (!atom.isConstant()) {
            edge(p, atomVertex(atom));
          }
        }
      }
      for (int a = 0; a < arity; a++) {
        if (grouped[a]) {
          continue;
        }
        String key = array[a] ? constantArray(args[a]) : null;
        if (key != null) {
          constants.add(a + "=" + key);
        } else if (array[a]) {
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
     * A text that is the same for two constraints exactly when they are the same constraint up to
     * the order of the arguments that the spec groups.
     */
    private String canonical(Spec spec, Atom[][] args, boolean[] array) {
      int arity = args.length;
      boolean[] grouped = new boolean[arity];
      StringBuilder key = new StringBuilder();
      if (spec != null) {
        List<String> sym = new ArrayList<>();
        for (int a : spec.symmetric) {
          if (a < arity) {
            grouped[a] = true;
            sym.add(id(args[a][0]));
          }
        }
        sym.sort(null);
        key.append(sym);
        for (int[] bag : spec.bags) {
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
          String constants = array[a] ? constantArray(args[a]) : null;
          if (constants != null) {
            key.append("[=").append(constants).append(',');
            continue;
          }
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
     * items at other indices. An item of constants only is part of the constraint's colour, and
     * equal items are one vertex with their number in its colour.
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
      if (atom.aVar() != null) {
        return varVertex(atom.aVar());
      }
      if (atom.space() >= 0) {
        return valueVertex(atom.space(), atom.value());
      }
      if (setSpaceOf != null && atom.other() instanceof SetVar s && setSpaceOf.containsKey(s)) {
        return otherVertex.computeIfAbsent(s, v -> setInSpace(s, setSpaceOf.get(s)));
      }
      if (atom.other() instanceof SetVar s && spaceOf == null && setsMove) {
        Integer v = otherVertex.get(s);
        if (v != null) {
          return v;
        }
        SetDomain d = s.dom();
        int free = d.lub().getSize() - d.glb().getSize();
        if (setElements + free <= MAX_SET_ELEMENTS) {
          setElements += free;
          v = vertex("S|" + d.glb() + "|" + d.lub() + "|" + d.card());
          otherVertex.put(s, v);
          int[] elements = new int[free];
          int k = 0;
          for (ValueEnumeration e = d.lub().valueEnumeration(); e.hasMoreElements(); ) {
            int value = e.nextElement();
            if (!d.glb().contains(value)) {
              int w = vertex("E|" + value);
              edge(v, w);
              elements[k++] = w;
              setOfElement.put(w, s);
            }
          }
          elementVertices.put(s, elements);
          sets.add(s);
          return v;
        }
      }
      // a float or set variable is kept in place: a colour of its own
      return otherVertex.computeIfAbsent(atom.other(), v -> vertex("u|" + otherVertex.size()));
    }

    /**
     * The vertex of a set variable of a space, joined to the values of its upper bound; a value of
     * its lower bound through a vertex of its own.
     */
    private int setInSpace(SetVar s, int space) {
      SetDomain d = s.dom();
      int v = vertex("T|" + space + "|" + d.card());
      for (ValueEnumeration e = d.lub().valueEnumeration(); e.hasMoreElements(); ) {
        int value = e.nextElement();
        if (d.glb().contains(value)) {
          int g = vertex("t|glb");
          edge(v, g);
          edge(g, valueVertex(space, value));
        } else {
          edge(v, valueVertex(space, value));
        }
      }
      return v;
    }

    /**
     * The vertex of a value of a space. When all variables of the space have the same domain, the
     * colour tells whether the value is in it; otherwise the domains are edges.
     */
    int valueVertex(int space, int value) {
      long key = ((long) space << 32) | (value & 0xffffffffL);
      Integer v = valueVertex.get(key);
      if (v == null) {
        Space s = spaces.get(space);
        String colour =
            "w|" + space + (s.sameDomain ? (s.values.contains(value) ? "|in" : "|out") : "");
        v = vertex(colour);
        valueVertex.put(key, v);
      }
      return v;
    }

    int varVertex(IntVar x) {
      Integer v = varVertices.get(x);
      if (v == null) {
        Integer space = spaceOf == null ? null : spaceOf.get(x);
        String key;
        if (x == objective) {
          key = "v|objective";
        } else if (space != null) {
          key = "n|" + space + "|" + x.getClass().getName();
        } else {
          key = "v|" + x.getClass().getName() + "|" + x.dom().getClass().getName() + "|" + x.dom();
        }
        v = vertex(key);
        varVertices.put(x, v);
        vars.add(x);
        if (space != null && !spaces.get(space).sameDomain) {
          for (ValueEnumeration e = x.dom().valueEnumeration(); e.hasMoreElements(); ) {
            edge(v, valueVertex(space, e.nextElement()));
          }
        }
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

    private void add(int from, int to) {
      if (degree[from] == adjacency[from].length) {
        adjacency[from] = Arrays.copyOf(adjacency[from], 2 * degree[from]);
      }
      adjacency[from][degree[from]++] = to;
    }
  }

  /** The elements of an array of constants, compared by their values. */
  private static final class Contents {
    private final Atom[] atoms;
    private final int hash;

    Contents(Atom[] atoms) {
      this.atoms = atoms;
      int h = atoms.length;
      for (Atom a : atoms) {
        h = 31 * h + a.constant().hashCode();
      }
      this.hash = h;
    }

    @Override
    public boolean equals(Object o) {
      if (!(o instanceof Contents c) || c.hash != hash || c.atoms.length != atoms.length) {
        return false;
      }
      for (int i = 0; i < atoms.length; i++) {
        if (atoms[i] != c.atoms[i] && !atoms[i].constant().equals(c.atoms[i].constant())) {
          return false;
        }
      }
      return true;
    }

    @Override
    public int hashCode() {
      return hash;
    }
  }

  /**
   * A short key for an array argument of constants only, the same for two arrays exactly when they
   * have the same elements, or null when the array holds a variable or a value of a value space.
   * The graph uses it in place of one entry per element, so that a table of a hundred thousand
   * tuples costs one string, not a hundred thousand.
   */
  private String constantArray(Atom[] arg) {
    if (constantArrays.containsKey(arg)) {
      return constantArrays.get(arg);
    }
    String key = null;
    if (Arrays.stream(arg).allMatch(Atom::isConstant)) {
      key = contentKeys.computeIfAbsent(new Contents(arg), c -> "k" + contentKeys.size());
    }
    constantArrays.put(arg, key);
    return key;
  }

  private boolean isArrayName(SimpleNode arg) {
    if (arg.getId() != JJTSCALARFLATEXPR || ((ASTScalarFlatExpr) arg).getType() != 2) {
      return false;
    }
    String ident = ((ASTScalarFlatExpr) arg).getIdent();
    return namedArrays.containsKey(ident)
        || dictionary.getIntArray(ident) != null
        || dictionary.getVariableArray(ident) != null
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
      case 0, 1 -> intConstant(e.getInt());
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
      return intConstant(i);
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
      return new Atom(null, other, null, -1, 0);
    }
    throw new Unsupported("identifier " + ident);
  }

  /**
   * The atoms of an array given by name; arrays of parameters are constants, arrays of float or set
   * variables are not supported.
   */
  private Atom[] namedArray(String ident) {
    Atom[] atoms = namedArrays.get(ident);
    if (atoms == null) {
      atoms = readArray(ident);
      namedArrays.put(ident, atoms);
    }
    return atoms;
  }

  private Atom[] readArray(String ident) {
    int[] ints = dictionary.getIntArray(ident);
    if (ints != null) {
      Atom[] atoms = new Atom[ints.length];
      for (int i = 0; i < ints.length; i++) {
        atoms[i] = intConstant(ints[i]);
      }
      return atoms;
    }
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
      return Arrays.stream(others).map(v -> new Atom(null, v, null, -1, 0)).toArray(Atom[]::new);
    }
    if (dictionary.getFloatArray(ident) != null) {
      return Arrays.stream(dictionary.getFloatArray(ident))
          .mapToObj(f -> constant("f" + f))
          .toArray(Atom[]::new);
    }
    throw new Unsupported("array " + ident);
  }

  private Atom variable(IntVar v) {
    return v.singleton() ? intConstant(v.value()) : new Atom(v, null, null, -1, 0);
  }

  private Atom intConstant(int c) {
    return intAtoms.computeIfAbsent(c, k -> new Atom(null, null, "i" + k, -1, k));
  }

  private static Atom constant(String c) {
    return new Atom(null, null, c, -1, 0);
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
