/*
 * IntensionTableDetector.java
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
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
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
import java.util.Set;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ASTSolveExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Replaces a small expression that MiniZinc flattened into several constraints by the table of its
 * solutions over the model's variables.
 *
 * <p>MiniZinc flattens one constraint of the model, such as {@code x mod y = 0 \/ y mod x = 0},
 * into constraints linked by introduced variables: two {@code int_mod} results, two half-reified
 * equalities and a clause. Each part propagates on its own and to bounds, so the conjunction prunes
 * far less than the relation it states between {@code x} and {@code y}. XCSP3 solvers keep such an
 * expression whole: ACE filters a small intension constraint by checking supports on the expression
 * tree (Lecoutre, "Constraint Networks", 2009, generic arc consistency), and Savile Row tabulates
 * small groups of constraints (Akgün, Gent, Jefferson, Miguel, Nightingale, Salamon, "Automatic
 * Discovery and Exploitation of Promising Subproblems for Tabulation", CP 2018; Dekker, Björdal,
 * Carlsson, Flener, Monette, "Auto-tabling for subproblem presolving in MiniZinc", Constraints 22,
 * 2017). This detector rebuilds the expression from the flattened model:
 *
 * <ol>
 *   <li>a variable is internal when it is not output, not in the solve item and not aliased; the
 *       constraints that share an internal variable form one group, so a group holds every
 *       constraint of each of its internal variables;
 *   <li>a group with at least two constraints and at most {@value #MAX_ARITY} other (outer)
 *       variables is solved over its outer variables, by a small search that computes functionally
 *       defined variables and branches on the others, when one of its constraints is a division, a
 *       modulo or an element over a variable array with two unfixed variables or more (these
 *       propagate to bounds while their relations have holes all over the box);
 *   <li>the table of the outer tuples that extend to a solution of the group replaces the group,
 *       and its internal variables leave the default search.
 * </ol>
 *
 * The table is equivalent to the group projected onto the outer variables, so every solution of the
 * outer variables is kept. It is not used when all solutions are searched for, since solutions that
 * differ only in internal variables would merge, nor under {@code --proof}. The system property
 * {@code org.jacop.fz.intensionTable=false} turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class IntensionTableDetector implements ParserTreeConstants {

  /** At most this many outer variables, the arity of a table. */
  static final int MAX_ARITY = 3;

  /** At most this many constraints in one group. */
  static final int MAX_GROUP = 16;

  /** At most this many tuples in one table. */
  static final int MAX_TUPLES = 10_000;

  /** At most this many search nodes to tabulate one group. */
  static final long MAX_NODES = 200_000;

  /** At most this many search nodes over all groups. */
  static final long BUDGET = 5_000_000;

  /** An internal variable is branched on only when its domain is at most this large. */
  static final int MAX_BRANCH = 1024;

  private final Support support;

  private final Set<SimpleNode> replaced = new HashSet<>();

  private final Set<Var> internal = new HashSet<>();

  private final Set<IntVar> tabled = Collections.newSetFromMap(new IdentityHashMap<>());

  private int tables;

  private int tuples;

  private long nodes;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public IntensionTableDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.intensionTable is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.intensionTable"));
  }

  /**
   * It tells if the detection is forced on also when all solutions are searched for (property value
   * {@code force}); solutions that differ only in internal variables then print once. Forced, it
   * also tabulates groups without a division, modulo or variable-array element (for tests).
   *
   * @return true if the system property org.jacop.fz.intensionTable is force.
   */
  public static boolean forced() {
    return "force".equalsIgnoreCase(System.getProperty("org.jacop.fz.intensionTable"));
  }

  /**
   * The constraints that a table replaced; they are not posted.
   *
   * @return the constraint nodes of the tabulated groups.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  /**
   * The internal variables of the tabulated groups, which no constraint holds any more.
   *
   * @return the internal variables.
   */
  public Set<Var> unconstrained() {
    return internal;
  }

  /**
   * The outer variables of the tables posted, whose domains the tables give holes.
   *
   * @return the variables, compared by identity.
   */
  public Set<IntVar> tabled() {
    return tabled;
  }

  /**
   * It scans the constraint items of the model and replaces each small group linked by internal
   * variables by a table over its outer variables.
   *
   * @param astTree the root of the parsed model.
   * @param skipped constraint nodes another detector already replaced; a group holding one is left.
   */
  public void detect(SimpleNode astTree, Set<SimpleNode> skipped) {
    List<Item> items = new ArrayList<>();
    Map<IntVar, Integer> occurrences = new IdentityHashMap<>();
    Set<IntVar> pinned = Collections.newSetFromMap(new IdentityHashMap<>());
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          support.checkTimeOut();
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            Item it = Item.read(support, (ASTConstElem) item);
            if (it == null || skipped.contains(item)) {
              // its variables stay outer: the constraint is posted as it is
              PartialCopyDetector.countVariables(support, item, occurrences);
              for (int k = 0; k < item.jjtGetNumChildren(); k++) {
                collectAll((SimpleNode) item.jjtGetChild(k), pinned);
              }
            } else {
              items.add(it);
            }
          }
        }
      } else if (node.getId() == JJTSOLVEITEM || node.getId() == JJTMODELEND) {
        collectAll(node, pinned);
      }
    }
    pinned.addAll(support.dictionary.aliasTable.keySet());
    pinned.addAll(support.dictionary.aliasTable.values());

    // groups: union-find over the items, joined by the variables only they hold
    Map<IntVar, Integer> firstItem = new IdentityHashMap<>();
    int[] parent = new int[items.size()];
    for (int i = 0; i < parent.length; i++) {
      parent[i] = i;
    }
    for (int i = 0; i < items.size(); i++) {
      for (IntVar v : items.get(i).vars) {
        if (isInternal(v, pinned)) {
          Integer f = firstItem.putIfAbsent(v, i);
          if (f != null) {
            union(parent, f, i);
          }
        }
      }
    }
    Map<Integer, List<Item>> groups = new LinkedHashMap<>();
    for (int i = 0; i < items.size(); i++) {
      groups.computeIfAbsent(find(parent, i), k -> new ArrayList<>()).add(items.get(i));
    }
    for (List<Item> group : groups.values()) {
      if (nodes >= BUDGET) {
        break;
      }
      support.checkTimeOut();
      if (group.size() >= 2 && group.size() <= MAX_GROUP) {
        tabulate(group, pinned);
      }
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% intension table detector: "
              + tables
              + " tables of "
              + replaced.size()
              + " constraints, "
              + tuples
              + " tuples, "
              + nodes
              + " nodes");
    }
  }

  private boolean isInternal(IntVar v, Set<IntVar> pinned) {
    return !v.singleton() && !pinned.contains(v) && !support.dictionary.isOutput(v);
  }

  private void collectAll(SimpleNode node, Set<IntVar> into) {
    Map<IntVar, Integer> found = new IdentityHashMap<>();
    collectAll(node, found);
    into.addAll(found.keySet());
  }

  private void collectAll(SimpleNode node, Map<IntVar, Integer> found) {
    PartialCopyDetector.countVariables(support, node, found);
    if (node instanceof ASTSolveExpr e && e.getIdent() != null) {
      // the objective: a variable, or an element of an array of variables (all of it is pinned)
      IntVar v = support.dictionary.getVariable(e.getIdent());
      IntVar[] array = support.dictionary.getVariableArray(e.getIdent());
      if (v != null) {
        found.merge(v, 1, Integer::sum);
      }
      if (array != null) {
        for (IntVar a : array) {
          found.merge(a, 1, Integer::sum);
        }
      }
    }
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      collectAll((SimpleNode) node.jjtGetChild(i), found);
    }
  }

  /**
   * Whether the constraint is a periodic operation (division, modulo) or an element over a variable
   * array with two unfixed variables or more. JaCoP propagates these to bounds, and their relations
   * have holes all over the box, so a table prunes far more. The other operations are left as they
   * are: on the MiniZinc Challenge models tables of linear, comparison, reified, Boolean,
   * constant-array element, product, absolute value, minimum and maximum groups pruned little more
   * and made each node slower (fast-food, celar, maximum-dag, cable-tree-wiring, open-stacks).
   */
  private static boolean weak(Item it) {
    if (it.vars.size() < 2) {
      return false;
    }
    return switch (it.op) {
      case DIV, MOD -> true;
      case ELEMENT -> {
        for (int i = 1; i < it.terms.length - 1; i++) {
          if (!it.terms[i].singleton()) {
            yield true;
          }
        }
        yield false;
      }
      default -> false;
    };
  }

  private void tabulate(List<Item> group, Set<IntVar> pinned) {
    if (!forced() && group.stream().noneMatch(IntensionTableDetector::weak)) {
      return;
    }
    // the variables of the group: outer ones first
    Map<IntVar, Integer> index = new IdentityHashMap<>();
    List<IntVar> outer = new ArrayList<>();
    List<IntVar> inner = new ArrayList<>();
    for (Item it : group) {
      for (IntVar v : it.vars) {
        if (!v.singleton() && !index.containsKey(v)) {
          index.put(v, -1);
          if (isInternal(v, pinned)) {
            inner.add(v);
          } else {
            outer.add(v);
          }
        }
      }
    }
    if (outer.isEmpty() || outer.size() > MAX_ARITY || inner.isEmpty()) {
      return;
    }
    double space = 1;
    for (IntVar v : outer) {
      space *= v.getSize();
    }
    IntVar[] vars = new IntVar[outer.size() + inner.size()];
    for (int i = 0; i < outer.size(); i++) {
      vars[i] = outer.get(i);
      index.put(vars[i], i);
    }
    for (int i = 0; i < inner.size(); i++) {
      vars[outer.size() + i] = inner.get(i);
      index.put(vars[outer.size() + i], outer.size() + i);
    }
    Bound[] bound = new Bound[group.size()];
    for (int c = 0; c < group.size(); c++) {
      bound[c] = new Bound(group.get(c), index);
    }
    // the tuples to enumerate: the outer box, less the largest outer variable a function defines
    int defined = 1;
    for (Bound b : bound) {
      int r = Tabulator.resultTerm(b.item);
      if (r >= 0 && b.at[r] >= 0 && b.at[r] < outer.size()) {
        defined = Math.max(defined, vars[b.at[r]].getSize());
      }
    }
    if (space / defined > MAX_TUPLES) {
      return;
    }
    Tabulator t = new Tabulator(vars, outer.size(), bound, Math.min(MAX_NODES, BUDGET - nodes));
    int[][] rows = t.run();
    nodes += t.nodes;
    if (rows == null) {
      return;
    }
    IntVar[] scope = outer.toArray(new IntVar[0]);
    for (Item it : group) {
      replaced.add(it.node);
    }
    internal.addAll(inner);
    if (rows.length == 0) {
      throw Store.failException;
    }
    if (support.options.debug()) {
      StringBuilder sig = new StringBuilder("% intension group: " + outer.size() + " outer,");
      group.stream().map(it -> it.node.getName()).sorted().forEach(n -> sig.append(' ').append(n));
      FzConsole.println(sig.append(", ").append(rows.length).append(" rows").toString());
    }
    if (rows.length < space) {
      support.pose(new HybridTable(scope, rows));
      Collections.addAll(tabled, scope);
      tables++;
      tuples += rows.length;
    }
  }

  private static int find(int[] parent, int i) {
    while (parent[i] != i) {
      parent[i] = parent[parent[i]];
      i = parent[i];
    }
    return i;
  }

  private static void union(int[] parent, int a, int b) {
    int ra = find(parent, a);
    int rb = find(parent, b);
    if (ra != rb) {
      parent[rb] = ra;
    }
  }

  /** The constraints the detector evaluates, with the place of their functionally defined value. */
  enum Op {
    INT_EQ,
    INT_NE,
    INT_LE,
    INT_LT,
    INT_EQ_REIF,
    INT_NE_REIF,
    INT_LE_REIF,
    INT_LT_REIF,
    INT_EQ_IMP,
    INT_NE_IMP,
    INT_LE_IMP,
    INT_LT_IMP,
    LIN_EQ,
    LIN_NE,
    LIN_LE,
    LIN_EQ_REIF,
    LIN_NE_REIF,
    LIN_LE_REIF,
    LIN_EQ_IMP,
    LIN_NE_IMP,
    LIN_LE_IMP,
    PLUS,
    TIMES,
    DIV,
    MOD,
    ABS,
    MIN,
    MAX,
    BOOL2INT,
    BOOL_NOT,
    BOOL_EQ,
    BOOL_EQ_REIF,
    BOOL_XOR_REIF,
    BOOL_AND_REIF,
    BOOL_OR_REIF,
    BOOL_LE,
    BOOL_LT,
    CLAUSE,
    ARRAY_OR,
    ARRAY_AND,
    ELEMENT,
    SET_IN,
    SET_IN_REIF,
    SET_IN_IMP;
  }

  /**
   * One constraint of the model: its operation, its terms (variables and constants in a fixed
   * layout), constant coefficients and a constant set.
   */
  static final class Item {
    final ASTConstElem node;
    final Op op;
    final IntVar[] terms;
    final int[] coefficients;
    final IntDomain set;
    final List<IntVar> vars = new ArrayList<>();

    private Item(ASTConstElem node, Op op, IntVar[] terms, int[] coefficients, IntDomain set) {
      this.node = node;
      this.op = op;
      this.terms = terms;
      this.coefficients = coefficients;
      this.set = set;
      Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
      for (IntVar v : terms) {
        if (!v.singleton() && seen.add(v)) {
          vars.add(v);
        }
      }
    }

    static Item read(Support s, ASTConstElem node) {
      String name = node.getName();
      Op op = op(name);
      if (op == null) {
        return null;
      }
      try {
        return switch (op) {
          case LIN_EQ, LIN_NE, LIN_LE -> linear(s, node, op, false);
          case LIN_EQ_REIF, LIN_NE_REIF, LIN_LE_REIF, LIN_EQ_IMP, LIN_NE_IMP, LIN_LE_IMP ->
              linear(s, node, op, true);
          case CLAUSE -> {
            IntVar[] pos = s.getVarArray(child(node, 0));
            IntVar[] neg = s.getVarArray(child(node, 1));
            IntVar[] all = new IntVar[pos.length + neg.length];
            System.arraycopy(pos, 0, all, 0, pos.length);
            System.arraycopy(neg, 0, all, pos.length, neg.length);
            yield new Item(node, op, all, new int[] {pos.length}, null);
          }
          case ARRAY_OR, ARRAY_AND -> {
            IntVar[] a = s.getVarArray(child(node, 0));
            IntVar[] all = Arrays.copyOf(a, a.length + 1);
            all[a.length] = s.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
            yield new Item(node, op, all, null, null);
          }
          case ELEMENT -> {
            // index, array, value; the array is the middle of the terms
            IntVar[] a = s.getVarArray(child(node, 1));
            IntVar[] all = new IntVar[a.length + 2];
            all[0] = s.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
            System.arraycopy(a, 0, all, 1, a.length);
            all[a.length + 1] = s.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
            int first = 1;
            if (name.endsWith("_nonshifted")) {
              first = s.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));
            }
            yield new Item(node, op, all, new int[] {first}, null);
          }
          case SET_IN, SET_IN_REIF, SET_IN_IMP -> {
            IntDomain set = s.getSetLiteral(node, 1);
            if (set == null) {
              yield null;
            }
            IntVar x = s.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
            IntVar[] all =
                op == Op.SET_IN
                    ? new IntVar[] {x}
                    : new IntVar[] {x, s.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2))};
            yield new Item(node, op, all, null, set);
          }
          default -> {
            IntVar[] all = new IntVar[node.jjtGetNumChildren()];
            for (int i = 0; i < all.length; i++) {
              if (!(node.jjtGetChild(i) instanceof ASTScalarFlatExpr e)) {
                yield null;
              }
              all[i] = s.getVariable(e);
            }
            yield new Item(node, op, all, null, null);
          }
        };
      } catch (RuntimeException e) {
        // an argument the detector does not read (a float, a set variable): the constraint stays
        return null;
      }
    }

    private static Item linear(Support s, ASTConstElem node, Op op, boolean reified) {
      int[] a = s.getIntArray(child(node, 0));
      IntVar[] x = s.getVarArray(child(node, 1));
      if (a == null || a.length != x.length) {
        return null;
      }
      int c = s.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
      int[] coefficients = Arrays.copyOf(a, a.length + 1);
      coefficients[a.length] = c;
      IntVar[] all = Arrays.copyOf(x, x.length + (reified ? 1 : 0));
      if (reified) {
        all[x.length] = s.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));
      }
      return new Item(node, op, all, coefficients, null);
    }

    private static Op op(String name) {
      return switch (name) {
        case "int_eq" -> Op.INT_EQ;
        case "int_ne" -> Op.INT_NE;
        case "int_le" -> Op.INT_LE;
        case "int_lt" -> Op.INT_LT;
        case "int_eq_reif" -> Op.INT_EQ_REIF;
        case "int_ne_reif" -> Op.INT_NE_REIF;
        case "int_le_reif" -> Op.INT_LE_REIF;
        case "int_lt_reif" -> Op.INT_LT_REIF;
        case "int_eq_imp" -> Op.INT_EQ_IMP;
        case "int_ne_imp" -> Op.INT_NE_IMP;
        case "int_le_imp" -> Op.INT_LE_IMP;
        case "int_lt_imp" -> Op.INT_LT_IMP;
        case "int_lin_eq" -> Op.LIN_EQ;
        case "int_lin_ne" -> Op.LIN_NE;
        case "int_lin_le" -> Op.LIN_LE;
        case "int_lin_eq_reif" -> Op.LIN_EQ_REIF;
        case "int_lin_ne_reif" -> Op.LIN_NE_REIF;
        case "int_lin_le_reif" -> Op.LIN_LE_REIF;
        case "int_lin_eq_imp" -> Op.LIN_EQ_IMP;
        case "int_lin_ne_imp" -> Op.LIN_NE_IMP;
        case "int_lin_le_imp" -> Op.LIN_LE_IMP;
        case "int_plus" -> Op.PLUS;
        case "int_times" -> Op.TIMES;
        case "int_div" -> Op.DIV;
        case "int_mod" -> Op.MOD;
        case "int_abs" -> Op.ABS;
        case "int_min" -> Op.MIN;
        case "int_max" -> Op.MAX;
        case "bool2int" -> Op.BOOL2INT;
        case "bool_not" -> Op.BOOL_NOT;
        case "bool_eq" -> Op.BOOL_EQ;
        case "bool_eq_reif" -> Op.BOOL_EQ_REIF;
        case "bool_xor" -> Op.BOOL_XOR_REIF;
        case "bool_and" -> Op.BOOL_AND_REIF;
        case "bool_or" -> Op.BOOL_OR_REIF;
        case "bool_le" -> Op.BOOL_LE;
        case "bool_lt" -> Op.BOOL_LT;
        case "bool_clause" -> Op.CLAUSE;
        case "array_bool_or" -> Op.ARRAY_OR;
        case "array_bool_and" -> Op.ARRAY_AND;
        case "array_int_element",
            "array_var_int_element",
            "array_bool_element",
            "array_var_bool_element",
            "jacop_array_var_int_element_nonshifted",
            "jacop_array_var_bool_element_nonshifted" ->
            Op.ELEMENT;
        case "set_in" -> Op.SET_IN;
        case "set_in_reif" -> Op.SET_IN_REIF;
        case "set_in_imp" -> Op.SET_IN_IMP;
        default -> null;
      };
    }

    private static SimpleNode child(SimpleNode node, int i) {
      return (SimpleNode) node.jjtGetChild(i);
    }
  }

  /** A constraint of a group over the group's variable indexes; -1 marks a constant term. */
  static final class Bound {
    final Item item;
    final int[] at;
    final long[] constant;

    Bound(Item item, Map<IntVar, Integer> index) {
      this.item = item;
      at = new int[item.terms.length];
      constant = new long[item.terms.length];
      for (int i = 0; i < at.length; i++) {
        IntVar v = item.terms[i];
        if (v.singleton()) {
          at[i] = -1;
          constant[i] = v.value();
        } else {
          at[i] = index.get(v);
        }
      }
    }
  }

  /** The search that lists the outer tuples of a group that extend to a solution. */
  static final class Tabulator {
    private static final long FAIL = Long.MIN_VALUE;
    private static final long MANY = Long.MAX_VALUE;

    private final IntVar[] vars;
    private final int outer;
    private final Bound[] bounds;
    private final long limit;
    private final long[] value;
    private final boolean[] known;
    private final int[] trail;
    private int top;
    private final boolean[] result;
    private final List<int[]> rows = new ArrayList<>();
    long nodes;
    private boolean aborted;

    Tabulator(IntVar[] vars, int outer, Bound[] bounds, long limit) {
      this.vars = vars;
      this.outer = outer;
      this.bounds = bounds;
      this.limit = limit;
      value = new long[vars.length];
      known = new boolean[vars.length];
      trail = new int[vars.length];
      result = new boolean[vars.length];
      for (Bound b : bounds) {
        int r = resultTerm(b.item);
        if (r >= 0 && b.at[r] >= 0) {
          result[b.at[r]] = true;
        }
      }
    }

    /**
     * Lists the tuples.
     *
     * @return the outer tuples, or null when the limits were reached or a variable could not be
     *     settled.
     */
    int[][] run() {
      outerSearch();
      if (aborted) {
        return null;
      }
      return rows.toArray(new int[0][]);
    }

    private void outerSearch() {
      if (aborted || ++nodes > limit) {
        aborted = true;
        return;
      }
      int mark = top;
      if (propagate()) {
        int pick = -1;
        for (int i = 0; i < outer; i++) {
          if (!known[i]
              && (pick < 0
                  || vars[i].getSize() < vars[pick].getSize()
                  || vars[i].getSize() == vars[pick].getSize() && result[pick] && !result[i])) {
            pick = i;
          }
        }
        if (pick < 0) {
          if (innerSearch()) {
            int[] row = new int[outer];
            for (int i = 0; i < outer; i++) {
              row[i] = (int) value[i];
            }
            rows.add(row);
            if (rows.size() > MAX_TUPLES) {
              aborted = true;
            }
          }
        } else {
          for (ValueEnumeration e = vars[pick].dom().valueEnumeration();
              e.hasMoreElements() && !aborted; ) {
            int m = top;
            assign(pick, e.nextElement());
            outerSearch();
            undo(m);
          }
        }
      }
      undo(mark);
    }

    // whether the internal variables extend the current outer tuple to a solution
    private boolean innerSearch() {
      if (aborted || ++nodes > limit) {
        aborted = true;
        return false;
      }
      int mark = top;
      boolean found = false;
      if (propagate()) {
        int pick = -1;
        for (int i = outer; i < vars.length; i++) {
          if (!known[i] && (pick < 0 || vars[i].getSize() < vars[pick].getSize())) {
            pick = i;
          }
        }
        if (pick < 0) {
          found = true;
        } else if (vars[pick].getSize() > MAX_BRANCH) {
          aborted = true;
        } else {
          for (ValueEnumeration e = vars[pick].dom().valueEnumeration();
              e.hasMoreElements() && !found && !aborted; ) {
            int m = top;
            assign(pick, e.nextElement());
            found = innerSearch();
            undo(m);
          }
        }
      }
      undo(mark);
      return found;
    }

    private void assign(int i, long v) {
      value[i] = v;
      known[i] = true;
      trail[top++] = i;
    }

    private void undo(int mark) {
      while (top > mark) {
        known[trail[--top]] = false;
      }
    }

    // checks the constraints with every term known and computes the terms they define
    private boolean propagate() {
      boolean changed = true;
      while (changed) {
        changed = false;
        for (Bound b : bounds) {
          int unknown = -1;
          int count = 0;
          for (int i = 0; i < b.at.length && count < 2; i++) {
            int x = b.at[i];
            if (x >= 0 && !known[x] && (count == 0 || b.at[unknown] != x)) {
              count++;
              unknown = i;
            }
          }
          if (count == 0) {
            if (!check(b)) {
              return false;
            }
          } else if (count == 1) {
            long v = solve(b, unknown);
            if (v == FAIL) {
              return false;
            }
            if (v != MANY) {
              int x = b.at[unknown];
              if (v < Integer.MIN_VALUE
                  || v > Integer.MAX_VALUE
                  || !vars[x].domain.contains((int) v)) {
                return false;
              }
              assign(x, v);
              if (!check(b)) {
                return false;
              }
              changed = true;
            }
          }
        }
      }
      return true;
    }

    private long term(Bound b, int i) {
      return b.at[i] < 0 ? b.constant[i] : value[b.at[i]];
    }

    // the value of the single unknown term i, FAIL if none fits, MANY if not defined by the others
    private long solve(Bound b, int i) {
      Item it = b.item;
      switch (it.op) {
        case INT_EQ, BOOL_EQ, BOOL2INT -> {
          return term(b, 1 - i);
        }
        case BOOL_NOT -> {
          return 1 - term(b, 1 - i);
        }
        case LIN_EQ, PLUS -> {
          return solveLinear(b, i);
        }
        default -> {
          int r = resultTerm(it);
          if (r == i) {
            // every other term is known: the result is a function of them
            for (int k = 0; k < b.at.length; k++) {
              if (b.at[k] >= 0 && b.at[k] == b.at[i] && k != i) {
                return MANY;
              }
            }
            return evaluate(b);
          }
          return MANY;
        }
      }
    }

    private long solveLinear(Bound b, int i) {
      long a;
      long rest;
      if (b.item.op == Op.PLUS) {
        // x + y = z
        long x = term(b, 0);
        long y = term(b, 1);
        long z = term(b, 2);
        return switch (i) {
          case 0 -> z - y;
          case 1 -> z - x;
          default -> x + y;
        };
      }
      int[] c = b.item.coefficients;
      rest = c[c.length - 1];
      a = 0;
      for (int k = 0; k < b.at.length; k++) {
        if (b.at[k] >= 0 && b.at[k] == b.at[i]) {
          a += c[k];
        } else {
          rest -= (long) c[k] * term(b, k);
        }
      }
      if (a == 0) {
        return rest == 0 ? MANY : FAIL;
      }
      return rest % a == 0 ? rest / a : FAIL;
    }

    // the value of the result term of a function, every other term known
    private long evaluate(Bound b) {
      Item it = b.item;
      return switch (it.op) {
        case TIMES -> term(b, 0) * term(b, 1);
        case DIV -> term(b, 1) == 0 ? FAIL : term(b, 0) / term(b, 1);
        case MOD -> term(b, 1) == 0 ? FAIL : term(b, 0) % term(b, 1);
        case ABS -> Math.abs(term(b, 0));
        case MIN -> Math.min(term(b, 0), term(b, 1));
        case MAX -> Math.max(term(b, 0), term(b, 1));
        case ARRAY_OR -> {
          for (int k = 0; k < b.at.length - 1; k++) {
            if (term(b, k) != 0) {
              yield 1;
            }
          }
          yield 0;
        }
        case ARRAY_AND -> {
          for (int k = 0; k < b.at.length - 1; k++) {
            if (term(b, k) == 0) {
              yield 0;
            }
          }
          yield 1;
        }
        case ELEMENT -> {
          long k = term(b, 0) - it.coefficients[0];
          yield k < 0 || k >= b.at.length - 2 ? FAIL : term(b, (int) k + 1);
        }
        default -> {
          // a reification: the truth of the relation
          int last = b.at.length - 1;
          yield holds(b, last) ? 1 : 0;
        }
      };
    }

    // the term a function or a reification defines, or -1
    static int resultTerm(Item it) {
      return switch (it.op) {
        case INT_EQ_REIF,
            INT_NE_REIF,
            INT_LE_REIF,
            INT_LT_REIF,
            LIN_EQ_REIF,
            LIN_NE_REIF,
            LIN_LE_REIF,
            BOOL_EQ_REIF,
            BOOL_XOR_REIF,
            BOOL_AND_REIF,
            BOOL_OR_REIF,
            SET_IN_REIF,
            ARRAY_OR,
            ARRAY_AND,
            ELEMENT,
            TIMES,
            DIV,
            MOD,
            ABS,
            MIN,
            MAX ->
            it.terms.length - 1;
        default -> -1;
      };
    }

    // the relation stated by the terms before term end, for the reified and implied forms
    private boolean holds(Bound b, int end) {
      Item it = b.item;
      return switch (it.op) {
        case INT_EQ_REIF, INT_EQ_IMP, BOOL_EQ_REIF -> term(b, 0) == term(b, 1);
        case INT_NE_REIF, INT_NE_IMP, BOOL_XOR_REIF -> term(b, 0) != term(b, 1);
        case INT_LE_REIF, INT_LE_IMP -> term(b, 0) <= term(b, 1);
        case INT_LT_REIF, INT_LT_IMP -> term(b, 0) < term(b, 1);
        case BOOL_AND_REIF -> term(b, 0) != 0 && term(b, 1) != 0;
        case BOOL_OR_REIF -> term(b, 0) != 0 || term(b, 1) != 0;
        case LIN_EQ_REIF, LIN_EQ_IMP -> linear(b, end) == it.coefficients[end];
        case LIN_NE_REIF, LIN_NE_IMP -> linear(b, end) != it.coefficients[end];
        case LIN_LE_REIF, LIN_LE_IMP -> linear(b, end) <= it.coefficients[end];
        case SET_IN_REIF, SET_IN_IMP -> it.set.contains((int) term(b, 0));
        default -> throw new IllegalStateException(it.op.toString());
      };
    }

    private long linear(Bound b, int end) {
      long s = 0;
      for (int k = 0; k < end; k++) {
        s += it(b).coefficients[k] * term(b, k);
      }
      return s;
    }

    private static Item it(Bound b) {
      return b.item;
    }

    private boolean check(Bound b) {
      Item it = b.item;
      int n = b.at.length;
      return switch (it.op) {
        case INT_EQ, BOOL_EQ, BOOL2INT -> term(b, 0) == term(b, 1);
        case INT_NE -> term(b, 0) != term(b, 1);
        case INT_LE, BOOL_LE -> term(b, 0) <= term(b, 1);
        case INT_LT, BOOL_LT -> term(b, 0) < term(b, 1);
        case BOOL_NOT -> term(b, 0) != term(b, 1);
        case PLUS -> term(b, 0) + term(b, 1) == term(b, 2);
        case LIN_EQ -> linear(b, n) == it.coefficients[n];
        case LIN_NE -> linear(b, n) != it.coefficients[n];
        case LIN_LE -> linear(b, n) <= it.coefficients[n];
        case INT_EQ_IMP, INT_NE_IMP, INT_LE_IMP, INT_LT_IMP, SET_IN_IMP ->
            term(b, n - 1) == 0 || holds(b, n - 1);
        case LIN_EQ_IMP, LIN_NE_IMP, LIN_LE_IMP -> term(b, n - 1) == 0 || holds(b, n - 1);
        case SET_IN -> it.set.contains((int) term(b, 0));
        case CLAUSE -> {
          int positives = it.coefficients[0];
          for (int k = 0; k < n; k++) {
            if (k < positives ? term(b, k) != 0 : term(b, k) == 0) {
              yield true;
            }
          }
          yield false;
        }
        default -> {
          long v = evaluate(b);
          yield v != FAIL && v == term(b, n - 1);
        }
      };
    }
  }
}
