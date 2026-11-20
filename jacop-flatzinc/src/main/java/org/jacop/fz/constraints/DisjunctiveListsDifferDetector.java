/*
 * DisjunctiveListsDifferDetector.java
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
import org.jacop.constraints.AllDifferentLists;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It recognises "lists x and y differ" written as a disjunction of disequalities, {@code (x[1] !=
 * y[1]) \/ ... \/ (x[k] != y[k])}, and posts the largest group of lists that all differ pairwise as
 * one {@link AllDifferentLists}. MiniZinc flattens each disjunction into a clause {@code
 * bool_clause([b1, ..., bk], [])} and one half reification per position, {@code b_t -> x[t] !=
 * y[t]} ({@code int_lin_ne_imp}, {@code int_ne_imp}, or the full reifications). XCSP3 models of
 * timetabling (ExaminationTimetabling of the XCSP 2026 competition) state "no two events in the
 * same room in the same period" this way, over every pair of events: 32,094 clauses and 64,188
 * reified disequalities over 261 events, whose Booleans are two thirds of the variables of the
 * model.
 *
 * <p>The pairs form a graph over the lists. A disequality {@code x[t] != y[t]} posted on its own
 * ({@code int_ne}, {@code int_lin_ne}) also makes the lists differ, so it is an edge too, though it
 * stays posted: the exam models leave out the disjunction of two events that may never share a
 * period. In each connected group of lists, the lists with the fewest edges are dropped one at a
 * time until the rest all differ pairwise (a greedy clique), and that clique, if it has at least
 * {@link #MIN_LISTS} lists, gets one {@link AllDifferentLists}; the disjunctions inside it are not
 * posted, the others are. A clause qualifies only when each of its Booleans occurs in no other
 * constraint, the solve item and the output.
 *
 * <p>Propagation: {@link AllDifferentLists} removes the last free value of a list that would make
 * it equal to a fixed list, as the clauses do by unit propagation (F. Boussemart, C. Lecoutre, G.
 * Audemard and C. Piette, "XCSP3-core: A format for representing constraint
 * satisfaction/optimization problems", arXiv:2009.00514, 2020, section 4.1.1, allDifferent on
 * lists), without the Booleans. On by default; {@code -Dorg.jacop.fz.listsDifferClauses=false}
 * turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class DisjunctiveListsDifferDetector implements ParserTreeConstants {

  /** The fewest lists a clique must have to be posted. */
  static final int MIN_LISTS = 3;

  /** The most lists in one group whose clique is searched. */
  static final int MAX_LISTS = 20_000;

  private final Support support;

  private final Set<IntVar> pinned;

  private final Set<SimpleNode> replaced = Collections.newSetFromMap(new IdentityHashMap<>());

  private final Set<Var> removed = Collections.newSetFromMap(new IdentityHashMap<>());

  // b -> x != y: the two variables and the constraint node, by b
  private record Diseq(IntVar x, IntVar y, SimpleNode node) {}

  private final Map<IntVar, Diseq> defs = new IdentityHashMap<>();

  private final Map<IntVar, Integer> occurrences = new IdentityHashMap<>();

  private final List<ASTConstElem> clauses = new ArrayList<>();

  // disequalities x != y posted on their own
  private final List<IntVar[]> plain = new ArrayList<>();

  /** A list of variables compared by identity. */
  private record VarList(IntVar[] vars) {
    @Override
    public boolean equals(Object o) {
      if (!(o instanceof VarList(IntVar[] v)) || v.length != vars.length) {
        return false;
      }
      for (int i = 0; i < vars.length; i++) {
        if (v[i] != vars[i]) {
          return false;
        }
      }
      return true;
    }

    @Override
    public int hashCode() {
      int h = 1;
      for (IntVar x : vars) {
        h = 31 * h + System.identityHashCode(x);
      }
      return h;
    }

    @Override
    public String toString() {
      return Arrays.toString(vars);
    }
  }

  // a clause read as lists a != b, with the nodes it replaces
  private record Pair(int a, int b, List<SimpleNode> nodes, List<IntVar> booleans) {}

  private final Map<VarList, Integer> ids = new LinkedHashMap<>();

  private final List<VarList> lists = new ArrayList<>();

  private final List<Pair> pairs = new ArrayList<>();

  /** Statistics: the lists of the posted cliques. */
  int cliqueLists;

  /** Statistics: the AllDifferentLists posted. */
  int posted;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   * @param pinned the variables of the solve item, which must stay.
   */
  public DisjunctiveListsDifferDetector(Support support, Set<IntVar> pinned) {
    this.support = support;
    this.pinned = pinned;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.listsDifferClauses is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.listsDifferClauses"));
  }

  /**
   * The clauses and reified disequalities posted as AllDifferentLists; they are not posted.
   *
   * @return the replaced constraint nodes.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  /**
   * The Booleans of the replaced clauses, which no constraint uses any more.
   *
   * @return the removed Booleans.
   */
  public Set<Var> removed() {
    return removed;
  }

  /**
   * It scans the constraint items of the model and posts the cliques of lists that differ.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    long start = System.nanoTime();
    support.forEachConstraint(astTree, this::collect);
    if (clauses.isEmpty()) {
      return;
    }
    for (ASTConstElem clause : clauses) {
      readClause(clause);
    }
    if (pairs.isEmpty()) {
      return;
    }
    post();
    if (support.options.debug() && posted > 0) {
      FzConsole.println(
          "% lists differ clauses: "
              + pairs.size()
              + " clauses over "
              + lists.size()
              + " lists, "
              + posted
              + " AllDifferentLists over "
              + cliqueLists
              + " lists, "
              + replaced.size()
              + " constraints replaced, "
              + (System.nanoTime() - start) / 1_000_000
              + " ms");
    }
  }

  private void collect(ASTConstElem node) {
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      PartialCopyDetector.countVariables(support, (SimpleNode) node.jjtGetChild(i), occurrences);
    }
    switch (node.getName()) {
      case "bool_clause" -> {
        if (support.getVarArray(child(node, 1)).length == 0
            && support.getVarArray(child(node, 0)).length >= 2) {
          clauses.add(node);
        }
      }
      case "int_ne_imp", "int_ne_reif" -> {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        if (p1.getType() != 0 && p2.getType() != 0) {
          define(
              support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2)),
              support.getVariable(p1),
              support.getVariable(p2),
              node);
        }
      }
      case "int_lin_ne_imp", "int_lin_ne_reif" -> {
        IntVar[] x = linearDifference(node);
        if (x != null) {
          define(support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3)), x[0], x[1], node);
        }
      }
      case "int_ne" -> {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        if (p1.getType() != 0 && p2.getType() != 0) {
          plain.add(new IntVar[] {support.getVariable(p1), support.getVariable(p2)});
        }
      }
      case "int_lin_ne" -> {
        IntVar[] x = linearDifference(node);
        if (x != null) {
          plain.add(x);
        }
      }
      default -> {
        // not part of a disjunction of disequalities
      }
    }
  }

  // x and y when the linear constraint is a * x - a * y (!=) 0
  private IntVar[] linearDifference(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    if (a == null || a.length != 2 || a[0] == 0 || a[0] != -a[1]) {
      return null;
    }
    IntVar[] x = support.getVarArray(child(node, 1));
    if (x.length != 2 || support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)) != 0) {
      return null;
    }
    return x;
  }

  private void define(IntVar b, IntVar x, IntVar y, SimpleNode node) {
    if (b == null || b.singleton() || x == y || x.singleton() || y.singleton()) {
      return;
    }
    if (defs.containsKey(b)) {
      // two definitions of one Boolean: neither is read
      defs.put(b, null);
      return;
    }
    defs.put(b, new Diseq(x, y, node));
  }

  // the lists of a clause whose Booleans each define one disequality and occur nowhere else
  private void readClause(ASTConstElem clause) {
    IntVar[] b = support.getVarArray(child(clause, 0));
    int k = b.length;
    IntVar[] x = new IntVar[k];
    IntVar[] y = new IntVar[k];
    List<SimpleNode> nodes = new ArrayList<>(k + 1);
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    for (int t = 0; t < k; t++) {
      Diseq d = defs.get(b[t]);
      if (d == null
          || !seen.add(b[t])
          || occurrences.getOrDefault(b[t], 0) != 2
          || pinned.contains(b[t])
          || support.dictionary.isOutput(b[t])) {
        return;
      }
      x[t] = d.x();
      y[t] = d.y();
      nodes.add(d.node());
    }
    // positions in one order: by the index of the variable of x, with y following
    Integer[] order = new Integer[k];
    for (int t = 0; t < k; t++) {
      order[t] = t;
    }
    Arrays.sort(order, (p, q) -> Integer.compare(x[p].index(), x[q].index()));
    IntVar[] xs = new IntVar[k];
    IntVar[] ys = new IntVar[k];
    for (int t = 0; t < k; t++) {
      xs[t] = x[order[t]];
      ys[t] = y[order[t]];
    }
    if (!canonical(xs) || !canonical(ys) || overlap(xs, ys)) {
      return;
    }
    nodes.add(clause);
    int a = id(xs);
    int c = id(ys);
    pairs.add(new Pair(a, c, nodes, Arrays.asList(b)));
  }

  // a list is read in the order of its variables' indexes, so both lists of a pair must be sorted
  // the same way for their positions to match
  private static boolean canonical(IntVar[] v) {
    for (int t = 1; t < v.length; t++) {
      if (v[t - 1].index() >= v[t].index()) {
        return false;
      }
    }
    return true;
  }

  private static boolean overlap(IntVar[] x, IntVar[] y) {
    for (IntVar a : x) {
      for (IntVar b : y) {
        if (a == b) {
          return true;
        }
      }
    }
    return false;
  }

  private int id(IntVar[] v) {
    VarList key = new VarList(v);
    Integer i = ids.get(key);
    if (i == null) {
      i = lists.size();
      ids.put(key, i);
      lists.add(key);
    }
    return i;
  }

  private static long edge(int a, int b) {
    return a < b ? ((long) a << 32) | b : ((long) b << 32) | a;
  }

  private void post() {
    int m = lists.size();
    Set<Long> edges = new HashSet<>();
    Map<Long, Pair> byEdge = new HashMap<>();
    for (Pair p : pairs) {
      if (p.a() != p.b()) {
        edges.add(edge(p.a(), p.b()));
        byEdge.putIfAbsent(edge(p.a(), p.b()), p);
      }
    }
    impliedEdges(edges);
    // adjacency and connected groups
    List<Set<Integer>> adj = new ArrayList<>(m);
    for (int i = 0; i < m; i++) {
      adj.add(new HashSet<>());
    }
    int[] parent = new int[m];
    for (int i = 0; i < m; i++) {
      parent[i] = i;
    }
    for (long e : edges) {
      int a = (int) (e >>> 32);
      int b = (int) e;
      adj.get(a).add(b);
      adj.get(b).add(a);
      parent[find(parent, a)] = find(parent, b);
    }
    Map<Integer, List<Integer>> groups = new LinkedHashMap<>();
    for (int i = 0; i < m; i++) {
      groups.computeIfAbsent(find(parent, i), r -> new ArrayList<>()).add(i);
    }
    for (List<Integer> group : groups.values()) {
      if (group.size() < MIN_LISTS || group.size() > MAX_LISTS) {
        continue;
      }
      List<Integer> clique = clique(group, adj);
      if (clique.size() < MIN_LISTS) {
        continue;
      }
      IntVar[][] x = new IntVar[clique.size()][];
      for (int i = 0; i < x.length; i++) {
        x[i] = lists.get(clique.get(i)).vars();
      }
      support.pose(new AllDifferentLists(x));
      posted++;
      cliqueLists += clique.size();
      for (int i = 0; i < clique.size(); i++) {
        for (int j = i + 1; j < clique.size(); j++) {
          Pair p = byEdge.get(edge(clique.get(i), clique.get(j)));
          if (p != null) {
            replace(p);
          }
        }
      }
    }
  }

  private void replace(Pair p) {
    replaced.addAll(p.nodes());
    removed.addAll(p.booleans());
  }

  // the edges of the disequalities posted on their own: lists a and b differ when a[t] != b[t]
  private void impliedEdges(Set<Long> edges) {
    if (plain.isEmpty()) {
      return;
    }
    Map<IntVar, List<int[]>> where = new IdentityHashMap<>();
    for (int i = 0; i < lists.size(); i++) {
      IntVar[] v = lists.get(i).vars();
      for (int t = 0; t < v.length; t++) {
        where.computeIfAbsent(v[t], z -> new ArrayList<>()).add(new int[] {i, t});
      }
    }
    for (IntVar[] d : plain) {
      List<int[]> wx = where.get(d[0]);
      List<int[]> wy = where.get(d[1]);
      if (wx == null || wy == null) {
        continue;
      }
      for (int[] p : wx) {
        for (int[] q : wy) {
          if (p[0] != q[0]
              && p[1] == q[1]
              && lists.get(p[0]).vars().length == lists.get(q[0]).vars().length) {
            edges.add(edge(p[0], q[0]));
          }
        }
      }
    }
  }

  // a clique of the group: drop the list with the fewest neighbours left until all are adjacent
  private static List<Integer> clique(List<Integer> group, List<Set<Integer>> adj) {
    Set<Integer> left = new HashSet<>(group);
    Map<Integer, Integer> degree = new HashMap<>();
    for (int i : group) {
      int d = 0;
      for (int j : adj.get(i)) {
        if (left.contains(j)) {
          d++;
        }
      }
      degree.put(i, d);
    }
    while (left.size() >= MIN_LISTS) {
      int worst = -1;
      int worstDegree = Integer.MAX_VALUE;
      for (int i : left) {
        int d = degree.get(i);
        if (d < worstDegree || (d == worstDegree && i > worst)) {
          worst = i;
          worstDegree = d;
        }
      }
      if (worstDegree == left.size() - 1) {
        break;
      }
      left.remove(worst);
      for (int j : adj.get(worst)) {
        if (left.contains(j)) {
          degree.merge(j, -1, Integer::sum);
        }
      }
    }
    List<Integer> clique = new ArrayList<>(left);
    Collections.sort(clique);
    return clique;
  }

  private static int find(int[] parent, int i) {
    while (parent[i] != i) {
      parent[i] = parent[parent[i]];
      i = parent[i];
    }
    return i;
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }
}
