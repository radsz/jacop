/*
 * AntichainDetector.java
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
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * It posts the LYM inequality of a group of integer vectors that are pairwise incomparable in the
 * product order. Vectors u and v are incomparable when {@code u[c] < v[c]} for some coordinate c
 * and {@code v[d] < u[d]} for some coordinate d, so a group of pairwise incomparable vectors is an
 * antichain of the product of the chains {@code lo[c]..hi[c]} of their coordinates. Let {@code
 * N(r)} be the number of elements of rank r of that product, the rank of a vector being {@code
 * sum(c) (x[c] - lo[c])}. A product of chains is an LYM poset (it has the normalized matching
 * property: L. H. Harper, The morphology of partially ordered sets, Journal of Combinatorial Theory
 * A 17, 1974, pp. 44-58; W. N. Hsieh and D. J. Kleitman, Normalized matching in direct products of
 * partial orders, Studies in Applied Mathematics 52, 1973, pp. 285-289; K. Engel, Sperner Theory,
 * Cambridge University Press, 1997, chapter 4), so every antichain A satisfies {@code sum(a in A) 1
 * / N(rank(a)) <= 1}. For subsets (chains of two elements) this is the inequality of D. Lubell (A
 * short proof of Sperner's lemma, Journal of Combinatorial Theory 1, 1966, p. 299), K. Yamamoto
 * (1954) and L. D. Meshalkin (1963). It gives Sperner's theorem (E. Sperner, Ein Satz über
 * Untermengen einer endlichen Menge, Mathematische Zeitschrift 27, 1928, pp. 544-548) and its
 * multiset form (N. G. de Bruijn, C. van Ebbenhorst Tengbergen and D. Kruyswijk, On the set of
 * divisors of a number, Nieuw Archief voor Wiskunde 23, 1951, pp. 191-193): no antichain has more
 * elements than the largest rank.
 *
 * <p>The models never state this counting argument, and search alone cannot find it: the XCSP3
 * problems Antichain1 (subsets of a 9- or 10-element set, 2026 competition) and Antichain2
 * (multisets) ask for exactly the largest rank plus one vectors in the UNSAT instances (127 = C(9,
 * 4) + 1, 253 = C(10, 5) + 1, 142), and exactly the largest rank in the SAT ones. JaCoP posts, for
 * each vector i, its rank {@code r[i] = sum(c) (x[i][c] - lo[c])}, its weight {@code w[i] = floor(S
 * / N(r[i]))} as an element constraint and {@code sum(w) <= S}, with S a multiple of the largest N.
 * With more vectors than the largest rank the sum fails at the root; with as many it leaves each
 * vector only the largest ranks. The rounding down keeps the inequality valid, so the constraint is
 * redundant (implied by the incomparability constraints alone, whatever else the model says).
 *
 * <p>A relation "u[c] < v[c] for some c" is read in two forms: a clause over literals each of which
 * implies {@code u[c] < v[c]} (a {@code jacop_among} of the literals with value 1 and a count of at
 * least one, {@code bool_clause} or {@code array_bool_or}, with literals from {@code
 * int_lin_le_imp}, {@code int_lin_le_reif}, {@code int_lt_imp}, {@code int_lt_reif}, {@code
 * bool_lt_imp} and {@code bool_lt_reif}), and two element constraints with the same index into u
 * and v whose results are in {@code a < b}. The vectors and coordinates are the classes of the
 * variables on the same side of a relation and at the same position of its two sides; a group is
 * posted when every vector has one variable of every coordinate and every ordered pair of its
 * vectors has a relation. The inequality is posted only when it removes, at the root, some rank
 * with more than one element.
 *
 * <p>Setting the system property {@code org.jacop.fz.antichain} to false turns the detection off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class AntichainDetector {

  // the most vectors of a group (pairs of vectors are checked one by one)
  static final int MAX_VECTORS = 5_000;

  // the most coordinates of a vector
  static final int MAX_COORDINATES = 1_000;

  private final Support support;

  // the integer of bool2int(b, i), by i
  private final Map<IntVar, IntVar> boolOf = new IdentityHashMap<>();

  // the literals r with r -> u < v, by r
  private final Map<IntVar, IntVar[]> lessOf = new IdentityHashMap<>();

  // the literals of the clauses
  private final List<IntVar[]> clauses = new ArrayList<>();

  // the element constraints a = list[k]
  private static final class Element {
    private final IntVar index;
    private final IntVar[] list;
    private final int offset;

    Element(IntVar index, IntVar[] list, int offset) {
      this.index = index;
      this.list = list;
      this.offset = offset;
    }

    IntVar index() {
      return index;
    }

    IntVar[] list() {
      return list;
    }

    int offset() {
      return offset;
    }
  }

  private final Map<IntVar, Element> elementOf = new IdentityHashMap<>();

  // the relations a < b between results of elements
  private final List<IntVar[]> resultLess = new ArrayList<>();

  // the relations "u[p] < v[p] for some p", as the pairs (u[p], v[p])
  private final List<IntVar[][]> relations = new ArrayList<>();

  private boolean infeasible;

  private int groups;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public AntichainDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.antichain is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.antichain"));
  }

  /**
   * It tells whether some group has more vectors than the largest rank of its product of chains. It
   * is valid after {@link #detect}.
   *
   * @return true when the model has no solution.
   */
  public boolean infeasible() {
    return infeasible;
  }

  /**
   * It tells how many groups got the inequality. It is valid after {@link #detect}.
   *
   * @return the number of groups.
   */
  public int groups() {
    return groups;
  }

  /**
   * It scans the constraint items of the model and posts the inequalities. It is called after the
   * constraints of the model are posted.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    buildRelations();
    if (relations.isEmpty()) {
      return;
    }
    for (List<IntVar[][]> component : components()) {
      if (infeasible) {
        break;
      }
      post(component);
    }
    if (support.options.debug()) {
      FzConsole.println("% antichain: " + groups + " groups" + (infeasible ? ", infeasible" : ""));
    }
    if (groups > 0 && support.options.getStatistics()) {
      FzConsole.println("%%%mzn-stat: antichainGroups=" + groups + "\n%%%mzn-stat-end");
    }
  }

  private IntVar canonical(IntVar v) {
    IntVar b = boolOf.get(v);
    return b == null ? v : b;
  }

  private static boolean binary(IntVar v) {
    return v.min() >= 0 && v.max() <= 1;
  }

  private IntVar variable(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "bool2int" -> {
        IntVar b = variable(node, 0);
        IntVar i = variable(node, 1);
        if (b != i) {
          boolOf.put(i, b);
        }
      }
      case "int_lin_le_imp", "int_lin_le_reif" -> linearLess(node, variable(node, 3));
      case "int_lin_le" -> linearLess(node, null);
      case "int_lt_imp", "int_lt_reif", "bool_lt_imp", "bool_lt_reif" ->
          less(variable(node, 0), variable(node, 1), variable(node, 2));
      case "int_lt" -> less(variable(node, 0), variable(node, 1), null);
      case "jacop_among" -> {
        IntDomain s = support.getSetLiteral(node, 1);
        if (s.getSize() == 1 && s.min() == 1 && variable(node, 2).min() >= 1) {
          clauses.add(support.getVarArray((SimpleNode) node.jjtGetChild(0)));
        }
      }
      case "bool_clause" -> {
        if (support.getVarArray((SimpleNode) node.jjtGetChild(1)).length == 0) {
          clauses.add(support.getVarArray((SimpleNode) node.jjtGetChild(0)));
        }
      }
      case "array_bool_or" -> {
        if (variable(node, 1).singleton(1)) {
          clauses.add(support.getVarArray((SimpleNode) node.jjtGetChild(0)));
        }
      }
      case "jacop_array_var_int_element_nonshifted" ->
          element(node, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)) /* first index */);
      case "array_var_int_element", "array_var_bool_element" -> element(node, 1);
      default -> {
        // not read
      }
    }
  }

  // a = list[k] with k counted from first
  private void element(ASTConstElem node, int first) {
    IntVar k = variable(node, 0);
    IntVar[] list = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar a = variable(node, 2);
    if (list == null || a.singleton()) {
      return;
    }
    elementOf.putIfAbsent(a, new Element(k, list, first));
  }

  // c * u - c * v <= rhs with c > 0 and rhs / c < 0: u < v (when r holds, if there is r)
  private void linearLess(ASTConstElem node, IntVar r) {
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    // -a[1] in long: [MIN_VALUE, MIN_VALUE] weighs u + v, not u - v
    if (a == null
        || v == null
        || a.length != 2
        || v.length != 2
        || a[0] == 0
        || a[0] != -(long) a[1]) {
      return;
    }
    long c = Math.abs((long) a[0]);
    long rhs = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (Math.floorDiv(rhs, c) > -1) {
      return;
    }
    if (a[0] > 0) {
      less(v[0], v[1], r);
    } else {
      less(v[1], v[0], r);
    }
  }

  private void less(IntVar u, IntVar v, IntVar r) {
    if (u == v || u.singleton() || v.singleton()) {
      return;
    }
    if (r == null) {
      resultLess.add(new IntVar[] {u, v});
    } else if (binary(r) && !r.singleton()) {
      lessOf.putIfAbsent(canonical(r), new IntVar[] {u, v});
    }
  }

  // the relations of the clauses and of the elements
  private void buildRelations() {
    for (IntVar[] clause : clauses) {
      if (clause == null || clause.length < 2 || clause.length > MAX_COORDINATES) {
        continue;
      }
      IntVar[][] pairs = new IntVar[clause.length][];
      boolean all = true;
      for (int k = 0; k < clause.length && all; k++) {
        IntVar[] p = binary(clause[k]) ? lessOf.get(canonical(clause[k])) : null;
        all = p != null;
        if (all) {
          pairs[k] = new IntVar[] {canonical(p[0]), canonical(p[1])};
        }
      }
      if (all) {
        relations.add(pairs);
      }
    }
    for (IntVar[] ab : resultLess) {
      Element a = elementOf.get(ab[0]);
      Element b = elementOf.get(ab[1]);
      if (a == null
          || b == null
          || a.index() != b.index()
          || a.offset() != b.offset()
          || a.list().length != b.list().length
          || a.list() == b.list()) {
        continue;
      }
      IntVar k = a.index();
      List<IntVar[]> pairs = new ArrayList<>();
      for (int p = 0; p < a.list().length; p++) {
        if (k.domain.contains(p + a.offset())) {
          pairs.add(new IntVar[] {canonical(a.list()[p]), canonical(b.list()[p])});
        }
      }
      if (pairs.size() >= 2 && pairs.size() <= MAX_COORDINATES) {
        relations.add(pairs.toArray(new IntVar[0][]));
      }
    }
  }

  // union-find over variables
  private static final class Classes {
    final Map<IntVar, IntVar> parent = new IdentityHashMap<>();

    IntVar find(IntVar v) {
      IntVar p = parent.get(v);
      if (p == null) {
        parent.put(v, v);
        return v;
      }
      if (p == v) {
        return v;
      }
      IntVar root = find(p);
      parent.put(v, root);
      return root;
    }

    void union(IntVar a, IntVar b) {
      IntVar ra = find(a);
      IntVar rb = find(b);
      if (ra != rb) {
        parent.put(ra, rb);
      }
    }
  }

  private final Classes vectors = new Classes();
  private final Classes coordinates = new Classes();

  // the relations grouped by the connected components of their vectors
  private List<List<IntVar[][]>> components() {
    Classes groupsOf = new Classes();
    for (IntVar[][] pairs : relations) {
      for (IntVar[] p : pairs) {
        vectors.union(pairs[0][0], p[0]);
        vectors.union(pairs[0][1], p[1]);
        coordinates.union(p[0], p[1]);
        groupsOf.union(pairs[0][0], p[0]);
        groupsOf.union(pairs[0][0], p[1]);
      }
    }
    Map<IntVar, List<IntVar[][]>> byGroup = new LinkedHashMap<>();
    for (IntVar[][] pairs : relations) {
      byGroup.computeIfAbsent(groupsOf.find(pairs[0][0]), g -> new ArrayList<>()).add(pairs);
    }
    return new ArrayList<>(byGroup.values());
  }

  // posts the inequality of a component when its vectors form a grid and are pairwise related
  private void post(List<IntVar[][]> component) {
    // the vectors and coordinates in order of first appearance
    Map<IntVar, Integer> vectorIndex = new IdentityHashMap<>();
    Map<IntVar, Integer> coordinateIndex = new IdentityHashMap<>();
    List<Map<Integer, IntVar>> cells = new ArrayList<>();
    for (IntVar[][] pairs : component) {
      for (IntVar[] p : pairs) {
        for (IntVar x : p) {
          int vi = vectorIndex.computeIfAbsent(vectors.find(x), k -> vectorIndex.size());
          int ci =
              coordinateIndex.computeIfAbsent(coordinates.find(x), k -> coordinateIndex.size());
          if (vi == cells.size()) {
            cells.add(new LinkedHashMap<>());
          }
          IntVar old = cells.get(vi).putIfAbsent(ci, x);
          if (old != null && old != x) {
            return; // two variables of one vector in one coordinate
          }
          if (vectorIndex.size() > MAX_VECTORS || coordinateIndex.size() > MAX_COORDINATES) {
            return;
          }
        }
      }
    }
    int n = vectorIndex.size();
    int m = coordinateIndex.size();
    if (n < 2 || m < 2) {
      return;
    }
    IntVar[][] x = new IntVar[n][m];
    for (int i = 0; i < n; i++) {
      if (cells.get(i).size() != m) {
        return;
      }
      for (Map.Entry<Integer, IntVar> e : cells.get(i).entrySet()) {
        x[i][e.getKey()] = e.getValue();
      }
    }
    // every ordered pair of vectors has a relation
    Set<Long> related = new HashSet<>();
    for (IntVar[][] pairs : component) {
      int u = vectorIndex.get(vectors.find(pairs[0][0]));
      int v = vectorIndex.get(vectors.find(pairs[0][1]));
      if (u == v) {
        return;
      }
      related.add((long) u * n + v);
    }
    if (related.size() != (long) n * (n - 1)) {
      return;
    }
    // the chains lo[c]..hi[c] and the numbers of elements by rank of their product
    long[] lo = new long[m];
    int top = 0;
    for (int c = 0; c < m; c++) {
      long low = Long.MAX_VALUE;
      long high = Long.MIN_VALUE;
      for (int i = 0; i < n; i++) {
        low = Math.min(low, x[i][c].min());
        high = Math.max(high, x[i][c].max());
      }
      lo[c] = low;
      if (high - low > MAX_COORDINATES || top + high - low > 100_000) {
        return;
      }
      top += (int) (high - low);
    }
    double[] count = {1};
    int length = 0;
    for (int c = 0; c < m; c++) {
      int span = 0;
      for (int i = 0; i < n; i++) {
        span = (int) Math.max(span, x[i][c].max() - lo[c]);
      }
      double[] next = new double[length + span + 1];
      for (int r = 0; r <= length; r++) {
        for (int t = 0; t <= span; t++) {
          next[r + t] += count[r];
        }
      }
      count = next;
      length += span;
    }
    double width = 0;
    for (double nr : count) {
      width = Math.max(width, nr);
    }
    if (n > width) {
      infeasible = true;
      groups++;
      return;
    }
    // exact numbers are needed from here: n <= width <= MAX_VECTORS keeps them small
    if (width > Integer.MAX_VALUE / 4) {
      return;
    }
    long most = (long) width;
    // S, a multiple of the largest rank, with n * S an int
    long scale = most * Math.max(1, (Integer.MAX_VALUE / 2) / (n * most));
    if (scale / most < 1 || n * scale > Integer.MAX_VALUE / 2) {
      return;
    }
    int[] weight = new int[length + 1];
    boolean prunes = false;
    long least = scale / most;
    for (int r = 0; r <= length; r++) {
      long w = count[r] >= scale ? 1 : scale / (long) count[r];
      weight[r] = (int) w;
      // the rank r is removed at the root when the other vectors at their least weight leave less
      prunes |= count[r] >= 2 && (n - 1) * least + w > scale;
    }
    if (!prunes) {
      return;
    }
    IntVar[] w = new IntVar[n];
    for (int i = 0; i < n; i++) {
      IntVar[] terms = new IntVar[m + 1];
      int[] a = new int[m + 1];
      long shift = 0;
      for (int c = 0; c < m; c++) {
        terms[c] = x[i][c];
        a[c] = 1;
        shift += lo[c];
      }
      IntVar rank = new IntVar(support.store, 0, length);
      terms[m] = rank;
      a[m] = -1;
      support.pose(new LinearInt(terms, a, "==", (int) shift));
      w[i] = new IntVar(support.store, (int) least, (int) scale);
      support.pose(new ElementInteger(rank, weight, w[i], -1));
    }
    int[] ones = new int[n];
    Arrays.fill(ones, 1);
    support.pose(new LinearInt(w, ones, "<=", (int) scale));
    groups++;
  }

  /**
   * It fails the store when {@link #infeasible()} holds.
   *
   * @throws org.jacop.core.FailException when the model has no solution.
   */
  public void failIfInfeasible() {
    if (infeasible) {
      throw Store.failException;
    }
  }
}
