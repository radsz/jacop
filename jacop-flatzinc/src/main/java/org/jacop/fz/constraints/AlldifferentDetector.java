/*
 * AlldifferentDetector.java
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
import java.util.TreeSet;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds all-different constraints written by hand as cliques of pairwise disequalities and posts
 * an {@link Alldiff} on each of them as a redundant constraint. The disequalities are {@code
 * int_ne(x, y)} and {@code int_lin_ne([a, -a], [x, y], c)}, that is {@code x - y != d}. A clique
 * may have offsets: {@code x[i] + o[i]} are all different when {@code x[i] - x[j] != o[j] - o[i]}
 * for every pair, which is how the diagonals of n-queens models are written. A shifted variable
 * {@code x + o} is a new variable linked to x by {@link XplusCeqZ}.
 *
 * <p>The cliques are found greedily, starting from the variables with the most disequalities, and a
 * clique is kept when it has at least {@link #MIN_CLIQUE_SIZE} variables and at least half of its
 * pairs are not in a clique found before. The detection runs before the constraints are posted, and
 * the disequalities inside the cliques are not posted: the all-different constraint removes the
 * value of a fixed variable from the others, as they do, and also finds Hall intervals. The
 * all-different constraints have degree weight 0, and each variable is credited with the
 * disequalities on it that are not posted, so the static degrees that variable selections such as
 * most_constrained read are those of the model.
 *
 * <p>Disequalities implied by other constraints are edges too, though they are not replaced: two
 * elements {@code x[p] = y} and {@code x[q] = z} over the same array whose results y and z have
 * disjoint domains give {@code p != q} (shifted by the difference of the index bases), and an
 * equality {@code a*x - a*y = c} with c != 0 gives {@code x != y}. The positions of a sequence in a
 * permutation, as in Langford's problem written with element constraints, are all different only by
 * such implied disequalities. A clique of the model's own disequalities may use them. A clique of
 * implied disequalities alone is by default only recorded for the permutation sums of {@link
 * LinearSystemDetector}, not posted: the Alldiff over the element positions of LangfordBin made the
 * solvable instances much slower (079 2 s to 63 s, 240 solved in 15 s to none in 240 s). The system
 * property {@code org.jacop.fz.alldifferentImplied} set to {@code post} posts it as well, and
 * {@code off} does not collect implied disequalities.
 *
 * <p>Each clique is recorded with its offsets in {@link Support#allDifferentOffsets}, where {@link
 * LinearSystemDetector} finds the cliques that are permutations of the union of their domains.
 *
 * <p>Setting the system property {@code org.jacop.fz.alldifferent} to false turns the detection
 * off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class AlldifferentDetector implements ParserTreeConstants {

  /** The most elements over one array whose index pairs are compared. */
  static final int MAX_ELEMENT_GROUP = 1000;

  /** The most pairs of elements compared over all arrays. */
  static final long MAX_ELEMENT_PAIRS = 2_000_000L;

  // off, sum (cliques of implied disequalities only recorded, the default) or post (posted too)
  private final String implied =
      System.getProperty("org.jacop.fz.alldifferentImplied", "sum").toLowerCase();

  /** The fewest variables a clique must have to get an all-different constraint. */
  static final int MIN_CLIQUE_SIZE = 5;

  // the most neighbour checks spent on finding cliques
  static final long WORK_LIMIT = 20_000_000L;

  // the disequalities are kept when the system property org.jacop.fz.alldifferent is redundant
  // the disequalities are kept as well
  private final boolean redundant =
      "redundant".equalsIgnoreCase(System.getProperty("org.jacop.fz.alldifferent"));

  private final Support support;

  private final Map<IntVar, Integer> id = new IdentityHashMap<>();

  private final List<IntVar> nodes = new ArrayList<>();

  // adjacency.get(i).get(j) holds every d with nodes[i] - nodes[j] != d
  private final List<Map<Integer, Set<Integer>>> adjacency = new ArrayList<>();

  private final Set<Edge> covered = new HashSet<>();

  // the constraints stating each disequality
  private final Map<Edge, List<SimpleNode>> sources = new HashMap<>();

  private final Set<SimpleNode> replaced = Collections.newSetFromMap(new IdentityHashMap<>());

  // the pairs x - y != d stated by a disequality of the model, not only implied
  private final Set<Edge> stated = new HashSet<>();

  // the elements over each array: {index, base, result}, by the array's variables
  private final Map<List<IntVar>, List<ElementUse>> elements = new LinkedHashMap<>();

  private record ElementUse(IntVar index, int base, IntVar result) {}

  /** Statistics: the implied disequalities collected. */
  int impliedEdges;

  /** Statistics: the cliques that use an implied disequality. */
  int impliedCliques;

  private record Edge(int i, int j, int d) {
    static Edge of(int i, int j, int d) {
      return i < j ? new Edge(i, j, d) : new Edge(j, i, -d);
    }
  }

  private long work;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public AlldifferentDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.alldifferent is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.alldifferent"));
  }

  /**
   * It scans the constraint items of the model and posts an all-different constraint for each
   * clique of disequalities that it finds. It is called before the constraints are posted.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    long start = System.nanoTime();
    support.forEachConstraint(astTree, this::collect);
    elementEdges();
    if (nodes.size() < MIN_CLIQUE_SIZE) {
      return;
    }
    List<int[][]> cliques = cliques();
    for (int[][] clique : cliques) {
      post(clique);
    }
    if (impliedEdges > 0 && (support.options.debug() || support.options.searchStatistics())) {
      FzConsole.println(
          "%%%mzn-stat: alldifferentImpliedEdges="
              + impliedEdges
              + "\n%%%mzn-stat: alldifferentImpliedCliques="
              + impliedCliques
              + "\n%%%mzn-stat-end");
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% alldifferent cliques: "
              + nodes.size()
              + " variables, "
              + cliques.size()
              + " cliques, "
              + replaced.size()
              + " disequalities replaced, "
              + impliedEdges
              + " implied, "
              + (System.nanoTime() - start) / 1_000_000
              + " ms");
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "int_ne" -> {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        if (p1.getType() != 0 && p2.getType() != 0) {
          edge(support.getVariable(p1), support.getVariable(p2), 0, node);
        }
      }
      case "int_lin_ne" -> {
        int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        if (a == null || a.length != 2 || a[0] != -a[1] || a[0] == 0) {
          return;
        }
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        if (c % a[0] == 0) {
          // a * (x0 - x1) != c
          edge(x[0], x[1], c / a[0], node);
        }
      }
      case "int_lin_eq" -> {
        if (!"off".equals(implied)) {
          linearEquality(node);
        }
      }
      case "array_var_int_element", "array_var_bool_element" -> element(node, 1);
      case "jacop_array_var_int_element_nonshifted", "jacop_array_var_bool_element_nonshifted" ->
          element(node, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
      default -> {
        // not a disequality
      }
    }
  }

  // a * x0 - a * x1 = c with c != 0: x0 != x1
  private void linearEquality(ASTConstElem node) {
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    if (a == null || a.length != 2 || a[0] != -a[1] || a[0] == 0) {
      return;
    }
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (x != null && x.length == 2 && c != 0) {
      edge(x[0], x[1], 0, null);
    }
  }

  private void element(ASTConstElem node, int base) {
    if ("off".equals(implied)) {
      return;
    }
    IntVar index = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar[] array = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar result = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (index.singleton() || array == null || array.length < 2) {
      return;
    }
    elements
        .computeIfAbsent(Arrays.asList(array), k -> new ArrayList<>())
        .add(new ElementUse(index, base, result));
  }

  // x[p] = y and x[q] = z with disjoint domains of y and z: p - base_p != q - base_q
  private void elementEdges() {
    long pairs = 0;
    for (List<ElementUse> uses : elements.values()) {
      if (uses.size() < 2 || uses.size() > MAX_ELEMENT_GROUP) {
        continue;
      }
      pairs += (long) uses.size() * (uses.size() - 1) / 2;
      if (pairs > MAX_ELEMENT_PAIRS) {
        break;
      }
      for (int u = 0; u < uses.size(); u++) {
        ElementUse e = uses.get(u);
        for (int w = u + 1; w < uses.size(); w++) {
          ElementUse f = uses.get(w);
          if (!e.result().dom().isIntersecting(f.result().dom())) {
            // the base difference fits an int: both bases index the same array
            edge(e.index(), f.index(), e.base() - f.base(), null);
          }
        }
      }
    }
    elements.clear();
  }

  // x - y != d, stated by source or, when source is null, implied by other constraints
  private void edge(IntVar x, IntVar y, int d, SimpleNode source) {
    if (x == y || x.singleton() || y.singleton()) {
      return;
    }
    int i = node(x);
    int j = node(y);
    Edge edge = Edge.of(i, j, d);
    if (source != null) {
      sources.computeIfAbsent(edge, k -> new ArrayList<>()).add(source);
      stated.add(edge);
    } else {
      impliedEdges++;
    }
    adjacency.get(i).computeIfAbsent(j, k -> new TreeSet<>()).add(d);
    adjacency.get(j).computeIfAbsent(i, k -> new TreeSet<>()).add(-d);
  }

  private int node(IntVar x) {
    return id.computeIfAbsent(
        x,
        k -> {
          nodes.add(k);
          adjacency.add(new LinkedHashMap<>());
          return nodes.size() - 1;
        });
  }

  private int degree(int i) {
    int d = 0;
    for (Set<Integer> s : adjacency.get(i).values()) {
      d += s.size();
    }
    return d;
  }

  // each clique is an array of {node, offset} pairs
  private List<int[][]> cliques() {
    int n = nodes.size();
    int[] degree = new int[n];
    Integer[] order = new Integer[n];
    for (int i = 0; i < n; i++) {
      degree[i] = degree(i);
      order[i] = i;
    }
    Arrays.sort(
        order,
        (p, q) ->
            degree[q] != degree[p] ? Integer.compare(degree[q], degree[p]) : Integer.compare(p, q));
    int[] rank = new int[n];
    for (int r = 0; r < n; r++) {
      rank[order[r]] = r;
    }

    List<int[][]> found = new ArrayList<>();
    for (int r = 0; r < n && work < WORK_LIMIT; r++) {
      int seed = order[r];
      // the neighbours of the seed with their offsets, most connected first
      List<int[]> candidates = new ArrayList<>();
      for (Map.Entry<Integer, Set<Integer>> e : adjacency.get(seed).entrySet()) {
        for (int d : e.getValue()) {
          candidates.add(new int[] {e.getKey(), d});
        }
      }
      candidates.sort((p, q) -> Integer.compare(rank[p[0]], rank[q[0]]));
      for (int[] first : candidates) {
        if (work >= WORK_LIMIT) {
          break;
        }
        if (covered.contains(Edge.of(seed, first[0], first[1]))) {
          continue;
        }
        List<int[]> clique = grow(seed, first, candidates);
        if (clique.size() >= MIN_CLIQUE_SIZE && cover(clique)) {
          found.add(clique.toArray(new int[0][]));
        }
      }
    }
    return found;
  }

  // x[seed] + 0, x[first] + o, ... are pairwise different: x[m] - x[k] != o[k] - o[m]
  private List<int[]> grow(int seed, int[] first, List<int[]> candidates) {
    List<int[]> clique = new ArrayList<>();
    clique.add(new int[] {seed, 0});
    clique.add(first);
    for (int[] c : candidates) {
      if (c == first) {
        continue;
      }
      boolean fits = true;
      for (int k = 1; k < clique.size() && fits; k++) {
        int[] m = clique.get(k);
        work++;
        Set<Integer> ds = m[0] == c[0] ? null : adjacency.get(m[0]).get(c[0]);
        fits = ds != null && ds.contains(c[1] - m[1]);
      }
      if (fits) {
        clique.add(c);
      }
    }
    return clique;
  }

  // marks the pairs of the clique as covered; false if most of them were covered already
  private boolean cover(List<int[]> clique) {
    List<Edge> edges = new ArrayList<>();
    int fresh = 0;
    for (int p = 0; p < clique.size(); p++) {
      for (int q = p + 1; q < clique.size(); q++) {
        int[] a = clique.get(p);
        int[] b = clique.get(q);
        Edge e = Edge.of(a[0], b[0], b[1] - a[1]);
        edges.add(e);
        if (!covered.contains(e)) {
          fresh++;
        }
      }
    }
    if (2 * fresh < edges.size()) {
      return false;
    }
    if (!stated.containsAll(edges)) {
      impliedCliques++;
    }
    if ("sum".equals(implied) && edges.stream().noneMatch(stated::contains)) {
      // a clique of implied disequalities only: recorded for the permutation sums, not posted
      covered.addAll(edges);
      record(clique.toArray(new int[0][]));
      return false;
    }
    covered.addAll(edges);
    if (!redundant) {
      for (Edge e : edges) {
        for (SimpleNode source : sources.getOrDefault(e, List.of())) {
          if (replaced.add(source)) {
            // the static degree counts the disequality, which is not posted
            nodes.get(e.i()).adjustDegree(1);
            nodes.get(e.j()).adjustDegree(1);
          }
        }
      }
    }
    return true;
  }

  /**
   * It tells which constraints the all-different constraints replace: the disequalities between the
   * variables of each clique, which need not be posted.
   *
   * @return the constraint nodes of the replaced disequalities.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  private void post(int[][] clique) {
    IntVar[] x = new IntVar[clique.length];
    for (int k = 0; k < clique.length; k++) {
      IntVar v = nodes.get(clique[k][0]);
      int o = clique[k][1];
      if (o == 0) {
        x[k] = v;
      } else {
        x[k] = new IntVar(support.store, v.min() + o, v.max() + o);
        support.delayedConstraints.add(new XplusCeqZ(v, o, x[k]).setDegreeWeight(0));
      }
    }
    if (support.options.debug()) {
      FzConsole.println("% alldifferent on " + clique.length + " variables");
    }
    support.delayedConstraints.add(new Alldiff(x).setDegreeWeight(0));
    support.detectedAlldifferentLists.add(x);
    record(clique);
  }

  // the clique for the permutation sums: x[k] + o[k] are all different
  private void record(int[][] clique) {
    IntVar[] x = new IntVar[clique.length];
    int[] o = new int[clique.length];
    for (int k = 0; k < clique.length; k++) {
      x[k] = nodes.get(clique[k][0]);
      o[k] = clique[k][1];
    }
    support.allDifferentOffsets.add(new Support.Shifted(x, o));
  }
}
