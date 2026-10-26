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
 * value of a fixed variable from the others, as they do, and also finds Hall intervals.
 *
 * <p>Setting the system property {@code org.jacop.fz.alldifferent} to false turns the detection
 * off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class AlldifferentDetector implements ParserTreeConstants {

  /** The fewest variables a clique must have to get an all-different constraint. */
  static final int MIN_CLIQUE_SIZE = 5;

  // the most neighbour checks spent on finding cliques
  static final long WORK_LIMIT = 20_000_000L;

  // the disequalities are kept when the system property org.jacop.fz.alldifferent is redundant
  private static final boolean REDUNDANT =
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
    Support.forEachConstraint(astTree, this::collect);
    if (nodes.size() < MIN_CLIQUE_SIZE) {
      return;
    }
    List<int[][]> cliques = cliques();
    for (int[][] clique : cliques) {
      post(clique);
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% alldifferent cliques: "
              + nodes.size()
              + " variables, "
              + cliques.size()
              + " cliques, "
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
      default -> {
        // not a disequality
      }
    }
  }

  // x - y != d
  private void edge(IntVar x, IntVar y, int d, SimpleNode source) {
    if (x == y || x.singleton() || y.singleton()) {
      return;
    }
    int i = node(x);
    int j = node(y);
    sources.computeIfAbsent(Edge.of(i, j, d), k -> new ArrayList<>()).add(source);
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
    covered.addAll(edges);
    if (!REDUNDANT) {
      for (Edge e : edges) {
        replaced.addAll(sources.getOrDefault(e, List.of()));
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
        support.delayedConstraints.add(new XplusCeqZ(v, o, x[k]));
      }
    }
    if (support.options.debug()) {
      FzConsole.println("% alldifferent on " + clique.length + " variables");
    }
    support.delayedConstraints.add(new Alldiff(x));
  }
}
