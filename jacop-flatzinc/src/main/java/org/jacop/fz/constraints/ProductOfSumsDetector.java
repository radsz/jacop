/*
 * ProductOfSumsDetector.java
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It writes a sum of conjunctions over all pairs of two sets of Boolean variables as the product of
 * their counts: {@code sum(i in A, j in B) w * bool2int(a[i] /\ b[j]) = w * sum(a) * sum(b)}. Each
 * conjunction ({@code array_bool_and} of two variables) and its {@code bool2int} must have no other
 * use. The sum of the row is rewritten with the product variable; two {@link SumBool} constraints
 * and one {@link XmulYeqZ} replace the {@code |A| |B|} conjunctions.
 *
 * <p>Hypervolume objectives of diverse solution models flatten to this form: the cell {@code (e,
 * t)} of the objective grid is dominated by a solution when {@code E <= e /\ T <= t}, and the
 * conjunctions of the cells that only the free solution can dominate form a complete bipartite
 * graph between the literals {@code E <= e} and {@code T <= t} (the 2019 MiniZinc Challenge model
 * rcpsp-wet-diverse, after Ingmar, Garcia de la Banda, Stuckey and Tack, Modelling diversity of
 * solutions, AAAI 2020). Its largest instance has 1,176,224 conjunctions and ran out of memory at 4
 * GB before the search started.
 *
 * <p>Setting the system property {@code org.jacop.fz.productOfSums} to false turns the rewrite off.
 * Only groups of at least {@code org.jacop.fz.productOfSums.minTerms} (default 64) conjunctions are
 * rewritten.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ProductOfSumsDetector implements ParserTreeConstants {

  // the fewest conjunctions of a rewritten group
  private final int minTerms = Integer.getInteger("org.jacop.fz.productOfSums.minTerms", 64);

  private static final Set<String> ROWS = Set.of("int_lin_eq", "int_lin_le");

  private final Support support;

  // constraints other detectors replaced
  private final Set<SimpleNode> replaced;

  // y = bool2int(p)
  private record Indicator(IntVar p, SimpleNode node) {}

  // p = x /\ y
  private record Conjunction(IntVar x, IntVar y, SimpleNode node) {}

  private final Map<IntVar, Indicator> indicators = new IdentityHashMap<>();

  private final Map<IntVar, Conjunction> conjunctions = new IdentityHashMap<>();

  private final Map<IntVar, Integer> occurrences = new IdentityHashMap<>();

  private final List<ASTConstElem> rows = new ArrayList<>();

  private final Set<Var> removed = new HashSet<>();

  private final Set<SimpleNode> skipped = new HashSet<>();

  private int products;

  private int terms;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   * @param replaced the constraints other detectors replaced, which are left as they are.
   */
  public ProductOfSumsDetector(Support support, Set<SimpleNode> replaced) {
    this.support = support;
    this.replaced = replaced;
  }

  /**
   * It tells if the rewrite is on.
   *
   * @return false if the system property org.jacop.fz.productOfSums is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.productOfSums"));
  }

  /**
   * It rewrites the rows with sums of conjunctions over complete bipartite graphs.
   *
   * @param astTree the root of the parsed model.
   * @return the conjunction and bool2int nodes it replaces, which must not be posted.
   */
  public Set<SimpleNode> detect(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          support.checkTimeOut();
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            collect((ASTConstElem) item);
          }
        }
      } else if (node.getId() == JJTSOLVEITEM || node.getId() == JJTMODELEND) {
        // variables of the search annotations and the objective stay
        countAll(node);
      }
    }
    if (conjunctions.size() >= minTerms) {
      for (ASTConstElem row : rows) {
        support.checkTimeOut();
        rewrite(row);
      }
    }
    if (support.options.debug() && products > 0) {
      FzConsole.println(
          "% sums of conjunctions as products of sums: " + products + " (" + terms + " terms)");
    }
    return skipped;
  }

  /**
   * It returns the conjunction and indicator variables the rewrite left without constraints.
   *
   * @return the removed variables.
   */
  public Set<Var> removed() {
    return removed;
  }

  private void collect(ASTConstElem node) {
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      PartialCopyDetector.countVariables(support, (SimpleNode) node.jjtGetChild(i), occurrences);
    }
    if (replaced.contains(node)) {
      return;
    }
    switch (node.getName()) {
      case "bool2int" -> {
        IntVar p = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
        IntVar y = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
        // y is p when bool2int made y an alias of p
        if (!p.singleton() && !y.singleton()) {
          indicators.put(y, new Indicator(p, node));
        }
      }
      case "array_bool_and" -> {
        IntVar[] xs = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar p = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
        if (xs.length == 2 && xs[0] != xs[1] && !p.singleton()) {
          conjunctions.put(p, new Conjunction(xs[0], xs[1], node));
        }
      }
      default -> {
        if (ROWS.contains(node.getName())) {
          rows.add(node);
        }
      }
    }
  }

  // the conjunction of term y, or null if y is not an indicator of a conjunction used only here
  private Conjunction term(IntVar y) {
    Indicator ind = indicators.get(y);
    if (ind == null) {
      return null;
    }
    // an alias occurs in the conjunction, twice in bool2int and in the row
    boolean used =
        ind.p() == y
            ? occurrences.getOrDefault(y, 0) == 4
            : occurrences.getOrDefault(y, 0) == 2 && occurrences.getOrDefault(ind.p(), 0) == 2;
    if (!used || support.dictionary.isOutput(y) || support.dictionary.isOutput(ind.p())) {
      return null;
    }
    Conjunction c = conjunctions.get(ind.p());
    if (c == null || c.x().min() < 0 || c.y().min() < 0 || c.x().max() > 1 || c.y().max() > 1) {
      return null;
    }
    return c;
  }

  private void rewrite(ASTConstElem node) {
    if (support.linearRewrites.containsKey(node)) {
      return;
    }
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (a.length != v.length || v.length < minTerms) {
      return;
    }
    // candidate terms by coefficient
    Map<Integer, List<Integer>> groups = new LinkedHashMap<>();
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    Set<IntVar> repeated = Collections.newSetFromMap(new IdentityHashMap<>());
    for (IntVar x : v) {
      if (!seen.add(x)) {
        repeated.add(x);
      }
    }
    for (int i = 0; i < v.length; i++) {
      if (a[i] != 0 && !repeated.contains(v[i]) && term(v[i]) != null) {
        groups.computeIfAbsent(a[i], k -> new ArrayList<>()).add(i);
      }
    }
    boolean[] replaced = new boolean[v.length];
    List<Integer> newCoefficients = new ArrayList<>();
    List<IntVar> newVars = new ArrayList<>();
    for (Map.Entry<Integer, List<Integer>> g : groups.entrySet()) {
      if (g.getValue().size() >= minTerms) {
        components(g.getKey(), g.getValue(), v, replaced, newCoefficients, newVars);
      }
    }
    if (newVars.isEmpty()) {
      return;
    }
    for (int i = 0; i < v.length; i++) {
      if (!replaced[i]) {
        newCoefficients.add(a[i]);
        newVars.add(v[i]);
      }
    }
    support.linearRewrites.put(
        node,
        new LinearOverlapDetector.Rewrite(
            newCoefficients.stream().mapToInt(Integer::intValue).toArray(),
            newVars.toArray(new IntVar[0])));
  }

  // the terms of one coefficient split into the connected components of their conjunction graph
  private void components(
      int w,
      List<Integer> group,
      IntVar[] v,
      boolean[] replaced,
      List<Integer> newCoefficients,
      List<IntVar> newVars) {
    Map<IntVar, Integer> id = new IdentityHashMap<>();
    List<IntVar> vertices = new ArrayList<>();
    for (int i : group) {
      Conjunction c = term(v[i]);
      for (IntVar x : new IntVar[] {c.x(), c.y()}) {
        if (id.putIfAbsent(x, vertices.size()) == null) {
          vertices.add(x);
        }
      }
    }
    int n = vertices.size();
    int[] parent = new int[n];
    for (int k = 0; k < n; k++) {
      parent[k] = k;
    }
    List<List<Integer>> adjacency = new ArrayList<>(n);
    for (int k = 0; k < n; k++) {
      adjacency.add(new ArrayList<>());
    }
    for (int i : group) {
      Conjunction c = term(v[i]);
      int x = id.get(c.x());
      int y = id.get(c.y());
      adjacency.get(x).add(y);
      adjacency.get(y).add(x);
      parent[find(parent, x)] = find(parent, y);
    }
    // the terms of each component, by its root
    Map<Integer, List<Integer>> byRoot = new LinkedHashMap<>();
    for (int i : group) {
      Conjunction c = term(v[i]);
      byRoot.computeIfAbsent(find(parent, id.get(c.x())), k -> new ArrayList<>()).add(i);
    }
    int[] side = new int[n];
    Arrays.fill(side, -1);
    for (List<Integer> component : byRoot.values()) {
      if (component.size() < minTerms) {
        continue;
      }
      int start = id.get(term(v[component.get(0)]).x());
      List<IntVar> left = new ArrayList<>();
      List<IntVar> right = new ArrayList<>();
      if (!twoColour(start, adjacency, side, vertices, left, right)) {
        continue;
      }
      // complete bipartite and without repeated pairs: |A| |B| distinct edges
      Set<Long> edges = new HashSet<>();
      for (int i : component) {
        Conjunction c = term(v[i]);
        int x = id.get(c.x());
        int y = id.get(c.y());
        edges.add((long) Math.min(x, y) * n + Math.max(x, y));
      }
      long all = (long) left.size() * right.size();
      if (left.size() < 2
          || right.size() < 2
          || edges.size() != component.size()
          || all != component.size()
          || Math.abs((long) w) * all > Integer.MAX_VALUE) {
        continue;
      }
      IntVar countLeft = new IntVar(support.store, 0, left.size());
      IntVar countRight = new IntVar(support.store, 0, right.size());
      IntVar product = new IntVar(support.store, 0, (int) all);
      support.pose(new SumBool(left, "==", countLeft));
      support.pose(new SumBool(right, "==", countRight));
      support.pose(new XmulYeqZ(countLeft, countRight, product));
      support.dictionary.addDefinedVar(countLeft);
      support.dictionary.addDefinedVar(countRight);
      support.dictionary.addDefinedVar(product);
      newCoefficients.add(w);
      newVars.add(product);
      for (int i : component) {
        replaced[i] = true;
        Indicator ind = indicators.get(v[i]);
        removed.add(v[i]);
        removed.add(ind.p());
        skipped.add(ind.node());
        skipped.add(conjunctions.get(ind.p()).node());
      }
      products++;
      terms += component.size();
    }
  }

  private static int find(int[] parent, int x) {
    while (parent[x] != x) {
      parent[x] = parent[parent[x]];
      x = parent[x];
    }
    return x;
  }

  // two-colours the component of start; false if it has an odd cycle
  private static boolean twoColour(
      int start,
      List<List<Integer>> adjacency,
      int[] side,
      List<IntVar> vertices,
      List<IntVar> left,
      List<IntVar> right) {
    ArrayDeque<Integer> queue = new ArrayDeque<>();
    side[start] = 0;
    queue.add(start);
    boolean bipartite = true;
    while (!queue.isEmpty()) {
      int u = queue.poll();
      (side[u] == 0 ? left : right).add(vertices.get(u));
      for (int w : adjacency.get(u)) {
        if (side[w] == -1) {
          side[w] = 1 - side[u];
          queue.add(w);
        } else if (side[w] == side[u]) {
          bipartite = false;
        }
      }
    }
    return bipartite;
  }

  private void countAll(SimpleNode node) {
    PartialCopyDetector.countVariables(support, node, occurrences);
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      countAll((SimpleNode) node.jjtGetChild(i));
    }
  }
}
