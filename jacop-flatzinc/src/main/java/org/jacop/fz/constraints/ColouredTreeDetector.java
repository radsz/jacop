/*
 * ColouredTreeDetector.java
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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.graph.ColouredSpanningTreeBound;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds weighted spanning trees ({@code jacop_wst}, MiniZinc's {@code weighted_spanning_tree})
 * whose edges are also counted by limits {@code sum(e in S) es[e] <= c} ({@code int_lin_le}, {@code
 * int_lin_eq}, {@code bool_lin_le} or {@code bool_lin_eq} with all coefficients 1) and posts a
 * redundant {@link ColouredSpanningTreeBound} with a family of such limits over disjoint edge sets
 * (a partition matroid). The trees with the limits are then the common bases of two matroids, so
 * both their existence and their minimum cost are found exactly at every node. Limits that do not
 * restrict a tree (c at least n-1 or the size of S) are left out; when the sets overlap, larger
 * sets are taken first. Edge sets of degree limits overlap one another, so a model with both colour
 * and degree limits gets the colour ones.
 *
 * <p>Setting the system property {@code org.jacop.fz.colouredTree} to false turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ColouredTreeDetector implements ParserTreeConstants {

  private final Support support;

  private final List<ASTConstElem> trees = new ArrayList<>();
  private final List<IntVar[]> sumVars = new ArrayList<>();
  private final List<Integer> sumLimits = new ArrayList<>();

  /** Statistics: the constraints posted. */
  int posted;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public ColouredTreeDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.colouredTree is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.colouredTree"));
  }

  /**
   * It scans the model and posts a redundant {@link ColouredSpanningTreeBound} for every weighted
   * spanning tree with limits on the number of its edges in disjoint sets.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    if (trees.isEmpty() || sumVars.isEmpty()) {
      return;
    }
    for (ASTConstElem node : trees) {
      tree(node);
    }
    if (support.options.debug() && posted > 0) {
      FzConsole.println("% ColouredTreeDetector: " + posted + " coloured spanning tree bounds");
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_wst" -> trees.add(node);
      case "int_lin_le", "int_lin_eq", "bool_lin_le", "bool_lin_eq" -> {
        int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        for (int x : a) {
          if (x != 1) {
            return;
          }
        }
        sumVars.add(support.getVarArray((SimpleNode) node.jjtGetChild(1)));
        sumLimits.add(support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)));
      }
      default -> {
        // not used
      }
    }
  }

  private void tree(ASTConstElem node) {
    int n = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(0));
    int[] from = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] to = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    int[] w = support.getIntArray((SimpleNode) node.jjtGetChild(3));
    IntVar[] es = support.getVarArray((SimpleNode) node.jjtGetChild(4));
    IntVar cost = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(5));
    for (int x : w) {
      if (x < 0) {
        return;
      }
    }
    Map<IntVar, Integer> edge = new IdentityHashMap<>();
    for (int e = 0; e < es.length; e++) {
      if (edge.put(es[e], e) != null) {
        // an edge variable used twice
        return;
      }
    }

    // candidate limits: every variable an edge, no edge twice, restricting the tree
    List<int[]> sets = new ArrayList<>();
    List<Integer> limits = new ArrayList<>();
    for (int i = 0; i < sumVars.size(); i++) {
      IntVar[] v = sumVars.get(i);
      int c = sumLimits.get(i);
      if (c < 0 || c >= v.length || c >= n - 1) {
        continue;
      }
      int[] set = new int[v.length];
      boolean ok = true;
      for (int j = 0; j < v.length && ok; j++) {
        Integer e = edge.get(v[j]);
        ok = e != null;
        set[j] = ok ? e : -1;
      }
      if (ok && Arrays.stream(set).distinct().count() == set.length) {
        sets.add(set);
        limits.add(c);
      }
    }
    if (sets.isEmpty()) {
      return;
    }

    // disjoint sets, larger first
    Integer[] order = new Integer[sets.size()];
    for (int i = 0; i < order.length; i++) {
      order[i] = i;
    }
    Arrays.sort(order, (x, y) -> Integer.compare(sets.get(y).length, sets.get(x).length));
    int[] colours = new int[es.length];
    Arrays.fill(colours, -1);
    List<Integer> caps = new ArrayList<>();
    for (int i : order) {
      int[] set = sets.get(i);
      boolean free = true;
      for (int e : set) {
        free &= colours[e] < 0;
      }
      if (!free) {
        continue;
      }
      for (int e : set) {
        colours[e] = caps.size();
      }
      caps.add(limits.get(i));
    }
    support.pose(
        new ColouredSpanningTreeBound(
            n,
            from,
            to,
            w,
            colours,
            caps.stream().mapToInt(Integer::intValue).toArray(),
            es,
            cost,
            1));
    posted++;
  }
}
