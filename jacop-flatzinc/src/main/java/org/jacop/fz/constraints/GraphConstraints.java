/*
 * GraphConstraints.java
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

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.graph.BoundedPath;
import org.jacop.constraints.graph.Path;
import org.jacop.constraints.graph.Reachable;
import org.jacop.constraints.graph.Steiner;
import org.jacop.constraints.graph.Tree;
import org.jacop.constraints.graph.WeightedSpanningTree;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/*
 * Generation of graph constraints in flatzinc.
 *
 * @author Krzysztof Kuchcinski
 */
class GraphConstraints implements ParserTreeConstants {

  private static final String GRAPH_PACKAGE_PREFIX = "org.jacop.graph.";

  final Store store;
  final Support support;

  public GraphConstraints(Support support) {
    this.store = support.store;
    this.support = support;
  }

  @SuppressWarnings("unchecked")
  <T extends Constraint> void gen_jacop_graph_isomorphism(SimpleNode node) {

    IntDomain[] t = support.getSetArray((SimpleNode) node.jjtGetChild(0));
    IntDomain[] p = support.getSetArray((SimpleNode) node.jjtGetChild(1));
    int[] targetType = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    int[] patternType = support.getIntArray((SimpleNode) node.jjtGetChild(3));
    IntVar[] m = support.getVarArray((SimpleNode) node.jjtGetChild(4));
    int offset = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(5));
    String cName = "GraphIsomorphism";

    try {
      Class<?> c = Class.forName(GRAPH_PACKAGE_PREFIX + cName);
      Constructor<?> cons =
          c.getConstructor(
              IntDomain[].class,
              IntDomain[].class,
              int[].class,
              int[].class,
              IntVar[].class,
              int.class);
      Object constraint = cons.newInstance(t, p, targetType, patternType, m, offset);
      support.poseDc((DecomposedConstraint<T>) constraint);

    } catch (ClassNotFoundException
        | InvocationTargetException
        | IllegalAccessException
        | InstantiationException
        | NoSuchMethodException _) {
      throw new RuntimeException(
          "% Constraint "
              + cName
              + " is not available in this version; requires "
              + GRAPH_PACKAGE_PREFIX);
    }
  }

  void gen_jacop_graph_match(SimpleNode node) {
    genGraphMatchConstraint(node, "GraphMatch", true, false);
  }

  void gen_jacop_digraph_match(SimpleNode node) {
    genGraphMatchConstraint(node, "GraphMatch", false, false);
  }

  void gen_jacop_sub_graph_match(SimpleNode node) {
    genGraphMatchConstraint(node, "SubGraphMatch", true, true);
  }

  void gen_jacop_sub_digraph_match(SimpleNode node) {
    genGraphMatchConstraint(node, "SubGraphMatch", false, true);
  }

  /**
   * Shared helper for graph/digraph match and sub-graph/sub-digraph match constraint generation.
   *
   * @param node the AST node containing constraint parameters.
   * @param constraintName the constraint class name (e.g. "GraphMatch" or "SubGraphMatch").
   * @param isUndirected true for undirected graph, false for directed graph.
   * @param useTargetTypeForBound if true, uses target_type length for matchVars upper bound;
   *     otherwise uses pattern_type length.
   */
  private void genGraphMatchConstraint(
      SimpleNode node, String constraintName, boolean isUndirected, boolean useTargetTypeForBound) {

    int[] t = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    int[] p = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] target_type = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    int[] pattern_type = support.getIntArray((SimpleNode) node.jjtGetChild(3));
    IntVar[] match = support.getVarArray((SimpleNode) node.jjtGetChild(4));
    int indexMin = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(5));

    try {
      IntVar[] matchVars;
      if (indexMin == 0) {
        matchVars = match;
      } else {
        int upperBound = (useTargetTypeForBound ? target_type.length : pattern_type.length) - 1;
        matchVars = new IntVar[match.length];
        for (int i = 0; i < match.length; i++) {
          matchVars[i] = new IntVar(store, "node_" + i, 0, upperBound);
          support.pose(new XplusCeqZ(matchVars[i], indexMin, match[i]));
        }
      }

      Class<?> c = Class.forName(GRAPH_PACKAGE_PREFIX + constraintName);
      Constructor<?> cons =
          c.getConstructor(
              Store.class,
              int[].class,
              int[].class,
              int[].class,
              int[].class,
              int.class,
              IntVar[].class,
              boolean.class);
      Object constraint =
          cons.newInstance(
              store, t, p, target_type, pattern_type, indexMin, matchVars, isUndirected);
      support.pose((Constraint) constraint);

    } catch (ClassNotFoundException
        | InvocationTargetException
        | IllegalAccessException
        | InstantiationException
        | NoSuchMethodException _) {
      throw new RuntimeException(
          "% Constraint "
              + constraintName
              + " is not available in this version; requires "
              + GRAPH_PACKAGE_PREFIX);
    }
  }

  void gen_jacop_clique(SimpleNode node) {
    int[] g = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] c = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int indexMin = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    String cName = "Clique";

    int[] type = new int[c.length];
    Arrays.fill(type, 1);

    IntVar cost = new IntVar(store, 0, IntDomain.MAX_INT);

    try {
      Class<?> cls = Class.forName(GRAPH_PACKAGE_PREFIX + cName);
      Constructor<?> cons =
          cls.getConstructor(
              Store.class, int[].class, int[].class, int.class, IntVar[].class, IntVar.class);
      Object constraint = cons.newInstance(store, g, type, indexMin, c, cost);
      support.pose((Constraint) constraint);

    } catch (ClassNotFoundException
        | InvocationTargetException
        | IllegalAccessException
        | InstantiationException
        | NoSuchMethodException _) {
      throw new RuntimeException(
          "% Constraint "
              + cName
              + " is not available in this version; requires "
              + GRAPH_PACKAGE_PREFIX);
    }
  }

  // MiniZinc graph globals; node numbers start at base, the smallest index of ns

  private int[] ints(SimpleNode node, int i) {
    return support.getIntArray((SimpleNode) node.jjtGetChild(i));
  }

  private IntVar[] vars(SimpleNode node, int i) {
    return support.getVarArray((SimpleNode) node.jjtGetChild(i));
  }

  private IntVar var(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private int integer(SimpleNode node, int i) {
    return support.getInt((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  /** jacop_reachable and jacop_dreachable: from, to, r, ns, es, base. */
  void gen_jacop_reachable(SimpleNode node, boolean directed) {
    support.pose(
        new Reachable(
            ints(node, 0),
            ints(node, 1),
            var(node, 2),
            vars(node, 3),
            vars(node, 4),
            integer(node, 5),
            directed));
  }

  /** jacop_connected and jacop_dconnected: from, to, ns, es, base. */
  void gen_jacop_connected(SimpleNode node, boolean directed) {
    support.pose(
        new Reachable(
            ints(node, 0),
            ints(node, 1),
            null,
            vars(node, 2),
            vars(node, 3),
            integer(node, 4),
            directed));
  }

  /** jacop_tree and jacop_dtree: from, to, r, ns, es, base. */
  void gen_jacop_tree(SimpleNode node, boolean directed) {
    support.poseDc(
        new Tree(
            ints(node, 0),
            ints(node, 1),
            var(node, 2),
            vars(node, 3),
            vars(node, 4),
            integer(node, 5),
            directed));
  }

  /** jacop_path and jacop_dpath: from, to, s, t, ns, es, base. */
  void gen_jacop_path(SimpleNode node, boolean directed) {
    support.poseDc(
        new Path(
            ints(node, 0),
            ints(node, 1),
            var(node, 2),
            var(node, 3),
            vars(node, 4),
            vars(node, 5),
            integer(node, 6),
            directed));
  }

  /** jacop_bounded_path and jacop_bounded_dpath: from, to, w, s, t, ns, es, K, base. */
  void gen_jacop_bounded_path(SimpleNode node, boolean directed) {
    support.poseDc(
        new BoundedPath(
            ints(node, 0),
            ints(node, 1),
            ints(node, 2),
            var(node, 3),
            var(node, 4),
            vars(node, 5),
            vars(node, 6),
            var(node, 7),
            integer(node, 8),
            directed));
  }

  /** jacop_steiner: from, to, w, ns, es, K, base. */
  void gen_jacop_steiner(SimpleNode node) {
    support.poseDc(
        new Steiner(
            ints(node, 0),
            ints(node, 1),
            ints(node, 2),
            null,
            vars(node, 3),
            vars(node, 4),
            var(node, 5),
            integer(node, 6),
            false));
  }

  /** jacop_dsteiner: from, to, w, r, ns, es, K, base. */
  void gen_jacop_dsteiner(SimpleNode node) {
    support.poseDc(
        new Steiner(
            ints(node, 0),
            ints(node, 1),
            ints(node, 2),
            var(node, 3),
            vars(node, 4),
            vars(node, 5),
            var(node, 6),
            integer(node, 7),
            true));
  }

  /** jacop_wst: N, from, to, w, es, K; nodes 1..N. */
  void gen_jacop_wst(SimpleNode node) {
    support.poseDc(
        new WeightedSpanningTree(
            integer(node, 0),
            ints(node, 1),
            ints(node, 2),
            ints(node, 3),
            null,
            vars(node, 4),
            var(node, 5),
            1,
            false));
  }

  /** jacop_dwst: N, from, to, w, r, es, K; nodes 1..N. */
  void gen_jacop_dwst(SimpleNode node) {
    support.poseDc(
        new WeightedSpanningTree(
            integer(node, 0),
            ints(node, 1),
            ints(node, 2),
            ints(node, 3),
            var(node, 4),
            vars(node, 5),
            var(node, 6),
            1,
            true));
  }
}
