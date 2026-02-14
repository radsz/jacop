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
      Class<?> c = Class.forName("org.jacop.graph." + cName);
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
          "% Constraint " + cName + " is not available in this version; requires org.jacop.graph.");
    }
  }

  void gen_jacop_graph_match(SimpleNode node) {
    int[] t = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    int[] p = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] target_type = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    int[] pattern_type = support.getIntArray((SimpleNode) node.jjtGetChild(3));
    IntVar[] match = support.getVarArray((SimpleNode) node.jjtGetChild(4));
    int index_min = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(5));
    String cName = "GraphMatch";

    try {
      IntVar[] matchVars = null;
      if (index_min == 0) {
        for (int i = 0; i < match.length; i++) {
          matchVars = match;
        }
      } else {
        matchVars = new IntVar[match.length];
        for (int i = 0; i < match.length; i++) {
          matchVars[i] = new IntVar(store, "node_" + i, 0, pattern_type.length - 1);
          support.pose(new XplusCeqZ(matchVars[i], index_min, match[i]));
        }
      }

      Class<?> c = Class.forName("org.jacop.graph." + cName);
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
          cons.newInstance(store, t, p, target_type, pattern_type, index_min, matchVars, true);
      support.pose((Constraint) constraint);

    } catch (ClassNotFoundException
        | InvocationTargetException
        | IllegalAccessException
        | InstantiationException
        | NoSuchMethodException _) {
      throw new RuntimeException(
          "% Constraint " + cName + " is not available in this version; requires org.jacop.graph.");
    }
  }

  void gen_jacop_digraph_match(SimpleNode node) {
    int[] t = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    int[] p = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] target_type = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    int[] pattern_type = support.getIntArray((SimpleNode) node.jjtGetChild(3));
    IntVar[] match = support.getVarArray((SimpleNode) node.jjtGetChild(4));
    int index_min = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(5));
    String cName = "GraphMatch";

    try {
      IntVar[] matchVars = null;
      if (index_min == 0) {
        for (int i = 0; i < match.length; i++) {
          matchVars = match;
        }
      } else {
        matchVars = new IntVar[match.length];
        for (int i = 0; i < match.length; i++) {
          matchVars[i] = new IntVar(store, "node_" + i, 0, pattern_type.length - 1);
          support.pose(new XplusCeqZ(matchVars[i], index_min, match[i]));
        }
      }

      Class<?> c = Class.forName("org.jacop.graph." + cName);
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
          cons.newInstance(store, t, p, target_type, pattern_type, index_min, matchVars, false);
      support.pose((Constraint) constraint);

    } catch (ClassNotFoundException
        | InvocationTargetException
        | IllegalAccessException
        | InstantiationException
        | NoSuchMethodException _) {
      throw new RuntimeException(
          "% Constraint " + cName + " is not available in this version; requires org.jacop.graph.");
    }
  }

  void gen_jacop_sub_graph_match(SimpleNode node) {
    int[] t = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    int[] p = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] target_type = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    int[] pattern_type = support.getIntArray((SimpleNode) node.jjtGetChild(3));
    IntVar[] match = support.getVarArray((SimpleNode) node.jjtGetChild(4));
    int index_min = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(5));
    String cName = "SubGraphMatch";

    try {
      IntVar[] matchVars = null;
      if (index_min == 0) {
        for (int i = 0; i < match.length; i++) {
          matchVars = match;
        }
      } else {
        matchVars = new IntVar[match.length];
        for (int i = 0; i < match.length; i++) {
          matchVars[i] = new IntVar(store, "node_" + i, 0, target_type.length - 1);
          support.pose(new XplusCeqZ(matchVars[i], index_min, match[i]));
        }
      }

      Class<?> c = Class.forName("org.jacop.graph." + cName);
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
          cons.newInstance(store, t, p, target_type, pattern_type, index_min, matchVars, true);
      support.pose((Constraint) constraint);

    } catch (ClassNotFoundException
        | InvocationTargetException
        | IllegalAccessException
        | InstantiationException
        | NoSuchMethodException _) {
      throw new RuntimeException(
          "% Constraint " + cName + " is not available in this version; requires org.jacop.graph.");
    }
  }

  void gen_jacop_sub_digraph_match(SimpleNode node) {
    int[] t = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    int[] p = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int[] target_type = support.getIntArray((SimpleNode) node.jjtGetChild(2));
    int[] pattern_type = support.getIntArray((SimpleNode) node.jjtGetChild(3));
    IntVar[] match = support.getVarArray((SimpleNode) node.jjtGetChild(4));
    int index_min = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(5));
    String cName = "SubGraphMatch";

    try {
      IntVar[] matchVars = null;
      if (index_min == 0) {
        for (int i = 0; i < match.length; i++) {
          matchVars = match;
        }
      } else {
        matchVars = new IntVar[match.length];
        for (int i = 0; i < match.length; i++) {
          matchVars[i] = new IntVar(store, "node_" + i, 0, target_type.length - 1);
          support.pose(new XplusCeqZ(matchVars[i], index_min, match[i]));
        }
      }

      Class<?> c = Class.forName("org.jacop.graph." + cName);
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
          cons.newInstance(store, t, p, target_type, pattern_type, index_min, matchVars, false);
      support.pose((Constraint) constraint);

    } catch (ClassNotFoundException
        | InvocationTargetException
        | IllegalAccessException
        | InstantiationException
        | NoSuchMethodException _) {
      throw new RuntimeException(
          "% Constraint " + cName + " is not available in this version; requires org.jacop.graph.");
    }
  }

  void gen_jacop_clique(SimpleNode node) {
    int[] g = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] c = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int index_min = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    String cName = "Clique";

    int[] type = new int[c.length];
    Arrays.fill(type, 1);

    IntVar cost = new IntVar(store, 0, IntDomain.MAX_INT);

    // // CliqueDecomposed ctr = new CliqueDecomposed(store, graph, cost);
    // // support.poseDc(ctr);

    // the same as pattern graph");

    try {
      Class<?> cls = Class.forName("org.jacop.graph." + cName);
      Constructor<?> cons =
          cls.getConstructor(
              Store.class, int[].class, int[].class, int.class, IntVar[].class, IntVar.class);
      Object constraint = cons.newInstance(store, g, type, index_min, c, cost);
      support.pose((Constraint) constraint);

    } catch (ClassNotFoundException
        | InvocationTargetException
        | IllegalAccessException
        | InstantiationException
        | NoSuchMethodException _) {
      throw new RuntimeException(
          "% Constraint " + cName + " is not available in this version; requires org.jacop.graph.");
    }
  }
}
