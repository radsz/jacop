/*
 * MinOfSumsDetector.java
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
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.MinOfSums;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It merges sums into the minimum that is their only use: z = x + y (int_lin_eq [1, 1, -1]) and m =
 * min(..., z, ...) (jacop_minimum, int_min) become one {@link MinOfSums} without z, when z occurs
 * in no other constraint, in no annotation of the solve item, is not output and its domain holds
 * every value of x + y. Shortest-path models such as road-cons have one such sum for every pair of
 * edges, so the merge removes most of their variables and constraints.
 *
 * <p>Setting the system property {@code org.jacop.fz.minOfSums} to false turns the merging off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class MinOfSumsDetector implements ParserTreeConstants {

  private final Support support;

  // z = x + y, by z
  private record Sum(IntVar x, IntVar y, SimpleNode node) {}

  private final Map<IntVar, Sum> sums = new IdentityHashMap<>();

  private final Map<IntVar, Integer> occurrences = new IdentityHashMap<>();

  private final List<ASTConstElem> minimums = new ArrayList<>();

  private final Set<Var> removed = new HashSet<>();

  private int merged;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public MinOfSumsDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the merging is on.
   *
   * @return false if the system property org.jacop.fz.minOfSums is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.minOfSums"));
  }

  /**
   * It posts a {@link MinOfSums} for each minimum with merged sums.
   *
   * @param astTree the root of the parsed model.
   * @return the minimum and sum constraint nodes it replaces, which must not be posted.
   */
  public Set<SimpleNode> detect(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
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

    Set<SimpleNode> skipped = new HashSet<>();
    if (sums.isEmpty()) {
      return skipped;
    }
    Set<IntVar> aliased = new HashSet<>(support.dictionary.aliasTable.keySet());
    aliased.addAll(support.dictionary.aliasTable.values());
    for (ASTConstElem node : minimums) {
      IntVar m;
      IntVar[] list;
      if (node.getName().equals("int_min")) {
        list = new IntVar[] {var(node, 0), var(node, 1)};
        m = var(node, 2);
      } else {
        m = var(node, 0);
        list = support.getVarArray(child(node, 1));
      }
      IntVar[] x = new IntVar[list.length];
      IntVar[] y = new IntVar[list.length];
      List<SimpleNode> parts = new ArrayList<>();
      Set<IntVar> seen = new HashSet<>();
      for (int i = 0; i < list.length; i++) {
        IntVar z = list[i];
        Sum s = seen.add(z) ? sums.get(z) : null;
        if (s != null
            && occurrences.getOrDefault(z, 0) == 2
            && !aliased.contains(z)
            && !support.dictionary.isOutput(z)
            && s.x() != m
            && s.y() != m
            && (long) z.min() <= (long) s.x().min() + s.y().min()
            && (long) z.max() >= (long) s.x().max() + s.y().max()) {
          x[i] = s.x();
          y[i] = s.y();
          parts.add(s.node());
          removed.add(z);
        } else {
          x[i] = z;
        }
      }
      if (parts.isEmpty() || seen.contains(m)) {
        for (int i = 0; i < list.length; i++) {
          removed.remove(list[i]);
        }
        continue;
      }
      support.pose(new MinOfSums(x, y, m));
      skipped.add(node);
      skipped.addAll(parts);
      merged += parts.size();
    }
    if (support.options.debug()) {
      FzConsole.println("% sums merged into minimums: " + merged);
    }
    return skipped;
  }

  /**
   * It returns the sum variables the merge left without constraints.
   *
   * @return the removed variables.
   */
  public Set<Var> removed() {
    return removed;
  }

  private void collect(ASTConstElem node) {
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      count((SimpleNode) node.jjtGetChild(i));
    }
    switch (node.getName()) {
      case "int_lin_eq" -> sum(node);
      case "jacop_minimum", "int_min" -> minimums.add(node);
      default -> {
        // neither a sum nor a minimum
      }
    }
  }

  // z = x + y written as [1, 1, -1] * [x, y, z] = 0, in any order of the terms
  private void sum(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] v = support.getVarArray(child(node, 1));
    if (a.length != 3 || support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)) != 0) {
      return;
    }
    int k = -1;
    for (int i = 0; i < 3; i++) {
      if (a[i] == -1 && k == -1) {
        k = i;
      } else if (a[i] != 1) {
        return;
      }
    }
    if (k == -1) {
      return;
    }
    IntVar z = v[k];
    IntVar p = v[(k + 1) % 3];
    IntVar q = v[(k + 2) % 3];
    if (z == p || z == q || p == q || z.singleton()) {
      return;
    }
    if (sums.containsKey(z)) {
      // two definitions; neither is merged
      sums.put(z, new Sum(p, q, null));
      occurrences.merge(z, 2, Integer::sum);
      return;
    }
    sums.put(z, new Sum(p, q, node));
  }

  private IntVar var(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private void countAll(SimpleNode node) {
    count(node);
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      countAll((SimpleNode) node.jjtGetChild(i));
    }
  }

  /** It counts the variables of an argument, array elements included. */
  private void count(SimpleNode arg) {
    if (arg.getId() == JJTARRAYLITERAL) {
      for (int i = 0; i < arg.jjtGetNumChildren(); i++) {
        count((SimpleNode) arg.jjtGetChild(i));
      }
      return;
    }
    if (arg.getId() != JJTSCALARFLATEXPR) {
      return;
    }
    ASTScalarFlatExpr e = (ASTScalarFlatExpr) arg;
    if (e.getType() == 2) {
      IntVar[] array = support.dictionary.getVariableArray(e.getIdent());
      if (array != null) {
        for (IntVar v : array) {
          occurrences.merge(v, 1, Integer::sum);
        }
        return;
      }
      IntVar v = support.dictionary.getVariable(e.getIdent());
      if (v != null) {
        occurrences.merge(v, 1, Integer::sum);
      }
    } else if (e.getType() == 3 && support.dictionary.getVariableArray(e.getIdent()) != null) {
      // an element of an array of variables; other arrays hold parameters
      occurrences.merge(support.getVariable(e), 1, Integer::sum);
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }
}
