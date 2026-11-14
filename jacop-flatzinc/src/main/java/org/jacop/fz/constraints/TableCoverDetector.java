/*
 * TableCoverDetector.java
 * <p>
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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.TableCover;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * It finds tilings written as tables and an all different: an all different whose variables are
 * split, all of them, into the variable lists of tables without a variable in two tables (a group,
 * e.g. the cells of a piece, each with its table of placements), and posts a redundant {@link
 * TableCover} over the groups. The cover is exact when the variables take all values of their
 * domains, as many variables as values.
 *
 * <p>It is on without LCG and off with it: on XCSP3 Pentominoes at 240 s the cover takes plain
 * search ({@code --lcg off}) from 6 to 14 of 14 instances, but under LCG its reasons cost more than
 * its pruning saves on half of them. {@code -Dorg.jacop.fz.tableCover=true} or {@code =false} turns
 * it on or off in both modes.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class TableCoverDetector {

  static final int MIN_GROUPS = Integer.getInteger("org.jacop.fz.tableCoverGroups", 3);

  static final int MAX_TUPLES = Integer.getInteger("org.jacop.fz.tableCoverTuples", 200_000);

  private final Support support;

  private final List<IntVar[]> alldiffs = new ArrayList<>();
  private final List<IntVar[]> tableVars = new ArrayList<>();
  private final List<SimpleNode> tableNodes = new ArrayList<>();

  /** Statistics: the covers posted. */
  int covers;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public TableCoverDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on: by default without LCG only.
   *
   * @param lcg true if the model is solved with lazy clause generation.
   * @return the system property org.jacop.fz.tableCover if it is set, otherwise !lcg.
   */
  public static boolean enabled(boolean lcg) {
    String p = System.getProperty("org.jacop.fz.tableCover");
    if (p == null) {
      return !lcg;
    }
    return Boolean.parseBoolean(p);
  }

  /**
   * It reads the all different and table constraints of the model and posts the covers.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    if (alldiffs.isEmpty() || tableVars.size() < MIN_GROUPS) {
      return;
    }
    // the table of every variable that is in exactly one table
    Map<IntVar, Integer> tableOf = new IdentityHashMap<>();
    Map<IntVar, Boolean> twice = new IdentityHashMap<>();
    for (int t = 0; t < tableVars.size(); t++) {
      Map<IntVar, Boolean> local = new IdentityHashMap<>();
      for (IntVar v : tableVars.get(t)) {
        if (local.put(v, Boolean.TRUE) != null || tableOf.put(v, t) != null) {
          twice.put(v, Boolean.TRUE);
        }
      }
    }
    for (IntVar[] all : alldiffs) {
      post(all, tableOf, twice);
    }
    if (support.options.debug() && covers > 0) {
      FzConsole.println("% TableCover: " + covers + " covers");
    }
  }

  private void post(IntVar[] all, Map<IntVar, Integer> tableOf, Map<IntVar, Boolean> twice) {
    List<Integer> tables = new ArrayList<>();
    Map<Integer, Integer> seen = new java.util.HashMap<>();
    for (IntVar v : all) {
      Integer t = tableOf.get(v);
      if (t == null || twice.containsKey(v)) {
        return;
      }
      if (seen.merge(t, 1, Integer::sum) == 1) {
        tables.add(t);
      }
    }
    // every variable of the tables is in the all different
    for (int t : tables) {
      if (seen.get(t) != tableVars.get(t).length) {
        return;
      }
    }
    if (tables.size() < MIN_GROUPS) {
      return;
    }
    IntVar[][] groups = new IntVar[tables.size()][];
    int[][][] tuples = new int[tables.size()][][];
    long size = 0;
    for (int g = 0; g < tables.size(); g++) {
      int t = tables.get(g);
      groups[g] = tableVars.get(t);
      int k = groups[g].length;
      int[] flat = support.getIntArray((SimpleNode) tableNodes.get(t).jjtGetChild(1));
      if (flat == null || k == 0 || flat.length % k != 0) {
        return;
      }
      tuples[g] = new int[flat.length / k][k];
      for (int r = 0; r < flat.length / k; r++) {
        System.arraycopy(flat, r * k, tuples[g][r], 0, k);
      }
      size += tuples[g].length;
    }
    if (size > MAX_TUPLES) {
      return;
    }
    IntDomain union = all[0].domain.cloneLight();
    for (IntVar v : all) {
      union = union.union(v.domain);
    }
    boolean exact = union.getSize() == all.length;
    support.implied(() -> support.pose(new TableCover(groups, tuples, exact)));
    covers++;
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_alldiff", "jacop_alldistinct" -> {
        if (node.jjtGetNumChildren() >= 1) {
          IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
          if (v != null && v.length > 0) {
            alldiffs.add(v);
          }
        }
      }
      case "jacop_table_int" -> {
        if (node.jjtGetNumChildren() == 2) {
          IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
          if (v != null && v.length > 1) {
            tableVars.add(v);
            tableNodes.add(node);
          }
        }
      }
      default -> {
        // not a part of a tiling
      }
    }
  }
}
