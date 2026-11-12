/*
 * TableScopeMerger.java
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
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It intersects the positive tables posted over the same set of variables: the first of them gets
 * the rows that every table of the set allows (in its own column order) and the others are not
 * posted. Exact, and the merged table propagates at least as strongly as the tables apart. On by
 * default with {@link TableReformulation}; {@code -Dorg.jacop.fz.tableReformulation=false} turns
 * both off. Groups of more than {@code org.jacop.fz.tableMerge.rows} (2 * 10^6) rows in all are
 * left as they are.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class TableScopeMerger implements ParserTreeConstants {

  static final long MAX_ROWS = Long.getLong("org.jacop.fz.tableMerge.rows", 2_000_000L);

  private final Support support;

  private final Set<SimpleNode> replaced = new HashSet<>();

  /**
   * It creates a merger reading variables and tables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public TableScopeMerger(Support support) {
    this.support = support;
  }

  /**
   * It tells if the merging is on.
   *
   * @return false if the system property org.jacop.fz.tableReformulation is false.
   */
  public static boolean enabled() {
    return TableReformulation.enabled();
  }

  /**
   * The tables merged into another one; they are not posted.
   *
   * @return the constraint nodes of the merged tables.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  private record Table(SimpleNode node, IntVar[] vars) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Table(SimpleNode n, IntVar[] v) && node == n && Arrays.equals(vars, v);
    }

    @Override
    public int hashCode() {
      return 31 * System.identityHashCode(node) + Arrays.hashCode(vars);
    }

    @Override
    public String toString() {
      return "Table[node=" + node + ", vars=" + Arrays.toString(vars) + "]";
    }
  }

  /**
   * It scans the constraint items of the model and merges the tables over the same variables.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    Map<List<Integer>, List<Table>> groups = new LinkedHashMap<>();
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            collect((ASTConstElem) item, groups);
          }
        }
      }
    }
    int merged = 0;
    for (List<Table> group : groups.values()) {
      if (group.size() >= 2 && merge(group)) {
        merged++;
      }
    }
    if (support.options.debug() && merged > 0) {
      FzConsole.println(
          "% table scope merger: " + replaced.size() + " tables merged into " + merged);
    }
  }

  private void collect(ASTConstElem node, Map<List<Integer>, List<Table>> groups) {
    String name = node.getName();
    if (!"jacop_table_int".equals(name) && !"jacop_table_bool".equals(name)) {
      return;
    }
    IntVar[] vars = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    if (vars.length < 2) {
      return;
    }
    Map<IntVar, Boolean> distinct = new IdentityHashMap<>();
    List<Integer> key = new ArrayList<>(vars.length);
    for (IntVar x : vars) {
      if (x.singleton() || distinct.put(x, Boolean.TRUE) != null || x.index() < 0) {
        return;
      }
      key.add(x.index());
    }
    key.sort(null);
    groups.computeIfAbsent(key, k -> new ArrayList<>()).add(new Table(node, vars));
  }

  private boolean merge(List<Table> group) {
    long rows = 0;
    int[][] tables = new int[group.size()][];
    for (int g = 0; g < group.size(); g++) {
      tables[g] = support.getIntArray((SimpleNode) group.get(g).node().jjtGetChild(1));
      rows += tables[g].length / group.get(g).vars().length;
    }
    if (rows > MAX_ROWS) {
      return false;
    }
    IntVar[] base = group.get(0).vars();
    int n = base.length;
    Map<IntVar, Integer> position = new IdentityHashMap<>();
    for (int c = 0; c < n; c++) {
      position.put(base[c], c);
    }
    Set<List<Integer>> allowed = new HashSet<>();
    List<int[]> first = new ArrayList<>();
    for (int r = 0; r < tables[0].length / n; r++) {
      int[] row = Arrays.copyOfRange(tables[0], r * n, r * n + n);
      if (allowed.add(asList(row))) {
        first.add(row);
      }
    }
    for (int g = 1; g < group.size(); g++) {
      IntVar[] vars = group.get(g).vars();
      int[] to = new int[n];
      for (int c = 0; c < n; c++) {
        to[c] = position.get(vars[c]);
      }
      Set<List<Integer>> next = new HashSet<>();
      for (int r = 0; r < tables[g].length / n; r++) {
        int[] row = new int[n];
        for (int c = 0; c < n; c++) {
          row[to[c]] = tables[g][r * n + c];
        }
        List<Integer> key = asList(row);
        if (allowed.contains(key)) {
          next.add(key);
        }
      }
      allowed = next;
    }
    int[] flat = new int[allowed.size() * n];
    int k = 0;
    for (int[] row : first) {
      if (allowed.contains(asList(row))) {
        System.arraycopy(row, 0, flat, k, n);
        k += n;
      }
    }
    support.mergedTables.put(group.get(0).node(), flat);
    for (int g = 1; g < group.size(); g++) {
      replaced.add(group.get(g).node());
    }
    return true;
  }

  private static List<Integer> asList(int[] row) {
    return Arrays.stream(row).boxed().toList();
  }
}
