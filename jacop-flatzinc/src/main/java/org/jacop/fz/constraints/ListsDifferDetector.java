/*
 * ListsDifferDetector.java
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
import org.jacop.constraints.AllDifferentLists;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It recognises short tables that say two lists of variables differ and posts them as {@link
 * AllDifferentLists}: one constraint over each group of lists that all differ pairwise, and one
 * over the two lists of each other pair.
 *
 * <p>The table over x[0..n-1] ++ y[0..n-1] says that the lists differ when each of its rows fixes
 * one position k to a pair of different values, x[k] = a and y[k] = b, all others being stars, and
 * for every k it holds every such pair (a, b) of the domains of x[k] and y[k]. XCSP3 models write
 * "rows i and j differ" this way: BinaryPuzzle of the XCSP 2023 competition (pycsp3 with {@code
 * different} over lists) posts one such table for each pair of rows and each pair of columns, 6,320
 * tables of 160 rows over 160 variables at size 80.
 *
 * <p>Propagation is the same as the tables' (both are unit propagation of the disjunctions of
 * disequalities, F. Boussemart, C. Lecoutre, G. Audemard and C. Piette, "XCSP3-core: A format for
 * representing constraint satisfaction/optimization problems", arXiv:2009.00514, 2020, section
 * 4.1.1), but {@link AllDifferentLists} checks a group of m lists by hashing the fixed ones, not by
 * m(m-1)/2 tables of 2n rows each. On by default; {@code -Dorg.jacop.fz.listsDiffer=false} turns it
 * off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ListsDifferDetector implements ParserTreeConstants {

  private final Support support;

  private final Set<SimpleNode> replaced = new HashSet<>();

  /**
   * It creates a detector reading variables and tables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public ListsDifferDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.listsDiffer is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.listsDiffer"));
  }

  /**
   * The tables posted as AllDifferentLists; they are not posted themselves.
   *
   * @return the constraint nodes of the replaced tables.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  /** A list of variables compared by identity. */
  private record VarList(IntVar[] vars) {
    @Override
    public boolean equals(Object o) {
      if (!(o instanceof VarList(IntVar[] v)) || v.length != vars.length) {
        return false;
      }
      for (int i = 0; i < vars.length; i++) {
        if (v[i] != vars[i]) {
          return false;
        }
      }
      return true;
    }

    @Override
    public int hashCode() {
      int h = 1;
      for (IntVar x : vars) {
        h = 31 * h + System.identityHashCode(x);
      }
      return h;
    }

    @Override
    public String toString() {
      return Arrays.toString(vars);
    }
  }

  /**
   * It scans the constraint items of the model, posts the lists-differ tables as AllDifferentLists
   * and records them as replaced.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    Map<VarList, Integer> ids = new LinkedHashMap<>();
    List<int[]> pairs = new ArrayList<>();
    List<SimpleNode> nodes = new ArrayList<>();
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM
              && "jacop_short_table_int".equals(((ASTConstElem) item).getName())) {
            IntVar[][] lists = listsDiffer(item);
            if (lists != null) {
              int a = ids.computeIfAbsent(new VarList(lists[0]), k -> ids.size());
              int b = ids.computeIfAbsent(new VarList(lists[1]), k -> ids.size());
              pairs.add(new int[] {Math.min(a, b), Math.max(a, b)});
              nodes.add(item);
            }
          }
        }
      }
    }
    if (pairs.isEmpty()) {
      return;
    }
    replaced.addAll(nodes);
    post(new ArrayList<>(ids.keySet()), pairs);
  }

  // the two lists x and y when the table says x != y, otherwise null
  private IntVar[][] listsDiffer(SimpleNode node) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int size = v.length;
    if (size < 2 || size % 2 != 0) {
      return null;
    }
    Map<IntVar, Boolean> distinct = new IdentityHashMap<>();
    for (IntVar x : v) {
      if (!x.singleton() && distinct.put(x, Boolean.TRUE) != null) {
        return null;
      }
    }
    int n = size / 2;
    int[] tbl = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int star = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    // the pairs (a, b) each position k allows, as a * 2^32 + b
    List<Set<Long>> allowed = new ArrayList<>(n);
    for (int k = 0; k < n; k++) {
      allowed.add(new HashSet<>());
    }
    for (int r = 0; r < tbl.length / size; r++) {
      int k = -1;
      int count = 0;
      for (int c = 0; c < size; c++) {
        if (tbl[r * size + c] != star) {
          count++;
          if (k < 0) {
            k = c;
          }
        }
      }
      if (count != 2 || k >= n || tbl[r * size + k + n] == star) {
        return null;
      }
      int a = tbl[r * size + k];
      int b = tbl[r * size + k + n];
      if (a == b) {
        return null;
      }
      allowed.get(k).add(((long) a << 32) ^ (b & 0xffffffffL));
    }
    for (int k = 0; k < n; k++) {
      Set<Long> rows = allowed.get(k);
      long sa = v[k].getSize();
      long sb = v[k + n].getSize();
      if (sa * sb - Math.min(sa, sb) > rows.size()) {
        // fewer rows than different pairs of values, some pair is missing
        return null;
      }
      for (var ia = v[k].domain.valueEnumeration(); ia.hasMoreElements(); ) {
        int a = ia.nextElement();
        for (var ib = v[k + n].domain.valueEnumeration(); ib.hasMoreElements(); ) {
          int b = ib.nextElement();
          if (a != b && !rows.contains(((long) a << 32) ^ (b & 0xffffffffL))) {
            return null;
          }
        }
      }
    }
    return new IntVar[][] {Arrays.copyOfRange(v, 0, n), Arrays.copyOfRange(v, n, size)};
  }

  // one AllDifferentLists per component whose lists all differ pairwise, one per pair otherwise
  private void post(List<VarList> lists, List<int[]> pairs) {
    int m = lists.size();
    int[] parent = new int[m];
    for (int i = 0; i < m; i++) {
      parent[i] = i;
    }
    Set<Long> edges = new HashSet<>();
    for (int[] p : pairs) {
      edges.add(((long) p[0] << 32) | p[1]);
      parent[find(parent, p[0])] = find(parent, p[1]);
    }
    Map<Integer, List<Integer>> components = new LinkedHashMap<>();
    for (int i = 0; i < m; i++) {
      components.computeIfAbsent(find(parent, i), k -> new ArrayList<>()).add(i);
    }
    Map<Integer, List<Long>> componentEdges = new LinkedHashMap<>();
    for (long e : edges) {
      componentEdges.computeIfAbsent(find(parent, (int) (e >>> 32)), k -> new ArrayList<>()).add(e);
    }
    int groups = 0;
    for (Map.Entry<Integer, List<Integer>> entry : components.entrySet()) {
      List<Integer> component = entry.getValue();
      List<Long> inComponent = componentEdges.getOrDefault(entry.getKey(), List.of());
      long size = component.size();
      if (inComponent.size() == size * (size - 1) / 2) {
        IntVar[][] x = new IntVar[component.size()][];
        for (int i = 0; i < x.length; i++) {
          x[i] = lists.get(component.get(i)).vars();
        }
        support.pose(new AllDifferentLists(x));
        groups++;
      } else {
        for (long e : inComponent) {
          IntVar[] a = lists.get((int) (e >>> 32)).vars();
          IntVar[] b = lists.get((int) e).vars();
          support.pose(new AllDifferentLists(new IntVar[][] {a, b}));
          groups++;
        }
      }
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% lists differ detector: "
              + replaced.size()
              + " tables over "
              + m
              + " lists posted as "
              + groups
              + " AllDifferentLists");
    }
  }

  private static int find(int[] parent, int i) {
    while (parent[i] != i) {
      parent[i] = parent[parent[i]];
      i = parent[i];
    }
    return i;
  }
}
