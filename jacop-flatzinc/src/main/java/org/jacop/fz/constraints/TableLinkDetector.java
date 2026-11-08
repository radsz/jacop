/*
 * TableLinkDetector.java
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.table.HybridTable;
import org.jacop.constraints.table.TableLink;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Pairwise consistency between positive tables that share two or more variables, maintained inside
 * {@link HybridTable} through a {@link TableLink} per shared set, as in eSTR (C. Lecoutre, A.
 * Paparrizou, K. Stergiou, "Extending STR to a Higher-Order Consistency", AAAI 2013).
 *
 * <p>Generalized arc consistency on each table alone misses what two tables over a common set S of
 * variables know together: a row of one table whose values on S appear in no valid row of the other
 * is dead, although each of its values may have support elsewhere. Pairwise consistency removes
 * such rows (P. Janssen, P. Jégou, B. Nouguier, M.-C. Vilarem, "A filtering process for general
 * constraint satisfaction problems: achieving pairwise-consistency using an associated binary
 * representation", IEEE Workshop on Tools for Artificial Intelligence 1989). Each table numbers its
 * rows by their sub-tuple on S, and the link keeps the sub-tuples that every table over S still
 * supports.
 *
 * <p>The system property {@code org.jacop.fz.tableLinks=true} turns it on; it is off by default and
 * under lazy clause generation, whose table explanations do not know the links. {@code
 * org.jacop.fz.tableLinks.maxDegree} (default 32) skips variables that are in more tables when it
 * looks for shared sets and {@code .maxLinks} (default 8) bounds the links of one table.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class TableLinkDetector implements ParserTreeConstants {

  private static final int MAX_DEGREE = Integer.getInteger("org.jacop.fz.tableLinks.maxDegree", 32);

  private final int maxLinks = Integer.getInteger("org.jacop.fz.tableLinks.maxLinks", 8);

  private final Support support;

  private int linkCount;

  private int linkedCount;

  private long removedRows;

  /** One table: distinct non-fixed variables and the rows allowed by the domains. */
  private static final class Tab {
    final ASTConstElem node;
    final IntVar[] vars;
    final int[][] rows;
    final Map<IntVar, Integer> position = new IdentityHashMap<>();
    final List<Shared> shared = new ArrayList<>();

    Tab(ASTConstElem node, IntVar[] vars, int[][] rows) {
      this.node = node;
      this.vars = vars;
      this.rows = rows;
      for (int i = 0; i < vars.length; i++) {
        position.put(vars[i], i);
      }
    }
  }

  /** A set of variables shared by tables. */
  private static final class Shared {
    final IntVar[] vars;
    final List<Tab> tables = new ArrayList<>();

    Shared(IntVar[] vars) {
      this.vars = vars;
    }
  }

  /** A sub-tuple, compared by value. */
  private record Key(int[] values) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Key k && Arrays.equals(values, k.values);
    }

    @Override
    public int hashCode() {
      return Arrays.hashCode(values);
    }

    @Override
    public String toString() {
      return Arrays.toString(values);
    }
  }

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public TableLinkDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @param lcg true under lazy clause generation.
   * @return true if the system property org.jacop.fz.tableLinks is true and lcg is false.
   */
  public static boolean enabled(boolean lcg) {
    return !lcg && Boolean.getBoolean("org.jacop.fz.tableLinks");
  }

  /**
   * It scans the positive tables of the model and makes linked tables for those that share at least
   * two variables with another one; each is posted in place of its constraint node.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    List<Tab> tabs = new ArrayList<>();
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            Tab t = read((ASTConstElem) item);
            if (t != null) {
              tabs.add(t);
            }
          }
        }
      }
    }
    if (tabs.size() < 2) {
      return;
    }
    findSharedSets(tabs, occurrences(tabs));
    post(tabs);
    if (support.options.debug()) {
      FzConsole.println(
          "% table links: "
              + linkCount
              + " links, "
              + linkedCount
              + " tables linked, "
              + removedRows
              + " rows without a common sub-tuple");
    }
  }

  /** The table of a jacop_table_int or jacop_table_bool node, or null. */
  private Tab read(ASTConstElem node) {
    String name = node.getName();
    if (!("jacop_table_int".equals(name) || "jacop_table_bool".equals(name))
        || node.jjtGetNumChildren() != 2) {
      return null;
    }
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] tbl = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int size = v.length;
    if (size < 2 || tbl.length % size != 0) {
      return null;
    }
    Map<IntVar, Integer> position = new LinkedHashMap<>();
    for (IntVar x : v) {
      if (!x.singleton()) {
        position.putIfAbsent(x, position.size());
      }
    }
    if (position.size() < 2) {
      return null;
    }
    IntVar[] nv = position.keySet().toArray(new IntVar[0]);
    Set<Key> seen = new HashSet<>();
    List<int[]> kept = new ArrayList<>();
    for (int r = 0; r < tbl.length / size; r++) {
      int[] row = new int[nv.length];
      boolean[] set = new boolean[nv.length];
      boolean possible = true;
      for (int j = 0; j < size && possible; j++) {
        int value = tbl[size * r + j];
        if (!v[j].domain.contains(value)) {
          possible = false;
        } else if (!v[j].singleton()) {
          int k = position.get(v[j]);
          if (set[k] && row[k] != value) {
            possible = false;
          }
          row[k] = value;
          set[k] = true;
        }
      }
      if (possible && seen.add(new Key(row))) {
        kept.add(row);
      }
    }
    if (kept.isEmpty()) {
      // the table fails; posting it the usual way says so
      return null;
    }
    return new Tab(node, nv, kept.toArray(new int[0][]));
  }

  private static Map<IntVar, List<Tab>> occurrences(List<Tab> tabs) {
    Map<IntVar, List<Tab>> occ = new IdentityHashMap<>();
    for (Tab t : tabs) {
      for (IntVar x : t.vars) {
        occ.computeIfAbsent(x, k -> new ArrayList<>()).add(t);
      }
    }
    return occ;
  }

  /** One shared set per distinct set S of at least two variables common to two tables. */
  private void findSharedSets(List<Tab> tabs, Map<IntVar, List<Tab>> occ) {
    Map<Tab, Integer> index = new IdentityHashMap<>();
    for (int i = 0; i < tabs.size(); i++) {
      index.put(tabs.get(i), i);
    }
    Map<Key, Shared> byScope = new HashMap<>();
    Map<IntVar, Integer> varId = new IdentityHashMap<>();
    for (IntVar x : occ.keySet()) {
      varId.put(x, varId.size());
    }
    for (Tab a : tabs) {
      // the tables after a that share a variable with it, and how many
      Map<Tab, Integer> common = new LinkedHashMap<>();
      for (IntVar x : a.vars) {
        List<Tab> l = occ.get(x);
        if (l.size() > MAX_DEGREE) {
          continue;
        }
        for (Tab b : l) {
          if (index.get(b) > index.get(a)) {
            common.merge(b, 1, Integer::sum);
          }
        }
      }
      for (Map.Entry<Tab, Integer> e : common.entrySet()) {
        if (e.getValue() < 2) {
          continue;
        }
        Tab b = e.getKey();
        List<IntVar> s = new ArrayList<>();
        for (IntVar x : a.vars) {
          if (b.position.containsKey(x) && occ.get(x).size() <= MAX_DEGREE) {
            s.add(x);
          }
        }
        s.sort((x, y) -> Integer.compare(varId.get(x), varId.get(y)));
        int[] ids = new int[s.size()];
        for (int i = 0; i < ids.length; i++) {
          ids[i] = varId.get(s.get(i));
        }
        Key key = new Key(ids);
        Shared f = byScope.get(key);
        boolean hasA = f != null && f.tables.contains(a);
        boolean hasB = f != null && f.tables.contains(b);
        if ((!hasA && a.shared.size() >= maxLinks) || (!hasB && b.shared.size() >= maxLinks)) {
          continue;
        }
        if (f == null) {
          f = new Shared(s.toArray(new IntVar[0]));
          byScope.put(key, f);
        }
        if (!hasA) {
          f.tables.add(a);
          a.shared.add(f);
        }
        if (!hasB) {
          f.tables.add(b);
          b.shared.add(f);
        }
      }
    }
  }

  private static int[] project(int[] row, int[] pos) {
    int[] p = new int[pos.length];
    for (int i = 0; i < pos.length; i++) {
      p[i] = row[pos[i]];
    }
    return p;
  }

  private void post(List<Tab> tabs) {
    Map<Tab, HybridTable> tables = new IdentityHashMap<>();
    for (Tab t : tabs) {
      if (!t.shared.isEmpty()) {
        tables.put(t, new HybridTable(t.vars, t.rows));
      }
    }
    Set<Shared> done = new HashSet<>();
    for (Tab t : tabs) {
      for (Shared f : t.shared) {
        if (done.add(f)) {
          link(f, tables);
        }
      }
    }
    Map<SimpleNode, HybridTable> linked = new IdentityHashMap<>();
    for (Tab t : tabs) {
      HybridTable table = tables.get(t);
      if (table != null) {
        linked.put(t.node, table);
      }
    }
    support.linkedTables = linked;
    linkedCount = linked.size();
  }

  /** The sub-tuples on the shared set, numbered over all its tables, become the keys of a link. */
  private void link(Shared f, Map<Tab, HybridTable> tables) {
    Map<Key, Integer> id = new HashMap<>();
    int[][] keys = new int[f.tables.size()][];
    Map<Key, Integer> tablesWith = new HashMap<>();
    for (int t = 0; t < f.tables.size(); t++) {
      Tab tab = f.tables.get(t);
      int[] pos = new int[f.vars.length];
      for (int i = 0; i < f.vars.length; i++) {
        pos[i] = tab.position.get(f.vars[i]);
      }
      keys[t] = new int[tab.rows.length];
      Set<Key> here = new HashSet<>();
      for (int r = 0; r < tab.rows.length; r++) {
        Key k = new Key(project(tab.rows[r], pos));
        keys[t][r] = id.computeIfAbsent(k, any -> id.size());
        if (here.add(k)) {
          tablesWith.merge(k, 1, Integer::sum);
        }
      }
    }
    int all = f.tables.size();
    for (int t = 0; t < all; t++) {
      Tab tab = f.tables.get(t);
      int[] pos = new int[f.vars.length];
      for (int i = 0; i < f.vars.length; i++) {
        pos[i] = tab.position.get(f.vars[i]);
      }
      for (int[] row : tab.rows) {
        if (tablesWith.get(new Key(project(row, pos))) < all) {
          removedRows++;
        }
      }
    }
    TableLink link = new TableLink(id.size());
    for (int t = 0; t < all; t++) {
      tables.get(f.tables.get(t)).link(link, keys[t]);
    }
    linkCount++;
  }
}
