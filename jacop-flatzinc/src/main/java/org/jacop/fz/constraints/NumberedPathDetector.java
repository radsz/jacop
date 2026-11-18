/*
 * NumberedPathDetector.java
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
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Assignment;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * It recognises a Hamiltonian path written as a numbering and adds the successor model of the path
 * with a {@link Circuit}, as a redundant constraint.
 *
 * <p>The numbering model gives N cells the values 1..N (an all_different over N variables with
 * values in 1..N) and says, for each cell c, that c holds N or a neighbour d of c holds x[c] + 1:
 * {@code x[c] = N \/ among([x[d] = x[c] + 1 | d in nbr(c)], {1}) >= 1}. This is how the XCSP3
 * CalvinPuzzle models of the XCSP 2023 competition (pycsp3) number a tour of an n x n grid; their
 * table variants write the same as a short table over [x[c], x[d1], ..., x[dk]] with rows (v, *,
 * .., v + 1, .., *) and (N, *, .., *), which is recognised too. The numbering alone sees no
 * subtours: search finds the dead ends of a path only once it is nearly complete.
 *
 * <p>The added model has a successor variable s[c] in nbr(c) plus a node "end", and a node "start"
 * whose successor is the cell of value 1. Given the numbering, s[c] = d exactly when x[d] = x[c] +
 * 1, so the equivalences s[c] = d &lt;-&gt; (x[d] = x[c] + 1) (the model's own literals), s[c] =
 * end &lt;-&gt; x[c] = N and s[start] = d &lt;-&gt; x[d] = 1 hold in every solution, and the
 * successors form one circuit over the cells, start and end merged into one node. The Circuit
 * propagator (with its subtour reasoning, G. Pesant, M. Gendreau, J.-Y. Potvin and J.-M. Rousseau,
 * "An exact constraint logic programming algorithm for the traveling salesman problem with time
 * windows", Transportation Science 32(1), 1998) then prunes the arcs that would close a subtour.
 *
 * <p>On by default; {@code -Dorg.jacop.fz.numberedPath=false} turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class NumberedPathDetector {

  private final Support support;

  // the distance filter of the values by the cells of known values
  private static final boolean DISTANCES =
      !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.numberedPathDistances"));

  /** The model's literals b with b &lt;-&gt; x[p] - x[q] = 1, by b. */
  private final Map<IntVar, IntVar[]> successorLiterals = new IdentityHashMap<>();

  /** The model's literals b with b &lt;-&gt; x = w, by b. */
  private final Map<IntVar, Object[]> valueLiterals = new IdentityHashMap<>();

  /** The integer views of Booleans (bool2int), to the Boolean. */
  private final Map<IntVar, IntVar> boolOf = new IdentityHashMap<>();

  private final List<IntVar[]> alldiffs = new ArrayList<>();

  /** among(L, {1}, a): a to L. */
  private final Map<IntVar, IntVar[]> amongs = new IdentityHashMap<>();

  /** int_le_imp(1, a, r): r to a. */
  private final Map<IntVar, IntVar> atLeastOne = new IdentityHashMap<>();

  /** int_eq_imp(x, w, q): q to {x, w}. */
  private final Map<IntVar, Object[]> equalImplied = new IdentityHashMap<>();

  private final List<IntVar[]> binaryClauses = new ArrayList<>();

  /** Short tables: the scope, the tuples and the star value. */
  private final List<Object[]> shortTables = new ArrayList<>();

  private int paths;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public NumberedPathDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.numberedPath is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.numberedPath"));
  }

  /**
   * It scans the constraint items of the model and posts the successor model of each numbered path
   * it recognises. Nothing of the model is replaced.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    for (IntVar[] x : alldiffs) {
      tryPath(x);
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_alldiff" -> alldiffs.add(support.getVarArray((SimpleNode) node.jjtGetChild(0)));
      case "int_lin_eq_reif" -> {
        int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));
        if (!b.singleton()
            && a.length == 2
            && a[0] == -a[1]
            && Math.abs(a[0]) == 1
            && Math.abs(c) == 1) {
          // a0 * (x0 - x1) = c: x0 - x1 = 1 when a0 = c
          successorLiterals.put(
              b, a[0] == c ? new IntVar[] {x[0], x[1]} : new IntVar[] {x[1], x[0]});
        }
      }
      case "int_eq_reif" -> {
        IntVar x = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
        IntVar w = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
        IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
        if (b.singleton()) {
          return;
        }
        if (w.singleton() && !x.singleton()) {
          valueLiterals.put(b, new Object[] {x, w.value()});
        } else if (x.singleton() && !w.singleton()) {
          valueLiterals.put(b, new Object[] {w, x.value()});
        }
      }
      case "bool2int" -> {
        IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
        IntVar v = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
        boolOf.put(v, b);
      }
      case "jacop_among" -> {
        IntDomain values = support.getSetLiteral(node, 1);
        if (values.getSize() == 1 && values.min() == 1) {
          IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(0));
          amongs.put(support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2)), x);
        }
      }
      case "int_le_imp" -> {
        IntVar one = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
        if (one.singleton(1)) {
          atLeastOne.put(
              support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2)),
              support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1)));
        }
      }
      case "int_eq_imp" -> {
        IntVar x = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
        IntVar w = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
        if (w.singleton()) {
          equalImplied.put(
              support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2)),
              new Object[] {x, w.value()});
        }
      }
      case "bool_clause" -> {
        IntVar[] pos = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] neg = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        if (pos.length == 2 && neg.length == 0) {
          binaryClauses.add(pos);
        }
      }
      case "jacop_short_table_int" -> {
        IntVar[] scope = support.getVarArray((SimpleNode) node.jjtGetChild(0));
        int[] tuples = support.getIntArray((SimpleNode) node.jjtGetChild(1));
        int star = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        if (scope.length >= 2 && tuples.length % scope.length == 0) {
          shortTables.add(new Object[] {scope, tuples, star});
        }
      }
      default -> {
        // not part of the pattern
      }
    }
  }

  private IntVar bool(IntVar v) {
    return boolOf.getOrDefault(v, v);
  }

  private void tryPath(IntVar[] x) {
    int n = x.length;
    if (n < 4) {
      return;
    }
    Map<IntVar, Integer> cellOf = new IdentityHashMap<>();
    Map<Integer, Integer> fixedCell = new HashMap<>();
    for (int c = 0; c < n; c++) {
      if (x[c].min() < 1 || x[c].max() > n) {
        return;
      }
      if (x[c].singleton()) {
        fixedCell.put(x[c].value(), c);
      } else if (cellOf.put(x[c], c) != null) {
        return;
      }
    }
    // the rows: for each cell, its literals (x[d] = x[c] + 1) by neighbour d
    List<Map<Integer, IntVar>> rows = new ArrayList<>(n);
    for (int c = 0; c < n; c++) {
      rows.add(null);
    }
    for (IntVar[] clause : binaryClauses) {
      for (int k = 0; k < 2; k++) {
        Object[] eq = equalImplied.get(clause[1 - k]);
        IntVar a = atLeastOne.get(clause[k]);
        if (eq != null && a != null && (Integer) eq[1] == n) {
          Integer c = cellOf.get((IntVar) eq[0]);
          if (c != null) {
            addRow(rows, c, a, cellOf, fixedCell, x);
          }
        }
      }
    }
    // a fixed cell below N has its among at least 1 by the domain of the count
    for (Map.Entry<Integer, Integer> f : fixedCell.entrySet()) {
      if (f.getKey() != n) {
        for (Map.Entry<IntVar, IntVar[]> among : amongs.entrySet()) {
          if (among.getKey().min() >= 1 && rows.get(f.getValue()) == null) {
            addRow(rows, f.getValue(), among.getKey(), cellOf, fixedCell, x);
          }
        }
      }
    }
    for (Object[] table : shortTables) {
      addTableRow(
          rows, (IntVar[]) table[0], (int[]) table[1], (Integer) table[2], cellOf, fixedCell, n);
    }
    for (int c = 0; c < n; c++) {
      boolean last = x[c].singleton(n);
      if (rows.get(c) == null && !last) {
        return;
      }
    }
    post(x, rows);
  }

  /*
   * The row of cell c = scope[0] from a short table whose every tuple is (N, *, ..., *) or (v, *, ...,
   * v + 1, ..., *) with v + 1 at one position i: c holds N or a cell of the scope holds x[c] + 1.
   */
  private void addTableRow(
      List<Map<Integer, IntVar>> rows,
      IntVar[] scope,
      int[] tuples,
      int star,
      Map<IntVar, Integer> cellOf,
      Map<Integer, Integer> fixedCell,
      int n) {
    Integer c = cell(scope[0], cellOf, fixedCell);
    if (c == null || rows.get(c) != null || star >= 1 && star <= n + 1) {
      return;
    }
    int arity = scope.length;
    Map<Integer, IntVar> row = new LinkedHashMap<>();
    for (int t = 0; t < tuples.length; t += arity) {
      int v = tuples[t];
      if (v < 1 || v > n) {
        return;
      }
      int next = -1;
      for (int i = 1; i < arity; i++) {
        if (tuples[t + i] != star) {
          if (next != -1 || v == n || tuples[t + i] != v + 1) {
            return;
          }
          next = i;
        }
      }
      if (next == -1 && v != n) {
        return;
      }
      if (next != -1) {
        Integer d = cell(scope[next], cellOf, fixedCell);
        if (d == null || d.equals(c)) {
          return;
        }
        row.put(d, null);
      }
    }
    rows.set(c, row);
  }

  private static Integer cell(
      IntVar v, Map<IntVar, Integer> cellOf, Map<Integer, Integer> fixedCell) {
    return v.singleton() ? fixedCell.get(v.value()) : cellOf.get(v);
  }

  // the row of cell c from among(L, {1}, a) >= 1, when every literal of L is x[d] = x[c] + 1
  private void addRow(
      List<Map<Integer, IntVar>> rows,
      int c,
      IntVar a,
      Map<IntVar, Integer> cellOf,
      Map<Integer, Integer> fixedCell,
      IntVar[] x) {
    IntVar[] list = amongs.get(a);
    if (list == null || list.length == 0) {
      return;
    }
    Map<Integer, IntVar> row = new LinkedHashMap<>();
    for (IntVar v : list) {
      if (v.singleton(0)) {
        // an arc the compiler found impossible, such as one into the cell of value 1
        continue;
      }
      IntVar b = bool(v);
      Integer d = successorOf(b, c, cellOf, fixedCell, x);
      if (d == null || d == c || row.containsKey(d)) {
        return;
      }
      row.put(d, b);
    }
    rows.set(c, row);
  }

  // the cell d with b <-> x[d] = x[c] + 1, or null
  private Integer successorOf(
      IntVar b, int c, Map<IntVar, Integer> cellOf, Map<Integer, Integer> fixedCell, IntVar[] x) {
    IntVar[] s = successorLiterals.get(b);
    if (s != null) {
      Integer from = cellOf.get(s[1]);
      return from != null && from == c ? cellOf.get(s[0]) : null;
    }
    Object[] eq = valueLiterals.get(b);
    if (eq == null) {
      return null;
    }
    IntVar y = (IntVar) eq[0];
    int w = (Integer) eq[1];
    if (x[c].singleton()) {
      // x[y] = x[c] + 1 with x[c] fixed
      return w == x[c].value() + 1 ? cellOf.get(y) : null;
    }
    // x[c] = w, which is x[d] = x[c] + 1 for the fixed cell d of value w + 1
    return y == x[c] ? fixedCell.get(w + 1) : null;
  }

  private void post(IntVar[] x, List<Map<Integer, IntVar>> rows) {
    int n = x.length;
    var store = support.store;
    if (support.options.debug()) {
      FzConsole.println("% numbered path detector: circuit over " + n + " cells");
    }
    if (DISTANCES) {
      distanceFilter(x, rows);
    }
    // node n + 1 is start and end; values are 1-based
    IntVar[] s = new IntVar[n + 1];
    for (int c = 0; c < n; c++) {
      IntervalDomain dom = new IntervalDomain();
      Map<Integer, IntVar> row = rows.get(c);
      if (row != null) {
        for (int d : row.keySet()) {
          dom.unionAdapt(d + 1, d + 1);
        }
      }
      if (x[c].domain.contains(n)) {
        dom.unionAdapt(n + 1, n + 1);
      }
      s[c] = new IntVar(store, "path" + paths + "_s" + c, dom);
    }
    IntervalDomain firsts = new IntervalDomain();
    for (int c = 0; c < n; c++) {
      if (x[c].domain.contains(1)) {
        firsts.unionAdapt(c + 1, c + 1);
      }
    }
    s[n] = new IntVar(store, "path" + paths + "_start", firsts);
    for (int c = 0; c < n; c++) {
      Map<Integer, IntVar> row = rows.get(c);
      if (row != null) {
        for (Map.Entry<Integer, IntVar> e : row.entrySet()) {
          IntVar b = e.getValue();
          if (b == null) {
            // the model has no literal for x[d] = x[c] + 1 (table form)
            b = new BooleanVar(store, "path" + paths + "_arc" + c + "_" + e.getKey());
            support.pose(new Reified(new XplusCeqZ(x[c], 1, x[e.getKey()]), b));
          }
          support.pose(new Reified(new XeqC(s[c], e.getKey() + 1), b));
        }
      }
      if (x[c].domain.contains(n)) {
        BooleanVar last = new BooleanVar(store, "path" + paths + "_last" + c);
        support.pose(new Reified(new XeqC(s[c], n + 1), last));
        support.pose(new Reified(new XeqC(x[c], n), last));
      }
      if (x[c].domain.contains(1)) {
        BooleanVar first = new BooleanVar(store, "path" + paths + "_first" + c);
        support.pose(new Reified(new XeqC(s[n], c + 1), first));
        support.pose(new Reified(new XeqC(x[c], 1), first));
      }
    }
    support.pose(new Circuit(s));
    // the cell of each value, for the search that follows the path (Solve.pathSearch)
    IntVar[] position = new IntVar[n];
    for (int k = 0; k < n; k++) {
      position[k] = new IntVar(store, "path" + paths + "_cell" + (k + 1), 1, n);
    }
    support.delayedConstraints.add(new Assignment(x, position, 1, 1));
    support.dictionary.pathPositions.add(position);
    paths++;
  }

  /*
   * The values of a cell are bounded by its distances from the cells of known values: if x[g] = v
   * and the shortest path of neighbour steps from g to c has length f, then x[c] >= v + f or x[c] <
   * v, and if the one from c to g has length b, then x[c] <= v - b or x[c] > v (a path visits the
   * cells of values v, v + 1, ..., x[c] in neighbour steps). Hidato puzzles give many cells, and
   * the numbering model only finds such distances one step at a time in search. Repeated while it
   * fixes cells, together with the values that only one cell can hold.
   */
  private void distanceFilter(IntVar[] x, List<Map<Integer, IntVar>> rows) {
    int n = x.length;
    var store = support.store;
    int[][] out = new int[n][];
    int[] inDegree = new int[n];
    for (int c = 0; c < n; c++) {
      Map<Integer, IntVar> row = rows.get(c);
      out[c] =
          row == null ? new int[0] : row.keySet().stream().mapToInt(Integer::intValue).toArray();
      for (int d : out[c]) {
        inDegree[d]++;
      }
    }
    int[][] in = new int[n][];
    for (int d = 0; d < n; d++) {
      in[d] = new int[inDegree[d]];
      inDegree[d] = 0;
    }
    for (int c = 0; c < n; c++) {
      for (int d : out[c]) {
        in[d][inDegree[d]++] = c;
      }
    }
    boolean[] done = new boolean[n];
    long before = 0;
    for (IntVar v : x) {
      before += v.getSize();
    }
    boolean changed = true;
    while (changed) {
      changed = false;
      for (int g = 0; g < n; g++) {
        if (done[g] || !x[g].singleton()) {
          continue;
        }
        done[g] = true;
        int v = x[g].value();
        int[] forward = distances(out, g);
        int[] backward = distances(in, g);
        for (int c = 0; c < n; c++) {
          if (c == g || x[c].singleton()) {
            continue;
          }
          IntervalDomain allowed = new IntervalDomain();
          if (backward[c] > 0 && v - backward[c] >= 1) {
            allowed.unionAdapt(1, v - backward[c]);
          }
          if (forward[c] > 0 && v + forward[c] <= n) {
            allowed.unionAdapt(v + forward[c], n);
          }
          x[c].domain.in(store.level, x[c], allowed);
          changed |= x[c].singleton();
        }
      }
      // a value that one cell alone can hold
      int[] holder = new int[n + 1];
      java.util.Arrays.fill(holder, -1);
      for (int c = 0; c < n; c++) {
        IntDomain d = x[c].dom();
        for (var e = d.valueEnumeration(); e.hasMoreElements(); ) {
          int k = e.nextElement();
          holder[k] = holder[k] == -1 ? c : -2;
        }
      }
      for (int k = 1; k <= n; k++) {
        if (holder[k] >= 0 && !x[holder[k]].singleton()) {
          x[holder[k]].domain.in(store.level, x[holder[k]], k, k);
          changed = true;
        }
      }
    }
    long after = 0;
    for (IntVar v : x) {
      after += v.getSize();
    }
    if (support.options.debug()) {
      FzConsole.println("% numbered path distances: " + (before - after) + " values removed");
    }
  }

  // breadth-first numbers of steps from a cell, 0 for the cell and -1 when unreachable
  private static int[] distances(int[][] arcs, int from) {
    int[] dist = new int[arcs.length];
    java.util.Arrays.fill(dist, -1);
    int[] queue = new int[arcs.length];
    int head = 0;
    int tail = 0;
    dist[from] = 0;
    queue[tail++] = from;
    while (head < tail) {
      int c = queue[head++];
      for (int d : arcs[c]) {
        if (dist[d] < 0) {
          dist[d] = dist[c] + 1;
          queue[tail++] = d;
        }
      }
    }
    return dist;
  }
}
