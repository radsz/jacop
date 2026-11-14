/*
 * TableVariableElimination.java
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Eliminates the variables that occur in exactly two extensional constraints (tables, short tables,
 * elements over constant arrays) and nowhere else, by joining the two relations and projecting the
 * variable out: bucket elimination (Dechter, "Bucket elimination: a unifying framework for
 * reasoning", Artificial Intelligence 113, 1999) restricted to the variables of degree two, as in
 * "Boosting search with variable elimination in constraint optimization and constraint satisfaction
 * problems" (Larrosa and Dechter, Constraints 8(3), 2003), and the extensional analogue of bounded
 * variable elimination in SAT (Een and Biere, "Effective preprocessing in SAT through variable and
 * clause elimination", SAT 2005), which is why the SAT encodings (sCOP with CaDiCaL or Kissat)
 * solve such models fast.
 *
 * <p>MiniZinc flattens a nested lookup such as {@code tab[x, inv[y]]} into a chain of elements and
 * tables through auxiliary variables, each of which links two constraints only (XCSP3 SEDF: four
 * auxiliary variables and five constraints for each difference). The chain is Berge-acyclic, so the
 * joined table propagates exactly as strongly as the chain, but in one propagator instead of five,
 * and under LCG its explanations name x and y instead of chains of auxiliary literals.
 *
 * <p>A variable is eliminated only when the joined relation has no more columns than the larger of
 * the two and at most {@code org.jacop.fz.tableElimination.rows} rows (default 10,000), or no more
 * than the two together. Variables of the solve item, aliases and variables of other constraints
 * are kept. The eliminated variables are given values again from the kept ones when a solution is
 * printed ({@link #values()}). Off for all-solution search (an eliminated variable can have more
 * than one value for the same kept values) and with {@code -Dorg.jacop.fz.tableElimination=false}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class TableVariableElimination implements ParserTreeConstants {

  static final int MAX_ROWS = Integer.getInteger("org.jacop.fz.tableElimination.rows", 10_000);

  private final Support support;

  private final Set<SimpleNode> frozenNodes;

  private final Set<IntVar> frozenVars;

  /** A relation: its scope, its rows, and the constraint nodes it stands for. */
  static final class Relation {
    final IntVar[] scope;
    final int[][] rows;
    final List<SimpleNode> sources;
    final boolean joined;
    boolean alive = true;

    Relation(IntVar[] scope, int[][] rows, List<SimpleNode> sources, boolean joined) {
      this.scope = scope;
      this.rows = rows;
      this.sources = sources;
      this.joined = joined;
    }

    int column(IntVar x) {
      for (int i = 0; i < scope.length; i++) {
        if (scope[i] == x) {
          return i;
        }
      }
      return -1;
    }
  }

  /** One elimination: the variable and the two relations it was in. */
  private record Step(IntVar variable, Relation first, Relation second) {}

  private final List<Relation> relations = new ArrayList<>();

  private final Map<IntVar, List<Relation>> byVar = new IdentityHashMap<>();

  private final Map<IntVar, Integer> occurrences = new IdentityHashMap<>();

  private final List<Step> steps = new ArrayList<>();

  private final Set<SimpleNode> replaced = new HashSet<>();

  private final List<Relation> posted = new ArrayList<>();

  private final Set<Var> eliminatedVars = new LinkedHashSet<>();

  /**
   * It creates the elimination.
   *
   * @param support the support of the FlatZinc front end.
   * @param frozenNodes constraint nodes that earlier detectors replaced or merged; their variables
   *     count as used elsewhere.
   * @param frozenVars variables that must stay, such as those of the solve item.
   */
  public TableVariableElimination(
      Support support, Set<SimpleNode> frozenNodes, Set<IntVar> frozenVars) {
    this.support = support;
    this.frozenNodes = frozenNodes;
    this.frozenVars = frozenVars;
  }

  /**
   * It tells if the elimination is on.
   *
   * @return false if the system property org.jacop.fz.tableElimination is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.tableElimination"));
  }

  /**
   * The constraint nodes that joined tables replaced; they are not posted.
   *
   * @return the replaced constraint nodes.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  /**
   * The eliminated variables, in the order of elimination.
   *
   * @return the eliminated variables.
   */
  public Set<Var> eliminated() {
    return Collections.unmodifiableSet(eliminatedVars);
  }

  /**
   * The joined tables to post instead of the replaced constraints, as scope and rows.
   *
   * @return the scopes and rows of the joined tables.
   */
  public List<Map.Entry<IntVar[], int[][]>> tables() {
    List<Map.Entry<IntVar[], int[][]>> t = new ArrayList<>(posted.size());
    for (Relation r : posted) {
      t.add(Map.entry(r.scope, r.rows));
    }
    return t;
  }

  /**
   * It scans the constraint items and eliminates what it can.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          support.checkTimeOut();
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            ASTConstElem c = (ASTConstElem) item;
            for (int k = 0; k < c.jjtGetNumChildren(); k++) {
              PartialCopyDetector.countVariables(
                  support, (SimpleNode) c.jjtGetChild(k), occurrences);
            }
            if (!frozenNodes.contains(c)) {
              Relation r = relation(c);
              if (r != null) {
                add(r);
              }
            }
          }
        }
      }
    }
    eliminate();
    for (Relation r : relations) {
      if (r.alive && r.joined) {
        posted.add(r);
      }
    }
    if (support.options.debug() && !steps.isEmpty()) {
      FzConsole.println(
          "% table variable elimination: "
              + steps.size()
              + " variables eliminated, "
              + replaced.size()
              + " constraints replaced by "
              + posted.size()
              + " tables");
    }
  }

  private void add(Relation r) {
    relations.add(r);
    for (IntVar x : r.scope) {
      byVar.computeIfAbsent(x, k -> new ArrayList<>(2)).add(r);
    }
  }

  private void eliminate() {
    ArrayDeque<IntVar> queue = new ArrayDeque<>();
    Set<IntVar> queued = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Relation r : relations) {
      for (IntVar x : r.scope) {
        if (queued.add(x)) {
          queue.add(x);
        }
      }
    }
    Set<IntVar> aliased = Collections.newSetFromMap(new IdentityHashMap<>());
    aliased.addAll(support.dictionary.aliasTable.keySet());
    aliased.addAll(support.dictionary.aliasTable.values());
    while (!queue.isEmpty()) {
      support.checkTimeOut();
      IntVar y = queue.poll();
      queued.remove(y);
      List<Relation> in = live(y);
      boolean candidate =
          in.size() == 2
              && occurrences.getOrDefault(y, 0) == 2
              && !y.singleton()
              && !frozenVars.contains(y)
              && !aliased.contains(y);
      Relation r = candidate ? join(in.get(0), in.get(1), y) : null;
      if (r == null) {
        continue;
      }
      in.get(0).alive = false;
      in.get(1).alive = false;
      steps.add(new Step(y, in.get(0), in.get(1)));
      eliminatedVars.add(y);
      replaced.addAll(r.sources);
      // a variable of both relations now occurs once in the joined one
      for (IntVar x : r.scope) {
        if (in.get(0).column(x) >= 0 && in.get(1).column(x) >= 0) {
          occurrences.merge(x, -1, Integer::sum);
        }
      }
      occurrences.put(y, 0);
      add(r);
      for (IntVar x : r.scope) {
        if (queued.add(x)) {
          queue.add(x);
        }
      }
    }
  }

  private List<Relation> live(IntVar y) {
    List<Relation> all = byVar.get(y);
    if (all == null) {
      return List.of();
    }
    all.removeIf(r -> !r.alive);
    return all;
  }

  /** The join of a and b with y projected out, or null if it is too large. */
  private Relation join(Relation a, Relation b, IntVar y) {
    int ya = a.column(y);
    int yb = b.column(y);
    List<IntVar> scope = new ArrayList<>();
    for (IntVar x : a.scope) {
      if (x != y) {
        scope.add(x);
      }
    }
    int[] fromB = new int[b.scope.length];
    for (int c = 0; c < b.scope.length; c++) {
      IntVar x = b.scope[c];
      if (x == y) {
        fromB[c] = -1;
      } else {
        int k = scope.indexOf(x);
        if (k < 0) {
          k = scope.size();
          scope.add(x);
        }
        fromB[c] = k;
      }
    }
    int n = scope.size();
    if (n == 0 || n > Math.max(a.scope.length, b.scope.length)) {
      return null;
    }
    long limit = Math.max(MAX_ROWS, (long) a.rows.length + b.rows.length);
    Map<Integer, List<int[]>> byValue = new HashMap<>();
    for (int[] row : b.rows) {
      byValue.computeIfAbsent(row[yb], k -> new ArrayList<>()).add(row);
    }
    Map<Row, int[]> out = new LinkedHashMap<>();
    int[] fromA = new int[a.scope.length];
    int next = 0;
    for (int c = 0; c < a.scope.length; c++) {
      fromA[c] = c == ya ? -1 : next++;
    }
    for (int[] ra : a.rows) {
      List<int[]> match = byValue.get(ra[ya]);
      if (match == null) {
        continue;
      }
      for (int[] rb : match) {
        int[] row = new int[n];
        boolean[] set = new boolean[n];
        for (int c = 0; c < ra.length; c++) {
          if (fromA[c] >= 0) {
            row[fromA[c]] = ra[c];
            set[fromA[c]] = true;
          }
        }
        boolean ok = true;
        for (int c = 0; c < rb.length && ok; c++) {
          int k = fromB[c];
          if (k >= 0) {
            if (set[k] && row[k] != rb[c]) {
              ok = false;
            }
            row[k] = rb[c];
            set[k] = true;
          }
        }
        if (ok) {
          out.putIfAbsent(new Row(row), row);
          if (out.size() > limit) {
            return null;
          }
        }
      }
    }
    List<SimpleNode> sources = new ArrayList<>(a.sources);
    sources.addAll(b.sources);
    return new Relation(
        scope.toArray(new IntVar[0]), out.values().toArray(new int[0][]), sources, true);
  }

  /** A row as a hash key. */
  private record Row(int[] values) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Row(int[] v) && Arrays.equals(values, v);
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

  // ---------------------------------------------------------------------------------------------
  // the relations of the constraints

  private Relation relation(ASTConstElem node) {
    return switch (node.getName()) {
      case "jacop_table_int" -> table(node);
      case "jacop_short_table_int" -> shortTable(node);
      case "array_int_element", "array_var_int_element" -> element(node, 1);
      case "jacop_array_var_int_element_nonshifted" ->
          element(node, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3)));
      default -> null;
    };
  }

  private Relation table(ASTConstElem node) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    if (!distinctUnfixed(v)) {
      return null;
    }
    int[] tbl = support.mergedTables.get(node);
    if (tbl == null) {
      tbl = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    }
    int n = v.length;
    List<int[]> rows = new ArrayList<>();
    Set<Row> seen = new HashSet<>();
    for (int r = 0; r < tbl.length / n; r++) {
      int[] row = Arrays.copyOfRange(tbl, r * n, r * n + n);
      if (fits(v, row) && seen.add(new Row(row))) {
        rows.add(row);
      }
    }
    return new Relation(v, rows.toArray(new int[0][]), List.of(node), false);
  }

  private Relation shortTable(ASTConstElem node) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    if (!distinctUnfixed(v)) {
      return null;
    }
    int[] tbl = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int star = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    int n = v.length;
    Set<Row> seen = new LinkedHashSet<>();
    for (int r = 0; r < tbl.length / n; r++) {
      int[] row = Arrays.copyOfRange(tbl, r * n, r * n + n);
      if (!expand(v, row, star, 0, seen)) {
        return null;
      }
    }
    int[][] rows = new int[seen.size()][];
    int k = 0;
    for (Row row : seen) {
      rows[k++] = row.values();
    }
    return new Relation(v, rows, List.of(node), false);
  }

  // adds the rows that the short row matches within the domains; false if they are too many
  private boolean expand(IntVar[] v, int[] row, int star, int column, Set<Row> rows) {
    if (column == row.length) {
      rows.add(new Row(row.clone()));
      return rows.size() <= MAX_ROWS;
    }
    if (row[column] != star) {
      return !v[column].domain.contains(row[column]) || expand(v, row, star, column + 1, rows);
    }
    for (ValueEnumeration e = v[column].domain.valueEnumeration(); e.hasMoreElements(); ) {
      row[column] = e.nextElement();
      boolean ok = expand(v, row, star, column + 1, rows);
      row[column] = star;
      if (!ok) {
        return false;
      }
    }
    return true;
  }

  private Relation element(ASTConstElem node, int first) {
    IntVar index = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar value = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (index == value || index.singleton() || value.singleton()) {
      return null;
    }
    IntVar[] vars = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int[] array = new int[vars.length];
    for (int k = 0; k < vars.length; k++) {
      if (!vars[k].singleton()) {
        return null;
      }
      array[k] = vars[k].value();
    }
    List<int[]> rows = new ArrayList<>();
    for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements(); ) {
      int i = e.nextElement();
      int k = i - first;
      if (k >= 0 && k < array.length && value.domain.contains(array[k])) {
        rows.add(new int[] {i, array[k]});
      }
    }
    return new Relation(
        new IntVar[] {index, value}, rows.toArray(new int[0][]), List.of(node), false);
  }

  private static boolean distinctUnfixed(IntVar[] v) {
    if (v.length < 2) {
      return false;
    }
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    for (IntVar x : v) {
      if (x.singleton() || !seen.add(x)) {
        return false;
      }
    }
    return true;
  }

  private static boolean fits(IntVar[] v, int[] row) {
    for (int c = 0; c < v.length; c++) {
      if (!v[c].domain.contains(row[c])) {
        return false;
      }
    }
    return true;
  }

  // ---------------------------------------------------------------------------------------------
  // the values of the eliminated variables

  /**
   * The values of the eliminated variables in the current solution, derived from the values of the
   * kept variables in the reverse order of elimination: each value is one that both relations of
   * its variable allow. A kept variable that is not fixed matches any value of its domain.
   *
   * @return the values, by variable; empty if nothing was eliminated.
   */
  public Map<Var, Integer> values() {
    Map<Var, Integer> values = new IdentityHashMap<>();
    for (int s = steps.size() - 1; s >= 0; s--) {
      Step step = steps.get(s);
      Set<Integer> fromFirst = candidates(step.first(), step.variable(), values);
      Integer chosen = null;
      for (int value : candidates(step.second(), step.variable(), values)) {
        if (fromFirst.contains(value) && (chosen == null || value < chosen)) {
          chosen = value;
        }
      }
      if (chosen == null) {
        // cannot happen for a solution of the joined relation; keep the smallest value
        chosen = step.variable().min();
      }
      values.put(step.variable(), chosen);
    }
    return values;
  }

  private static Set<Integer> candidates(Relation r, IntVar y, Map<Var, Integer> values) {
    Set<Integer> c = new HashSet<>();
    int yc = r.column(y);
    for (int[] row : r.rows) {
      boolean ok = true;
      for (int k = 0; k < row.length && ok; k++) {
        if (k != yc) {
          IntVar x = r.scope[k];
          Integer known = values.get(x);
          IntDomain d = x.dom();
          ok = known != null ? known == row[k] : d.contains(row[k]);
        }
      }
      if (ok) {
        c.add(row[yc]);
      }
    }
    return c;
  }
}
