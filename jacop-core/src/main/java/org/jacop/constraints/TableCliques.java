/*
 * TableCliques.java
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

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.lp.LpColumn;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.LinearForm;

/**
 * At-most-one rows of the linear relaxation from tables (CP-SAT's table expansion with {@code
 * TransformIntoMaxCliques}). Each variable of a table with a small domain gets a 0/1 column {@code
 * b_v = [x = v]} for every value: the Boolean the model already has ({@link ChannelReif}, {@link
 * Reified} {@link XeqC}), or an {@link LpColumn} of the relaxation, which is not a variable of the
 * store, with {@code sum b_v = 1} and {@code x = sum v b_v}. A pair of values {@code (a, b)} that
 * no tuple of a table allows for two of its variables {@code (x, y)} is a conflict {@code b_{x,a} +
 * b_{y,b} <= 1}; a table over more than two variables gives the conflicts of its projection on each
 * pair. Together with the values of one variable, which conflict pairwise, the conflicts are the
 * edges of a graph on the columns. Each edge not yet in a row is extended greedily to a maximal
 * clique of that graph, and the clique is a row {@code sum b <= 1}, unless it holds the values of
 * one variable only, which its encoding already bounds.
 *
 * <p>The rows hold for every solution with the columns at the indicators of its values, and the
 * cliques make the relaxation much stronger than the conflicts on their own: on the spot5 instances
 * of the MiniZinc Challenge, a weighted sum of Booleans over binary tables, the relaxation of the
 * cliques is within 4 to 7 % of the optimum, that of the conflicts within about half. Nothing is
 * imposed on the store: the columns live in the relaxation only, so rows that do not help cost the
 * search nothing.
 *
 * <p>Each table also gets the rows of its convex hull over a column {@code l_t} per tuple t still
 * allowed by the domains (the formulation of a disjunction of points by Balas, "Disjunctive
 * programming", Annals of Discrete Mathematics 5, 1979, as used for tables by Bergman, Cire, van
 * Hoeve and Hooker, "Decision Diagrams for Optimization", Springer 2016, section 2.2): {@code sum
 * l_t = 1}, {@code sum of l_t over the tuples with x = v = b_{x,v}} for a variable with a small
 * domain, and {@code x = sum t_x l_t} for a variable with a large one, such as the result of a
 * two-dimensional element. When the values of one variable with a small domain tell the tuples
 * apart, as the index of elements merged into a table, its own columns are the tuple columns.
 * Otherwise a tuple column is a further LP-only column bounded by the domain of one variable of the
 * table. {@code -Dorg.jacop.lp.tableEncodings=false} leaves these rows out.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class TableCliques {

  /** The largest domain of a variable that gets columns for its values. */
  static final int MAX_DOMAIN = Integer.getInteger("org.jacop.lp.tableCliqueDomain", 16);

  /** The most columns of the graph; a larger graph makes no rows. */
  static final int MAX_LITERALS = Integer.getInteger("org.jacop.lp.tableCliqueLiterals", 8_000);

  /** The most rows. */
  static final int MAX_ROWS = Integer.getInteger("org.jacop.lp.tableCliqueRows", 20_000);

  /** The largest table, in variables, whose projections on pairs give conflicts. */
  public static final int MAX_ARITY = Integer.getInteger("org.jacop.lp.tableCliqueArity", 6);

  // the most tuples times pairs read from one table
  private static final long MAX_PROJECTION = 2_000_000;

  /** Whether the tables get the rows of their convex hull over tuple columns. */
  static final boolean TABLE_ENCODINGS =
      !"false".equals(System.getProperty("org.jacop.lp.tableEncodings"));

  /** The most tuple columns over all tables; a table that would go beyond gets no hull rows. */
  static final int MAX_TUPLE_COLUMNS = Integer.getInteger("org.jacop.lp.tableTupleColumns", 20_000);

  /** The most tuples of a table that gets hull rows. */
  static final int MAX_TUPLES = Integer.getInteger("org.jacop.lp.tableTuples", 2_000);

  private TableCliques() {}

  /**
   * A table constraint and its allowed tuples.
   *
   * @param x the variables, distinct
   * @param tuples the allowed tuples, each of the length of x
   */
  public record Table(IntVar[] x, int[][] tuples) {

    @Override
    public boolean equals(Object o) {
      return o instanceof Table t && Arrays.equals(x, t.x) && Arrays.deepEquals(tuples, t.tuples);
    }

    @Override
    public int hashCode() {
      return 31 * Arrays.hashCode(x) + Arrays.deepHashCode(tuples);
    }

    @Override
    public String toString() {
      return "Table" + Arrays.toString(x) + Arrays.deepToString(tuples);
    }
  }

  /**
   * The rows: the cliques and the encodings of the variables that got new columns, and the convex
   * hulls of the tables with the encodings of the further columns they need.
   *
   * @param rows the rows of the cliques and the encodings of their new value columns
   * @param columns the number of new value columns of the cliques ({@link LpColumn})
   * @param hulls the rows of the hulls, with the encodings of the value columns they add
   * @param hullColumns the number of new columns of the hulls, tuple and value columns
   */
  public record Result(
      List<LinearForm> rows, int columns, List<LinearForm> hulls, int hullColumns) {

    /**
     * Returns the rows of the cliques and of the hulls.
     *
     * @return the rows
     */
    public List<LinearForm> all() {
      List<LinearForm> all = new ArrayList<>(rows);
      all.addAll(hulls);
      return all;
    }
  }

  // two variables of a table, by position
  private record Pair(Table table, int i, int j) {}

  /**
   * Returns the clique rows of the tables over columns of their values, and the encodings of the
   * values that have no Boolean in the model. Nothing is imposed; with no conflict among two
   * variables, there are no rows. Must be called at the root, before the linear relaxation is made.
   *
   * @param tables the tables
   * @return the rows and the count of new columns
   */
  public static Result rows(List<Table> tables) {
    return rows(tables, Map.of());
  }

  /**
   * Returns the rows of {@link #rows(List)}, with the implications {@code z -> a} between Booleans
   * that the store does not hold as conjunctions, such as the binary clauses given to a SAT solver:
   * a Boolean that implies values of two or more variables of a table is at most the sum of the
   * columns of the tuples with those values.
   *
   * @param tables the tables
   * @param implied the Booleans each Boolean implies
   * @return the rows and the count of new columns
   */
  public static Result rows(List<Table> tables, Map<IntVar, List<IntVar>> implied) {
    return rows(tables, implied, MAX_DOMAIN);
  }

  /**
   * Returns the rows of {@link #rows(List, Map)}, with the hulls over the value columns of
   * variables of up to {@code hullDomain} values instead of {@code
   * -Dorg.jacop.lp.tableCliqueDomain} (16): a larger limit gives the tables keyed by a variable of
   * more values, such as the class of a slot in car sequencing (25 classes), the hull over the
   * columns of the key, which ties the other variables to its values and not only to its mean.
   *
   * @param tables the tables
   * @param implied the Booleans each Boolean implies
   * @param hullDomain the largest domain of a variable whose values get columns in the hulls
   * @return the rows and the count of new columns
   */
  public static Result rows(List<Table> tables, Map<IntVar, List<IntVar>> implied, int hullDomain) {
    Columns columns = new Columns(tables, implied);
    List<LinearForm> rows = new ArrayList<>();
    cliques(tables, columns, rows);
    List<LinearForm> all = new ArrayList<>(columns.rows);
    all.addAll(rows);
    int cliqueColumns = columns.count;
    // the encodings of the value columns made for the hulls go with them
    List<LinearForm> hulls = new ArrayList<>();
    columns.rows = hulls;
    if (TABLE_ENCODINGS) {
      hulls(tables, columns, hulls, hullDomain);
    }
    return new Result(all, cliqueColumns, hulls, columns.count - cliqueColumns);
  }

  // the clique rows of the conflicts of the tables
  private static void cliques(List<Table> tables, Columns cols, List<LinearForm> rows) {
    // the pairs of distinct variables with small domains, still unfixed, of the tables
    List<Pair> used = new ArrayList<>();
    Map<IntVar, Integer> first = new IdentityHashMap<>();
    List<IntVar> vars = new ArrayList<>();
    int literals = 0;
    for (Table t : tables) {
      int arity = t.x().length;
      if (arity < 2
          || arity > MAX_ARITY
          || (long) t.tuples().length * arity * (arity - 1) / 2 > MAX_PROJECTION) {
        continue;
      }
      for (int i = 0; i < arity; i++) {
        for (int j = i + 1; j < arity; j++) {
          IntVar x = t.x()[i];
          IntVar y = t.x()[j];
          if (x == y || x.singleton() || y.singleton() || !small(x) || !small(y)) {
            continue;
          }
          for (IntVar v : new IntVar[] {x, y}) {
            if (!first.containsKey(v)) {
              first.put(v, literals);
              vars.add(v);
              literals += v.getSize();
            }
          }
          used.add(new Pair(t, i, j));
          if (literals > MAX_LITERALS) {
            return;
          }
        }
      }
    }
    if (used.isEmpty()) {
      return;
    }
    // literal first(x) + k is x = the k-th value of the domain of x
    int n = literals;
    int[] value = new int[n];
    IntVar[] owner = new IntVar[n];
    for (IntVar x : vars) {
      int k = first.get(x);
      for (ValueEnumeration e = x.domain.valueEnumeration(); e.hasMoreElements(); k++) {
        value[k] = e.nextElement();
        owner[k] = x;
      }
    }
    BitSet[] adj = new BitSet[n];
    for (int i = 0; i < n; i++) {
      adj[i] = new BitSet(n);
    }
    boolean conflicts = false;
    for (Pair p : used) {
      IntVar x = p.table().x()[p.i()];
      IntVar y = p.table().x()[p.j()];
      Set<Long> allowed = new HashSet<>();
      for (int[] tuple : p.table().tuples()) {
        allowed.add(pair(tuple[p.i()], tuple[p.j()]));
      }
      int fx = first.get(x);
      int fy = first.get(y);
      for (int i = fx; i < fx + x.getSize(); i++) {
        for (int j = fy; j < fy + y.getSize(); j++) {
          if (!allowed.contains(pair(value[i], value[j]))) {
            adj[i].set(j);
            adj[j].set(i);
            conflicts = true;
          }
        }
      }
    }
    if (!conflicts) {
      return;
    }
    for (IntVar x : vars) {
      int fx = first.get(x);
      for (int i = fx; i < fx + x.getSize(); i++) {
        adj[i].set(fx, fx + x.getSize());
        adj[i].clear(i);
      }
    }
    IntVar[] columns = new IntVar[n];
    for (int i = 0; i < n; i++) {
      columns[i] = cols.column(owner[i], value[i]);
    }
    int encodingRows = rows.size();
    int[] degree = new int[n];
    for (int i = 0; i < n; i++) {
      degree[i] = adj[i].cardinality();
    }
    BitSet[] covered = new BitSet[n];
    for (int i = 0; i < n; i++) {
      covered[i] = new BitSet(n);
    }
    for (int u = 0; u < n && rows.size() - encodingRows < MAX_ROWS; u++) {
      for (int v = adj[u].nextSetBit(u + 1); v >= 0; v = adj[u].nextSetBit(v + 1)) {
        if (covered[u].get(v) || owner[u] == owner[v]) {
          continue;
        }
        List<Integer> clique = new ArrayList<>(List.of(u, v));
        BitSet candidates = (BitSet) adj[u].clone();
        candidates.and(adj[v]);
        while (!candidates.isEmpty()) {
          int best = -1;
          for (int w = candidates.nextSetBit(0); w >= 0; w = candidates.nextSetBit(w + 1)) {
            if (best < 0 || degree[w] > degree[best]) {
              best = w;
            }
          }
          clique.add(best);
          candidates.and(adj[best]);
        }
        IntVar[] bs = new IntVar[clique.size()];
        for (int k = 0; k < bs.length; k++) {
          int a = clique.get(k);
          bs[k] = columns[a];
          for (int b : clique) {
            covered[a].set(b);
          }
        }
        long[] ones = new long[bs.length];
        Arrays.fill(ones, 1);
        rows.add(new LinearForm(bs, ones, 1, LinearForm.LE));
      }
    }
  }

  // the rows of the convex hull of each table over its tuple columns
  private static void hulls(
      List<Table> tables, Columns cols, List<LinearForm> rows, int hullDomain) {
    int made = 0;
    for (Table t : tables) {
      IntVar[] x = t.x();
      int arity = x.length;
      if (arity < 2 || t.tuples().length > MAX_TUPLES) {
        continue;
      }
      List<int[]> live = new ArrayList<>();
      for (int[] tuple : t.tuples()) {
        if (allowed(x, tuple)) {
          live.add(tuple);
        }
      }
      if (live.size() < 2) {
        continue;
      }
      // a position with a small domain, and one whose values tell the tuples apart
      int some = -1;
      int key = -1;
      for (int j = 0; j < arity; j++) {
        if (!x[j].singleton() && small(x[j], hullDomain)) {
          some = some < 0 ? j : some;
          key = key < 0 && distinct(live, j) ? j : key;
        }
      }
      if (some < 0 || key < 0 && made + live.size() > MAX_TUPLE_COLUMNS) {
        continue;
      }
      int size = live.size();
      IntVar[] tupleColumn = new IntVar[size];
      for (int k = 0; k < size; k++) {
        tupleColumn[k] =
            key >= 0
                ? cols.column(x[key], live.get(k)[key])
                : LpColumn.arc(x[some], live.get(k)[some]);
      }
      if (key < 0) {
        made += size;
        cols.count += size;
        long[] ones = new long[size];
        Arrays.fill(ones, 1);
        rows.add(new LinearForm(tupleColumn, ones, 1, LinearForm.EQ));
      }
      conjunctions(x, live, tupleColumn, cols, rows);
      for (int j = 0; j < arity; j++) {
        if (j == key || x[j].singleton()) {
          continue;
        }
        // the values of x_j tie the tuples to other rows over its columns; when the tuples have
        // columns of their own, which only these rows link, and x_j has no columns yet, its value
        // is enough (a key's columns, as for the merged elements of table-layout)
        if (small(x[j], hullDomain) && (key < 0 || cols.made.containsKey(x[j]))) {
          valueRows(x[j], j, live, tupleColumn, cols, rows);
        } else {
          // x_j = sum of its values in the tuples, weighted by their columns
          IntVar[] vs = Arrays.copyOf(tupleColumn, size + 1);
          long[] w = new long[size + 1];
          for (int k = 0; k < size; k++) {
            w[k] = live.get(k)[j];
          }
          vs[size] = x[j];
          w[size] = -1;
          rows.add(new LinearForm(vs, w, 0, LinearForm.EQ));
        }
      }
    }
  }

  // z <= the sum of the columns of the tuples that agree with the value Booleans [x = v] that z
  // implies, for each Boolean z that implies values of two or more variables of the table (a
  // conjunction of their values): z = 1 makes every such x = v, so the tuple of the solution is one
  // of them
  private static void conjunctions(
      IntVar[] x, List<int[]> live, IntVar[] tupleColumn, Columns cols, List<LinearForm> rows) {
    Map<IntVar, Integer> position = new IdentityHashMap<>();
    for (int j = 0; j < x.length; j++) {
      position.put(x[j], j);
    }
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    for (IntVar xj : x) {
      for (IntVar b : cols.known.getOrDefault(xj, Map.of()).values()) {
        for (IntVar z : cols.impliedBy.getOrDefault(b, List.of())) {
          if (z.singleton() || !seen.add(z)) {
            continue;
          }
          int[] value = new int[x.length];
          boolean[] set = new boolean[x.length];
          int count = 0;
          boolean consistent = true;
          for (IntVar a : cols.implies.get(z)) {
            Literal l = cols.literal.get(a);
            Integer j = l == null ? null : position.get(l.x());
            if (j == null) {
              continue;
            }
            if (set[j] && value[j] != l.v()) {
              consistent = false;
            } else if (!set[j]) {
              set[j] = true;
              value[j] = l.v();
              count++;
            }
          }
          if (!consistent || count < 2) {
            continue;
          }
          List<IntVar> agreeing = new ArrayList<>();
          List<IntVar> others = new ArrayList<>();
          for (int k = 0; k < live.size(); k++) {
            (agrees(live.get(k), value, set) ? agreeing : others).add(tupleColumn[k]);
          }
          if (others.isEmpty()) {
            continue;
          }
          // the tuple columns sum to 1, so z <= sum of the agreeing ones is z + sum of the others
          // <= 1, the shorter of the two, which also keeps a z that no tuple agrees with in a row
          boolean below = !agreeing.isEmpty() && agreeing.size() <= others.size();
          List<IntVar> vs = new ArrayList<>();
          vs.add(z);
          vs.addAll(below ? agreeing : others);
          long[] w = new long[vs.size()];
          Arrays.fill(w, below ? -1 : 1);
          w[0] = 1;
          rows.add(new LinearForm(vs.toArray(new IntVar[0]), w, below ? 0 : 1, LinearForm.LE));
        }
      }
    }
  }

  private static boolean agrees(int[] tuple, int[] value, boolean[] set) {
    for (int j = 0; j < tuple.length; j++) {
      if (set[j] && tuple[j] != value[j]) {
        return false;
      }
    }
    return true;
  }

  // [x = v] = the sum of the columns of the tuples with value v at position j
  private static void valueRows(
      IntVar x,
      int j,
      List<int[]> live,
      IntVar[] tupleColumn,
      Columns cols,
      List<LinearForm> rows) {
    for (ValueEnumeration e = x.domain.valueEnumeration(); e.hasMoreElements(); ) {
      int v = e.nextElement();
      List<IntVar> vs = new ArrayList<>();
      for (int k = 0; k < live.size(); k++) {
        if (live.get(k)[j] == v) {
          vs.add(tupleColumn[k]);
        }
      }
      vs.add(cols.column(x, v));
      long[] w = new long[vs.size()];
      Arrays.fill(w, 1);
      w[w.length - 1] = -1;
      rows.add(new LinearForm(vs.toArray(new IntVar[0]), w, 0, LinearForm.EQ));
    }
  }

  private static boolean allowed(IntVar[] x, int[] tuple) {
    for (int j = 0; j < x.length; j++) {
      if (!x[j].domain.contains(tuple[j])) {
        return false;
      }
    }
    return true;
  }

  // whether the tuples have distinct values at position j
  private static boolean distinct(List<int[]> tuples, int j) {
    Set<Integer> seen = new HashSet<>();
    for (int[] tuple : tuples) {
      if (!seen.add(tuple[j])) {
        return false;
      }
    }
    return true;
  }

  private static boolean small(IntVar x) {
    return small(x, MAX_DOMAIN);
  }

  private static boolean small(IntVar x, int domain) {
    return x.getSize() <= domain && x.max() - x.min() < Integer.MAX_VALUE;
  }

  private static long pair(int a, int b) {
    return ((long) a << 32) ^ (b & 0xffffffffL);
  }

  // the column [x = v] of each value of the variables with small domains: the model's own Boolean,
  // or a new LP-only column; the variables with new columns get their encoding rows, sum b = 1 and
  // x = sum v b (those the model's Booleans cover have them from Linearizations.encodings)
  // the value v of variable x
  private record Literal(IntVar x, int v) {}

  private static final class Columns {
    final Map<IntVar, Map<Integer, IntVar>> known;
    // the value Boolean of the model behind each Boolean [x = v]
    final Map<IntVar, Literal> literal = new IdentityHashMap<>();
    final Map<IntVar, Map<Integer, IntVar>> made = new IdentityHashMap<>();
    // where the encodings of new columns go
    List<LinearForm> rows = new ArrayList<>();
    int count;

    Columns(List<Table> tables, Map<IntVar, List<IntVar>> given) {
      Set<Constraint> constraints = new LinkedHashSet<>();
      Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
      for (Table t : tables) {
        for (IntVar x : t.x()) {
          if (small(x) && seen.add(x)) {
            constraints.addAll(x.dom().constraints());
          }
        }
      }
      known = Linearizations.valueBooleans(constraints);
      for (Map.Entry<IntVar, Map<Integer, IntVar>> e : known.entrySet()) {
        for (Map.Entry<Integer, IntVar> b : e.getValue().entrySet()) {
          if (b.getValue() != e.getKey()) {
            literal.putIfAbsent(b.getValue(), new Literal(e.getKey(), b.getKey()));
          }
        }
      }
      // the conjunctions of the store over the value Booleans: their result implies each of them
      Set<Constraint> conjunctions = Collections.newSetFromMap(new IdentityHashMap<>());
      for (IntVar b : literal.keySet()) {
        for (Constraint c : b.dom().constraints()) {
          if ((c.getClass() == AndBoolSimple.class || c.getClass() == AndBoolVector.class)
              && conjunctions.add(c)) {
            if (c instanceof AndBoolSimple a) {
              implication(a.result, a.a);
              implication(a.result, a.b);
            } else {
              AndBoolVector a = (AndBoolVector) c;
              for (IntVar l : a.list) {
                implication(a.result, l);
              }
            }
          }
        }
      }
      for (Map.Entry<IntVar, List<IntVar>> e : given.entrySet()) {
        for (IntVar a : e.getValue()) {
          implication(e.getKey(), a);
        }
      }
    }

    // the Booleans each Boolean z implies (z -> a), and the inverse
    final Map<IntVar, List<IntVar>> implies = new IdentityHashMap<>();
    final Map<IntVar, List<IntVar>> impliedBy = new IdentityHashMap<>();

    void implication(IntVar z, IntVar a) {
      if (literal.containsKey(a)) {
        implies.computeIfAbsent(z, k -> new ArrayList<>()).add(a);
        impliedBy.computeIfAbsent(a, k -> new ArrayList<>()).add(z);
      }
    }

    IntVar column(IntVar x, int v) {
      Map<Integer, IntVar> m = made.get(x);
      if (m == null) {
        m = new LinkedHashMap<>();
        Map<Integer, IntVar> own = known.getOrDefault(x, Map.of());
        boolean fresh = false;
        for (ValueEnumeration e = x.domain.valueEnumeration(); e.hasMoreElements(); ) {
          int value = e.nextElement();
          IntVar b = own.get(value);
          if (b == null || b == x) {
            b = new LpColumn(x, value);
            fresh = true;
            count++;
          }
          m.put(value, b);
        }
        if (fresh) {
          int k = m.size();
          IntVar[] bs = m.values().toArray(new IntVar[0]);
          long[] ones = new long[k];
          Arrays.fill(ones, 1);
          rows.add(new LinearForm(bs, ones, 1, LinearForm.EQ));
          IntVar[] withX = Arrays.copyOf(bs, k + 1);
          long[] w = new long[k + 1];
          int i = 0;
          for (int value : m.keySet()) {
            w[i++] = value;
          }
          withX[k] = x;
          w[k] = -1;
          rows.add(new LinearForm(withX, w, 0, LinearForm.EQ));
        }
        made.put(x, m);
      }
      return m.get(v);
    }
  }
}
