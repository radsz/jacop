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
import java.util.HashSet;
import java.util.IdentityHashMap;
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
   * The rows: the cliques and the encodings of the variables that got new columns.
   *
   * @param rows the rows
   * @param columns the number of new columns ({@link LpColumn})
   */
  public record Result(List<LinearForm> rows, int columns) {}

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
            return new Result(List.of(), 0);
          }
        }
      }
    }
    if (used.isEmpty()) {
      return new Result(List.of(), 0);
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
      return new Result(List.of(), 0);
    }
    for (IntVar x : vars) {
      int fx = first.get(x);
      for (int i = fx; i < fx + x.getSize(); i++) {
        adj[i].set(fx, fx + x.getSize());
        adj[i].clear(i);
      }
    }
    List<LinearForm> rows = new ArrayList<>();
    IntVar[] columns = columns(vars, first, value, rows);
    int made = 0;
    for (IntVar c : columns) {
      made += c instanceof LpColumn ? 1 : 0;
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
    return new Result(rows, made);
  }

  private static boolean small(IntVar x) {
    return x.getSize() <= MAX_DOMAIN && x.max() - x.min() < Integer.MAX_VALUE;
  }

  private static long pair(int a, int b) {
    return ((long) a << 32) ^ (b & 0xffffffffL);
  }

  // the column of each literal: the model's own Boolean, or a new LP-only column; the variables
  // with new columns get their encoding rows, sum b = 1 and x = sum v b (those the model's
  // Booleans cover have them from Linearizations.encodings)
  private static IntVar[] columns(
      List<IntVar> vars, Map<IntVar, Integer> first, int[] value, List<LinearForm> rows) {
    Set<Constraint> constraints = new LinkedHashSet<>();
    for (IntVar x : vars) {
      constraints.addAll(x.dom().constraints());
    }
    Map<IntVar, Map<Integer, IntVar>> known = Linearizations.valueBooleans(constraints);
    IntVar[] b = new IntVar[value.length];
    for (IntVar x : vars) {
      Map<Integer, IntVar> own = known.getOrDefault(x, Map.of());
      int fx = first.get(x);
      boolean fresh = false;
      for (int i = fx; i < fx + x.getSize(); i++) {
        IntVar bi = own.get(value[i]);
        if (bi == null || bi == x) {
          bi = new LpColumn(x, value[i]);
          fresh = true;
        }
        b[i] = bi;
      }
      if (fresh) {
        int k = x.getSize();
        IntVar[] bs = Arrays.copyOfRange(b, fx, fx + k);
        long[] ones = new long[k];
        Arrays.fill(ones, 1);
        rows.add(new LinearForm(bs, ones, 1, LinearForm.EQ));
        IntVar[] withX = Arrays.copyOf(bs, k + 1);
        long[] w = new long[k + 1];
        for (int i = 0; i < k; i++) {
          w[i] = value[fx + i];
        }
        withX[k] = x;
        w[k] = -1;
        rows.add(new LinearForm(withX, w, 0, LinearForm.EQ));
      }
    }
    return b;
  }
}
