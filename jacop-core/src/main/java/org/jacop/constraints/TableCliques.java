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
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.LinearForm;

/**
 * At-most-one rows of the linear relaxation from binary tables (CP-SAT's table expansion with
 * {@code TransformIntoMaxCliques}). Each variable of a binary table with a small domain gets a
 * Boolean {@code b_v <-> x = v} for every value: the Booleans the model already has ({@link
 * ChannelReif}, {@link Reified} {@link XeqC}), and a {@link ChannelReif} over new Booleans for the
 * other values, so that {@link Linearizations#encodings} gives {@code sum b_v = 1} and {@code x =
 * sum v b_v}. A pair of values {@code (a, b)} that no tuple of a table over {@code (x, y)} allows
 * is a conflict {@code b_{x,a} + b_{y,b} <= 1}; together with the values of one variable, which
 * conflict pairwise, the conflicts are the edges of a graph on the Booleans. Each edge not yet in a
 * row is extended greedily to a maximal clique of that graph, and the clique is a row {@code sum b
 * <= 1}, unless it holds the values of one variable only, which its encoding already bounds.
 *
 * <p>The rows hold for every solution, and the cliques make the relaxation much stronger than the
 * conflicts on their own: on the spot5 instances of the MiniZinc Challenge, a weighted sum of
 * Booleans over binary tables, the relaxation of the cliques is within 4 to 7 % of the optimum,
 * that of the conflicts within about half.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class TableCliques {

  /** The largest domain of a variable that gets Booleans for its values. */
  static final int MAX_DOMAIN = Integer.getInteger("org.jacop.lp.tableCliqueDomain", 16);

  /** The most Booleans of the graph; a larger graph makes no rows. */
  static final int MAX_LITERALS = Integer.getInteger("org.jacop.lp.tableCliqueLiterals", 8_000);

  /** The most rows. */
  static final int MAX_ROWS = Integer.getInteger("org.jacop.lp.tableCliqueRows", 20_000);

  private TableCliques() {}

  /**
   * A table constraint over two variables and its allowed tuples.
   *
   * @param x the two variables
   * @param tuples the allowed tuples, each of length 2
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

  /** The rows and the number of new Booleans. */
  public record Result(List<LinearForm> rows, int booleans) {}

  /**
   * Returns the clique rows of the binary tables, and imposes the {@link ChannelReif} that gives
   * their variables a Boolean for each value they lack one for. Must be called at the root, before
   * the linear relaxation is made; with no conflict among two variables, nothing is imposed.
   *
   * @param store the store
   * @param tables the binary tables
   * @return the rows and the count of new Booleans
   */
  public static Result rows(Store store, List<Table> tables) {
    // the tables over two distinct variables with small domains, still unfixed
    List<Table> used = new ArrayList<>();
    Map<IntVar, Integer> first = new IdentityHashMap<>();
    List<IntVar> vars = new ArrayList<>();
    int literals = 0;
    for (Table t : tables) {
      IntVar x = t.x()[0];
      IntVar y = t.x()[1];
      if (x == y || x.singleton() || y.singleton() || !small(x) || !small(y)) {
        continue;
      }
      for (IntVar v : t.x()) {
        if (!first.containsKey(v)) {
          first.put(v, literals);
          vars.add(v);
          literals += v.getSize();
        }
      }
      used.add(t);
      if (literals > MAX_LITERALS) {
        return new Result(List.of(), 0);
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
    for (Table t : used) {
      IntVar x = t.x()[0];
      IntVar y = t.x()[1];
      Set<Long> allowed = new HashSet<>();
      for (int[] tuple : t.tuples()) {
        allowed.add(pair(tuple[0], tuple[1]));
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
    int[] created = new int[1];
    IntVar[] booleans = booleans(store, vars, first, value, created);
    int[] degree = new int[n];
    for (int i = 0; i < n; i++) {
      degree[i] = adj[i].cardinality();
    }
    List<LinearForm> rows = new ArrayList<>();
    BitSet[] covered = new BitSet[n];
    for (int i = 0; i < n; i++) {
      covered[i] = new BitSet(n);
    }
    for (int u = 0; u < n && rows.size() < MAX_ROWS; u++) {
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
          bs[k] = booleans[a];
          for (int b : clique) {
            covered[a].set(b);
          }
        }
        long[] ones = new long[bs.length];
        Arrays.fill(ones, 1);
        rows.add(new LinearForm(bs, ones, 1, LinearForm.LE));
      }
    }
    return new Result(rows, created[0]);
  }

  private static boolean small(IntVar x) {
    return x.getSize() <= MAX_DOMAIN && x.max() - x.min() < Integer.MAX_VALUE;
  }

  private static long pair(int a, int b) {
    return ((long) a << 32) ^ (b & 0xffffffffL);
  }

  // the Boolean of each literal: the model's own, or a new one channelled to its variable
  private static IntVar[] booleans(
      Store store, List<IntVar> vars, Map<IntVar, Integer> first, int[] value, int[] created) {
    Set<Constraint> constraints = new LinkedHashSet<>();
    for (IntVar x : vars) {
      constraints.addAll(x.dom().constraints());
    }
    Map<IntVar, Map<Integer, IntVar>> known = Linearizations.valueBooleans(constraints);
    IntVar[] b = new IntVar[value.length];
    for (IntVar x : vars) {
      Map<Integer, IntVar> own = known.getOrDefault(x, Map.of());
      Map<Integer, IntVar> missing = new LinkedHashMap<>();
      int fx = first.get(x);
      for (int i = fx; i < fx + x.getSize(); i++) {
        IntVar bi = own.get(value[i]);
        if (bi == null || bi == x) {
          bi = new IntVar(store, 0, 1);
          missing.put(value[i], bi);
        }
        b[i] = bi;
      }
      if (!missing.isEmpty()) {
        store.impose(new ChannelReif(x, missing));
        created[0] += missing.size();
      }
    }
    return b;
  }
}
