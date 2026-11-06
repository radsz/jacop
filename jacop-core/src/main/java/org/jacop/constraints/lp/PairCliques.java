/*
 * PairCliques.java
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

package org.jacop.constraints.lp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.core.IntVar;
import org.jacop.lcg.LinearForm;

/**
 * Merges the rows that forbid two 0/1 literals together into rows over cliques of such literals.
 *
 * <p>A row over two 0/1 variables that holds unless both of its raising literals are 1 (such as
 * {@code x + y <= 1} or {@code x - y <= 0}) is the conflict of those two literals. The conflicts
 * make a graph; a set of literals that conflict pairwise gives the row {@code sum of the literals
 * <= 1}, which implies the rows of all its pairs and is much stronger in the LP: pairwise conflicts
 * of k literals allow k / 2 in the relaxation, the clique row 1. Models state shifts that overlap,
 * or tasks that share a time, pair by pair (roster-shifts-bool: 25,776 pair rows, the root bound at
 * 9,722 for the optimum 5,281, and 5,281 with the cliques of each time point).
 *
 * <p>Each conflict not yet covered grows a maximal clique, greedily over the literals that conflict
 * with both of its literals, the most conflicting first. The pair rows covered by a clique of three
 * or more literals are replaced by the clique rows; the others stay.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class PairCliques {

  // the most literals in one clique, and in all the cliques together
  private static final int MAX_CLIQUE = 1_000;
  private static final long MAX_ENTRIES = 2_000_000;

  /** The rows, with the clique rows in place of the pair rows they cover. */
  final List<LinearForm> rows;

  /** The further rows, without the pair rows the cliques cover. */
  final List<LinearForm> further;

  /** The number of clique rows of three or more literals. */
  final int cliques;

  private PairCliques(List<LinearForm> rows, List<LinearForm> further, int cliques) {
    this.rows = rows;
    this.further = further;
    this.cliques = cliques;
  }

  /**
   * Returns the rows with the conflicts of pairs of 0/1 literals merged into cliques. The conflicts
   * come from both lists; the clique rows join the rows, since they hold wherever the pair rows
   * they cover do.
   *
   * @param given the rows; not changed
   * @param others further rows, such as the linearised rows of other constraints; not changed
   * @return the rows, the further rows and the number of clique rows
   */
  static PairCliques merge(List<LinearForm> given, List<LinearForm> others) {
    List<LinearForm> forms = new ArrayList<>(given);
    forms.addAll(others);
    Map<IntVar, Integer> column = new IdentityHashMap<>();
    List<IntVar> vars = new ArrayList<>();
    // the conflict of each pair row, as two literals: 2 j for x_j = 1, 2 j + 1 for x_j = 0
    int[][] pair = new int[forms.size()][];
    Map<Long, Integer> edges = new HashMap<>();
    for (int i = 0; i < forms.size(); i++) {
      int[] p = conflict(forms.get(i), column, vars);
      if (p != null) {
        long key = key(p[0], p[1]);
        if (!edges.containsKey(key)) {
          edges.put(key, i);
        }
        pair[i] = p;
      }
    }
    if (edges.size() < 3) {
      return new PairCliques(given, others, 0);
    }
    int literals = 2 * vars.size();
    List<List<Integer>> adjacent = new ArrayList<>(literals);
    for (int l = 0; l < literals; l++) {
      adjacent.add(new ArrayList<>());
    }
    for (int[] p : pair) {
      if (p != null && edges.get(key(p[0], p[1])) != null) {
        adjacent.get(p[0]).add(p[1]);
        adjacent.get(p[1]).add(p[0]);
      }
    }
    // pair rows that state the same conflict twice add the literal twice: once is enough
    int[][] neighbours = new int[literals][];
    for (int l = 0; l < literals; l++) {
      neighbours[l] = adjacent.get(l).stream().mapToInt(Integer::intValue).distinct().toArray();
    }
    Set<Long> covered = new HashSet<>();
    List<int[]> found = new ArrayList<>();
    long entries = 0;
    for (int i = 0; i < pair.length && entries < MAX_ENTRIES; i++) {
      int[] p = pair[i];
      if (p == null || covered.contains(key(p[0], p[1]))) {
        continue;
      }
      int[] clique = grow(p[0], p[1], neighbours, edges);
      if (clique.length < 3) {
        continue;
      }
      for (int a = 0; a < clique.length; a++) {
        for (int b = a + 1; b < clique.length; b++) {
          covered.add(key(clique[a], clique[b]));
        }
      }
      found.add(clique);
      entries += clique.length;
    }
    if (found.isEmpty()) {
      return new PairCliques(given, others, 0);
    }
    List<LinearForm> rows = new ArrayList<>();
    List<LinearForm> further = new ArrayList<>();
    for (int i = 0; i < forms.size(); i++) {
      int[] p = pair[i];
      if (p == null || !covered.contains(key(p[0], p[1]))) {
        (i < given.size() ? rows : further).add(forms.get(i));
      }
    }
    for (int[] clique : found) {
      rows.add(row(clique, vars));
    }
    return new PairCliques(rows, further, found.size());
  }

  // a maximal clique with the conflict of u and v, greedily over their common neighbours
  private static int[] grow(int u, int v, int[][] neighbours, Map<Long, Integer> edges) {
    List<Integer> clique = new ArrayList<>(List.of(u, v));
    int[] candidates = neighbours[u].length <= neighbours[v].length ? neighbours[u] : neighbours[v];
    int other = candidates == neighbours[u] ? v : u;
    Integer[] order =
        Arrays.stream(candidates)
            .filter(w -> w != other && edges.containsKey(key(w, other)))
            .boxed()
            .toArray(Integer[]::new);
    Arrays.sort(
        order,
        (a, b) ->
            neighbours[a].length != neighbours[b].length
                ? Integer.compare(neighbours[b].length, neighbours[a].length)
                : Integer.compare(a, b));
    for (int w : order) {
      if (clique.size() >= MAX_CLIQUE) {
        break;
      }
      boolean all = true;
      for (int c : clique) {
        if (c == (w ^ 1) || !edges.containsKey(key(w, c))) {
          all = false;
          break;
        }
      }
      if (all) {
        clique.add(w);
      }
    }
    return clique.stream().mapToInt(Integer::intValue).toArray();
  }

  // sum of the literals <= 1, as sum of the positive ones minus the negative ones <= 1 - negatives
  private static LinearForm row(int[] clique, List<IntVar> vars) {
    int[] ls = clique.clone();
    Arrays.sort(ls);
    IntVar[] xs = new IntVar[ls.length];
    long[] ws = new long[ls.length];
    long c = 1;
    for (int q = 0; q < ls.length; q++) {
      xs[q] = vars.get(ls[q] >> 1);
      if ((ls[q] & 1) == 0) {
        ws[q] = 1;
      } else {
        ws[q] = -1;
        c--;
      }
    }
    return new LinearForm(xs, ws, c, LinearForm.LE);
  }

  // the two literals whose conflict the row is, or null when it is not the conflict of two
  // literals; fixed variables count as constants (FlatZinc states x + y <= 1 as x + y - one <= 0)
  private static int[] conflict(LinearForm f, Map<IntVar, Integer> column, List<IntVar> vars) {
    if (f.relation() != LinearForm.LE && f.relation() != LinearForm.GE) {
      return null;
    }
    IntVar[] xs = f.vars();
    long[] ws = f.weights();
    // as sign * sum w x <= b
    long sign = f.relation() == LinearForm.LE ? 1 : -1;
    long b = sign * f.c();
    IntVar[] free = new IntVar[2];
    long[] a = new long[2];
    int count = 0;
    try {
      for (int k = 0; k < xs.length; k++) {
        IntVar x = xs[k];
        long w = Math.multiplyExact(sign, ws[k]);
        if (x.singleton()) {
          b = Math.subtractExact(b, Math.multiplyExact(w, x.value()));
        } else if (w != 0) {
          if (count == 2 || x.min() != 0 || x.max() != 1) {
            return null;
          }
          free[count] = x;
          a[count++] = w;
        }
      }
    } catch (ArithmeticException _) {
      return null;
    }
    if (count != 2 || free[0] == free[1]) {
      return null;
    }
    long least = Math.min(0, a[0]) + Math.min(0, a[1]);
    // each raising literal alone is allowed, the two together are not
    if (least + Math.abs(a[0]) > b
        || least + Math.abs(a[1]) > b
        || least + Math.abs(a[0]) + Math.abs(a[1]) <= b) {
      return null;
    }
    int[] p = new int[2];
    for (int k = 0; k < 2; k++) {
      int j =
          column.computeIfAbsent(
              free[k],
              x -> {
                vars.add(x);
                return vars.size() - 1;
              });
      p[k] = a[k] > 0 ? 2 * j : 2 * j + 1;
    }
    return p;
  }

  private static long key(int a, int b) {
    return a < b ? ((long) a << 32) | b : ((long) b << 32) | a;
  }
}
