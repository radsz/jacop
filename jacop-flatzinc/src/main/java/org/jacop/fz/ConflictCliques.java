/*
 * ConflictCliques.java
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
package org.jacop.fz;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.core.IntVar;
import org.jacop.lcg.LinearForm;

/**
 * Clique rows from the conflicts between values of 0/1 variables that root probing found: x = a and
 * y = b cannot hold together. Greedy maximal cliques of the conflict graph over the literals [x =
 * 1] and [x = 0] become rows sum [x = a] &lt;= 1, as in the conflict graphs of integer programming:
 * A. Atamtürk, G. L. Nemhauser and M. W. P. Savelsbergh, Conflict graphs in solving integer
 * programming problems, European Journal of Operational Research 121(1), 2000. Conflicts that no
 * clique of three literals or more covers are left out: the clauses of the solver hold them
 * already, and thousands of pair rows made the linear relaxation drop all its extra rows.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class ConflictCliques {

  private ConflictCliques() {}

  /**
   * Returns the clique rows of the conflicts.
   *
   * @param pairs the pairs of 0/1 variables in conflict
   * @param values the values of each pair that cannot hold together, each 0 or 1
   * @param maxEntries the most entries of all rows together
   * @return rows sum [x = a] &lt;= 1 of cliques of at least three literals
   */
  static List<LinearForm> rows(List<IntVar[]> pairs, List<int[]> values, long maxEntries) {
    Map<IntVar, Integer> index = new IdentityHashMap<>();
    List<IntVar> vars = new ArrayList<>();
    List<Set<Integer>> adjacent = new ArrayList<>();
    int[][] edges = new int[pairs.size()][];
    for (int k = 0; k < pairs.size(); k++) {
      IntVar x = pairs.get(k)[0];
      IntVar y = pairs.get(k)[1];
      if (x == y || x.singleton() || y.singleton()) {
        continue;
      }
      int u = 2 * column(x, index, vars, adjacent) + values.get(k)[0];
      int v = 2 * column(y, index, vars, adjacent) + values.get(k)[1];
      adjacent.get(u).add(v);
      adjacent.get(v).add(u);
      edges[k] = new int[] {u, v};
    }
    Set<Long> covered = new HashSet<>();
    List<LinearForm> rows = new ArrayList<>();
    long entries = 0;
    for (int[] e : edges) {
      if (e == null || covered.contains(key(e[0], e[1])) || entries >= maxEntries) {
        continue;
      }
      int[] clique = grow(e[0], e[1], adjacent);
      if (clique.length < 3) {
        continue;
      }
      for (int a = 0; a < clique.length; a++) {
        for (int b = a + 1; b < clique.length; b++) {
          covered.add(key(clique[a], clique[b]));
        }
      }
      rows.add(row(clique, vars));
      entries += clique.length;
    }
    return rows;
  }

  private static int column(
      IntVar x, Map<IntVar, Integer> index, List<IntVar> vars, List<Set<Integer>> adjacent) {
    Integer j = index.get(x);
    if (j == null) {
      j = vars.size();
      index.put(x, j);
      vars.add(x);
      adjacent.add(new HashSet<>());
      adjacent.add(new HashSet<>());
    }
    return j;
  }

  private static long key(int u, int v) {
    return u < v ? ((long) u << 32) | v : ((long) v << 32) | u;
  }

  // a maximal clique with u and v, greedily over their common neighbours, most connected first
  private static int[] grow(int u, int v, List<Set<Integer>> adjacent) {
    Set<Integer> small =
        adjacent.get(u).size() <= adjacent.get(v).size() ? adjacent.get(u) : adjacent.get(v);
    Set<Integer> large = small == adjacent.get(u) ? adjacent.get(v) : adjacent.get(u);
    Integer[] candidates = small.stream().filter(large::contains).toArray(Integer[]::new);
    Arrays.sort(
        candidates, (a, b) -> Integer.compare(adjacent.get(b).size(), adjacent.get(a).size()));
    List<Integer> clique = new ArrayList<>(List.of(u, v));
    for (int c : candidates) {
      boolean all = true;
      for (int member : clique) {
        if (!adjacent.get(c).contains(member)) {
          all = false;
          break;
        }
      }
      if (all) {
        clique.add(c);
      }
    }
    return clique.stream().mapToInt(Integer::intValue).toArray();
  }

  // sum [x = a] <= 1, with [x = 0] as 1 - x
  private static LinearForm row(int[] clique, List<IntVar> vars) {
    IntVar[] xs = new IntVar[clique.length];
    long[] ws = new long[clique.length];
    long c = 1;
    for (int k = 0; k < clique.length; k++) {
      xs[k] = vars.get(clique[k] / 2);
      boolean one = clique[k] % 2 == 1;
      ws[k] = one ? 1 : -1;
      if (!one) {
        c--;
      }
    }
    return new LinearForm(xs, ws, c, LinearForm.LE);
  }
}
