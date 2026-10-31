/*
 * CliqueCut.java
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
import java.util.BitSet;
import java.util.List;

/**
 * Clique cuts over the 0/1 columns of the rows.
 *
 * <p>A literal is a 0/1 column or its complement ({@code 1 - x}). Two literals conflict when a row
 * cannot hold with both of them at 1: with {@code s = b - minActivity} the slack of a row {@code
 * sum a x <= b} at the bounds that minimise it, the literals of weights {@code |a_i|} and {@code
 * |a_j|} conflict when {@code |a_i| + |a_j| > s}. A row gives its conflicts as cliques: the
 * literals of its largest weights, while the two smallest of them conflict, and each other literal
 * with the largest ones it conflicts with. A set of pairwise conflicting literals, drawn from
 * several rows, has at most one at 1, which no single row needs to say: from {@code x + y <= 1},
 * {@code y + z <= 1} and {@code x + z <= 1} it gives {@code x + y + z <= 1}.
 *
 * <p>The separation grows a clique greedily from each fractional literal, the largest LP values
 * first, keeps it when the LP solution breaks it, and then extends it with literals at 0 to a
 * maximal clique, which makes the cut stronger elsewhere. The bounds must be global (the root
 * bounds), so that the conflicts and the cuts are global too.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class CliqueCut {

  // the most literals in all the cliques together, and in the cliques of one row beyond its
  // largest one, against quadratic growth on long rows
  private static final int MAX_ENTRIES = 1_000_000;
  private static final int MAX_ROW_EXTRA = 2_000;

  private static final double EPS = 1e-6;

  // the cliques, as literals (2 j for x_j, 2 j + 1 for 1 - x_j), and the cliques of each literal
  private final List<int[]> cliques = new ArrayList<>();
  private final int[][] of;
  private final int columns;

  private CliqueCut(int columns, List<int[]> cliques) {
    this.columns = columns;
    this.cliques.addAll(cliques);
    int[] count = new int[2 * columns];
    for (int[] c : cliques) {
      for (int l : c) {
        count[l]++;
      }
    }
    of = new int[2 * columns][];
    for (int l = 0; l < of.length; l++) {
      of[l] = new int[count[l]];
    }
    Arrays.fill(count, 0);
    for (int q = 0; q < cliques.size(); q++) {
      for (int l : cliques.get(q)) {
        of[l][count[l]++] = q;
      }
    }
  }

  /**
   * Returns the conflict graph of the rows, or null when it has no clique.
   *
   * @param rowColumns the columns of each row
   * @param rowWeights the weights of each row
   * @param rowLo the lower side of each row
   * @param rowHi the upper side of each row
   * @param hasLo whether each row has its lower side
   * @param hasHi whether each row has its upper side
   * @param lo the global lower bounds by column
   * @param hi the global upper bounds by column
   * @return the conflict graph, or null
   */
  static CliqueCut of(
      int[][] rowColumns,
      long[][] rowWeights,
      long[] rowLo,
      long[] rowHi,
      boolean[] hasLo,
      boolean[] hasHi,
      long[] lo,
      long[] hi) {
    List<int[]> cliques = new ArrayList<>();
    int[] entries = {0};
    for (int i = 0; i < rowColumns.length; i++) {
      if (hasHi[i]) {
        side(rowColumns[i], rowWeights[i], 1, rowHi[i], lo, hi, cliques, entries);
      }
      if (hasLo[i]) {
        side(rowColumns[i], rowWeights[i], -1, -rowLo[i], lo, hi, cliques, entries);
      }
      if (entries[0] > MAX_ENTRIES) {
        break;
      }
    }
    return cliques.isEmpty() ? null : new CliqueCut(lo.length, cliques);
  }

  // the cliques of sign * sum w x <= b
  private static void side(
      int[] cs,
      long[] ws,
      long sign,
      long b,
      long[] lo,
      long[] hi,
      List<int[]> cliques,
      int[] entries) {
    long least = 0;
    List<long[]> binary = new ArrayList<>(); // {|a|, literal}
    try {
      for (int k = 0; k < cs.length; k++) {
        int j = cs[k];
        long a = Math.multiplyExact(sign, ws[k]);
        least =
            Math.addExact(
                least, Math.min(Math.multiplyExact(a, lo[j]), Math.multiplyExact(a, hi[j])));
        if (a != 0 && lo[j] == 0 && hi[j] == 1) {
          // the literal at 1 that raises the activity by |a|
          binary.add(new long[] {Math.abs(a), a > 0 ? 2L * j : 2L * j + 1});
        }
      }
      long slack = Math.subtractExact(b, least);
      if (slack < 0 || binary.size() < 2) {
        return;
      }
      binary.sort((p, q) -> p[0] != q[0] ? Long.compare(q[0], p[0]) : Long.compare(p[1], q[1]));
      int k = 1;
      while (k < binary.size() && binary.get(k - 1)[0] + binary.get(k)[0] > slack) {
        k++;
      }
      if (k >= 2) {
        add(binary, k, -1, cliques, entries);
      }
      // each later literal with the largest ones it conflicts with
      int extra = 0;
      for (int j = Math.max(k, 1); j < binary.size() && extra < MAX_ROW_EXTRA; j++) {
        long aj = binary.get(j)[0];
        int q = 0;
        while (q < k && binary.get(q)[0] + aj > slack) {
          q++;
        }
        if (q == 0) {
          break; // the weights only get smaller
        }
        add(binary, q, j, cliques, entries);
        extra += q + 1;
      }
    } catch (ArithmeticException _) {
      // a row whose activity overflows gives no conflicts
    }
  }

  private static void add(
      List<long[]> binary, int prefix, int other, List<int[]> cliques, int[] entries) {
    int[] c = new int[prefix + (other >= 0 ? 1 : 0)];
    for (int q = 0; q < prefix; q++) {
      c[q] = (int) binary.get(q)[1];
    }
    if (other >= 0) {
      c[prefix] = (int) binary.get(other)[1];
    }
    cliques.add(c);
    entries[0] += c.length;
  }

  // the literals that conflict with l
  private BitSet neighbours(int l) {
    BitSet n = new BitSet(2 * columns);
    for (int q : of[l]) {
      for (int m : cliques.get(q)) {
        n.set(m);
      }
    }
    n.clear(l);
    return n;
  }

  /**
   * Adds the clique cuts that the LP solution breaks.
   *
   * @param value the LP solution by column
   * @param found the cuts found
   */
  void separate(double[] value, List<MirCut> found) {
    int lits = 2 * columns;
    double[] v = new double[lits];
    List<Integer> seeds = new ArrayList<>();
    for (int j = 0; j < columns; j++) {
      v[2 * j] = value[j];
      v[2 * j + 1] = 1 - value[j];
    }
    for (int l = 0; l < lits; l++) {
      if (of[l].length > 0 && v[l] > EPS && v[l] < 1 - EPS) {
        seeds.add(l);
      }
    }
    seeds.sort((p, q) -> v[p] != v[q] ? Double.compare(v[q], v[p]) : Integer.compare(p, q));
    BitSet used = new BitSet(lits);
    for (int u : seeds) {
      if (used.get(u)) {
        continue; // already in a cut of this round
      }
      BitSet candidates = neighbours(u);
      List<Integer> order = new ArrayList<>();
      for (int l = candidates.nextSetBit(0); l >= 0; l = candidates.nextSetBit(l + 1)) {
        order.add(l);
      }
      order.sort((p, q) -> v[p] != v[q] ? Double.compare(v[q], v[p]) : Integer.compare(p, q));
      List<Integer> clique = new ArrayList<>();
      clique.add(u);
      double sum = v[u];
      for (int l : order) {
        if (candidates.get(l) && (l ^ 1) != u) {
          clique.add(l);
          sum += Math.max(0, v[l]);
          candidates.and(neighbours(l));
          candidates.clear(l ^ 1);
        }
      }
      if (sum > 1 + EPS && clique.size() >= 2) {
        MirCut c = cut(clique, value);
        if (c != null) {
          found.add(c);
          for (int l : clique) {
            if (v[l] > EPS) {
              used.set(l);
            }
          }
        }
      }
    }
  }

  // sum of the literals <= 1, as sum_pos x - sum_neg x <= 1 - |neg|, over increasing columns
  private static MirCut cut(List<Integer> clique, double[] value) {
    int[] ls = clique.stream().mapToInt(Integer::intValue).sorted().toArray();
    int[] cols = new int[ls.length];
    long[] ws = new long[ls.length];
    long rhs = 1;
    for (int q = 0; q < ls.length; q++) {
      cols[q] = ls[q] >> 1;
      if ((ls[q] & 1) == 0) {
        ws[q] = 1;
      } else {
        ws[q] = -1;
        rhs--;
      }
    }
    for (int q = 1; q < cols.length; q++) {
      if (cols[q] == cols[q - 1]) {
        return null; // a column and its complement: the clique says nothing about the others
      }
    }
    return MirCut.row(cols, ws, rhs, value);
  }
}
