/*
 * ZeroHalfCuts.java
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
import java.util.Comparator;
import java.util.List;

/**
 * Separation of {0,1/2}-Chvatal-Gomory (zero-half) cuts: a combination of integer rows {@code sum
 * a_i x <= b_i} with multipliers 1/2 whose weights are integral except at the columns where the
 * rounding is free, and whose right side is half-integral, rounds to a valid cut {@code floor(u A)
 * x <= floor(u b)}. With the columns shifted to their nearer bound ({@code x'_j >= 0}, the distance
 * of the LP value to that bound) and {@code s_i} the slack of row i at the LP solution, a set R of
 * rows whose sum is odd on the right side gives a cut violated by {@code (1 - sum_{i in R} s_i -
 * sum_{j odd in R} x'_j) / 2}, so the separation looks, over GF(2), for a set of rows of small
 * slack whose odd columns have small distance.
 *
 * <p>Exact separation is NP-hard (Caprara and Fischetti, "{0,1/2}-Chvatal-Gomory cuts", Math.
 * Programming 74, 1996). This is the heuristic of Koster, Zymolka and Kutschka ("Algorithms to
 * separate {0,1/2}-Chvatal-Gomory cuts", Algorithmica 55, 2009), in the form CP-SAT and SCIP use:
 * columns at a bound leave the matrix, a column in one row only moves its distance into that row's
 * slack, rows of slack 1 or more leave, and each row of zero slack eliminates its column of largest
 * distance from the other rows (a Gaussian elimination step over GF(2) that costs nothing). Rows
 * that end with an odd right side and a small total of slack and distance are the cuts. The caller
 * turns each set of rows into an exact integer aggregate and rounds it with the MIR of {@link
 * MirCut} with divisor 2, which for a half-integral aggregate is the zero-half cut.
 *
 * <p>Everything is deterministic (fixed orders, ties by index) and the elimination stops after a
 * fixed amount of work.
 *
 * @author Radoslaw Szymanek and Claude
 * @version 5.0
 */
final class ZeroHalfCuts {

  // a column whose LP value is this close to a bound costs nothing in a cut
  private static final double AT_BOUND = 1e-6;

  // the least violation of a cut (in the scale of the half-rounding: at most 1/2)
  private static final double MIN_VIOLATION = 0.1;

  // the most rows a pivot row may combine
  private static final int MAX_COMBINED = 100;

  // the most columns of the GF(2) matrix: beyond it the separator does nothing
  static final int MAX_COLUMNS = 20_000;

  // the most words XORed in the elimination
  private static final long MAX_WORK = 20_000_000L;

  private ZeroHalfCuts() {}

  /**
   * Returns the sets of rows of the most violated zero-half cuts, each as the ascending indices of
   * the rows given, most violated first.
   *
   * @param columns the columns of each row {@code sum w x <= b}
   * @param weights the weights of each row, aligned with its columns
   * @param odd whether the right side of each row is odd once the odd columns are at their nearer
   *     bound
   * @param slack the slack of each row at the LP solution, at least 0
   * @param distance the distance of each column's LP value to its nearer bound
   * @param maxCuts the most sets returned
   * @return the sets of rows
   */
  static List<int[]> separate(
      int[][] columns,
      long[][] weights,
      boolean[] odd,
      double[] slack,
      double[] distance,
      int maxCuts) {
    int rows = columns.length;
    // the columns that cost something and have an odd weight somewhere, numbered compactly
    int[] index = new int[distance.length];
    Arrays.fill(index, -1);
    int count = 0;
    for (int i = 0; i < rows; i++) {
      for (int k = 0; k < columns[i].length; k++) {
        int j = columns[i][k];
        if ((weights[i][k] & 1) != 0 && distance[j] > AT_BOUND && index[j] < 0) {
          index[j] = count++;
        }
      }
    }
    if (count > MAX_COLUMNS) {
      return List.of();
    }
    double[] w = new double[count];
    for (int j = 0; j < distance.length; j++) {
      if (index[j] >= 0) {
        w[index[j]] = distance[j];
      }
    }
    int colWords = Math.max(1, (count + 63) >>> 6);
    int rowWords = (rows + 63) >>> 6;
    long[][] bits = new long[rows][colWords];
    long[][] mult = new long[rows][rowWords];
    boolean[] parity = odd.clone();
    double[] s = slack.clone();
    int[] degree = new int[count];
    for (int i = 0; i < rows; i++) {
      mult[i][i >>> 6] |= 1L << i;
      for (int k = 0; k < columns[i].length; k++) {
        int j = columns[i][k];
        if ((weights[i][k] & 1) != 0 && index[j] >= 0) {
          int c = index[j];
          // a column twice in a row cancels over GF(2)
          long bit = 1L << c;
          if ((bits[i][c >>> 6] & bit) != 0) {
            bits[i][c >>> 6] &= ~bit;
            degree[c]--;
          } else {
            bits[i][c >>> 6] |= bit;
            degree[c]++;
          }
        }
      }
    }
    boolean[] dead = new boolean[rows];
    for (int i = 0; i < rows; i++) {
      dead[i] = s[i] >= 1 - AT_BOUND;
      if (dead[i]) {
        dropRow(bits[i], degree);
      }
    }
    foldSingletons(bits, s, w, degree, dead);
    Integer[] order = new Integer[rows];
    for (int i = 0; i < rows; i++) {
      order[i] = i;
    }
    int[] size = new int[rows];
    for (int i = 0; i < rows; i++) {
      size[i] = popCount(bits[i]);
    }
    Arrays.sort(order, Comparator.comparingInt((Integer i) -> size[i]).thenComparingInt(i -> i));
    long work = 0;
    for (int next = 0; next < rows && work <= MAX_WORK; next++) {
      int r = order[next];
      boolean pivots = !dead[r] && s[r] <= AT_BOUND && popCount(mult[r]) <= MAX_COMBINED;
      int pivot = pivots ? largest(bits[r], w) : -1;
      if (pivot < 0) {
        continue;
      }
      long bit = 1L << pivot;
      int word = pivot >>> 6;
      for (int q = 0; q < rows; q++) {
        if (q != r && !dead[q] && (bits[q][word] & bit) != 0) {
          for (int t = 0; t < colWords; t++) {
            long both = bits[q][t] & bits[r][t];
            long before = bits[q][t];
            bits[q][t] ^= bits[r][t];
            // the degrees follow the columns that enter or leave row q
            long changed = before ^ bits[q][t];
            while (changed != 0) {
              int c = (t << 6) + Long.numberOfTrailingZeros(changed);
              changed &= changed - 1;
              degree[c] += (both & (1L << (c & 63))) == 0 ? 1 : -1;
            }
          }
          for (int t = 0; t < rowWords; t++) {
            mult[q][t] ^= mult[r][t];
          }
          parity[q] ^= parity[r];
          s[q] += s[r];
          work += colWords + rowWords;
          if (s[q] >= 1 - AT_BOUND) {
            dead[q] = true;
            dropRow(bits[q], degree);
          }
        }
      }
      // the pivot column is now in row r only: its distance goes to the slack of r
      if ((bits[r][word] & bit) != 0) {
        bits[r][word] &= ~bit;
        degree[pivot]--;
        s[r] += w[pivot];
      }
      if (s[r] >= 1 - AT_BOUND) {
        dead[r] = true;
        dropRow(bits[r], degree);
      }
      foldSingletons(bits, s, w, degree, dead);
    }
    List<Integer> found = new ArrayList<>();
    double[] violation = new double[rows];
    for (int i = 0; i < rows; i++) {
      if (dead[i] || !parity[i]) {
        continue;
      }
      double cost = s[i];
      for (int t = 0; t < colWords; t++) {
        long b = bits[i][t];
        while (b != 0) {
          cost += w[(t << 6) + Long.numberOfTrailingZeros(b)];
          b &= b - 1;
        }
      }
      violation[i] = (1 - cost) / 2;
      if (violation[i] >= MIN_VIOLATION) {
        found.add(i);
      }
    }
    found.sort(Comparator.comparingDouble((Integer i) -> -violation[i]).thenComparingInt(i -> i));
    List<int[]> sets = new ArrayList<>();
    List<long[]> taken = new ArrayList<>();
    for (int next = 0; next < found.size() && sets.size() < maxCuts; next++) {
      int i = found.get(next);
      boolean duplicate = false;
      for (long[] m : taken) {
        duplicate |= Arrays.equals(m, mult[i]);
      }
      if (duplicate) {
        continue;
      }
      taken.add(mult[i]);
      int[] set = new int[popCount(mult[i])];
      int k = 0;
      for (int t = 0; t < rowWords; t++) {
        long b = mult[i][t];
        while (b != 0) {
          set[k++] = (t << 6) + Long.numberOfTrailingZeros(b);
          b &= b - 1;
        }
      }
      sets.add(set);
    }
    return sets;
  }

  // the column of the row with the largest distance, the first on ties, or -1 if the row is empty
  private static int largest(long[] row, double[] w) {
    int pivot = -1;
    for (int word = 0; word < row.length; word++) {
      long b = row[word];
      while (b != 0) {
        int c = (word << 6) + Long.numberOfTrailingZeros(b);
        b &= b - 1;
        if (pivot < 0 || w[c] > w[pivot]) {
          pivot = c;
        }
      }
    }
    return pivot;
  }

  // a column left in one live row only: its distance goes to that row's slack, which costs the
  // same in every combination that row enters
  private static void foldSingletons(
      long[][] bits, double[] s, double[] w, int[] degree, boolean[] dead) {
    boolean again = true;
    while (again) {
      again = false;
      for (int i = 0; i < bits.length; i++) {
        if (dead[i]) {
          continue;
        }
        for (int t = 0; t < bits[i].length; t++) {
          long b = bits[i][t];
          while (b != 0) {
            int c = (t << 6) + Long.numberOfTrailingZeros(b);
            b &= b - 1;
            if (degree[c] == 1) {
              bits[i][t] &= ~(1L << (c & 63));
              degree[c] = 0;
              s[i] += w[c];
            }
          }
        }
        if (s[i] >= 1 - AT_BOUND) {
          dead[i] = true;
          again |= dropRow(bits[i], degree);
        }
      }
    }
  }

  // removes the columns of a row that leaves, and says whether a column became a singleton
  private static boolean dropRow(long[] bits, int[] degree) {
    boolean single = false;
    for (int t = 0; t < bits.length; t++) {
      long b = bits[t];
      while (b != 0) {
        int c = (t << 6) + Long.numberOfTrailingZeros(b);
        b &= b - 1;
        degree[c]--;
        single |= degree[c] == 1;
      }
      bits[t] = 0;
    }
    return single;
  }

  private static int popCount(long[] words) {
    int c = 0;
    for (long word : words) {
      c += Long.bitCount(word);
    }
    return c;
  }
}
