/*
 * TableCompressor.java
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

package org.jacop.constraints.table;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.core.IntVar;

/**
 * It compresses a table of tuples of values into fewer hybrid tuples with the same solutions: the
 * tuples that differ only in one column are merged into one tuple with {@code in S} on that column,
 * or {@code *} when S covers the domain of the column (Katsirelos and Walsh, CP 2007, in the greedy
 * form used to build short and compressed tables). Every tuple must be within the domains.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class TableCompressor {

  private TableCompressor() {}

  /**
   * It compresses a table. The values of each tuple must be in the domains of the variables.
   *
   * @param x the variables of the columns.
   * @param tuples the tuples, without duplicates.
   * @return the compressed tuples, equivalent to the tuples on the domains of the variables, or
   *     null when no two tuples differ in one column only.
   */
  public static Restriction[][] compress(IntVar[] x, int[][] tuples) {
    return compress(x, tuples, true);
  }

  /**
   * It compresses a table. The values of each tuple must be in the domains of the variables.
   *
   * @param x the variables of the columns.
   * @param tuples the tuples, without duplicates.
   * @param sets true to merge into sets of values, false to merge only rows covering a whole domain
   *     into {@code *}.
   * @return the compressed tuples, equivalent to the tuples on the domains of the variables, or
   *     null when no two tuples differ in one column only.
   */
  public static Restriction[][] compress(IntVar[] x, int[][] tuples, boolean sets) {
    int arity = x.length;
    if (!mayMerge(tuples, arity)) {
      return null;
    }
    // cells[t][i] is the sorted set of values tuple t allows in column i.
    int[][][] cells = new int[tuples.length][arity][];
    for (int t = 0; t < tuples.length; t++) {
      for (int i = 0; i < arity; i++) {
        cells[t][i] = new int[] {tuples[t][i]};
      }
    }
    List<int[][]> rows = new ArrayList<>(Arrays.asList(cells));
    boolean merged = true;
    while (merged && rows.size() > 1) {
      merged = false;
      for (int i = 0; i < arity; i++) {
        int before = rows.size();
        rows = mergeColumn(rows, i, x[i].getSize(), sets);
        merged |= rows.size() < before;
      }
    }

    Map<Integer, Restriction> equal = new HashMap<>();
    Restriction[][] result = new Restriction[rows.size()][arity];
    for (int t = 0; t < result.length; t++) {
      int[][] row = rows.get(t);
      for (int i = 0; i < arity; i++) {
        int[] s = row[i];
        if (s.length == 1) {
          result[t][i] = equal.computeIfAbsent(s[0], Restriction::eq);
        } else if (s.length == x[i].getSize()) {
          result[t][i] = Restriction.any();
        } else {
          result[t][i] = Restriction.in(s);
        }
      }
    }
    return result;
  }

  /**
   * It tells whether two tuples may be equal except in one column, by comparing the hashes of the
   * tuples without each column; it is much cheaper than a merge pass.
   */
  private static boolean mayMerge(int[][] tuples, int arity) {
    long[] hashes = new long[tuples.length];
    for (int i = 0; i < arity; i++) {
      for (int t = 0; t < tuples.length; t++) {
        long h = 1;
        for (int j = 0; j < arity; j++) {
          if (j != i) {
            h = h * 1_000_003L + tuples[t][j];
          }
        }
        hashes[t] = h;
      }
      Arrays.sort(hashes);
      for (int t = 1; t < hashes.length; t++) {
        if (hashes[t] == hashes[t - 1]) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * It merges the rows that are equal except in column i when they cover the whole domain of the
   * column, or into a set of values when sets are allowed.
   */
  private static List<int[][]> mergeColumn(
      List<int[][]> rows, int i, int domainSize, boolean sets) {
    Map<RowKey, List<int[][]>> groups = new HashMap<>();
    List<List<int[][]>> order = new ArrayList<>();
    for (int[][] row : rows) {
      List<int[][]> group = groups.computeIfAbsent(new RowKey(row, i), k -> new ArrayList<>());
      if (group.isEmpty()) {
        order.add(group);
      }
      group.add(row);
    }
    if (order.size() == rows.size()) {
      return rows;
    }
    List<int[][]> result = new ArrayList<>();
    for (List<int[][]> group : order) {
      int[] u = group.get(0)[i];
      for (int k = 1; k < group.size(); k++) {
        u = union(u, group.get(k)[i]);
      }
      if (group.size() > 1 && (sets || u.length == domainSize)) {
        int[][] merged = group.get(0).clone();
        merged[i] = u;
        result.add(merged);
      } else {
        result.addAll(group);
      }
    }
    return result;
  }

  private static int[] union(int[] a, int[] b) {
    int[] u = new int[a.length + b.length];
    int n = 0;
    int p = 0;
    int q = 0;
    while (p < a.length || q < b.length) {
      int v;
      if (q == b.length || p < a.length && a[p] < b[q]) {
        v = a[p++];
      } else if (p == a.length || b[q] < a[p]) {
        v = b[q++];
      } else {
        v = a[p++];
        q++;
      }
      u[n++] = v;
    }
    return n == u.length ? u : Arrays.copyOf(u, n);
  }

  /** A row without one column, compared by the values of the other cells. */
  private static final class RowKey {
    private final int[][] row;
    private final int skip;
    private final int hash;

    RowKey(int[][] row, int skip) {
      this.row = row;
      this.skip = skip;
      int h = 1;
      for (int i = 0; i < row.length; i++) {
        if (i != skip) {
          h = 31 * h + Arrays.hashCode(row[i]);
        }
      }
      this.hash = h;
    }

    @Override
    public int hashCode() {
      return hash;
    }

    @Override
    public boolean equals(Object o) {
      if (!(o instanceof RowKey other) || other.hash != hash) {
        return false;
      }
      for (int i = 0; i < row.length; i++) {
        if (i != skip && !Arrays.equals(row[i], other.row[i])) {
          return false;
        }
      }
      return true;
    }
  }
}
