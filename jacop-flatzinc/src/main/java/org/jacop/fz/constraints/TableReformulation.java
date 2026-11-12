/*
 * TableReformulation.java
 * <p>
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
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Exact reformulation of a positive table at posting. A table whose rows are distinct is split, as
 * long as one of these rules applies, into
 *
 * <ul>
 *   <li>a unary constraint {@code x_j in S_j} for a <em>free column</em> j: the table is the
 *       product of its projection on the other columns and the set S_j of the values of column j,
 *       so the column is dropped (a column with one value is the special case that fixes x_j); a
 *       <em>Cartesian</em> table, the product of all its columns, ends as unary constraints only;
 *   <li>a binary table {@code (x_i, x_j)} for a <em>functional dependency</em> {@code x_i -> x_j}
 *       (the value of column i determines the value of column j in every row) of a table with at
 *       least three columns: the table is the join of its projection without column j and the pairs
 *       of values of columns i and j, so column j is dropped from it.
 * </ul>
 *
 * <p>Every rule writes the table as a join of two parts that share at most one variable, so the
 * parts form a Berge-acyclic network and generalised arc consistency on the parts prunes exactly
 * what it prunes on the table. The parts are smaller, and their explanations under lazy clause
 * generation name fewer variables. The functional dependency rule is the one of H. Cambazard and B.
 * O'Sullivan, Reformulating Positive Table Constraints Using Functional Dependencies, CP 2008, LNCS
 * 5202, pp. 418-432, restricted to dependencies with a one-column left-hand side.
 *
 * <p>{@code -Dorg.jacop.fz.tableReformulation=false} turns it off; tables whose rows times columns
 * squared exceed {@code org.jacop.fz.tableReformulation.work} (5 * 10^7) are left as they are.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class TableReformulation {

  static final long MAX_WORK = Long.getLong("org.jacop.fz.tableReformulation.work", 50_000_000L);

  /**
   * A unary part: the variable of the column takes one of the values.
   *
   * @param column the column of the table.
   * @param values the values, in increasing order.
   */
  record Unary(int column, int[] values) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Unary u && column == u.column && Arrays.equals(values, u.values);
    }

    @Override
    public int hashCode() {
      return 31 * column + Arrays.hashCode(values);
    }

    @Override
    public String toString() {
      return "Unary[column=" + column + ", values=" + Arrays.toString(values) + "]";
    }
  }

  /**
   * A binary part over two columns, the second a function of the first.
   *
   * @param from the column that determines the other.
   * @param to the determined column.
   * @param pairs the distinct pairs (value of from, value of to).
   * @param identity true when every pair has twice the same value (the columns are equal).
   */
  record Binary(int from, int to, int[][] pairs, boolean identity) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Binary b
          && from == b.from
          && to == b.to
          && identity == b.identity
          && Arrays.deepEquals(pairs, b.pairs);
    }

    @Override
    public int hashCode() {
      return 31 * (31 * from + to) + Arrays.deepHashCode(pairs);
    }

    @Override
    public String toString() {
      return "Binary[from=" + from + ", to=" + to + ", pairs=" + Arrays.deepToString(pairs) + "]";
    }
  }

  /**
   * The parts of a reformulated table.
   *
   * @param unary the unary parts.
   * @param binary the binary parts.
   * @param rest the columns of the remaining table, in their order, empty when no table remains.
   * @param restRows the distinct rows of the remaining table over those columns.
   */
  record Result(List<Unary> unary, List<Binary> binary, int[] rest, int[][] restRows) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Result r
          && unary.equals(r.unary)
          && binary.equals(r.binary)
          && Arrays.equals(rest, r.rest)
          && Arrays.deepEquals(restRows, r.restRows);
    }

    @Override
    public int hashCode() {
      return 31 * (31 * unary.hashCode() + binary.hashCode()) + Arrays.hashCode(rest);
    }

    @Override
    public String toString() {
      return "Result[unary="
          + unary
          + ", binary="
          + binary
          + ", rest="
          + Arrays.toString(rest)
          + ", rows="
          + restRows.length
          + "]";
    }
  }

  private TableReformulation() {}

  /**
   * It tells if the reformulation is on.
   *
   * @return false if the system property org.jacop.fz.tableReformulation is false.
   */
  static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.tableReformulation"));
  }

  /**
   * It reformulates a table.
   *
   * @param table the rows, at least one, all of the same length of at least two; repeated rows are
   *     allowed.
   * @return the parts, or null when no rule applies (or the table is too large to check).
   */
  static Result reformulate(int[][] table) {
    int n = table[0].length;
    if (n < 2 || (long) table.length * n * n > MAX_WORK) {
      return null;
    }
    // the values of each column coded 0..k-1
    int[][] values = new int[n][];
    int[][] rows = code(table, values);
    boolean[] active = new boolean[n];
    Arrays.fill(active, true);
    int m = n;
    List<Unary> unary = new ArrayList<>();
    List<Binary> binary = new ArrayList<>();
    boolean changed = true;
    while (changed && m > 0) {
      changed = false;
      for (int j = 0; j < n && m > 0; j++) {
        if (!active[j]) {
          continue;
        }
        if (m == 1) {
          unary.add(new Unary(j, present(rows, j, values[j])));
          active[j] = false;
          m = 0;
          break;
        }
        int[][] projected = freeColumn(rows, j, active, values[j].length);
        if (projected != null) {
          unary.add(new Unary(j, present(rows, j, values[j])));
          active[j] = false;
          m--;
          rows = projected;
          changed = true;
        }
      }
      for (int i = 0; i < n && m >= 3; i++) {
        for (int j = 0; j < n && m >= 3 && active[i]; j++) {
          if (i != j && active[j] && dependent(rows, i, j, values[i].length)) {
            binary.add(pairs(rows, i, j, values));
            active[j] = false;
            m--;
            changed = true;
          }
        }
      }
    }
    if (m == n) {
      return null;
    }
    int[] rest = new int[m];
    int k = 0;
    for (int j = 0; j < n; j++) {
      if (active[j]) {
        rest[k++] = j;
      }
    }
    int[][] restRows = new int[m == 0 ? 0 : rows.length][m];
    for (int r = 0; r < restRows.length; r++) {
      for (int c = 0; c < m; c++) {
        restRows[r][c] = values[rest[c]][rows[r][rest[c]]];
      }
    }
    return new Result(unary, binary, rest, restRows);
  }

  // the distinct rows with every value replaced by its code in values[column]
  private static int[][] code(int[][] table, int[][] values) {
    int n = table[0].length;
    int[][] rows = new int[table.length][n];
    for (int c = 0; c < n; c++) {
      Map<Integer, Integer> index = new HashMap<>();
      for (int[] row : table) {
        index.putIfAbsent(row[c], 0);
      }
      int[] sorted = index.keySet().stream().mapToInt(Integer::intValue).sorted().toArray();
      for (int v = 0; v < sorted.length; v++) {
        index.put(sorted[v], v);
      }
      values[c] = sorted;
      for (int r = 0; r < table.length; r++) {
        rows[r][c] = index.get(table[r][c]);
      }
    }
    Set<Key> seen = new HashSet<>();
    int kept = 0;
    for (int[] row : rows) {
      if (seen.add(new Key(row))) {
        rows[kept++] = row;
      }
    }
    return kept == rows.length ? rows : Arrays.copyOf(rows, kept);
  }

  // the values of column j that occur in the rows, in increasing order
  private static int[] present(int[][] rows, int j, int[] values) {
    boolean[] seen = new boolean[values.length];
    for (int[] row : rows) {
      seen[row[j]] = true;
    }
    int[] out = new int[values.length];
    int k = 0;
    for (int v = 0; v < values.length; v++) {
      if (seen[v]) {
        out[k++] = values[v];
      }
    }
    return Arrays.copyOf(out, k);
  }

  /*
   * The distinct rows of the projection without column j when the table is that projection times
   * the values of column j, null otherwise. The rows are distinct, so the table is such a product
   * exactly when every value of j occurs equally often and the projection has rows / |S_j| rows.
   */
  private static int[][] freeColumn(int[][] rows, int j, boolean[] active, int codes) {
    int[] count = new int[codes];
    int k = 0;
    for (int[] row : rows) {
      if (count[row[j]]++ == 0) {
        k++;
      }
    }
    if (rows.length % k != 0) {
      return null;
    }
    int each = rows.length / k;
    for (int c : count) {
      if (c != 0 && c != each) {
        return null;
      }
    }
    // a projected row keeps column j as -1, so it compares on the other active columns only
    Set<Key> seen = new HashSet<>();
    int[][] projected = new int[each][];
    int p = 0;
    for (int[] row : rows) {
      int[] q = row.clone();
      for (int c = 0; c < q.length; c++) {
        if (!active[c] || c == j) {
          q[c] = -1;
        }
      }
      if (seen.add(new Key(q))) {
        if (p == each) {
          return null;
        }
        projected[p++] = row;
      }
    }
    return p == each ? projected : null;
  }

  // true when the value of column i determines the value of column j in every row
  private static boolean dependent(int[][] rows, int i, int j, int codes) {
    int[] f = new int[codes];
    Arrays.fill(f, -1);
    for (int[] row : rows) {
      int a = row[i];
      if (f[a] == -1) {
        f[a] = row[j];
      } else if (f[a] != row[j]) {
        return false;
      }
    }
    return true;
  }

  private static Binary pairs(int[][] rows, int i, int j, int[][] values) {
    int[] f = new int[values[i].length];
    Arrays.fill(f, -1);
    for (int[] row : rows) {
      f[row[i]] = row[j];
    }
    List<int[]> out = new ArrayList<>();
    boolean identity = true;
    for (int a = 0; a < f.length; a++) {
      if (f[a] != -1) {
        int x = values[i][a];
        int y = values[j][f[a]];
        out.add(new int[] {x, y});
        identity &= x == y;
      }
    }
    return new Binary(i, j, out.toArray(new int[0][]), identity);
  }

  // a row compared by content
  private static final class Key {
    private final int[] row;
    private final int hash;

    Key(int[] row) {
      this.row = row;
      this.hash = Arrays.hashCode(row);
    }

    @Override
    public boolean equals(Object o) {
      return o instanceof Key k && hash == k.hash && Arrays.equals(row, k.row);
    }

    @Override
    public int hashCode() {
      return hash;
    }
  }
}
