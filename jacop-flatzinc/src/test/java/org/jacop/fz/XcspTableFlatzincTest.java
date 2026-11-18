/*
 * XcspTableFlatzincTest.java
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks jacop_short_table_int (a table whose value star matches any value) and
 * jacop_negative_table_int (forbidden tuples), which JaCoP's mznlib posts for the short and
 * negative tables of the XCSP3 bench, against brute force on random tables over variables with
 * holes, with repeated variables in the scope and with and without lazy clause generation.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class XcspTableFlatzincTest {

  private static final int STAR = -9;

  @TempDir Path tmp;

  @Test
  void rowOfStarsAllowsEverything() throws IOException {
    int[][] rows = {{1, STAR}, {STAR, STAR}};
    String fzn = model(new int[] {0, 1}, 2, rows, true);
    assertEquals(16, solveAll(fzn).size());
  }

  @Test
  void repeatedVariableNeedsEqualValues() throws IOException {
    // x0 occurs twice: the row (1, 3) cannot match, the row (3, *) gives x0 = 3
    int[][] rows = {{1, 3}, {3, STAR}};
    String fzn = model(new int[] {0, 0}, 1, rows, true);
    assertEquals(Set.of("x = array1d(1..1, [3]);"), solveAll(fzn));
  }

  @Test
  void randomShortTablesMatchBruteForce() throws IOException {
    randomTables(true, 20261101);
  }

  @Test
  void randomNegativeTablesMatchBruteForce() throws IOException {
    randomTables(false, 20261102);
  }

  @Test
  void sharedShortTablesMatchBruteForce() throws IOException {
    sharedTables("short", 20261116);
  }

  @Test
  void sharedTablesMatchBruteForce() throws IOException {
    sharedTables("table", 20261117);
  }

  @Test
  void sharedNegativeTablesMatchBruteForce() throws IOException {
    sharedTables("negative", 20261118);
  }

  /**
   * Tables with the same rows given under two names (MiniZinc writes a large table once for every
   * few constraints) and posted on several scopes, one of them over a variable with a smaller
   * domain, so that the front end keeps the arrays once and the short tables share the index of
   * their rows. Each table has more than 1,024 entries, the length from which arrays are kept once.
   */
  private void sharedTables(String kind, long seed) throws IOException {
    Random random = new Random(seed);
    int arity = 3;
    int vars = 4;
    int[][] scopes = {{0, 1, 2}, {1, 2, 3}, {3, 0, 1}, {2, 3, 0}};
    for (int run = 0; run < 4; run++) {
      boolean positive = !"negative".equals(kind);
      int[][] rows = new int[360][arity];
      for (int[] row : rows) {
        for (int i = 0; i < arity; i++) {
          row[i] = "short".equals(kind) && random.nextInt(4) == 0 ? STAR : random.nextInt(5);
        }
      }
      if (positive) {
        // few rows allowed: a solution must pick rows that agree on the shared variables
        rows = Arrays.copyOf(rows, 6 + random.nextInt(8));
        int[][] padded = new int[360][];
        for (int r = 0; r < padded.length; r++) {
          padded[r] = rows[r % rows.length];
        }
        rows = padded;
      }
      String cells =
          Arrays.stream(rows)
              .flatMapToInt(Arrays::stream)
              .mapToObj(String::valueOf)
              .collect(Collectors.joining(",", "[", "]"));
      StringBuilder fzn = new StringBuilder();
      String predicate =
          switch (kind) {
            case "short" -> "jacop_short_table_int";
            case "negative" -> "jacop_negative_table_int";
            default -> "jacop_table_int";
          };
      fzn.append("predicate ")
          .append(predicate)
          .append("(array [int] of var int: x,array [int] of int: t")
          .append("short".equals(kind) ? ",int: star" : "")
          .append(");\n");
      for (String name : new String[] {"T1", "T2"}) {
        fzn.append("array [1..")
            .append(rows.length * arity)
            .append("] of int: ")
            .append(name)
            .append(" = ")
            .append(cells)
            .append(";\n");
      }
      for (int i = 0; i < vars; i++) {
        // x3 has the smaller domain, so the rows kept for its scopes differ
        fzn.append(i == 3 ? "var {0,1}: x" : "var {0,1,3,4}: x").append(i).append(";\n");
      }
      fzn.append("array [1..")
          .append(vars)
          .append("] of var int: x:: output_array([1..")
          .append(vars)
          .append("]) = [x0,x1,x2,x3];\n");
      for (int c = 0; c < scopes.length; c++) {
        fzn.append("constraint ")
            .append(predicate)
            .append('(')
            .append(
                Arrays.stream(scopes[c])
                    .mapToObj(i -> "x" + i)
                    .collect(Collectors.joining(",", "[", "]")))
            .append(c % 2 == 0 ? ",T1" : ",T2")
            .append("short".equals(kind) ? "," + STAR : "")
            .append(");\n");
      }
      fzn.append("solve satisfy;\n");
      Set<String> expected = new TreeSet<>();
      int[][] tableRows = rows;
      int[] x = new int[vars];
      for (int a = 0; a < 4 * 4 * 4 * 2; a++) {
        int[] values = {0, 1, 3, 4};
        x[0] = values[a % 4];
        x[1] = values[a / 4 % 4];
        x[2] = values[a / 16 % 4];
        x[3] = a / 64;
        boolean all = true;
        for (int[] scope : scopes) {
          boolean match = Arrays.stream(tableRows).anyMatch(row -> allowed(x, scope, row));
          all &= match == positive;
        }
        if (all) {
          expected.add(
              Arrays.stream(x)
                  .mapToObj(String::valueOf)
                  .collect(Collectors.joining(", ", "x = array1d(1..4, [", "]);")));
        }
      }
      String message = kind + " run " + run;
      assertEquals(expected, solveAll(fzn.toString()), message);
      assertEquals(expected, solveAll(fzn.toString(), "--lcg", "off"), message);
    }
  }

  @Test
  void listsDifferMatchesBruteForce() throws IOException {
    // short tables saying two lists differ (BinaryPuzzle of XCSP 2023) become AllDifferentLists
    Random random = new Random(20261116);
    for (int run = 0; run < 40; run++) {
      int[] values = random.nextBoolean() ? new int[] {0, 1} : new int[] {0, 1, 3};
      int n = 1 + random.nextInt(2);
      int m = 2 + random.nextInt(3);
      int vars = Math.min(m * n, values.length == 2 ? 7 : 5);
      int[][] lists = new int[m][n];
      for (int[] list : lists) {
        for (int k = 0; k < n; k++) {
          list[k] = random.nextInt(vars);
        }
      }
      // all pairs (one AllDifferentLists) or some of them (one per pair)
      boolean all = random.nextBoolean();
      boolean dropRow = random.nextInt(5) == 0;
      StringBuilder constraints = new StringBuilder();
      List<int[]> pairs = new ArrayList<>();
      for (int i = 0; i < m; i++) {
        for (int j = i + 1; j < m; j++) {
          if (all || random.nextBoolean()) {
            pairs.add(new int[] {i, j});
          }
        }
      }
      List<int[][]> tables = new ArrayList<>();
      for (int[] pair : pairs) {
        List<int[]> rows = new ArrayList<>();
        for (int k = 0; k < n; k++) {
          for (int a : values) {
            for (int b : values) {
              if (a != b) {
                int[] row = new int[2 * n];
                Arrays.fill(row, STAR);
                row[k] = a;
                row[n + k] = b;
                rows.add(row);
              }
            }
          }
        }
        if (dropRow) {
          rows.remove(random.nextInt(rows.size()));
        }
        int[][] table = rows.toArray(new int[0][]);
        tables.add(table);
        int[] scope = new int[2 * n];
        System.arraycopy(lists[pair[0]], 0, scope, 0, n);
        System.arraycopy(lists[pair[1]], 0, scope, n, n);
        constraints.append(shortTable(scope, table));
      }
      Set<String> expected = new TreeSet<>();
      enumerateLists(new int[vars], 0, values, lists, pairs, tables, expected);
      String fzn = header(vars, values) + constraints + "solve satisfy;\n";
      String message = "run " + run + "\n" + fzn;
      assertEquals(expected, solveAll(fzn), message);
      assertEquals(expected, solveAll(fzn, "--lcg", "off"), message);
    }
  }

  /**
   * Tables that are one row away from saying that two lists differ, so that the detector must leave
   * them alone: a row fixing both lists to the same value, a row fixing a third cell, a row whose
   * two cells are not the same position of both lists, a row fixing two cells of one list, or a
   * list with a variable twice. A detector that took any of them for "the lists differ" and
   * replaced the table would add solutions.
   */
  @Test
  void listsDifferNearMissesMatchBruteForce() throws IOException {
    Random random = new Random(20261118);
    int fired = 0;
    for (int run = 0; run < 60; run++) {
      int[] values = random.nextBoolean() ? new int[] {0, 1} : new int[] {0, 1, 3};
      int n = 2;
      int m = 2 + random.nextInt(2);
      int vars = m * n;
      int[][] lists = new int[m][n];
      for (int i = 0; i < m; i++) {
        for (int k = 0; k < n; k++) {
          lists[i][k] = i * n + k;
        }
      }
      int perturb = run % 6;
      if (perturb == 5) {
        lists[0][1] = lists[0][0];
      }
      StringBuilder constraints = new StringBuilder();
      List<int[]> pairs = new ArrayList<>();
      for (int i = 0; i < m; i++) {
        for (int j = i + 1; j < m; j++) {
          pairs.add(new int[] {i, j});
        }
      }
      List<int[][]> tables = new ArrayList<>();
      for (int p = 0; p < pairs.size(); p++) {
        int[] pair = pairs.get(p);
        List<int[]> rows = new ArrayList<>();
        for (int k = 0; k < n; k++) {
          for (int a : values) {
            for (int b : values) {
              if (a != b) {
                int[] row = new int[2 * n];
                Arrays.fill(row, STAR);
                row[k] = a;
                row[n + k] = b;
                rows.add(row);
              }
            }
          }
        }
        if (p == 0) {
          int[] row = rows.get(random.nextInt(rows.size()));
          int k = row[0] != STAR ? 0 : 1;
          switch (perturb) {
            case 1 -> row[n + k] = row[k]; // the same value in both lists
            case 2 -> row[1 - k] = values[random.nextInt(values.length)]; // a third cell
            case 3 -> { // the second cell at another position of the other list
              row[n + 1 - k] = row[n + k];
              row[n + k] = STAR;
            }
            case 4 -> { // both cells in the first list
              row[1 - k] = row[n + k];
              row[n + k] = STAR;
            }
            default -> {
              // unchanged: the detector replaces the table
            }
          }
        }
        int[][] table = rows.toArray(new int[0][]);
        tables.add(table);
        int[] scope = new int[2 * n];
        System.arraycopy(lists[pair[0]], 0, scope, 0, n);
        System.arraycopy(lists[pair[1]], 0, scope, n, n);
        constraints.append(shortTable(scope, table));
      }
      Set<String> expected = new TreeSet<>();
      enumerateLists(new int[vars], 0, values, lists, pairs, tables, expected);
      String fzn = header(vars, values) + constraints + "solve satisfy;\n";
      String message = "run " + run + " perturb " + perturb + "\n" + fzn;
      java.util.regex.Matcher detected =
          java.util.regex.Pattern.compile("% lists differ detector: (\\d+) tables")
              .matcher(solve(fzn, "-debug"));
      int replaced = detected.find() ? Integer.parseInt(detected.group(1)) : 0;
      if (perturb == 0) {
        assertEquals(pairs.size(), replaced, message);
        fired++;
      } else {
        assertTrue(replaced < pairs.size(), "replaced " + replaced + "\n" + message);
      }
      assertEquals(expected, solveAll(fzn), message);
      assertEquals(expected, solveAll(fzn, "--lcg", "off"), message);
    }
    assertEquals(10, fired);
  }

  @Test
  void numberedPathMatchesBruteForce() throws IOException {
    // a tour numbered 1..k over random arcs (CalvinPuzzle of XCSP 2023) gets a redundant circuit
    Random random = new Random(20261117);
    for (int run = 0; run < 40; run++) {
      int k = 4 + random.nextInt(3);
      boolean fixedFirst = random.nextBoolean();
      boolean table = random.nextBoolean();
      boolean[][] arc = new boolean[k][k];
      for (int c = 0; c < k; c++) {
        for (int d = 0; d < k; d++) {
          arc[c][d] = c != d && random.nextInt(10) < 5;
        }
        // at least one arc that the cell of value 1 does not make impossible
        int d = 1 + random.nextInt(k - 1);
        arc[c][d == c ? (c + 1) % k == 0 ? 1 : (c + 1) % k : d] = true;
      }
      String fzn = numberedPath(k, arc, fixedFirst, table, random);
      Set<String> expected = new TreeSet<>();
      int[] x = new int[k];
      enumeratePaths(x, 0, new boolean[k + 1], arc, fixedFirst, expected);
      String message = "run " + run + "\n" + fzn;
      assertTrue(
          solve(fzn, "-debug").contains("numbered path detector: circuit over " + k), message);
      assertEquals(expected, solveAll(fzn), message);
      assertEquals(expected, solveAll(fzn, "--lcg", "off"), message);
    }
  }

  /**
   * Numbering models one change away from the pattern, so that the detector must not post its
   * circuit: a cell without its condition, a cell whose condition ends at N - 1, a literal x[d] =
   * x[c] + 2, or a cell whose domain goes past N. A circuit posted on any of them as if it were a
   * numbered path could remove solutions; the solutions are compared with the detector off.
   */
  @Test
  void numberedPathNearMissesKeepTheirSolutions() throws IOException {
    Random random = new Random(20261118);
    int changed = 0;
    for (int run = 0; run < 48; run++) {
      int k = 4 + random.nextInt(2);
      boolean table = run % 2 == 1;
      boolean[][] arc = new boolean[k][k];
      for (int c = 0; c < k; c++) {
        for (int d = 0; d < k; d++) {
          arc[c][d] = c != d && random.nextInt(10) < 6;
        }
        arc[c][(c + 1) % k] = true;
      }
      String fzn = numberedPath(k, arc, false, table, random);
      int c = 1 + random.nextInt(k - 1);
      String near =
          switch (run / 2 % 4) {
            case 0 -> table ? dropTableOf(fzn, "x" + c) : dropLine(fzn, "bool_clause([r" + c + ",");
            case 1 ->
                table
                    ? fzn.replace("[" + k + ",", "[" + (k - 1) + ",")
                    : fzn.replace("int_eq_imp(x" + c + "," + k, "int_eq_imp(x" + c + "," + (k - 1));
            case 2 ->
                table
                    ? fzn.replaceFirst(",1," + STAR, ",2," + STAR)
                    : fzn.replaceFirst("\\],1,e", "],2,e").replaceFirst("\\],-1,e", "],-2,e");
            default ->
                fzn.replace("var 1.." + k + ": x" + c + ";", "var 1.." + (k + 1) + ": x" + c + ";");
          };
      changed += near.equals(fzn) ? 0 : 1;
      String message = "run " + run + "\n" + near;
      if (!near.equals(fzn)) {
        System.err.println(
            "NPNEAR "
                + run / 2 % 4
                + " table="
                + table
                + " circuit="
                + solve(near, "-debug").contains("numbered path detector: circuit"));
      }
      System.setProperty("org.jacop.fz.numberedPath", "false");
      Set<String> expected;
      try {
        expected = solveAll(near);
      } finally {
        System.clearProperty("org.jacop.fz.numberedPath");
      }
      assertEquals(expected, solveAll(near), message);
      assertEquals(expected, solveAll(near, "--lcg", "off"), message);
    }
    assertTrue(changed >= 40, "changed " + changed);
  }

  // the model without the constraint line that contains the given text
  private static String dropLine(String fzn, String text) {
    return Arrays.stream(fzn.split("\n"))
            .filter(l -> !l.contains(text))
            .collect(Collectors.joining("\n"))
        + "\n";
  }

  // the model without the short table whose scope starts with the given variable
  private static String dropTableOf(String fzn, String x) {
    return dropLine(fzn, "jacop_short_table_int([" + x + ",");
  }

  private static String numberedPath(
      int k, boolean[][] arc, boolean fixedFirst, boolean table, Random random) {
    StringBuilder fzn = new StringBuilder();
    StringBuilder constraints = new StringBuilder();
    String[] cell = new String[k];
    for (int c = 0; c < k; c++) {
      cell[c] = c == 0 && fixedFirst ? "1" : "x" + c;
      if (!cell[c].equals("1")) {
        fzn.append("var 1..").append(k).append(": x").append(c).append(";\n");
      }
    }
    for (int c = 0; c < k; c++) {
      List<Integer> next = new ArrayList<>();
      for (int d = 0; d < k; d++) {
        if (arc[c][d]) {
          next.add(d);
        }
      }
      if (table) {
        List<int[]> rows = new ArrayList<>();
        for (int v = 1; v < k; v++) {
          for (int i = 0; i < next.size(); i++) {
            int[] row = new int[next.size() + 1];
            Arrays.fill(row, STAR);
            row[0] = v;
            row[i + 1] = v + 1;
            rows.add(row);
          }
        }
        int[] last = new int[next.size() + 1];
        Arrays.fill(last, STAR);
        last[0] = k;
        rows.add(last);
        String scope =
            cell[c] + next.stream().map(d -> "," + cell[d]).collect(Collectors.joining());
        String cells =
            rows.stream()
                .flatMapToInt(Arrays::stream)
                .mapToObj(String::valueOf)
                .collect(Collectors.joining(","));
        constraints
            .append("constraint jacop_short_table_int([")
            .append(scope)
            .append("],[")
            .append(cells)
            .append("],")
            .append(STAR)
            .append(");\n");
        continue;
      }
      // the literals x[d] = x[c] + 1 as the MiniZinc compiler writes them
      List<String> literals = new ArrayList<>();
      for (int d : next) {
        String e = "e" + c + "_" + d;
        String i = "i" + c + "_" + d;
        if (fixedFirst && d == 0) {
          literals.add("0");
          continue;
        }
        fzn.append("var bool: ").append(e).append(";\nvar 0..1: ").append(i).append(";\n");
        if (fixedFirst && c == 0) {
          constraints.append("constraint int_eq_reif(").append(cell[d]).append(",2,");
        } else if (random.nextBoolean()) {
          constraints.append(
              "constraint int_lin_eq_reif([1,-1],[" + cell[d] + "," + cell[c] + "],1,");
        } else {
          constraints.append(
              "constraint int_lin_eq_reif([-1,1],[" + cell[d] + "," + cell[c] + "],-1,");
        }
        constraints.append(e).append(");\nconstraint bool2int(").append(e).append(',');
        constraints.append(i).append(");\n");
        literals.add(i);
      }
      boolean first = fixedFirst && c == 0;
      fzn.append("var ").append(first ? 1 : 0).append("..").append(next.size());
      fzn.append(": a").append(c).append(";\n");
      constraints
          .append("constraint jacop_among([")
          .append(String.join(",", literals))
          .append("],1..1,a")
          .append(c)
          .append(");\n");
      if (!first) {
        fzn.append("var bool: r").append(c).append(";\nvar bool: q").append(c).append(";\n");
        constraints.append("constraint int_le_imp(1,a").append(c).append(",r").append(c);
        constraints.append(");\nconstraint int_eq_imp(x").append(c).append(',').append(k);
        constraints.append(",q").append(c).append(");\nconstraint bool_clause([r").append(c);
        constraints.append(",q").append(c).append("],[]);\n");
      }
    }
    String all = String.join(",", cell);
    constraints.append("constraint jacop_alldiff([").append(all).append("]);\n");
    fzn.append("array [1..")
        .append(k)
        .append("] of var int: x:: output_array([1..")
        .append(k)
        .append("]) = [")
        .append(all)
        .append("];\n");
    return "predicate jacop_alldiff(array [int] of var int: x);\n"
        + "predicate jacop_among(array [int] of var int: x,set of int: v,var int: n);\n"
        + "predicate jacop_short_table_int(array [int] of var int: x,array [int] of int: t,int: s);\n"
        + "predicate int_le_imp(var int: a,var int: b,var bool: r);\n"
        + "predicate int_eq_imp(var int: a,var int: b,var bool: r);\n"
        + fzn
        + constraints
        + "solve satisfy;\n";
  }

  private static void enumeratePaths(
      int[] x, int c, boolean[] used, boolean[][] arc, boolean fixedFirst, Set<String> solutions) {
    int k = x.length;
    if (c == k) {
      for (int a = 0; a < k; a++) {
        boolean ok = x[a] == k;
        for (int d = 0; d < k && !ok; d++) {
          ok = arc[a][d] && x[d] == x[a] + 1;
        }
        if (!ok) {
          return;
        }
      }
      solutions.add(
          "x = array1d(1.."
              + k
              + ", "
              + Arrays.stream(x)
                  .mapToObj(String::valueOf)
                  .collect(Collectors.joining(", ", "[", "]"))
              + ");");
      return;
    }
    for (int v = 1; v <= k; v++) {
      if (!used[v] && (!fixedFirst || (c == 0) == (v == 1))) {
        used[v] = true;
        x[c] = v;
        enumeratePaths(x, c + 1, used, arc, fixedFirst, solutions);
        used[v] = false;
      }
    }
  }

  private static void enumerateLists(
      int[] x,
      int i,
      int[] values,
      int[][] lists,
      List<int[]> pairs,
      List<int[][]> tables,
      Set<String> out) {
    if (i == x.length) {
      for (int p = 0; p < pairs.size(); p++) {
        int[] a = lists[pairs.get(p)[0]];
        int[] b = lists[pairs.get(p)[1]];
        int[] scope = new int[a.length + b.length];
        System.arraycopy(a, 0, scope, 0, a.length);
        System.arraycopy(b, 0, scope, a.length, b.length);
        if (Arrays.stream(tables.get(p)).noneMatch(row -> allowed(x, scope, row))) {
          return;
        }
      }
      out.add(
          Arrays.stream(x)
              .mapToObj(String::valueOf)
              .collect(Collectors.joining(", ", "x = array1d(1.." + x.length + ", [", "]);")));
      return;
    }
    for (int v : values) {
      x[i] = v;
      enumerateLists(x, i + 1, values, lists, pairs, tables, out);
    }
  }

  private static String header(int vars, int[] values) {
    String domain =
        Arrays.stream(values).mapToObj(String::valueOf).collect(Collectors.joining(",", "{", "}"));
    StringBuilder fzn = new StringBuilder();
    fzn.append(
        "predicate jacop_short_table_int(array [int] of var int: x,array [int] of int: t,"
            + "int: star);\n");
    for (int i = 0; i < vars; i++) {
      fzn.append("var ").append(domain).append(": x").append(i).append(";\n");
    }
    fzn.append("array [1..")
        .append(vars)
        .append("] of var int: x:: output_array([1..")
        .append(vars)
        .append("]) = ")
        .append(
            IntStream.range(0, vars)
                .mapToObj(i -> "x" + i)
                .collect(Collectors.joining(",", "[", "]")))
        .append(";\n");
    return fzn.toString();
  }

  private static String shortTable(int[] scope, int[][] rows) {
    String cells =
        Arrays.stream(rows)
            .flatMapToInt(Arrays::stream)
            .mapToObj(String::valueOf)
            .collect(Collectors.joining(",", "[", "]"));
    String xs =
        Arrays.stream(scope).mapToObj(i -> "x" + i).collect(Collectors.joining(",", "[", "]"));
    return "constraint jacop_short_table_int(" + xs + "," + cells + "," + STAR + ");\n";
  }

  /**
   * Short tables over 0/1 variables whose rows each fix one variable are posted as clauses: rows
   * that fix a variable to a value outside {0, 1} are dropped, a variable fixed to 0 and to 1 makes
   * the table always true, and the star can be 0 when the rows use only 1 (Crypto1 of XCSP 2022).
   */
  @Test
  void clauseShortTablesMatchBruteForce() throws IOException {
    Random random = new Random(20261117);
    for (int run = 0; run < 40; run++) {
      int vars = 1 + random.nextInt(4);
      int arity = 1 + random.nextInt(4);
      int star = random.nextBoolean() ? STAR : 0;
      int[] scope = new int[arity];
      for (int i = 0; i < arity; i++) {
        scope[i] = random.nextInt(vars);
      }
      int[][] rows = new int[1 + random.nextInt(5)][arity];
      for (int[] row : rows) {
        Arrays.fill(row, star);
        int[] values = star == 0 ? new int[] {1, 1, 1, 3} : new int[] {0, 1, 1, 0, 3};
        row[random.nextInt(arity)] = values[random.nextInt(values.length)];
      }
      Set<String> expected = new TreeSet<>();
      for (int a = 0; a < 1 << vars; a++) {
        int[] x = new int[vars];
        for (int i = 0; i < vars; i++) {
          x[i] = a >> i & 1;
        }
        boolean match =
            Arrays.stream(rows)
                .anyMatch(
                    row ->
                        IntStream.range(0, arity)
                            .allMatch(i -> row[i] == star || x[scope[i]] == row[i]));
        if (match) {
          expected.add(
              Arrays.stream(x)
                  .mapToObj(String::valueOf)
                  .collect(Collectors.joining(", ", "x = array1d(1.." + vars + ", [", "]);")));
        }
      }
      String fzn =
          model(scope, vars, rows, true)
              .replace("var {0,1,3,4}:", "var 0..1:")
              .replace("," + STAR + ");\nsolve", "," + star + ");\nsolve");
      String message = "run " + run + "\n" + fzn;
      assertEquals(expected, solveAll(fzn), message);
      assertEquals(expected, solveAll(fzn, "--lcg", "off"), message);
    }
  }

  private void randomTables(boolean positive, long seed) throws IOException {
    Random random = new Random(seed);
    for (int run = 0; run < 30; run++) {
      int vars = 1 + random.nextInt(3);
      int arity = 1 + random.nextInt(4);
      int[] scope = new int[arity];
      for (int i = 0; i < arity; i++) {
        scope[i] = random.nextInt(vars);
      }
      int[][] rows = new int[random.nextInt(6)][arity];
      for (int[] row : rows) {
        for (int i = 0; i < arity; i++) {
          row[i] = positive && random.nextInt(3) == 0 ? STAR : random.nextInt(5);
        }
      }
      Set<String> expected = new TreeSet<>();
      enumerate(new int[vars], 0, scope, rows, positive, expected);
      String fzn = model(scope, vars, rows, positive);
      String message = "run " + run + "\n" + fzn;
      assertEquals(expected, solveAll(fzn), message);
      assertEquals(expected, solveAll(fzn, "--lcg", "off"), message);
    }
  }

  private static boolean allowed(int[] x, int[] scope, int[] row) {
    for (int i = 0; i < scope.length; i++) {
      if (row[i] != STAR && x[scope[i]] != row[i]) {
        return false;
      }
    }
    return true;
  }

  // the variables range over {0, 1, 3, 4}: 2 is a hole
  private static void enumerate(
      int[] x, int i, int[] scope, int[][] rows, boolean positive, Set<String> out) {
    if (i == x.length) {
      boolean match = Arrays.stream(rows).anyMatch(row -> allowed(x, scope, row));
      if (match == positive) {
        out.add(
            Arrays.stream(x)
                .mapToObj(String::valueOf)
                .collect(Collectors.joining(", ", "x = array1d(1.." + x.length + ", [", "]);")));
      }
      return;
    }
    for (int v : new int[] {0, 1, 3, 4}) {
      x[i] = v;
      enumerate(x, i + 1, scope, rows, positive, out);
    }
  }

  private static String model(int[] scope, int vars, int[][] rows, boolean positive) {
    StringBuilder fzn = new StringBuilder();
    fzn.append(
        positive
            ? "predicate jacop_short_table_int(array [int] of var int: x,array [int] of int: t,"
                + "int: star);\n"
            : "predicate jacop_negative_table_int(array [int] of var int: x,"
                + "array [int] of int: t);\n");
    for (int i = 0; i < vars; i++) {
      fzn.append("var {0,1,3,4}: x").append(i).append(";\n");
    }
    fzn.append("array [1..")
        .append(vars)
        .append("] of var int: x:: output_array([1..")
        .append(vars)
        .append("]) = ")
        .append(
            IntStream.range(0, vars)
                .mapToObj(i -> "x" + i)
                .collect(Collectors.joining(",", "[", "]")))
        .append(";\n");
    String cells =
        Arrays.stream(rows)
            .flatMapToInt(Arrays::stream)
            .mapToObj(String::valueOf)
            .collect(Collectors.joining(",", "[", "]"));
    String xs =
        Arrays.stream(scope).mapToObj(i -> "x" + i).collect(Collectors.joining(",", "[", "]"));
    fzn.append("constraint jacop_")
        .append(positive ? "short" : "negative")
        .append("_table_int(")
        .append(xs)
        .append(',')
        .append(cells)
        .append(positive ? "," + STAR : "")
        .append(");\nsolve satisfy;\n");
    return fzn.toString();
  }

  private String solve(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  private Set<String> solveAll(String model, String... options) throws IOException {
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = "-a";
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(solve(model, args).split("----------"))
        .map(String::strip)
        .filter(s -> s.startsWith("x = "))
        .forEach(solutions::add);
    return solutions;
  }
}
