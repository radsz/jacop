/*
 * PartitionSumsFlatzincTest.java
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
import static org.junit.jupiter.api.Assertions.assertFalse;
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
import java.util.function.IntPredicate;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * The implied sums of the FlatZinc front end over unit sums that partition an all_different (the
 * rows and the columns of a grid, as in a heterosquare): random small grids keep exactly their
 * solutions, found by enumeration, and the rule fires when the rows or the columns are such a
 * partition.
 */
class PartitionSumsFlatzincTest {

  @TempDir Path tmp;

  /** The FlatZinc of a random grid model and its solutions by enumeration. */
  private record Model(String fzn, Set<String> bruteForce) {}

  private static Model randomModel(Random random) {
    int rows = 2 + random.nextInt(2);
    int cols = 3 + random.nextInt(rows == 2 ? 2 : 1);
    int cells = rows * cols;
    // values 1..cells (a permutation) or a few more
    int top = cells + random.nextInt(2);
    int[][] domains = new int[cells][];
    for (int i = 0; i < cells; i++) {
      int skip = random.nextInt(4) == 0 ? 1 + random.nextInt(top) : 0;
      domains[i] = IntStream.rangeClosed(1, top).filter(v -> v != skip).toArray();
    }
    boolean colSums = rows >= 3 && random.nextBoolean();
    boolean sumsDifferent = random.nextInt(3) != 0;
    int nSums = rows + (colSums ? cols : 0);
    // the bounds of each sum: around its mean, sometimes too narrow
    int mean = (top + 1) * cols / 2;
    int[] lo = new int[nSums];
    int[] hi = new int[nSums];
    for (int k = 0; k < nSums; k++) {
      int m = k < rows ? mean : (top + 1) * rows / 2;
      lo[k] = m - random.nextInt(cols + 1);
      hi[k] = m + random.nextInt(cols + 1);
    }

    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < cells; i++) {
      fzn.append("var ").append(set(domains[i])).append(": x").append(i).append(";\n");
    }
    for (int k = 0; k < nSums; k++) {
      fzn.append("var ").append(lo[k]).append("..").append(hi[k]).append(": s").append(k);
      fzn.append(";\n");
    }
    fzn.append(array("x", cells)).append(array("s", nSums));
    fzn.append("constraint jacop_alldiff([").append(names("x", cells)).append("]);\n");
    List<int[]> blocks = new ArrayList<>();
    for (int r = 0; r < rows; r++) {
      int row = r;
      blocks.add(IntStream.range(0, cols).map(c -> row * cols + c).toArray());
    }
    if (colSums) {
      for (int c = 0; c < cols; c++) {
        int col = c;
        blocks.add(IntStream.range(0, rows).map(r -> r * cols + col).toArray());
      }
    }
    for (int k = 0; k < nSums; k++) {
      StringBuilder coefs = new StringBuilder();
      StringBuilder vars = new StringBuilder();
      for (int i : blocks.get(k)) {
        coefs.append("1,");
        vars.append('x').append(i).append(',');
      }
      fzn.append("constraint int_lin_eq([")
          .append(coefs)
          .append("-1],[")
          .append(vars)
          .append('s')
          .append(k)
          .append("],0);\n");
    }
    if (sumsDifferent) {
      fzn.append("constraint jacop_alldiff([").append(names("s", nSums)).append("]);\n");
    }
    fzn.append("solve satisfy;\n");

    Set<String> expected = new TreeSet<>();
    int[] x = new int[cells];
    enumerate(
        0,
        x,
        new boolean[top + 1],
        domains,
        // a row is checked as soon as it is complete
        i -> {
          if ((i + 1) % cols != 0) {
            return true;
          }
          int r = i / cols;
          int sum = Arrays.stream(blocks.get(r)).map(j -> x[j]).sum();
          return lo[r] <= sum && sum <= hi[r];
        },
        () -> {
          int[] s = new int[nSums];
          for (int k = 0; k < nSums; k++) {
            s[k] = Arrays.stream(blocks.get(k)).map(i -> x[i]).sum();
            if (s[k] < lo[k] || s[k] > hi[k]) {
              return;
            }
          }
          if (sumsDifferent && Arrays.stream(s).distinct().count() != nSums) {
            return;
          }
          expected.add(
              String.join(
                  " ",
                  new TreeSet<>(
                      List.of(
                          "s = array1d(1.." + nSums + ", " + Arrays.toString(s) + ");",
                          "x = array1d(1.." + cells + ", " + Arrays.toString(x) + ");"))));
        });
    return new Model(fzn.toString(), expected);
  }

  private static void enumerate(
      int i, int[] x, boolean[] used, int[][] domains, IntPredicate prefix, Runnable visitor) {
    if (i == x.length) {
      visitor.run();
      return;
    }
    for (int v : domains[i]) {
      if (!used[v]) {
        used[v] = true;
        x[i] = v;
        if (prefix.test(i)) {
          enumerate(i + 1, x, used, domains, prefix, visitor);
        }
        used[v] = false;
      }
    }
  }

  private static String names(String prefix, int n) {
    StringBuilder s = new StringBuilder();
    for (int i = 0; i < n; i++) {
      s.append(i == 0 ? "" : ",").append(prefix).append(i);
    }
    return s.toString();
  }

  private static String array(String name, int n) {
    return "array [1.."
        + n
        + "] of var int: "
        + name
        + ":: output_array([1.."
        + n
        + "]) = ["
        + names(name, n)
        + "];\n";
  }

  private static String set(int[] values) {
    StringBuilder s = new StringBuilder("{");
    for (int k = 0; k < values.length; k++) {
      s.append(k == 0 ? "" : ",").append(values[k]);
    }
    return s.append('}').toString();
  }

  @Test
  void partitionSumsKeepAllSolutions() throws IOException {
    Random random = new Random(29);
    int detected = 0;
    int trials = Integer.getInteger("partitionSums.trials", 80);
    for (int trial = 0; trial < trials; trial++) {
      Model model = randomModel(random);
      String out = run(model.fzn(), "-a", "-debug");
      boolean found = out.contains("% partition sums");
      if (found) {
        detected++;
      }
      // a model found infeasible while it is read never reaches the detection
      if (!model.bruteForce().isEmpty()) {
        assertTrue(found, "not detected, trial " + trial + "\n" + model.fzn());
      }
      assertEquals(model.bruteForce(), solutions(out), "trial " + trial + "\n" + model.fzn());
    }
    assertTrue(detected > trials / 4, "detected " + detected);
  }

  @Test
  void heterosquareCountingFailsAtTheRootAndCanBeTurnedOff() throws IOException {
    // a 3x3 permutation of 1..9 whose rows and columns sum to different values of at least 16:
    // the six sums add up to 2 * 45 = 90 < 16 + 17 + ... + 21 = 111
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < 9; i++) {
      fzn.append("var 1..9: x").append(i).append(";\n");
    }
    for (int k = 0; k < 6; k++) {
      fzn.append("var 16..24: s").append(k).append(";\n");
    }
    fzn.append(array("x", 9)).append(array("s", 6));
    fzn.append("constraint jacop_alldiff([").append(names("x", 9)).append("]);\n");
    for (int k = 0; k < 6; k++) {
      int[] b = k < 3 ? new int[] {3 * k, 3 * k + 1, 3 * k + 2} : new int[] {k - 3, k, k + 3};
      fzn.append("constraint int_lin_eq([1,1,1,-1],[x")
          .append(b[0])
          .append(",x")
          .append(b[1])
          .append(",x")
          .append(b[2])
          .append(",s")
          .append(k)
          .append("],0);\n");
    }
    fzn.append("constraint jacop_alldiff([").append(names("s", 6)).append("]);\n");
    fzn.append("solve satisfy;\n");
    String out = run(fzn.toString(), "-s", "-debug");
    assertTrue(out.contains("% partition sums: 2 partition(s)"), out);
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
    // the counting fails while the model is posted, before any search
    assertFalse(out.contains("----------"), out);
    String property = "org.jacop.fz.partitionSums";
    System.setProperty(property, "false");
    try {
      String off = run(fzn.toString(), "-s", "-debug");
      assertFalse(off.contains("% partition sums"));
      assertTrue(off.contains("=====UNSATISFIABLE====="), off);
    } finally {
      System.clearProperty(property);
    }
  }

  private String run(String model, String... options) throws IOException {
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

  private static Set<String> solutions(String out) {
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(out.split("----------"))
        .map(
            s ->
                String.join(
                    " ",
                    new TreeSet<>(
                        Arrays.stream(s.strip().split("\\R"))
                            .filter(l -> !l.isBlank() && !l.startsWith("%"))
                            .toList())))
        .filter(s -> !s.isEmpty() && !s.startsWith("==========") && !s.contains("UNSATISFIABLE"))
        .forEach(solutions::add);
    return solutions;
  }
}
