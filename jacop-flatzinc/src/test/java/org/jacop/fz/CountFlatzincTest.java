/*
 * CountFlatzincTest.java
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
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the FlatZinc posting of jacop_count, where the counts over one list are posted as one
 * CountValues, by comparing all solutions with a brute-force enumeration.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class CountFlatzincTest {

  @TempDir Path tmp;

  @Test
  void magicSequenceIsOnePropagator() throws IOException {
    // magicseq: n counts over the same list, each queued on every change of a list variable and
    // each scanning the list; n = 300 found no solution in 60 s as 300 Count constraints
    int n = 300;
    String xs =
        IntStream.range(0, n).mapToObj(i -> "x" + i).collect(Collectors.joining(",", "[", "]"));
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var 0..").append(n).append(": x").append(i).append(";\n");
    }
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([0..")
        .append(n - 1)
        .append("]) = ")
        .append(xs)
        .append(";\n");
    for (int i = 0; i < n; i++) {
      fzn.append("constraint jacop_count(x,").append(i).append(",x").append(i).append(");\n");
    }
    fzn.append("solve satisfy;\n");

    String out = solve(fzn.toString(), "-s", "-t", "20000");

    assertTrue(out.contains("%%%mzn-stat: propagators=1\n"), out);
    int[] x =
        Arrays.stream(out.substring(out.indexOf('[') + 1, out.indexOf(']')).split(","))
            .mapToInt(s -> Integer.parseInt(s.strip()))
            .toArray();
    for (int i = 0; i < n; i++) {
      int value = i;
      assertEquals(x[i], Arrays.stream(x).filter(v -> v == value).count(), "x[" + i + "]");
    }
  }

  @Test
  void randomModelsHaveTheSolutionsOfBruteForce() throws IOException {
    // several counts over shared lists, with repeated values, counters that are counted too,
    // fixed counters and constants in the lists
    Random random = new Random(7);
    for (int trial = 0; trial < 1000; trial++) {
      RandomModel model = new RandomModel(random);
      assertEquals(
          model.bruteForce(), solveAll(model.fzn()), "trial " + trial + "\n" + model.fzn());
    }
  }

  /**
   * A random model of jacop_count constraints over one or two lists of pool variables p0, p1, ...
   * and constants. A counter is a pool variable, a fixed number, or a counter variable c0, c1, ...
   */
  private static final class RandomModel {

    final int[][] pool;
    final int[][] lists;
    final int[] list;
    final int[] value;
    final int[] counter;
    final int[] fixed;
    final int[][] counterDomain;

    /** Entries of the lists are pool indexes, or a constant v encoded as -(v + 1). */
    RandomModel(Random random) {
      pool = new int[1 + random.nextInt(4)][];
      for (int i = 0; i < pool.length; i++) {
        pool[i] = random.nextInt(6) == 0 ? new int[] {random.nextInt(4)} : subset(random, 0, 3);
      }
      lists = new int[1 + random.nextInt(2)][];
      for (int l = 0; l < lists.length; l++) {
        lists[l] = new int[1 + random.nextInt(4)];
        for (int i = 0; i < lists[l].length; i++) {
          lists[l][i] =
              random.nextInt(5) == 0 ? -(random.nextInt(4) + 1) : random.nextInt(pool.length);
        }
      }
      int k = 1 + random.nextInt(5);
      list = new int[k];
      value = new int[k];
      counter = new int[k];
      fixed = new int[k];
      counterDomain = new int[k][];
      for (int i = 0; i < k; i++) {
        list[i] = random.nextInt(lists.length);
        value[i] = random.nextInt(5) - 1;
        int kind = random.nextInt(6);
        counter[i] = kind == 0 ? random.nextInt(pool.length) : kind == 1 ? -2 : -1;
        fixed[i] = random.nextInt(lists[list[i]].length + 1);
        counterDomain[i] = subset(random, 0, lists[list[i]].length);
      }
    }

    int listValue(int[] assignment, int l, int i) {
      int e = lists[l][i];
      return e >= 0 ? assignment[e] : -e - 1;
    }

    String counterName(int i) {
      return counter[i] >= 0 ? "p" + counter[i] : counter[i] == -2 ? "" + fixed[i] : "c" + i;
    }

    String fzn() {
      StringBuilder fzn = new StringBuilder();
      for (int i = 0; i < pool.length; i++) {
        fzn.append("var ").append(set(pool[i])).append(": p").append(i).append(":: output_var;\n");
      }
      for (int i = 0; i < counter.length; i++) {
        if (counter[i] == -1) {
          fzn.append("var ")
              .append(set(counterDomain[i]))
              .append(": c")
              .append(i)
              .append(":: output_var;\n");
        }
      }
      for (int l = 0; l < lists.length; l++) {
        fzn.append("array [1..")
            .append(lists[l].length)
            .append("] of var int: l")
            .append(l)
            .append(" = ")
            .append(
                Arrays.stream(lists[l])
                    .mapToObj(i -> i >= 0 ? "p" + i : String.valueOf(-i - 1))
                    .collect(Collectors.joining(",", "[", "]")))
            .append(";\n");
      }
      for (int i = 0; i < counter.length; i++) {
        fzn.append("constraint jacop_count(l")
            .append(list[i])
            .append(",")
            .append(value[i])
            .append(",")
            .append(counterName(i))
            .append(");\n");
      }
      fzn.append("solve satisfy;\n");
      return fzn.toString();
    }

    Set<String> bruteForce() {
      // the pool variables followed by the counters c0, c1, ... (fixed to 0 when not used)
      int[][] domains = Arrays.copyOf(pool, pool.length + counter.length);
      for (int i = 0; i < counter.length; i++) {
        domains[pool.length + i] = counter[i] == -1 ? counterDomain[i] : new int[] {0};
      }
      Set<String> solutions = new TreeSet<>();
      enumerate(domains, new int[domains.length], 0, solutions);
      return solutions;
    }

    private void enumerate(int[][] domains, int[] assignment, int i, Set<String> solutions) {
      if (i < domains.length) {
        for (int v : domains[i]) {
          assignment[i] = v;
          enumerate(domains, assignment, i + 1, solutions);
        }
        return;
      }
      for (int c = 0; c < counter.length; c++) {
        int count = 0;
        for (int j = 0; j < lists[list[c]].length; j++) {
          if (listValue(assignment, list[c], j) == value[c]) {
            count++;
          }
        }
        int counted =
            switch (counter[c]) {
              case -1 -> assignment[pool.length + c];
              case -2 -> fixed[c];
              default -> assignment[counter[c]];
            };
        if (counted != count) {
          return;
        }
      }
      List<String> output = new ArrayList<>();
      for (int p = 0; p < pool.length; p++) {
        output.add("p" + p + " = " + assignment[p] + ";");
      }
      for (int c = 0; c < counter.length; c++) {
        if (counter[c] == -1) {
          output.add("c" + c + " = " + assignment[pool.length + c] + ";");
        }
      }
      Collections.sort(output);
      solutions.add(String.join(" ", output));
    }

    private static String set(int[] values) {
      return Arrays.stream(values)
          .mapToObj(String::valueOf)
          .collect(Collectors.joining(",", "{", "}"));
    }

    private static int[] subset(Random random, int lo, int hi) {
      List<Integer> values = new ArrayList<>();
      for (int v = lo; v <= hi; v++) {
        if (random.nextInt(3) != 0) {
          values.add(v);
        }
      }
      if (values.isEmpty()) {
        values.add(lo + random.nextInt(hi - lo + 1));
      }
      return values.stream().mapToInt(Integer::intValue).toArray();
    }
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

  private Set<String> solveAll(String model) throws IOException {
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(solve(model, "-a").split("----------"))
        .map(s -> String.join(" ", new TreeSet<>(Arrays.asList(s.strip().split("\\R")))))
        .filter(s -> !s.isEmpty() && !s.startsWith("==========") && !s.contains("UNSATISFIABLE"))
        .forEach(solutions::add);
    return solutions;
  }
}
