/*
 * GlobalCardinalityFlatzincTest.java
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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the FlatZinc posting of the global cardinality constraints (jacop_gcc, the closed
 * jacop_global_cardinality variants and jacop_count_values) by comparing all solutions with a
 * brute-force enumeration.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class GlobalCardinalityFlatzincTest {

  private static final String[] KINDS = {
    "jacop_gcc",
    "jacop_global_cardinality_closed",
    "jacop_global_cardinality_low_up_closed",
    "jacop_count_values",
    "jacop_count_values_bounds"
  };

  @TempDir Path tmp;

  @Test
  void gccRestrictsVariablesWhoseBoundIsTheFirstCountedValue() throws IOException {
    // x = {0,5} reaches the first counted value 5 with its maximum, so it was not restricted to
    // the counted values and GCC threw an IllegalArgumentException
    String fzn =
        """
        var {0,5}: x:: output_var;
        var 5..6: y:: output_var;
        var 0..2: c5:: output_var;
        var 0..2: c6:: output_var;
        constraint jacop_gcc([x,y],[c5,c6],5);
        solve satisfy;
        """;

    assertEquals(
        Set.of("c5 = 1; c6 = 1; x = 5; y = 6;", "c5 = 2; c6 = 0; x = 5; y = 5;"), solveAll(fzn));
  }

  @Test
  void closedGccWithUnsortedCover() throws IOException {
    // the counters were given to GCC in cover order, while GCC takes them in increasing order of
    // values, so c3 counted value 1 and x = y = 1 was reported
    String fzn =
        """
        var 1..3: x:: output_var;
        var 1..3: y:: output_var;
        var 0..2: c3:: output_var;
        var 0..2: c1:: output_var;
        var 0..2: c2:: output_var;
        constraint jacop_global_cardinality_closed([x,y],[3,1,2],[c3,c1,c2]);
        constraint int_eq(c3,2);
        solve satisfy;
        """;

    assertEquals(Set.of("c1 = 0; c2 = 0; c3 = 2; x = 3; y = 3;"), solveAll(fzn));
  }

  @Test
  void closedLowUpGccWithUnsortedCover() throws IOException {
    String fzn =
        """
        var 1..3: x:: output_var;
        var 1..3: y:: output_var;
        constraint jacop_global_cardinality_low_up_closed([x,y],[3,1,2],[2,0,0],[2,0,0]);
        solve satisfy;
        """;

    assertEquals(Set.of("x = 3; y = 3;"), solveAll(fzn));
  }

  @Test
  void closedGccWithCoverValueNoVariableCanTake() throws IOException {
    // value 5 can not be taken, so its counter is zero; GCC was given three counters for two
    // values and threw an IllegalArgumentException
    String fzn =
        """
        var {1,9}: x:: output_var;
        var {1,9}: y:: output_var;
        var 0..2: c1:: output_var;
        var 0..2: c5:: output_var;
        var 0..2: c9:: output_var;
        constraint jacop_global_cardinality_closed([x,y],[1,5,9],[c1,c5,c9]);
        solve satisfy;
        """;

    assertEquals(
        Set.of(
            "c1 = 0; c5 = 0; c9 = 2; x = 9; y = 9;",
            "c1 = 1; c5 = 0; c9 = 1; x = 1; y = 9;",
            "c1 = 1; c5 = 0; c9 = 1; x = 9; y = 1;",
            "c1 = 2; c5 = 0; c9 = 0; x = 1; y = 1;"),
        solveAll(fzn));
  }

  @Test
  void gccWithRepeatedVariable() throws IOException {
    // GCC does not accept a repeated variable and threw an IllegalArgumentException
    String fzn =
        """
        var 1..2: x:: output_var;
        var 1..2: y:: output_var;
        var 0..3: c1:: output_var;
        var 0..3: c2:: output_var;
        constraint jacop_gcc([x,x,y],[c1,c2],1);
        constraint int_eq(c1,1);
        solve satisfy;
        """;

    assertEquals(Set.of("c1 = 1; c2 = 2; x = 2; y = 1;"), solveAll(fzn));
  }

  @Test
  void closedGccWithCounterThatIsCountedToo() throws IOException {
    // p counts value 3, which no variable can take, so p = 0; fixing p shrank the union of the
    // domains after the counters for GCC had been chosen
    String fzn =
        """
        var 0..2: p:: output_var;
        var 0..1: c0:: output_var;
        var 0..1: c1:: output_var;
        constraint jacop_global_cardinality_closed([p],[0,3,1],[c0,p,c1]);
        solve satisfy;
        """;

    assertEquals(Set.of("c0 = 1; c1 = 0; p = 0;"), solveAll(fzn));
  }

  @Test
  void randomModelsHaveTheSolutionsOfBruteForce() throws IOException {
    // random domains, repeated variables, constants, counters that are also counted, and unsorted
    // or repeated cover values
    Random random = new Random(5);
    for (int trial = 0; trial < 1000; trial++) {
      String kind = KINDS[trial % KINDS.length];
      RandomModel model = new RandomModel(random, kind);
      assertEquals(
          model.bruteForce(), solveAll(model.fzn()), "trial " + trial + "\n" + model.fzn());
    }
  }

  /**
   * A random model of one global cardinality constraint over pool variables p0, p1, ... and
   * counters c0, c1, ... that are not pool variables.
   */
  private static final class RandomModel {

    final String kind;
    final int[][] pool;
    final int[] x;
    final int[] cover;
    final int[] counter;
    final int[][] counterDomain;
    final int[] low;
    final int[] up;
    final boolean domainAnnotation;

    /** Entries of x are pool indexes, or a constant v encoded as -(v + 1). */
    RandomModel(Random random, String kind) {
      this.kind = kind;
      pool = new int[1 + random.nextInt(4)][];
      for (int i = 0; i < pool.length; i++) {
        pool[i] = random.nextInt(6) == 0 ? new int[] {random.nextInt(4)} : subset(random, 0, 3);
      }
      int n = 1 + random.nextInt(4);
      x = new int[n];
      for (int i = 0; i < n; i++) {
        x[i] = random.nextInt(5) == 0 ? -(random.nextInt(4) + 1) : random.nextInt(pool.length);
      }
      int k = 1 + random.nextInt(4);
      int first = random.nextInt(3);
      cover = new int[k];
      counter = new int[k];
      counterDomain = new int[k][];
      low = new int[k];
      up = new int[k];
      for (int i = 0; i < k; i++) {
        cover[i] = kind.equals("jacop_gcc") ? first + i : random.nextInt(5) - 1;
        counter[i] = random.nextInt(6) == 0 ? random.nextInt(pool.length) : -1;
        counterDomain[i] = subset(random, 0, n);
        low[i] = random.nextInt(3) == 0 ? 0 : random.nextInt(n + 1);
        up[i] = low[i] + random.nextInt(n + 1 - low[i]);
      }
      domainAnnotation = random.nextBoolean();
    }

    boolean withCounters() {
      return !kind.endsWith("bounds") && !kind.contains("low_up");
    }

    boolean closed() {
      return !kind.startsWith("jacop_count_values");
    }

    int xValue(int[] assignment, int i) {
      return x[i] >= 0 ? assignment[x[i]] : -x[i] - 1;
    }

    String fzn() {
      StringBuilder fzn = new StringBuilder();
      for (int i = 0; i < pool.length; i++) {
        fzn.append("var ").append(set(pool[i])).append(": p").append(i).append(":: output_var;\n");
      }
      List<String> counters = new ArrayList<>();
      for (int i = 0; i < cover.length; i++) {
        if (counter[i] >= 0) {
          counters.add("p" + counter[i]);
        } else {
          counters.add("c" + i);
          if (withCounters()) {
            fzn.append("var ")
                .append(set(counterDomain[i]))
                .append(": c")
                .append(i)
                .append(":: output_var;\n");
          }
        }
      }
      String xs =
          Arrays.stream(x)
              .mapToObj(i -> i >= 0 ? "p" + i : String.valueOf(-i - 1))
              .collect(Collectors.joining(",", "[", "]"));
      String arguments =
          switch (kind) {
            case "jacop_gcc" -> xs + "," + counters + "," + cover[0];
            case "jacop_global_cardinality_closed", "jacop_count_values" ->
                xs + "," + Arrays.toString(cover) + "," + counters;
            default ->
                xs
                    + ","
                    + Arrays.toString(cover)
                    + ","
                    + Arrays.toString(low)
                    + ","
                    + Arrays.toString(up);
          };
      fzn.append("constraint ")
          .append(kind)
          .append("(")
          .append(arguments.replace(" ", ""))
          .append(")")
          .append(domainAnnotation ? " :: domain" : "")
          .append(";\nsolve satisfy;\n");
      return fzn.toString();
    }

    Set<String> bruteForce() {
      // the pool variables followed by the counters c0, c1, ... (fixed to 0 when not used)
      int[][] domains = Arrays.copyOf(pool, pool.length + cover.length);
      for (int i = 0; i < cover.length; i++) {
        domains[pool.length + i] =
            withCounters() && counter[i] < 0 ? counterDomain[i] : new int[] {0};
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
      for (int j = 0; j < x.length; j++) {
        int value = xValue(assignment, j);
        if (closed() && Arrays.stream(cover).noneMatch(c -> c == value)) {
          return;
        }
      }
      for (int c = 0; c < cover.length; c++) {
        int count = 0;
        for (int j = 0; j < x.length; j++) {
          if (xValue(assignment, j) == cover[c]) {
            count++;
          }
        }
        if (withCounters()) {
          int counted = counter[c] >= 0 ? assignment[counter[c]] : assignment[pool.length + c];
          if (counted != count) {
            return;
          }
        } else if (count < low[c] || count > up[c]) {
          return;
        }
      }
      List<String> output = new ArrayList<>();
      for (int p = 0; p < pool.length; p++) {
        output.add("p" + p + " = " + assignment[p] + ";");
      }
      for (int c = 0; c < cover.length; c++) {
        if (withCounters() && counter[c] < 0) {
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

  private Set<String> solveAll(String model) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(new String[] {"-a", fzn.toString()});
    } finally {
      System.setOut(originalOut);
    }
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(buffer.toString(StandardCharsets.UTF_8).split("----------"))
        .map(s -> String.join(" ", new TreeSet<>(Arrays.asList(s.strip().split("\\R")))))
        .filter(s -> !s.isEmpty() && !s.startsWith("==========") && !s.contains("UNSATISFIABLE"))
        .forEach(solutions::add);
    return solutions;
  }
}
