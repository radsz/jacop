/*
 * BinPackingCliqueFlatzincTest.java
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
import java.util.Arrays;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the surrogate dimension and the cliques that the FlatZinc front end posts for bin packing
 * constraints over the same bins (vector bin packing): all solutions must match a brute-force
 * enumeration.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class BinPackingCliqueFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.binPackingCliques";

  @TempDir Path tmp;

  /** The FlatZinc of a random vector bin packing and its solutions by enumeration. */
  private record Model(String fzn, Set<String> bruteForce) {}

  private static Model randomModel(Random random) {
    int n = 3 + random.nextInt(4);
    int bins = 2 + random.nextInt(2);
    int dims = 1 + random.nextInt(3);
    boolean loads = random.nextBoolean();
    int[][] w = new int[dims][n];
    int[][] cap = new int[dims][bins];
    for (int d = 0; d < dims; d++) {
      for (int i = 0; i < n; i++) {
        w[d][i] = random.nextInt(7);
      }
      for (int b = 0; b < bins; b++) {
        cap[d][b] = 4 + random.nextInt(6);
      }
    }
    // a repeated bin variable merges two items
    int[] var = new int[n];
    for (int i = 0; i < n; i++) {
      var[i] = random.nextInt(8) == 0 && i > 0 ? random.nextInt(i) : i;
    }

    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var 1..").append(bins).append(": x").append(i).append(";\n");
    }
    StringBuilder xs = new StringBuilder();
    for (int i = 0; i < n; i++) {
      xs.append(i == 0 ? "" : ",").append('x').append(i);
    }
    StringBuilder items = new StringBuilder();
    for (int i = 0; i < n; i++) {
      items.append(i == 0 ? "" : ",").append('x').append(var[i]);
    }
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(xs)
        .append("];\n");
    StringBuilder constraints = new StringBuilder();
    for (int d = 0; d < dims; d++) {
      if (loads) {
        StringBuilder l = new StringBuilder();
        for (int b = 0; b < bins; b++) {
          fzn.append("var 0..").append(cap[d][b]).append(": l").append(d).append('_').append(b);
          fzn.append(";\n");
          l.append(b == 0 ? "" : ",").append('l').append(d).append('_').append(b);
        }
        constraints
            .append("constraint jacop_bin_packing([")
            .append(items)
            .append("],[")
            .append(l)
            .append("],")
            .append(Arrays.toString(w[d]).replace(" ", ""))
            .append(",1);\n");
      } else {
        constraints
            .append("constraint jacop_bin_packing_capacity([")
            .append(items)
            .append("],")
            .append(Arrays.toString(cap[d]).replace(" ", ""))
            .append(',')
            .append(Arrays.toString(w[d]).replace(" ", ""))
            .append(",1);\n");
      }
    }
    fzn.append(constraints).append("solve satisfy;\n");

    Set<String> expected = new TreeSet<>();
    int[] x = new int[n];
    int total = (int) Math.pow(bins, n);
    for (int code = 0; code < total; code++) {
      int c = code;
      for (int i = 0; i < n; i++) {
        x[i] = 1 + c % bins;
        c /= bins;
      }
      if (fits(x, var, w, cap, bins)) {
        expected.add("x = array1d(1.." + n + ", " + Arrays.toString(x) + ");");
      }
    }
    return new Model(fzn.toString(), expected);
  }

  private static boolean fits(int[] x, int[] var, int[][] w, int[][] cap, int bins) {
    for (int d = 0; d < w.length; d++) {
      int[] load = new int[bins];
      for (int i = 0; i < x.length; i++) {
        load[x[var[i]] - 1] += w[d][i];
      }
      for (int b = 0; b < bins; b++) {
        if (load[b] > cap[d][b]) {
          return false;
        }
      }
    }
    return true;
  }

  @Test
  void cliquesKeepAllSolutions() throws IOException {
    Random random = new Random(17);
    int withCliques = 0;
    for (String mode : new String[] {"vector", "all"}) {
      System.setProperty(PROPERTY, mode);
      try {
        for (int trial = 0; trial < 300; trial++) {
          Model model = randomModel(random);
          String out = run(model.fzn(), "-a", "-debug");
          if (out.contains("alldistinct(")) {
            withCliques++;
          }
          assertEquals(
              model.bruteForce(),
              solutions(out),
              "mode " + mode + ", trial " + trial + "\n" + model.fzn());
        }
      } finally {
        System.clearProperty(PROPERTY);
      }
    }
    assertTrue(withCliques > 100, "cliques in " + withCliques + " models");
  }

  @Test
  void crossDimensionCliqueIsOffByDefault() throws IOException {
    // each pair of items exceeds the capacity in one dimension only, a different one per pair
    String fzn =
        """
        var 1..3: x0;
        var 1..3: x1;
        var 1..3: x2;
        array [1..3] of var int: x:: output_array([1..3]) = [x0,x1,x2];
        constraint jacop_bin_packing_capacity([x0,x1,x2],[10,10,10],[6,1,6],1);
        constraint jacop_bin_packing_capacity([x0,x1,x2],[10,10,10],[1,6,6],1);
        constraint jacop_bin_packing_capacity([x0,x1,x2],[10,10,10],[6,6,1],1);
        solve satisfy;
        """;
    String off = run(fzn, "-a", "-debug");
    assertFalse(off.contains("alldistinct("));
    System.setProperty(PROPERTY, "vector");
    try {
      String on = run(fzn, "-a", "-debug");
      assertTrue(on.contains("alldistinct("));
      assertEquals(solutions(off), solutions(on));
      assertEquals(6, solutions(on).size());
    } finally {
      System.clearProperty(PROPERTY);
    }
  }

  @Test
  void surrogateDimensionIsOnByDefault() throws IOException {
    // sizes (w, 80 - w): no bin holds three items in the summed dimension, so seven items do not
    // fit three bins, while each dimension alone fits them
    String fzn =
        """
        var 1..3: x0;
        var 1..3: x1;
        var 1..3: x2;
        var 1..3: x3;
        var 1..3: x4;
        var 1..3: x5;
        var 1..3: x6;
        array [1..7] of var int: x:: output_array([1..7]) = [x0,x1,x2,x3,x4,x5,x6];
        constraint jacop_bin_packing_capacity([x0,x1,x2,x3,x4,x5,x6],[100,100,100],\
        [10,20,30,40,50,60,70],1);
        constraint jacop_bin_packing_capacity([x0,x1,x2,x3,x4,x5,x6],[100,100,100],\
        [70,60,50,40,30,20,10],1);
        solve satisfy;
        """;
    String on = run(fzn, "-s", "-debug");
    assertTrue(on.contains("1 surrogate dimensions"), on);
    assertTrue(on.contains("UNSATISFIABLE"), on);
    System.setProperty("org.jacop.fz.binPackingSurrogate", "false");
    try {
      String off = run(fzn, "-s", "-debug");
      assertFalse(off.contains("surrogate dimensions"), off);
      assertTrue(off.contains("UNSATISFIABLE"), off);
    } finally {
      System.clearProperty("org.jacop.fz.binPackingSurrogate");
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
                    Arrays.stream(s.strip().split("\\R"))
                        .filter(l -> !l.isBlank() && !l.startsWith("%"))
                        .toList()))
        .filter(s -> !s.isEmpty() && !s.startsWith("==========") && !s.contains("UNSATISFIABLE"))
        .forEach(solutions::add);
    return solutions;
  }
}
