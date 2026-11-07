/*
 * BinPackingCardinalityFlatzincTest.java
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
import java.util.Arrays;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks that the FlatZinc front end gives a bin packing constraint the counts of a cardinality
 * constraint over the same bin variables (bin packing with cardinality): all solutions must match a
 * brute-force enumeration, with the pairing on and off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class BinPackingCardinalityFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.binPackingCardinality";

  @TempDir Path tmp;

  /** The FlatZinc of a random bin packing with cardinality and its solutions by enumeration. */
  private record Model(String fzn, Set<String> bruteForce) {}

  // the cardinality constraint: bounds, closed bounds or closed with counter variables
  private enum Kind {
    COUNT_VALUES_BOUNDS,
    LOW_UP_CLOSED,
    CLOSED_COUNTERS
  }

  private static Model randomModel(Random random) {
    int n = 3 + random.nextInt(4);
    int bins = 2 + random.nextInt(2);
    Kind kind = Kind.values()[random.nextInt(Kind.values().length)];
    boolean capacity = random.nextBoolean();
    int[] w = new int[n];
    for (int i = 0; i < n; i++) {
      w[i] = random.nextInt(6);
    }
    int[] cap = new int[bins];
    for (int b = 0; b < bins; b++) {
      cap[b] = 3 + random.nextInt(8);
    }
    // the cover may miss a bin or hold a value that is no bin
    int[] cover = new int[bins];
    int[] low = new int[bins];
    int[] up = new int[bins];
    for (int b = 0; b < bins; b++) {
      cover[b] = random.nextInt(6) == 0 ? bins + 1 : b + 1;
      low[b] = random.nextInt(3);
      up[b] = low[b] + random.nextInt(3);
    }
    // a repeated bin variable is counted once per occurrence
    int[] var = new int[n];
    for (int i = 0; i < n; i++) {
      var[i] = random.nextInt(8) == 0 && i > 0 ? random.nextInt(i) : i;
    }

    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var 1..").append(bins + 1).append(": x").append(i).append(";\n");
    }
    StringBuilder xs = new StringBuilder();
    StringBuilder items = new StringBuilder();
    for (int i = 0; i < n; i++) {
      xs.append(i == 0 ? "" : ",").append('x').append(i);
      items.append(i == 0 ? "" : ",").append('x').append(var[i]);
    }
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(xs)
        .append("];\n");
    String bp;
    if (capacity) {
      bp = "jacop_bin_packing_capacity([" + items + "]," + list(cap) + "," + list(w) + ",1)";
    } else {
      StringBuilder l = new StringBuilder();
      for (int b = 0; b < bins; b++) {
        fzn.append("var 0..").append(cap[b]).append(": l").append(b).append(";\n");
        l.append(b == 0 ? "" : ",").append('l').append(b);
      }
      bp = "jacop_bin_packing([" + items + "],[" + l + "]," + list(w) + ",1)";
    }
    String cc =
        switch (kind) {
          case COUNT_VALUES_BOUNDS ->
              "jacop_count_values_bounds(["
                  + items
                  + "],"
                  + list(cover)
                  + ","
                  + list(low)
                  + ","
                  + list(up)
                  + ")";
          case LOW_UP_CLOSED ->
              "jacop_global_cardinality_low_up_closed(["
                  + items
                  + "],"
                  + list(cover)
                  + ","
                  + list(low)
                  + ","
                  + list(up)
                  + ")";
          case CLOSED_COUNTERS -> {
            StringBuilder c = new StringBuilder();
            for (int b = 0; b < bins; b++) {
              fzn.append("var ").append(low[b]).append("..").append(up[b]).append(": c");
              fzn.append(b).append(";\n");
              c.append(b == 0 ? "" : ",").append('c').append(b);
            }
            yield "jacop_global_cardinality_closed(["
                + items
                + "],"
                + list(cover)
                + ",["
                + c
                + "])";
          }
        };
    // either order of the two constraints
    if (random.nextBoolean()) {
      fzn.append("constraint ").append(bp).append(";\nconstraint ").append(cc).append(";\n");
    } else {
      fzn.append("constraint ").append(cc).append(";\nconstraint ").append(bp).append(";\n");
    }
    fzn.append("solve satisfy;\n");

    Set<String> expected = new TreeSet<>();
    int[] x = new int[n];
    int values = bins + 1;
    int total = (int) Math.pow(values, n);
    for (int code = 0; code < total; code++) {
      int c = code;
      for (int i = 0; i < n; i++) {
        x[i] = 1 + c % values;
        c /= values;
      }
      if (holds(x, var, w, cap, cover, low, up, kind)) {
        expected.add("x = array1d(1.." + n + ", " + Arrays.toString(x) + ");");
      }
    }
    return new Model(fzn.toString(), expected);
  }

  private static boolean holds(
      int[] x, int[] var, int[] w, int[] cap, int[] cover, int[] low, int[] up, Kind kind) {
    int bins = cap.length;
    int[] load = new int[bins];
    for (int i = 0; i < var.length; i++) {
      int b = x[var[i]];
      if (b > bins) {
        return false; // no such bin
      }
      load[b - 1] += w[i];
    }
    for (int b = 0; b < bins; b++) {
      if (load[b] > cap[b]) {
        return false;
      }
    }
    // a repeated cover value is counted within the intersection of its bounds
    for (int k = 0; k < cover.length; k++) {
      int count = 0;
      for (int v : var) {
        count += x[v] == cover[k] ? 1 : 0;
      }
      if (count < low[k] || count > up[k]) {
        return false;
      }
    }
    if (kind != Kind.COUNT_VALUES_BOUNDS) {
      for (int v : var) {
        if (Arrays.stream(cover).noneMatch(c -> c == x[v])) {
          return false; // closed
        }
      }
    }
    return true;
  }

  private static String list(int[] a) {
    return Arrays.toString(a).replace(" ", "");
  }

  @Test
  void cardinalityKeepsAllSolutions() throws IOException {
    Random random = new Random(29);
    int paired = 0;
    for (int trial = 0; trial < 400; trial++) {
      Model model = randomModel(random);
      String on = run(model.fzn(), true, "-a", "-debug");
      if (on.contains("bin packing with cardinality")) {
        paired++;
      }
      assertEquals(model.bruteForce(), solutions(on), "trial " + trial + "\n" + model.fzn());
      String off = run(model.fzn(), false, "-a");
      assertEquals(model.bruteForce(), solutions(off), "trial " + trial + "\n" + model.fzn());
    }
    assertTrue(paired > 200, "paired in " + paired + " models");
  }

  private String run(String model, boolean pairing, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    if (!pairing) {
      System.setProperty(PROPERTY, "false");
    }
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(PROPERTY);
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
