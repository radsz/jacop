/*
 * BinPackingPermutationsFlatzincTest.java
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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the dual viewpoint the FlatZinc front end posts for a bin packing whose items fall into
 * all_different groups filling every bin with one item ({@code BinPackingPermutations}): all
 * solutions of random models must match a brute-force enumeration, with the detection on and off,
 * and an optimisation under the model's search must find the same solutions in the same order.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class BinPackingPermutationsFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.binPackingPermutations";

  @TempDir Path tmp;

  /** The FlatZinc of a random model, its solutions by enumeration and the number of items. */
  private record Model(String fzn, Set<String> bruteForce) {}

  private static Model randomModel(Random random, boolean optimise) {
    int bins = 3;
    int groups = 1 + random.nextInt(2);
    int extra = random.nextInt(3);
    int n = groups * bins + extra;
    // a group of item variables whose domain also holds a value that is no bin is no permutation
    boolean wide = random.nextInt(5) == 0;
    int[] w = new int[n];
    for (int i = 0; i < n; i++) {
      w[i] = random.nextInt(8);
    }
    int[] max = new int[n];
    for (int i = 0; i < n; i++) {
      max[i] = i < groups * bins && !wide ? bins : bins + (random.nextInt(3) == 0 ? 1 : 0);
    }
    // a fixed item, as symmetry breaking fixes the first group of team assignment
    int fixed = random.nextInt(3) == 0 ? random.nextInt(n) : -1;
    int[] low = new int[bins];
    int[] up = new int[bins];
    for (int b = 0; b < bins; b++) {
      low[b] = random.nextInt(8);
      up[b] = low[b] + 4 + random.nextInt(10);
    }

    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < n; i++) {
      if (i == fixed) {
        fzn.append("var 1..1: x").append(i).append(";\n");
      } else {
        fzn.append("var 1..").append(max[i]).append(": x").append(i).append(";\n");
      }
    }
    StringBuilder l = new StringBuilder();
    for (int b = 0; b < bins; b++) {
      fzn.append("var ").append(low[b]).append("..").append(up[b]).append(": l").append(b);
      fzn.append(":: output_var;\n");
      l.append(b == 0 ? "" : ",").append('l').append(b);
    }
    if (optimise) {
      fzn.append("var -100..100: z:: output_var;\n");
    }
    StringBuilder xs = new StringBuilder();
    for (int i = 0; i < n; i++) {
      xs.append(i == 0 ? "" : ",").append('x').append(i);
    }
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([1..")
        .append(n)
        .append("]) = [")
        .append(xs)
        .append("];\n");
    for (int g = 0; g < groups; g++) {
      StringBuilder a = new StringBuilder();
      for (int t = 0; t < bins; t++) {
        a.append(t == 0 ? "" : ",").append('x').append(g * bins + t);
      }
      fzn.append("constraint jacop_alldiff([").append(a).append("]);\n");
    }
    fzn.append("constraint jacop_bin_packing([")
        .append(xs)
        .append("],[")
        .append(l)
        .append("],")
        .append(list(w))
        .append(",1);\n");
    if (optimise) {
      // z = l0 - l2, maximised
      fzn.append("constraint int_lin_eq([1,-1,1],[z,l0,l2],0);\n");
      fzn.append("solve :: int_search(x,input_order,indomain_min,complete) maximize z;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }

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
      int[] load = holds(x, max, fixed, groups, w, low, up);
      if (load != null) {
        expected.add(
            "l0 = "
                + load[0]
                + "; l1 = "
                + load[1]
                + "; l2 = "
                + load[2]
                + "; x = array1d(1.."
                + n
                + ", "
                + Arrays.toString(x)
                + ");");
      }
    }
    return new Model(fzn.toString(), expected);
  }

  // the loads of a solution, or null
  private static int[] holds(
      int[] x, int[] max, int fixed, int groups, int[] w, int[] low, int[] up) {
    int bins = low.length;
    int[] load = new int[bins];
    for (int i = 0; i < x.length; i++) {
      if (x[i] > max[i] || i == fixed && x[i] != 1 || x[i] > bins) {
        return null;
      }
      load[x[i] - 1] += w[i];
    }
    for (int g = 0; g < groups; g++) {
      for (int s = 0; s < bins; s++) {
        for (int t = s + 1; t < bins; t++) {
          if (x[g * bins + s] == x[g * bins + t]) {
            return null;
          }
        }
      }
    }
    for (int b = 0; b < bins; b++) {
      if (load[b] < low[b] || load[b] > up[b]) {
        return null;
      }
    }
    return load;
  }

  private static String list(int[] a) {
    return Arrays.toString(a).replace(" ", "");
  }

  @Test
  void permutationsKeepAllSolutions() throws IOException {
    Random random = new Random(31);
    int detected = 0;
    for (int trial = 0; trial < 300; trial++) {
      Model model = randomModel(random, false);
      String on = run(model.fzn(), true, "-a", "-debug");
      if (on.contains("bin packing permutations")) {
        detected++;
      }
      assertEquals(model.bruteForce(), solutions(on), "trial " + trial + "\n" + model.fzn());
      String off = run(model.fzn(), false, "-a");
      assertEquals(model.bruteForce(), solutions(off), "trial " + trial + "\n" + model.fzn());
    }
    assertTrue(detected > 100, "detected in " + detected + " models");
  }

  @Test
  void permutationsKeepTheSearchOfTheModel() throws IOException {
    Random random = new Random(37);
    for (int trial = 0; trial < 100; trial++) {
      Model model = randomModel(random, true);
      List<String> on = sequence(run(model.fzn(), true, "-a"));
      List<String> off = sequence(run(model.fzn(), false, "-a"));
      assertEquals(off, on, "trial " + trial + "\n" + model.fzn());
    }
  }

  private String run(String model, boolean detect, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    if (!detect) {
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

  // the solutions in the order they were printed
  private static List<String> sequence(String out) {
    List<String> solutions = new ArrayList<>();
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

  private static Set<String> solutions(String out) {
    return new TreeSet<>(sequence(out));
  }
}
