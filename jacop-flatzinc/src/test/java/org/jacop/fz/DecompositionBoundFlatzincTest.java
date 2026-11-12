/*
 * DecompositionBoundFlatzincTest.java
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the decomposition bound ({@code -Dorg.jacop.fz.decomposition=true}): on random models of a
 * few blocks linked by counting and linear constraints, the certified bound is on the right side of
 * the optimum and the optimum stays, with and without lazy clause generation.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class DecompositionBoundFlatzincTest {

  private static final Pattern BOUND = Pattern.compile("dbBound=(-?\\d+)");

  @TempDir Path tmp;

  private static String randomModel(Random random, boolean maximize) {
    int blocks = 2 + random.nextInt(3);
    int size = 3;
    StringBuilder fzn = new StringBuilder();
    List<String> all = new ArrayList<>();
    List<List<String>> members = new ArrayList<>();
    for (int b = 0; b < blocks; b++) {
      List<String> block = new ArrayList<>();
      for (int i = 0; i < size; i++) {
        String x = "x" + b + "_" + i;
        fzn.append("var 0..2: ").append(x).append(";\n");
        block.add(x);
        all.add(x);
      }
      members.add(block);
    }
    fzn.append("var -100..100: obj:: output_var;\n");
    for (List<String> block : members) {
      fzn.append("constraint int_ne(").append(block.get(0)).append(',').append(block.get(1));
      fzn.append(");\nconstraint int_ne(").append(block.get(1)).append(',').append(block.get(2));
      fzn.append(");\n");
      if (random.nextBoolean()) {
        int[] w = block.stream().mapToInt(v -> random.nextInt(5) - 2).toArray();
        fzn.append("constraint int_lin_le(")
            .append(Arrays.toString(w).replace(" ", ""))
            .append(",[")
            .append(String.join(",", block))
            .append("],")
            .append(random.nextInt(4))
            .append(");\n");
      }
    }
    // the linking rows: counts of a value over one variable of each block, a linear row over a
    // variable of each block
    int counts = 1 + random.nextInt(2);
    for (int k = 0; k < counts; k++) {
      List<String> list = new ArrayList<>();
      for (List<String> block : members) {
        list.add(block.get(random.nextInt(size)));
      }
      int lb = random.nextInt(2);
      fzn.append("constraint jacop_count_values_bounds([")
          .append(String.join(",", list))
          .append("],[")
          .append(random.nextInt(3))
          .append("],[")
          .append(lb)
          .append("],[")
          .append(lb + random.nextInt(blocks))
          .append("]);\n");
    }
    if (random.nextBoolean()) {
      List<String> list = new ArrayList<>();
      for (List<String> block : members) {
        list.add(block.get(random.nextInt(size)));
      }
      int[] w = list.stream().mapToInt(v -> 1 + random.nextInt(3)).toArray();
      fzn.append("constraint int_lin_le(")
          .append(Arrays.toString(w).replace(" ", ""))
          .append(",[")
          .append(String.join(",", list))
          .append("],")
          .append(2 * blocks + random.nextInt(3))
          .append(");\n");
    }
    int[] w = new int[all.size() + 1];
    for (int i = 0; i < all.size(); i++) {
      w[i] = random.nextInt(9) - 4;
    }
    w[all.size()] = -1;
    fzn.append("constraint int_lin_eq(")
        .append(Arrays.toString(w).replace(" ", ""))
        .append(",[")
        .append(String.join(",", all))
        .append(",obj],0);\n");
    fzn.append(maximize ? "solve maximize obj;\n" : "solve minimize obj;\n");
    return fzn.toString();
  }

  @Test
  void theBoundHoldsAndTheOptimumStays() throws IOException {
    Random random = new Random(21);
    int certified = 0;
    int tight = 0;
    for (int trial = 0; trial < 150; trial++) {
      boolean maximize = random.nextBoolean();
      String model = randomModel(random, maximize);
      String lcg = trial % 2 == 0 ? "on" : "off";
      String reference = optimum(run(model, false, false, "--lcg", lcg));
      // every other pair of trials prices the blocks in copies with lazy clause generation
      boolean copy = trial % 4 >= 2;
      String out = run(model, true, copy, "-s", "--search-statistics", "--lcg", lcg);
      String context = "trial " + trial + "\n" + model + "\n" + out;
      assertEquals(reference, optimum(out), context);
      Matcher m = BOUND.matcher(out);
      if (m.find() && !reference.equals("UNSATISFIABLE")) {
        long bound = Long.parseLong(m.group(1));
        long opt = Long.parseLong(reference);
        assertTrue(maximize ? bound >= opt : bound <= opt, context);
        certified++;
        tight += bound == opt ? 1 : 0;
      }
    }
    assertTrue(certified > 50, "certified " + certified);
    assertTrue(tight > 10, "tight " + tight);
  }

  /** Two blocks of which the cheap assignments need the same value of a count of at most one. */
  @Test
  void theBoundIsAboveTheRootBound() throws IOException {
    StringBuilder fzn = new StringBuilder();
    for (int b = 0; b < 2; b++) {
      for (int i = 0; i < 3; i++) {
        fzn.append("var 0..2: x").append(b).append(i).append(";\n");
      }
    }
    fzn.append("var 0..100: obj:: output_var;\n");
    for (int b = 0; b < 2; b++) {
      fzn.append("constraint int_ne(x").append(b).append("0,x").append(b).append("1);\n");
      fzn.append("constraint int_ne(x").append(b).append("1,x").append(b).append("2);\n");
      fzn.append("constraint int_ne(x").append(b).append("0,x").append(b).append("2);\n");
    }
    // each block is a permutation of 0..2 that costs 2 x?0, and at most one block has x?0 = 0: the
    // root bound is 0 and the decomposition bound the optimum, 2
    fzn.append("constraint jacop_count_values_bounds([x00,x10],[0],[0],[1]);\n");
    fzn.append("constraint int_lin_eq([2,2,-1],[x00,x10,obj],0);\n");
    fzn.append("solve minimize obj;\n");
    String model = fzn.toString();
    String out = run(model, true, false, "-s", "--search-statistics");
    assertEquals("2", optimum(out), out);
    Matcher m = BOUND.matcher(out);
    assertTrue(m.find(), out);
    assertEquals(2, Long.parseLong(m.group(1)), out);
  }

  private String run(String model, boolean decomposition, boolean copy, String... options)
      throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      if (decomposition) {
        System.setProperty("org.jacop.fz.decomposition", "true");
        System.setProperty("org.jacop.fz.decomposition.large", "2");
        if (copy) {
          System.setProperty("org.jacop.fz.decomposition.storeMs", "0");
        }
      }
      new Fz2jacop().callMain(args);
    } finally {
      System.clearProperty("org.jacop.fz.decomposition");
      System.clearProperty("org.jacop.fz.decomposition.large");
      System.clearProperty("org.jacop.fz.decomposition.storeMs");
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  // the value of obj in the last solution, or the status when there is none
  private static String optimum(String out) {
    String last = "UNSATISFIABLE";
    for (String line : out.split("\\R")) {
      if (line.startsWith("obj = ")) {
        last = line.substring(6, line.length() - 1);
      }
    }
    return last;
  }
}
