/*
 * CommonSubexpressionsFlatzincTest.java
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
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random models in which constraints compute the same function of the same inputs, as MiniZinc
 * leaves them after its own aliasing: merging their outputs and removing duplicates must keep every
 * solution and every optimum.
 */
class CommonSubexpressionsFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.cse";

  @TempDir Path tmp;

  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    int n = 3 + random.nextInt(2);
    for (int i = 0; i < n; i++) {
      fzn.append("var 0..").append(2 + random.nextInt(2)).append(": x").append(i);
      fzn.append(":: output_var;\n");
    }
    List<String> constraints = new ArrayList<>();
    List<String> bools = new ArrayList<>();
    List<String> ints = new ArrayList<>();
    int k = 4 + random.nextInt(5);
    for (int c = 0; c < k; c++) {
      // inputs from a small pool, so that the same function of the same inputs comes again
      String x = "x" + random.nextInt(2);
      String y = "x" + (1 + random.nextInt(2));
      String b = "b" + c;
      String r = "r" + c;
      switch (random.nextInt(8)) {
        case 0 -> {
          constraints.add("constraint int_eq_reif(" + x + "," + y + "," + b + ")");
          bools.add(b);
        }
        case 1 -> {
          constraints.add("constraint int_le_reif(" + x + "," + y + "," + b + ")");
          bools.add(b);
        }
        case 2 -> {
          constraints.add("constraint int_ne_reif(" + y + "," + x + "," + b + ")");
          bools.add(b);
        }
        case 3 -> {
          constraints.add(
              "constraint int_lin_le_reif([1,-1],["
                  + x
                  + ","
                  + y
                  + "],"
                  + random.nextInt(2)
                  + ","
                  + b
                  + ")");
          bools.add(b);
        }
        case 4 -> {
          constraints.add("constraint int_plus(" + x + "," + y + "," + r + ")");
          ints.add(r);
        }
        case 5 -> {
          constraints.add("constraint int_max(" + y + "," + x + "," + r + ")");
          ints.add(r);
        }
        case 6 -> {
          constraints.add("constraint int_le(" + x + "," + y + ")");
          constraints.add("constraint int_le(" + x + "," + y + ")");
        }
        default -> {
          constraints.add("constraint int_times(" + x + "," + y + "," + r + ")");
          ints.add(r);
        }
      }
    }
    // connectives over the reified outputs, which become equal after merging
    for (int c = 0; c + 1 < bools.size() && c < 3; c++) {
      String a = bools.get(random.nextInt(bools.size()));
      String b = bools.get(random.nextInt(bools.size()));
      constraints.add("constraint bool_and(" + a + "," + b + ",a" + c + ")");
      constraints.add("constraint bool_and(" + b + "," + a + ",a" + c + "x)");
      constraints.add("constraint bool_clause([a" + c + ",a" + c + "x],[" + a + "])");
      fzn.append("var bool: a").append(c).append(";\nvar bool: a").append(c).append("x;\n");
    }
    // equalities left in the model
    if (bools.size() >= 2 && random.nextBoolean()) {
      constraints.add("constraint bool_eq(" + bools.get(0) + "," + bools.get(1) + ")");
    }
    if (ints.size() >= 2 && random.nextBoolean()) {
      constraints.add(
          "constraint int_lin_eq([1,-1],["
              + ints.get(0)
              + ","
              + ints.get(ints.size() - 1)
              + "],0)");
    }
    if (!bools.isEmpty() && random.nextInt(3) == 0) {
      constraints.add("constraint array_bool_or([" + bools.get(0) + "],o)");
      constraints.add("constraint bool_clause([o],[" + bools.get(bools.size() - 1) + "])");
      fzn.append("var bool: o;\n");
    }
    // the integers of the Booleans, summed with the integer outputs
    List<String> terms = new ArrayList<>(ints);
    for (int i = 0; i < bools.size(); i++) {
      constraints.add("constraint bool2int(" + bools.get(i) + ",i" + i + ")");
      fzn.append("var 0..1: i").append(i).append(";\n");
      terms.add("i" + i);
    }
    for (String b : bools) {
      fzn.append("var bool: ").append(b).append(random.nextInt(4) == 0 ? ":: output_var" : "");
      fzn.append(";\n");
    }
    for (String r : ints) {
      fzn.append("var 0..9: ").append(r).append(";\n");
    }
    if (!terms.isEmpty()) {
      int[] a = IntStream.range(0, terms.size()).map(i -> 1 + random.nextInt(2)).toArray();
      String sum =
          "constraint int_lin_le("
              + Arrays.toString(a).replace(" ", "")
              + ","
              + terms.stream().collect(Collectors.joining(",", "[", "]"))
              + ","
              + (terms.size() + random.nextInt(4 * terms.size()))
              + ")";
      constraints.add(sum);
    }
    if (optimise) {
      fzn.append("var -100..100: obj:: output_var;\n");
    }
    constraints.forEach(c -> fzn.append(c).append(";\n"));
    if (optimise) {
      List<String> all = new ArrayList<>(terms);
      for (int i = 0; i < n; i++) {
        all.add("x" + i);
      }
      int[] a =
          IntStream.range(0, all.size() + 1)
              .map(i -> i == all.size() ? -1 : random.nextInt(5) - 2)
              .toArray();
      all.add("obj");
      fzn.append("constraint int_lin_eq(")
          .append(Arrays.toString(a).replace(" ", ""))
          .append(",")
          .append(all.stream().collect(Collectors.joining(",", "[", "]")))
          .append(",0);\n");
      fzn.append(random.nextBoolean() ? "solve maximize obj;\n" : "solve minimize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  @Test
  void mergingKeepsAllSolutions() throws IOException {
    Random random = new Random(43);
    int merged = 0;
    int trials = Integer.getInteger("cse.trials", 300);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String on = run(model, true, "-a", "-debug");
      merged += on.contains("% common subexpressions") ? 1 : 0;
      String off = run(model, false, "-a");
      assertEquals(solutions(off), solutions(on), "trial " + trial + "\n" + model + "\n" + on);
    }
    assertTrue(merged > trials / 2, "merged " + merged);
  }

  @Test
  void mergingKeepsOptima() throws IOException {
    Random random = new Random(44);
    int trials = Integer.getInteger("cse.trials", 300) * 2 / 3;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, true);
      String expected = optimum(run(model, false, "--lcg", "off"));
      for (String[] options :
          List.of(
              new String[] {"--lcg", "off"}, new String[] {"--lcg", "on"}, new String[] {"-f"})) {
        assertEquals(
            expected,
            optimum(run(model, true, options)),
            "trial " + trial + " " + Arrays.toString(options) + "\n" + model);
      }
    }
  }

  @Test
  void equalReificationsBecomeOne() throws IOException {
    String model =
        """
        var 0..3: x:: output_var;
        var 0..3: y:: output_var;
        var bool: b1;
        var bool: b2;
        var 0..1: i1;
        var 0..1: i2;
        constraint int_eq_reif(x,y,b1);
        constraint int_eq_reif(y,x,b2);
        constraint bool2int(b1,i1);
        constraint bool2int(b2,i2);
        constraint int_lin_le([1,1],[i1,i2],1);
        solve satisfy;
        """;
    String out = run(model, true, "-a", "-debug");
    assertTrue(out.contains("% common subexpressions: 1 outputs merged"), out);
    // i1 + i2 <= 1 with i1 = i2 means x != y
    assertEquals(12, solutions(out), out);
    assertEquals(12, solutions(run(model, false, "-a")));
  }

  /** An int_eq or bool_eq with a constant is neither an equality of two variables nor a key. */
  @Test
  void equalitiesWithConstantsAreKept() throws IOException {
    String model =
        """
        var 0..3: x:: output_var;
        var 0..3: y:: output_var;
        var bool: b:: output_var;
        constraint int_eq(x,2);
        constraint int_eq(2,y);
        constraint bool_eq(b,true);
        constraint int_le(x,y);
        constraint int_le(x,y);
        solve satisfy;
        """;
    String out = run(model, true, "-a", "-debug");
    assertTrue(out.contains("1 duplicate constraints removed"), out);
    assertEquals(1, solutions(out), out);
    assertTrue(out.contains("x = 2;") && out.contains("y = 2;") && out.contains("b = true;"), out);
  }

  private static int solutions(String out) {
    return out.split("----------", -1).length - 1;
  }

  private String run(String model, boolean cse, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, String.valueOf(cse));
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(PROPERTY);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  // the value of obj in the last solution, or the status when there is none
  private static String optimum(String out) {
    String last = "UNSATISFIABLE";
    for (String line : out.split("\\R")) {
      if (line.startsWith("obj = ")) {
        last = line.substring(line.indexOf('=') + 2, line.length() - 1);
      }
    }
    assertTrue(out.contains("==========") || out.contains("UNSATISFIABLE"), out);
    return last;
  }
}
