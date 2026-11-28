/*
 * FactoredRowFlatzincTest.java
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
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random models with a linear row whose variables are all multiplied by one variable (the product
 * rows of {@link org.jacop.fz.constraints.FactoredRowDetector}): factors of either sign or of both
 * signs, equality and inequality rows, repeated variables, a product of the factor with itself and
 * a missing product. The redundant rows must keep every solution and every optimum, and a small
 * cutting stock model must get its material bound at the root.
 */
class FactoredRowFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.factoredRows";

  @TempDir Path tmp;

  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    List<String> cs = new ArrayList<>();
    int n = 2 + random.nextInt(3);
    int sign = random.nextInt(3);
    int mMin = sign == 0 ? 0 : sign == 1 ? -3 : -2;
    int mMax = sign == 0 ? 3 : sign == 1 ? 0 : 2;
    fzn.append("var ").append(mMin).append("..").append(mMax).append(": m:: output_var;\n");
    String[] xs = new String[n];
    List<String> zs = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      // a repeated variable, or the factor itself
      if (i > 0 && random.nextInt(6) == 0) {
        xs[i] = xs[0];
        continue;
      }
      if (random.nextInt(8) == 0) {
        xs[i] = "m";
      } else {
        xs[i] = "x" + i;
        int lo = random.nextInt(3) - 1;
        fzn.append("var ").append(lo).append("..").append(lo + 1 + random.nextInt(3));
        fzn.append(": x").append(i).append(":: output_var;\n");
      }
    }
    boolean missing = random.nextInt(6) == 0;
    List<String> done = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      if (done.contains(xs[i]) || (missing && i == n - 1)) {
        continue;
      }
      done.add(xs[i]);
      String z = "z" + i;
      zs.add(z);
      fzn.append("var -20..20: ").append(z).append(":: output_var;\n");
      cs.add(
          random.nextBoolean()
              ? "int_times(" + xs[i] + ",m," + z + ")"
              : "int_times(m," + xs[i] + "," + z + ")");
    }
    List<String> a = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      int c = random.nextInt(7) - 3;
      a.add(String.valueOf(c == 0 ? 2 : c));
    }
    String kind = random.nextInt(3) == 0 ? "int_lin_eq" : "int_lin_le";
    cs.add(
        kind
            + "(["
            + String.join(",", a)
            + "],["
            + String.join(",", xs)
            + "],"
            + (random.nextInt(7) - 2)
            + ")");
    fzn.append("var -60..60: obj:: output_var;\n");
    List<String> w = new ArrayList<>();
    for (int k = 0; k < zs.size(); k++) {
      w.add(String.valueOf(random.nextInt(5) - 2));
    }
    w.add("-1");
    List<String> terms = new ArrayList<>(zs);
    terms.add("obj");
    cs.add("int_lin_eq([" + String.join(",", w) + "],[" + String.join(",", terms) + "],0)");
    cs.forEach(s -> fzn.append("constraint ").append(s).append(";\n"));
    String direction = random.nextBoolean() ? "maximize" : "minimize";
    fzn.append(optimise ? "solve " + direction + " obj;\n" : "solve satisfy;\n");
    return fzn.toString();
  }

  @Test
  void productRowsKeepAllSolutions() throws IOException {
    Random random = new Random(91);
    int fired = 0;
    int trials = Integer.getInteger("factoredrows.trials", 200);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String on = run(model, true, "-a", "-s", "-v");
      fired += on.contains("factoredRows=") ? 1 : 0;
      String off = run(model, false, "-a");
      assertEquals(solutions(off), solutions(on), "trial " + trial + "\n" + model + "\n" + on);
    }
    assertTrue(fired > trials / 3, "fired " + fired);
    assertTrue(fired < trials, "fired " + fired);
  }

  @Test
  void productRowsKeepOptima() throws IOException {
    Random random = new Random(92);
    int trials = Integer.getInteger("factoredrows.trials", 200) / 2;
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
  void cuttingStockGetsTheMaterialBoundAtTheRoot() throws IOException {
    // the 2019 MiniZinc Challenge stack-cuttingstock d3 without the stack limit: 4 patterns of a
    // stock of 25, sizes 2, 3, 7, 8, 12 and demands 12, 8, 11, 30, 2; material 389 > 15 * 25
    int[] size = {2, 3, 7, 8, 12};
    int[] number = {12, 8, 11, 30, 2};
    int k = 4;
    StringBuilder fzn = new StringBuilder();
    List<String> cs = new ArrayList<>();
    List<String> ms = new ArrayList<>();
    for (int c = 0; c < k; c++) {
      fzn.append("var 0..30: m").append(c).append(":: output_var;\n");
      ms.add("m" + c);
      List<String> xs = new ArrayList<>();
      List<String> w = new ArrayList<>();
      for (int p = 0; p < size.length; p++) {
        fzn.append("var 0..25: x").append(c).append('_').append(p).append(";\n");
        fzn.append("var 0..750: z").append(c).append('_').append(p).append(";\n");
        cs.add("int_times(x" + c + "_" + p + ",m" + c + ",z" + c + "_" + p + ")");
        xs.add("x" + c + "_" + p);
        w.add(String.valueOf(size[p]));
      }
      cs.add("int_lin_le([" + String.join(",", w) + "],[" + String.join(",", xs) + "],25)");
    }
    for (int p = 0; p < size.length; p++) {
      List<String> zs = new ArrayList<>();
      for (int c = 0; c < k; c++) {
        zs.add("z" + c + "_" + p);
      }
      cs.add("int_lin_le([-1,-1,-1,-1],[" + String.join(",", zs) + "]," + -number[p] + ")");
    }
    fzn.append("var 0..120: obj:: output_var;\n");
    cs.add("int_lin_eq([1,1,1,1,-1],[" + String.join(",", ms) + ",obj],0)");
    cs.forEach(s -> fzn.append("constraint ").append(s).append(";\n"));
    fzn.append("solve minimize obj;\n");
    String model = fzn.toString();
    String on = run(model, true, "-s", "-v");
    assertTrue(on.contains("%%%mzn-stat: factoredRows=4"), on);
    assertTrue(on.contains("%%%mzn-stat: lpRootBound=15.5"), on);
    assertEquals("16", optimum(on));
  }

  private static int solutions(String out) {
    return out.split("----------", -1).length - 1;
  }

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

  private String run(String model, boolean detect, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, String.valueOf(detect));
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(PROPERTY);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
