/*
 * ProductOfSumsFlatzincTest.java
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
 * Random models in the shape MiniZinc gives the hypervolume objective of a diverse solution model
 * (the 2019 Challenge rcpsp-wet-diverse): a sum of {@code bool2int(E <= e /\ T <= t)} over all
 * pairs of thresholds, sometimes with a missing or repeated pair, an output conjunction or a second
 * coefficient, where the product of sums rewrite must not fire. It must keep every solution and
 * every optimum.
 */
class ProductOfSumsFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.productOfSums";

  private static final String MIN_TERMS = "org.jacop.fz.productOfSums.minTerms";

  @TempDir Path tmp;

  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    List<String> cs = new ArrayList<>();
    int maxE = 3 + random.nextInt(4);
    int maxT = 3 + random.nextInt(4);
    fzn.append("var 0..").append(maxE).append(": E:: output_var;\n");
    fzn.append("var 0..").append(maxT).append(": T:: output_var;\n");
    // distinct thresholds, as in the model, and sometimes one the domain makes true
    int na = 2 + random.nextInt(maxE - 1);
    int nb = 2 + random.nextInt(maxT - 1);
    int shift = random.nextInt(2);
    for (int i = 0; i < na; i++) {
      fzn.append("var bool: a").append(i).append(";\n");
      cs.add("int_le_reif(E," + (maxE + shift - na + i) + ",a" + i + ")");
    }
    for (int j = 0; j < nb; j++) {
      fzn.append("var bool: b").append(j).append(";\n");
      cs.add("int_le_reif(T," + (maxT + shift - nb + j) + ",b" + j + ")");
    }
    int w = random.nextBoolean() ? 1 : random.nextInt(5) - 2;
    w = w == 0 ? 3 : w;
    int flaw = random.nextInt(6);
    List<String> coefficients = new ArrayList<>();
    List<String> terms = new ArrayList<>();
    for (int i = 0; i < na; i++) {
      for (int j = 0; j < nb; j++) {
        if (flaw == 1 && i == 0 && j == 0) {
          // a missing pair
          continue;
        }
        String p = "p" + i + "_" + j;
        String y = "y" + i + "_" + j;
        fzn.append("var bool: ").append(p).append(flaw == 2 && i + j == 1 ? ":: output_var" : "");
        fzn.append(";\nvar 0..1: ").append(y).append(";\n");
        cs.add(
            random.nextBoolean()
                ? "array_bool_and([a" + i + ",b" + j + "]," + p + ")"
                : "array_bool_and([b" + j + ",a" + i + "]," + p + ")");
        cs.add("bool2int(" + p + "," + y + ")");
        coefficients.add(String.valueOf(flaw == 3 && i == 1 && j == 1 ? w + 1 : w));
        terms.add(y);
      }
    }
    if (flaw == 4) {
      // a repeated pair
      fzn.append("var bool: q;\nvar 0..1: z;\n");
      cs.add("array_bool_and([a0,b0],q)");
      cs.add("bool2int(q,z)");
      coefficients.add(String.valueOf(w));
      terms.add("z");
    }
    fzn.append("var -300..300: obj:: output_var;\n");
    coefficients.add(String.valueOf(random.nextInt(5) - 2));
    terms.add("E");
    coefficients.add("-1");
    terms.add("obj");
    cs.add(
        "int_lin_eq(["
            + String.join(",", coefficients)
            + "],["
            + String.join(",", terms)
            + "],"
            + (random.nextInt(7) - 3)
            + ")");
    cs.add("int_lin_le([1,1],[E,T]," + (2 + random.nextInt(maxE + maxT - 1)) + ")");
    if (!optimise) {
      cs.add("int_le(" + (random.nextInt(9) - 4) + ",obj)");
    }
    cs.forEach(s -> fzn.append("constraint ").append(s).append(";\n"));
    String direction = random.nextBoolean() ? "maximize" : "minimize";
    fzn.append(optimise ? "solve " + direction + " obj;\n" : "solve satisfy;\n");
    return fzn.toString();
  }

  @Test
  void rewritingKeepsAllSolutions() throws IOException {
    Random random = new Random(81);
    int rewritten = 0;
    int trials = Integer.getInteger("productsums.trials", 150);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String on = run(model, true, "-a", "-debug");
      rewritten += on.contains("% sums of conjunctions as products of sums: ") ? 1 : 0;
      String off = run(model, false, "-a");
      assertEquals(solutions(off), solutions(on), "trial " + trial + "\n" + model + "\n" + on);
    }
    assertTrue(rewritten > trials / 3, "rewritten " + rewritten);
    assertTrue(rewritten < trials, "rewritten " + rewritten);
  }

  @Test
  void rewritingKeepsOptima() throws IOException {
    Random random = new Random(82);
    int trials = Integer.getInteger("productsums.trials", 150) / 2;
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
    System.setProperty(MIN_TERMS, "4");
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(PROPERTY);
      System.clearProperty(MIN_TERMS);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
