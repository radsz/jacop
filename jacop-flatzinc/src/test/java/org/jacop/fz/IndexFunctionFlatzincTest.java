/*
 * IndexFunctionFlatzincTest.java
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
 * Random models in the shape MiniZinc gives an option chosen per item with attributes looked up by
 * the choice (the 2020 Challenge stable-goods model): products of two lookups by one index, and
 * clauses of implied comparisons between lookups by two indexes and a variable array. The index
 * function detector must keep every solution and every optimum.
 */
class IndexFunctionFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.indexFunctions";

  @TempDir Path tmp;

  private static String constants(Random random, int n, int lo, int hi) {
    StringBuilder s = new StringBuilder("[");
    for (int i = 0; i < n; i++) {
      s.append(i > 0 ? "," : "").append(lo + random.nextInt(hi - lo + 1));
    }
    return s.append(']').toString();
  }

  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    List<String> cs = new ArrayList<>();
    int items = 2 + random.nextInt(2);
    int options = 2 + random.nextInt(3);
    int goods = 3;
    // r[g]: the remainders, a variable array indexed by a looked up good
    fzn.append("array [1..").append(goods).append("] of int: VAL = ");
    fzn.append(constants(random, goods, 1, 5)).append(";\n");
    for (int g = 1; g <= goods; g++) {
      fzn.append("var 0..4: r").append(g).append(":: output_var;\n");
    }
    fzn.append("array [1..").append(goods).append("] of var int: R = [r1,r2,r3];\n");
    List<String> loads = new ArrayList<>();
    List<String> weights = new ArrayList<>();
    for (int p = 0; p < items; p++) {
      String good = "G" + p;
      String num = "N" + p;
      fzn.append("array [1..").append(options).append("] of int: ").append(good).append(" = ");
      fzn.append(constants(random, options, 1, goods)).append(";\n");
      fzn.append("array [1..").append(options).append("] of int: ").append(num).append(" = ");
      fzn.append(constants(random, options, 0, 3)).append(";\n");
      fzn.append("var 1..").append(options).append(": pref").append(p).append(":: output_var;\n");
      fzn.append("var 1..").append(goods).append(": g").append(p).append(";\n");
      fzn.append("var 0..3: n").append(p).append(";\n");
      fzn.append("var 0..4: rem").append(p).append(";\n");
      cs.add("jacop_array_var_int_element_nonshifted(pref" + p + "," + good + ",g" + p + ",1)");
      cs.add("jacop_array_var_int_element_nonshifted(pref" + p + "," + num + ",n" + p + ",1)");
      cs.add("jacop_array_var_int_element_nonshifted(g" + p + ",R,rem" + p + ",1)");
      for (int g = 1; g <= goods; g++) {
        String b = "is" + p + "_" + g;
        String i = "i" + p + "_" + g;
        String z = "z" + p + "_" + g;
        fzn.append("var bool: ").append(b).append(";\n");
        fzn.append("var 0..1: ").append(i).append(";\n");
        fzn.append("var 0..3: ").append(z).append(";\n");
        cs.add("int_eq_reif(g" + p + "," + g + "," + b + ")");
        cs.add("bool2int(" + b + "," + i + ")");
        cs.add(
            random.nextBoolean()
                ? "int_times(" + i + ",n" + p + "," + z + ")"
                : "int_times(n" + p + "," + i + "," + z + ")");
        loads.add(z);
        weights.add(String.valueOf(g));
      }
    }
    // the usage of each good plus its remainder is 4
    for (int g = 1; g <= goods; g++) {
      StringBuilder vars = new StringBuilder("[");
      StringBuilder ones = new StringBuilder("[");
      for (int p = 0; p < items; p++) {
        vars.append(p > 0 ? "," : "").append('z').append(p).append('_').append(g);
        ones.append(p > 0 ? "," : "").append('1');
      }
      cs.add("int_lin_eq(" + ones + ",1]," + vars + ",r" + g + "],4)");
    }
    // a stability-like clause per pair: one of the implied comparisons holds
    int k = 0;
    for (int p = 0; p < items; p++) {
      for (int q = p + 1; q < items; q++) {
        String b1 = "c" + k++;
        String b2 = "c" + k++;
        String b3 = "c" + k++;
        fzn.append("var bool: ").append(b1).append(";\nvar bool: ").append(b2);
        fzn.append(";\nvar bool: ").append(b3).append(";\n");
        cs.add(
            "int_lin_le_imp([1,-1],[n"
                + p
                + ",rem"
                + q
                + "],"
                + random.nextInt(2)
                + ","
                + b1
                + ")");
        cs.add("int_eq_imp(g" + p + ",g" + q + "," + b2 + ")");
        cs.add(
            random.nextBoolean()
                ? "int_le_imp(n" + q + ",n" + p + "," + b3 + ")"
                : "int_ne_imp(n" + q + "," + random.nextInt(3) + "," + b3 + ")");
        cs.add("bool_clause([" + b1 + "," + b2 + "," + b3 + "],[])");
      }
    }
    if (optimise) {
      fzn.append("var 0..60: obj:: output_var;\n");
      cs.add("int_lin_eq([1,1,1,-1],[r1,r2,r3,obj],0)");
    }
    cs.forEach(s -> fzn.append("constraint ").append(s).append(";\n"));
    fzn.append(optimise ? "solve maximize obj;\n" : "solve satisfy;\n");
    return fzn.toString();
  }

  @Test
  void rewritingKeepsAllSolutions() throws IOException {
    Random random = new Random(71);
    int rewritten = 0;
    int unfolded = 0;
    int trials = Integer.getInteger("indexfn.trials", 150);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String on = run(model, true, "-a", "-debug");
      rewritten += on.contains("% index function products: ") ? 1 : 0;
      unfolded += on.contains("unfolded clauses: 0 ") ? 0 : 1;
      String off = run(model, false, "-a");
      assertEquals(solutions(off), solutions(on), "trial " + trial + "\n" + model + "\n" + on);
    }
    assertTrue(rewritten > trials / 2, "rewritten " + rewritten);
    assertTrue(unfolded > trials / 2, "unfolded " + unfolded);
  }

  @Test
  void rewritingKeepsOptima() throws IOException {
    Random random = new Random(72);
    int trials = Integer.getInteger("indexfn.trials", 150) / 2;
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
