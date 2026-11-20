/*
 * CyclicDistanceFlatzincTest.java
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
 * Random models with distances on a cycle, min(|x - y|, c - |x - y|), written as MiniZinc flattens
 * them (int_lin_eq, int_abs, int_lin_eq, int_min): the cyclic distance detector must keep every
 * solution and every optimum, whether it replaces the parts or adds next to them.
 */
class CyclicDistanceFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.cyclicDistance";

  @TempDir Path tmp;

  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    int c = 3 + random.nextInt(5);
    int n = 3 + random.nextInt(2);
    // positions, sometimes with a range wider than the cycle (no detection then)
    int top = random.nextInt(6) == 0 ? c + 1 : c - 1;
    for (int i = 0; i < n; i++) {
      fzn.append("var 0..").append(top).append(": x").append(i).append(":: output_var;\n");
    }
    List<String> constraints = new ArrayList<>();
    List<String> ds = new ArrayList<>();
    int edges = 2 + random.nextInt(3);
    for (int k = 0; k < edges; k++) {
      int i = random.nextInt(n);
      int j = (i + 1 + random.nextInt(n - 1)) % n;
      String e = "e" + k;
      String a = "a" + k;
      String b = "b" + k;
      String d = "d" + k;
      fzn.append("var ").append(-top).append("..").append(top).append(": ").append(e);
      fzn.append(random.nextInt(5) == 0 ? ":: output_var;\n" : ";\n");
      fzn.append("var 0..").append(top).append(": ").append(a).append(";\n");
      fzn.append("var ").append(c - top).append("..").append(c).append(": ").append(b);
      fzn.append(random.nextInt(6) == 0 ? ":: output_var;\n" : ";\n");
      fzn.append("var 0..").append(c).append(": ").append(d).append(":: output_var;\n");
      constraints.add("constraint int_lin_eq([1,-1,-1],[x" + i + ",x" + j + "," + e + "],0)");
      constraints.add("constraint int_abs(" + e + "," + a + ")");
      constraints.add(
          random.nextBoolean()
              ? "constraint int_lin_eq([-1,-1],[" + a + "," + b + "]," + -c + ")"
              : "constraint int_lin_eq([1,1],[" + b + "," + a + "]," + c + ")");
      constraints.add(
          random.nextBoolean()
              ? "constraint int_min(" + a + "," + b + "," + d + ")"
              : "constraint int_min(" + b + "," + a + "," + d + ")");
      // another use of a or e keeps it
      if (random.nextInt(6) == 0) {
        constraints.add("constraint int_le(" + a + "," + (c - 1) + ")");
      }
      if (random.nextInt(6) == 0) {
        constraints.add("constraint int_ne(" + e + ",1)");
      }
      ds.add(d);
    }
    if (random.nextBoolean()) {
      StringBuilder all = new StringBuilder("[");
      for (int i = 0; i < n; i++) {
        all.append(i > 0 ? "," : "").append('x').append(i);
      }
      constraints.add("constraint jacop_alldiff(" + all + "])");
    }
    if (optimise) {
      fzn.append("var 0..").append(c).append(": obj:: output_var;\n");
      fzn.append("array [1..").append(ds.size()).append("] of var int: ds = ");
      fzn.append(ds.toString().replace(" ", "")).append(";\n");
      constraints.add("constraint jacop_maximum(obj,ds)");
    } else {
      constraints.add("constraint int_le(" + ds.get(0) + "," + (1 + random.nextInt(c / 2)) + ")");
    }
    constraints.forEach(s -> fzn.append(s).append(";\n"));
    fzn.append(optimise ? "solve minimize obj;\n" : "solve satisfy;\n");
    return fzn.toString();
  }

  @Test
  void detectionKeepsAllSolutions() throws IOException {
    Random random = new Random(61);
    int detected = 0;
    int trials = Integer.getInteger("cyclic.trials", 200);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String on = run(model, true, "-a", "-debug");
      detected += on.contains("% cyclic distances: 0") ? 0 : 1;
      String off = run(model, false, "-a");
      assertEquals(solutions(off), solutions(on), "trial " + trial + "\n" + model + "\n" + on);
    }
    assertTrue(detected > trials / 2, "detected " + detected);
  }

  @Test
  void detectionKeepsOptima() throws IOException {
    Random random = new Random(62);
    int trials = Integer.getInteger("cyclic.trials", 200) / 2;
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

  /**
   * A distance whose a, b or e is declared equal to another variable (var int: q = a0): the
   * equality is posted on that variable outside the constraint items, so the detector must keep it
   * like an alias, or q loses its link when a0 is dropped.
   */
  @Test
  void variablesOfDeclaredEqualitiesAreKept() throws IOException {
    Random random = new Random(63);
    int trials = Integer.getInteger("cyclic.trials", 200) / 4;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String target = new String[] {"a0", "b0", "e0"}[random.nextInt(3)];
      int at = model.indexOf("constraint ");
      model =
          model.substring(0, at)
              + "var int: q:: output_var = "
              + target
              + ";\n"
              + model.substring(at);
      String on = run(model, true, "-a");
      String off = run(model, false, "-a");
      assertEquals(solutions(off), solutions(on), "trial " + trial + "\n" + model);
    }
  }

  /**
   * A distance whose a, b or e is declared with a domain narrower than |e|, c - a or the difference
   * it stands for: the declaration is a constraint, which the replacement of a and b and the
   * substitution of e would drop. The solutions must stay those of the detector off (13 or 19 here,
   * where dropping a domain gave 25).
   */
  @Test
  void narrowDomainsOfTheDroppedVariablesAreKept() throws IOException {
    String[][] domains = {
      {"-4..4", "0..4", "1..5"},
      {"-4..4", "0..1", "1..5"},
      {"-4..4", "0..2", "1..5"},
      {"-4..4", "1..4", "1..5"},
      {"-4..4", "0..4", "4..5"},
      {"-4..4", "0..4", "1..4"},
      {"-2..2", "0..4", "1..5"},
      {"-4..3", "0..4", "1..5"},
      {"0..4", "0..4", "1..5"}
    };
    for (String[] d : domains) {
      String model =
          "var 0..4: x0:: output_var;\n"
              + "var 0..4: x1:: output_var;\n"
              + "var "
              + d[0]
              + ": e0;\nvar "
              + d[1]
              + ": a0;\nvar "
              + d[2]
              + ": b0;\n"
              + "var 0..5: d0:: output_var;\n"
              + "constraint int_lin_eq([1,-1,-1],[x0,x1,e0],0);\n"
              + "constraint int_abs(e0,a0);\n"
              + "constraint int_lin_eq([-1,-1],[a0,b0],-5);\n"
              + "constraint int_min(a0,b0,d0);\n"
              + "solve satisfy;\n";
      String on = run(model, true, "-a", "-debug");
      assertTrue(on.contains("% cyclic distances: 1"), on);
      assertEquals(solutions(run(model, false, "-a")), solutions(on), Arrays.toString(d));
    }
  }

  /**
   * Unless the property forces it, the distances are rewritten only in a model with at least
   * org.jacop.fz.cyclicDistance.minDistances of them (400 by default): the small random models keep
   * the minimum, and with the threshold at 1 they are rewritten with the same solutions.
   */
  @Test
  void onlyModelsWithManyDistancesAreRewrittenByDefault() throws IOException {
    Random random = new Random(63);
    int rewritten = 0;
    for (int trial = 0; trial < 20; trial++) {
      String model = randomModel(random, false);
      String off = run(model, false, "-a");
      String auto = run(model, null, "-a", "-debug");
      assertTrue(!auto.contains("% cyclic distances: ") || auto.contains("fewer than 400"), auto);
      assertEquals(solutions(off), solutions(auto), "trial " + trial + "\n" + model);
      System.setProperty(PROPERTY + ".minDistances", "1");
      try {
        String low = run(model, null, "-a", "-debug");
        rewritten += low.contains("% cyclic distances: 0") ? 0 : 1;
        assertEquals(solutions(off), solutions(low), "trial " + trial + "\n" + model + "\n" + low);
      } finally {
        System.clearProperty(PROPERTY + ".minDistances");
      }
    }
    assertTrue(rewritten > 10, "rewritten " + rewritten);
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

  private String run(String model, Boolean detect, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    if (detect != null) {
      System.setProperty(PROPERTY, String.valueOf(detect));
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
}
