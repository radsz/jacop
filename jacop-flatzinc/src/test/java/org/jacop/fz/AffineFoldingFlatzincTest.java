/*
 * AffineFoldingFlatzincTest.java
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
import java.lang.reflect.Constructor;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random models with variables defined as affine functions of others and used in linear
 * constraints, as MiniZinc leaves products by constants inside sums: folding them into the rows
 * must keep every solution and every optimum.
 */
class AffineFoldingFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.affineFolding";

  private static final String ROWS = "org.jacop.fz.affineFoldingRows";

  @TempDir Path tmp;

  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    int n = 2 + random.nextInt(2);
    for (int i = 0; i < n; i++) {
      fzn.append("var ").append(random.nextInt(2) - 1).append("..").append(2 + random.nextInt(2));
      fzn.append(": x").append(i).append(":: output_var;\n");
    }
    List<String> constraints = new ArrayList<>();
    List<String> zs = new ArrayList<>();
    int k = 2 + random.nextInt(4);
    for (int d = 0; d < k; d++) {
      String x = random.nextInt(4) == 0 && !zs.isEmpty() ? zs.get(0) : "x" + random.nextInt(n);
      String z = "z" + d;
      int c = random.nextInt(7) - 3;
      int q = random.nextInt(5) - 2;
      switch (random.nextInt(4)) {
        case 0 -> constraints.add("constraint int_times(" + c + "," + x + "," + z + ")");
        case 1 -> constraints.add("constraint int_times(" + x + "," + c + "," + z + ")");
        case 2 -> constraints.add("constraint int_plus(" + x + "," + q + "," + z + ")");
        default -> {
          int a = random.nextBoolean() ? 1 : -1;
          int b = random.nextInt(5) - 2;
          constraints.add(
              "constraint int_lin_eq([" + a + "," + b + "],[" + z + "," + x + "]," + q + ")");
        }
      }
      // a narrowed domain sometimes cuts the image of x, which makes the definition a constraint
      fzn.append(random.nextInt(3) == 0 ? "var -3..3: " : "var -20..20: ").append(z).append(";\n");
      zs.add(z);
    }
    // the rows that use the defined variables, with the variables they are defined from
    List<String> bools = new ArrayList<>();
    int rows = 1 + random.nextInt(3);
    for (int r = 0; r < rows; r++) {
      List<String> vars = new ArrayList<>();
      List<Integer> coefficients = new ArrayList<>();
      int terms = 1 + random.nextInt(3);
      for (int t = 0; t < terms; t++) {
        vars.add(random.nextInt(3) == 0 ? "x" + random.nextInt(n) : zs.get(random.nextInt(k)));
        coefficients.add(random.nextInt(5) - 2);
      }
      String a = coefficients.toString().replace(" ", "");
      String v = vars.toString().replace(" ", "");
      int rhs = random.nextInt(9) - 4;
      String b = "b" + r;
      switch (random.nextInt(6)) {
        case 0 -> constraints.add("constraint int_lin_le(" + a + "," + v + "," + rhs + ")");
        case 1 -> constraints.add("constraint int_lin_eq(" + a + "," + v + "," + rhs + ")");
        case 2 -> constraints.add("constraint int_lin_ne(" + a + "," + v + "," + rhs + ")");
        case 3 -> {
          constraints.add("constraint int_lin_le_reif(" + a + "," + v + "," + rhs + "," + b + ")");
          bools.add(b);
        }
        case 4 -> {
          constraints.add("constraint int_lin_eq_imp(" + a + "," + v + "," + rhs + "," + b + ")");
          bools.add(b);
        }
        default -> {
          constraints.add("constraint int_lin_ne_reif(" + a + "," + v + "," + rhs + "," + b + ")");
          bools.add(b);
        }
      }
    }
    // an occurrence outside the rows keeps the variable
    if (random.nextInt(4) == 0) {
      constraints.add("constraint int_le(" + zs.get(random.nextInt(k)) + ",x0)");
    }
    for (String b : bools) {
      fzn.append("var bool: ").append(b).append(":: output_var;\n");
    }
    if (optimise) {
      fzn.append("var -1000..1000: obj:: output_var;\n");
      StringBuilder a = new StringBuilder("[");
      StringBuilder v = new StringBuilder("[");
      for (String z : zs) {
        a.append(random.nextInt(5) - 2).append(',');
        v.append(z).append(',');
      }
      a.append("-1]");
      v.append("obj]");
      constraints.add("constraint int_lin_eq(" + a + "," + v + ",0)");
    }
    constraints.forEach(c -> fzn.append(c).append(";\n"));
    if (optimise) {
      fzn.append(random.nextBoolean() ? "solve maximize obj;\n" : "solve minimize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  /**
   * The occurrences of each variable are kept in a small array set, not in a HashSet with its own
   * map and table: those took 250 MB of the 1.46 million Boolean variables of XCSP 2022
   * RoomMate-sr0700 while the model was read. A constraint is a repeat only of the last one added,
   * since the arguments of one constraint are read together.
   */
  @Test
  @SuppressWarnings("unchecked")
  void occurrencesAreSmallSetsWithoutRepeats() throws Exception {
    Constructor<?> make =
        Class.forName("org.jacop.fz.constraints.AffineFolding$Occurrences")
            .getDeclaredConstructor();
    make.setAccessible(true);
    Set<ASTConstElem> set = (Set<ASTConstElem>) make.newInstance();
    ASTConstElem a = new ASTConstElem(ParserTreeConstants.JJTCONSTELEM);
    ASTConstElem b = new ASTConstElem(ParserTreeConstants.JJTCONSTELEM);
    ASTConstElem c = new ASTConstElem(ParserTreeConstants.JJTCONSTELEM);
    assertTrue(set.add(a));
    assertFalse(set.add(a));
    assertTrue(set.add(b));
    assertTrue(set.add(c));
    assertFalse(set.add(c));
    assertEquals(List.of(a, b, c), new ArrayList<>(set));
    assertEquals(3, set.size());
    assertFalse(set instanceof HashSet);
  }

  @Test
  void foldingKeepsAllSolutions() throws IOException {
    Random random = new Random(51);
    int folded = 0;
    int trials = Integer.getInteger("affine.trials", 300);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      // every other trial also folds variables shared by several rows
      String on =
          trial % 2 == 0 ? run(model, true, "-a", "-debug") : runShared(model, "-a", "-debug");
      folded += on.contains("% affine folding") ? 1 : 0;
      String off = run(model, false, "-a");
      assertEquals(solutions(off), solutions(on), "trial " + trial + "\n" + model + "\n" + on);
    }
    assertTrue(folded > trials / 2, "folded " + folded);
  }

  @Test
  void foldingKeepsOptima() throws IOException {
    Random random = new Random(52);
    int trials = Integer.getInteger("affine.trials", 300) * 2 / 3;
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
        assertEquals(
            expected,
            optimum(runShared(model, options)),
            "trial " + trial + " shared " + Arrays.toString(options) + "\n" + model);
      }
    }
  }

  /** The three forms of definition, a row with both z and x, and a domain that cuts the image. */
  @Test
  void definitionsFoldIntoTheirRows() throws IOException {
    String model =
        """
        var 0..3: x:: output_var;
        var 0..3: y:: output_var;
        var 0..30: z1;
        var -10..10: z2;
        var -20..20: z3;
        var 0..5: z4;
        constraint int_times(10,x,z1);
        constraint int_plus(y,-2,z2);
        constraint int_lin_eq([-1,3],[z3,x],1);
        constraint int_times(2,y,z4);
        constraint int_lin_le([1,1,1,1],[z1,z2,z3,x],25);
        constraint int_lin_ne([1,-1],[z4,y],2);
        solve satisfy;
        """;
    String out = run(model, true, "-a", "-debug");
    // z4 in 0..5 cuts 2*y at y = 3, so its definition stays a constraint
    assertTrue(out.contains("% affine folding: 3 variables folded into 1 linear constraints"), out);
    assertEquals(solutions(run(model, false, "-a")), solutions(out), out);
  }

  // folding variables in any number of rows
  private String runShared(String model, String... options) throws IOException {
    System.setProperty(ROWS, "1000");
    try {
      return run(model, true, options);
    } finally {
      System.clearProperty(ROWS);
    }
  }

  private static int solutions(String out) {
    return out.split("----------", -1).length - 1;
  }

  private String run(String model, boolean folding, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, String.valueOf(folding));
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
