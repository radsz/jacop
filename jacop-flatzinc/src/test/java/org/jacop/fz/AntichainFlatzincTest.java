/*
 * AntichainFlatzincTest.java
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
 * The LYM inequality of {@link org.jacop.fz.constraints.AntichainDetector} keeps the solutions of
 * random models of pairwise incomparable vectors, in the clause and the element forms of the
 * relations, and proves Sperner's bound at the root.
 */
class AntichainFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.antichain";

  @TempDir Path tmp;

  // the forms of a literal b -> u < v
  private static final String[] LESS = {
    "int_lin_le_imp([1,-1],[%s,%s],-1,%s)",
    "int_lin_le_reif([2,-2],[%s,%s],-1,%s)",
    "int_lt_reif(%s,%s,%s)",
    "int_lt_imp(%s,%s,%s)"
  };

  /**
   * A random model of n vectors of m coordinates over 0..h (sometimes one coordinate wider), each
   * ordered pair of vectors with "u[c] < v[c] for some c" in a random form, and sometimes a random
   * unary constraint on one coordinate.
   */
  private static String randomModel(Random random, boolean elements, int n) {
    int m = 2 + random.nextInt(2);
    int h = 1 + random.nextInt(2);
    int wide = random.nextInt(3) == 0 ? random.nextInt(m) : -1;
    StringBuilder fzn = new StringBuilder();
    StringBuilder con = new StringBuilder();
    for (int i = 0; i < n; i++) {
      for (int c = 0; c < m; c++) {
        fzn.append(String.format("var 0..%d: x%d_%d:: output_var;%n", c == wide ? h + 1 : h, i, c));
      }
    }
    int pair = 0;
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (i == j) {
          continue;
        }
        pair++;
        if (elements) {
          String k = "k" + pair;
          fzn.append(
              String.format(
                  "var 0..%d: %s;%nvar 0..%d: a%d;%nvar 0..%d: b%d;%n",
                  m - 1, k, h + 1, pair, h + 1, pair));
          con.append(
              String.format(
                  "constraint jacop_array_var_int_element_nonshifted(%s,%s,a%d,0);%n",
                  k, vector(i, m), pair));
          con.append(
              String.format(
                  "constraint jacop_array_var_int_element_nonshifted(%s,%s,b%d,0);%n",
                  k, vector(j, m), pair));
          con.append(String.format("constraint int_lin_le([1,-1],[a%d,b%d],-1);%n", pair, pair));
          continue;
        }
        List<String> literals = new ArrayList<>();
        for (int c = 0; c < m; c++) {
          String b = "l" + pair + "_" + c;
          fzn.append("var bool: ").append(b).append(";\n");
          String form = LESS[random.nextInt(LESS.length)];
          con.append("constraint ")
              .append(String.format(form, "x" + i + "_" + c, "x" + j + "_" + c, b))
              .append(";\n");
          literals.add(b);
        }
        String list = literals.toString().replace(" ", "");
        switch (random.nextInt(3)) {
          case 0 -> con.append("constraint bool_clause(").append(list).append(",[]);\n");
          case 1 -> con.append("constraint array_bool_or(").append(list).append(",true);\n");
          default -> {
            List<String> ints = new ArrayList<>();
            for (String b : literals) {
              fzn.append("var 0..1: i").append(b).append(";\n");
              con.append("constraint bool2int(").append(b).append(",i").append(b).append(");\n");
              ints.add("i" + b);
            }
            fzn.append(String.format("var 1..%d: n%d;%n", m, pair));
            con.append("constraint jacop_among(")
                .append(ints.toString().replace(" ", ""))
                .append(",1..1,n")
                .append(pair)
                .append(");\n");
          }
        }
      }
    }
    if (random.nextBoolean()) {
      con.append(
          String.format("constraint int_le(%d,x0_%d);%n", random.nextInt(2), random.nextInt(m)));
    }
    return fzn.append(con).append("solve satisfy;\n").toString();
  }

  private static String vector(int i, int m) {
    StringBuilder s = new StringBuilder("[");
    for (int c = 0; c < m; c++) {
      s.append(c > 0 ? "," : "").append("x").append(i).append('_').append(c);
    }
    return s.append(']').toString();
  }

  @Test
  void inequalityKeepsSolutions() throws IOException {
    Random random = new Random(7);
    int trials = Integer.getInteger("antichain.trials", 100);
    int posted = 0;
    int unsatisfiable = 0;
    for (int trial = 0; trial < trials; trial++) {
      // the width of the product of chains is at most 7 here: n up to 8 reaches past it; all
      // solutions are counted on the small models, whose literals and indices multiply them
      int n = 2 + random.nextInt(7);
      String model = randomModel(random, trial % 2 == 1, n);
      String[] all = n <= 4 ? new String[] {"-a"} : new String[0];
      String with = run(model, true, concat(all, "-debug", "--lcg", "off"));
      posted += with.contains("% antichain: 1 groups") ? 1 : 0;
      int expected = solutions(run(model, false, concat(all, "--lcg", "off")));
      unsatisfiable += expected == 0 ? 1 : 0;
      assertEquals(expected, solutions(with), "trial " + trial + " cp\n" + model);
      assertEquals(
          expected > 0,
          solutions(run(model, true, "--lcg", "on", "-f")) > 0,
          "trial " + trial + " lcg -f\n" + model);
    }
    assertTrue(posted > trials / 4, "posted " + posted);
    assertTrue(unsatisfiable > 0 && unsatisfiable < trials, "unsatisfiable " + unsatisfiable);
  }

  /**
   * Seven subsets of a 4-element set cannot be pairwise incomparable (Sperner: at most C(4, 2) =
   * 6): the inequality fails the model at the root, and six subsets are forced into the middle
   * level.
   */
  @Test
  void spernerBoundAtTheRoot() throws IOException {
    Random random = new Random(1);
    String seven = spernerModel(7, random);
    String with = run(seven, true, "-debug", "-s");
    assertTrue(with.contains("% antichain: 1 groups, infeasible"), with);
    assertTrue(with.contains("=====UNSATISFIABLE====="), with);
    assertTrue(run(seven, false).contains("=====UNSATISFIABLE====="));
    String six = spernerModel(6, random);
    String solution = run(six, true, "-debug");
    assertTrue(solution.contains("% antichain: 1 groups"), solution);
    for (int i = 0; i < 6; i++) {
      int rank = 0;
      for (int c = 0; c < 4; c++) {
        rank += solution.contains(String.format("x%d_%d = 1;", i, c)) ? 1 : 0;
      }
      assertEquals(2, rank, solution);
    }
  }

  private static String spernerModel(int n, Random random) {
    StringBuilder fzn = new StringBuilder();
    StringBuilder con = new StringBuilder();
    for (int i = 0; i < n; i++) {
      for (int c = 0; c < 4; c++) {
        fzn.append(String.format("var 0..1: x%d_%d:: output_var;%n", i, c));
      }
    }
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (i != j) {
          List<String> literals = new ArrayList<>();
          for (int c = 0; c < 4; c++) {
            String b = "l" + i + "_" + j + "_" + c;
            fzn.append("var bool: ").append(b).append(";\n");
            String less =
                String.format(
                    LESS[random.nextInt(LESS.length)], "x" + i + "_" + c, "x" + j + "_" + c, b);
            con.append("constraint ").append(less).append(";\n");
            literals.add(b);
          }
          con.append("constraint bool_clause(")
              .append(literals.toString().replace(" ", ""))
              .append(",[]);\n");
        }
      }
    }
    return fzn.append(con).append("solve satisfy;\n").toString();
  }

  private String run(String model, boolean detect, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, Boolean.toString(detect));
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(PROPERTY);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  private static String[] concat(String[] first, String... rest) {
    String[] all = Arrays.copyOf(first, first.length + rest.length);
    System.arraycopy(rest, 0, all, first.length, rest.length);
    return all;
  }

  private static int solutions(String out) {
    assertTrue(
        out.contains("==========") || out.contains("UNSATISFIABLE") || out.contains("----------"),
        out);
    int count = 0;
    for (String line : out.split("\\R")) {
      count += "----------".equals(line) ? 1 : 0;
    }
    return count;
  }
}
