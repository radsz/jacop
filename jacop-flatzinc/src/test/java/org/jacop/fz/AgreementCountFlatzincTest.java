/*
 * AgreementCountFlatzincTest.java
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
 * The pigeonhole bounds of {@link org.jacop.fz.constraints.AgreementCountDetector} keep the optima
 * of random models whose pairs of variables have equality indicators, and prove a small code
 * unsatisfiable at the root by the check of the bounds against the distance rows.
 */
class AgreementCountFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.agreementCount";

  @TempDir Path tmp;

  // whether the bounds are also posted as constraints (the property's value rows)
  private boolean rows;

  // the forms of an indicator b of the pair (x, y); the first two are b <-> x = y, the others
  // b <-> x != y or b -> x != y
  private static final String[] FORMS = {
    "int_eq_reif(%s,%s,%s)",
    "int_lin_eq_reif([1,-1],[%s,%s],0,%s)",
    "int_ne_reif(%s,%s,%s)",
    "int_ne_imp(%s,%s,%s)",
    "int_lin_ne_reif([1,-1],[%s,%s],0,%s)",
    "int_lin_ne_imp([2,-2],[%s,%s],0,%s)"
  };

  /**
   * A random code in the shape of the XCSP3 Hamming models: words of two or three letters over a
   * small alphabet (sometimes with a hole), an indicator for every pair of letters in a position in
   * one of the forms above, and for every pair of words a bound on the sum of their indicators; the
   * objective is a weighted sum of the letters.
   */
  private static String randomModel(Random random) {
    StringBuilder fzn = new StringBuilder();
    int m = 4 + random.nextInt(3);
    int n = 2 + random.nextInt(2);
    int q = 2 + random.nextInt(2);
    int hole = random.nextInt(4) == 0 ? random.nextInt(q) : -1;
    StringBuilder domain = new StringBuilder("{");
    for (int v = 0; v <= q; v++) {
      if (v != hole) {
        domain.append(domain.length() > 1 ? "," : "").append(v);
      }
    }
    domain.append("}");
    List<String> letters = new ArrayList<>();
    for (int i = 0; i < m; i++) {
      for (int k = 0; k < n; k++) {
        fzn.append("var ").append(domain).append(": x").append(i).append('_').append(k);
        fzn.append(":: output_var;\n");
        letters.add("x" + i + "_" + k);
      }
    }
    StringBuilder con = new StringBuilder();
    for (int i = 0; i < m; i++) {
      for (int j = i + 1; j < m; j++) {
        List<String> terms = new ArrayList<>();
        List<Integer> weights = new ArrayList<>();
        int differences = 0;
        for (int k = 0; k < n; k++) {
          int form = random.nextInt(FORMS.length);
          String b = "b" + i + "_" + j + "_" + k;
          String c = "c" + i + "_" + j + "_" + k;
          fzn.append("var bool: ").append(b).append(";\nvar 0..1: ").append(c).append(";\n");
          con.append("constraint ")
              .append(String.format(FORMS[form], "x" + i + "_" + k, "x" + j + "_" + k, b))
              .append(";\nconstraint bool2int(")
              .append(b)
              .append(',')
              .append(c)
              .append(");\n");
          terms.add(c);
          // count the agreements: an equality indicator, or one minus a difference one
          if (form < 2) {
            weights.add(1);
          } else {
            weights.add(-1);
            differences++;
          }
        }
        // at most a agreements of words i and j: sum(w * c) + differences <= a
        int a = random.nextInt(n);
        con.append("constraint int_lin_le(")
            .append(weights)
            .append(",")
            .append(terms)
            .append(",")
            .append(a - differences)
            .append(");\n");
      }
    }
    fzn.append("var -1000..1000: obj:: output_var;\n");
    List<Integer> w = new ArrayList<>();
    for (int i = 0; i < letters.size(); i++) {
      w.add(random.nextInt(5) - 2);
    }
    w.add(-1);
    List<String> objTerms = new ArrayList<>(letters);
    objTerms.add("obj");
    con.append("constraint int_lin_eq(").append(w).append(",").append(objTerms).append(",0);\n");
    fzn.append(con.toString().replace(", ", ","));
    fzn.append("solve minimize obj;\n");
    return fzn.toString();
  }

  @Test
  void boundsKeepOptima() throws IOException {
    Random random = new Random(43);
    int trials = Integer.getInteger("agreementCount.trials", 200);
    int posted = 0;
    int unsatisfiable = 0;
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random);
      String debug = run(model, true, "-debug", "-t", "5000");
      posted += debug.contains("% agreement count:") && !debug.contains("count: 0 groups") ? 1 : 0;
      String expected = optimum(run(model, false, "--lcg", "off"), model);
      unsatisfiable += "UNSATISFIABLE".equals(expected) ? 1 : 0;
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "on", "-f"), model),
          "trial " + trial + " lcg -f\n" + model);
      assertEquals(
          expected,
          optimum(run(model, true, "--lcg", "off"), model),
          "trial " + trial + " cp\n" + model);
      rows = true;
      try {
        assertEquals(
            expected,
            optimum(run(model, true, "--lcg", "on", "-f"), model),
            "trial " + trial + " rows lcg -f\n" + model);
      } finally {
        rows = false;
      }
    }
    assertTrue(posted > trials / 2, "posted " + posted);
    assertTrue(unsatisfiable > 0 && unsatisfiable < trials, "unsatisfiable " + unsatisfiable);
  }

  /**
   * Five binary words of length 4 at distance at least 3 from each other agree in at most one
   * position per pair, 10 agreements, while each position of five binary letters has at least 4
   * equal pairs, 16 in all: the root check fails the model, without it search does.
   */
  @Test
  void smallCodeFailsAtTheRoot() throws IOException {
    StringBuilder fzn = new StringBuilder();
    int m = 5;
    int n = 4;
    for (int i = 0; i < m; i++) {
      for (int k = 0; k < n; k++) {
        fzn.append("var 0..1: x").append(i).append('_').append(k).append(":: output_var;\n");
      }
    }
    StringBuilder con = new StringBuilder();
    for (int i = 0; i < m; i++) {
      for (int j = i + 1; j < m; j++) {
        List<String> terms = new ArrayList<>();
        for (int k = 0; k < n; k++) {
          String b = "b" + i + "_" + j + "_" + k;
          String c = "c" + i + "_" + j + "_" + k;
          fzn.append("var bool: ").append(b).append(";\nvar 0..1: ").append(c).append(";\n");
          con.append(
              String.format(
                  "constraint int_lin_ne_imp([1,-1],[x%d_%d,x%d_%d],0,%s);%n", i, k, j, k, b));
          con.append("constraint bool2int(").append(b).append(',').append(c).append(");\n");
          terms.add(c);
        }
        int[] minus = new int[n];
        Arrays.fill(minus, -1);
        con.append("constraint int_lin_le(")
            .append(Arrays.toString(minus).replace(" ", ""))
            .append(",")
            .append(terms.toString().replace(" ", ""))
            .append(",-3);\n");
      }
    }
    String model = fzn.append(con).append("solve satisfy;\n").toString();
    String with = run(model, true, "-debug", "-s");
    assertTrue(with.contains("% agreement count: 4 groups, infeasible"), with);
    assertTrue(with.contains("=====UNSATISFIABLE====="), with);
    assertTrue(run(model, false).contains("=====UNSATISFIABLE====="));
  }

  private String run(String model, boolean bounds, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(PROPERTY, bounds && rows ? "rows" : Boolean.toString(bounds));
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
  private static String optimum(String out, String model) {
    String last = "UNSATISFIABLE";
    for (String line : out.split("\\R")) {
      if (line.startsWith("obj = ")) {
        last = line.substring(line.indexOf('=') + 2, line.length() - 1);
      }
    }
    assertTrue(out.contains("==========") || out.contains("UNSATISFIABLE"), out + "\n" + model);
    return last;
  }
}
