/*
 * TableMddFlatzincTest.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * preservation of specified reasonable legal notices and author attributions
 * in the material and in all works containing the material.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
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
 * Random models with short tables (jacop_short_table_int, as the XCSP3 translations post them):
 * compiled into decision diagrams ({@code org.jacop.fz.tableMdd.rows}) they must keep every
 * solution and every optimum of the tables.
 */
class TableMddFlatzincTest {

  private static final String ROWS = "org.jacop.fz.tableMdd.rows";
  private static final String RATIO = "org.jacop.fz.tableMdd.ratio";

  @TempDir Path tmp;

  private static String randomModel(Random random, boolean optimise) {
    StringBuilder fzn = new StringBuilder();
    int n = 3 + random.nextInt(3);
    int top = 2 + random.nextInt(3);
    for (int i = 0; i < n; i++) {
      fzn.append("var ");
      if (random.nextInt(4) == 0) {
        // a hole in the domain
        fzn.append("{0,").append(top).append('}');
      } else {
        fzn.append("0..").append(top);
      }
      fzn.append(": x").append(i).append(":: output_var;\n");
    }
    List<String> constraints = new ArrayList<>();
    int star = -1;
    // one table on several scopes, sometimes with a variable twice
    int arity = 2 + random.nextInt(Math.min(3, n - 1));
    List<Integer> rows = new ArrayList<>();
    int count = 1 + random.nextInt(12);
    for (int r = 0; r < count; r++) {
      for (int c = 0; c < arity; c++) {
        rows.add(random.nextInt(4) == 0 ? star : random.nextInt(top + 2));
      }
    }
    String table = rows.toString().replace(" ", "");
    int scopes = 1 + random.nextInt(3);
    for (int s = 0; s < scopes; s++) {
      StringBuilder scope = new StringBuilder("[");
      for (int c = 0; c < arity; c++) {
        int v = random.nextInt(8) == 0 && c > 0 ? random.nextInt(n) : (s + c) % n;
        scope.append(c > 0 ? "," : "").append('x').append(v);
      }
      scope.append(']');
      constraints.add("constraint jacop_short_table_int(" + scope + "," + table + "," + star + ")");
    }
    if (optimise) {
      StringBuilder coefficients = new StringBuilder("[");
      StringBuilder all = new StringBuilder("[");
      for (int i = 0; i < n; i++) {
        coefficients.append(i > 0 ? "," : "").append(random.nextInt(7) - 3);
        all.append(i > 0 ? "," : "").append('x').append(i);
      }
      fzn.append("var -100..100: obj:: output_var;\n");
      constraints.add("constraint int_lin_eq(" + coefficients + ",-1]," + all + ",obj],0)");
    }
    constraints.forEach(s -> fzn.append(s).append(";\n"));
    fzn.append(optimise ? "solve minimize obj;\n" : "solve satisfy;\n");
    return fzn.toString();
  }

  /** The Benzenoide rule on one hexagon and three neighbours, as XCSP 2023 lists it in rows. */
  private static String connectivityModel(int top) {
    StringBuilder fzn = new StringBuilder();
    List<Integer> rows = new ArrayList<>();
    for (int y = 0; y <= top; y++) {
      for (int x = 0; x <= 1; x++) {
        for (int a = 0; a <= top; a++) {
          for (int b = 0; b <= top; b++) {
            for (int c = 0; c <= top; c++) {
              int[] nb = {a, b, c};
              boolean ok;
              if (x == 0 || y == 0) {
                ok = x == 0 && y == 0;
              } else if (y == 1) {
                ok = true;
              } else {
                final int yy = y;
                ok =
                    Arrays.stream(nb).anyMatch(v -> v == yy - 1)
                        && Arrays.stream(nb).allMatch(v -> v == 0 || v >= yy - 1);
              }
              if (ok) {
                rows.addAll(List.of(y, x, a, b, c));
              }
            }
          }
        }
      }
    }
    String table = rows.toString().replace(" ", "");
    String[] names = {"y0", "y1", "y2", "y3"};
    for (String name : names) {
      fzn.append("var 0..").append(top).append(": ").append(name).append(":: output_var;\n");
    }
    fzn.append("var bool: b0:: output_var;\nvar 0..1: x0;\n");
    fzn.append("constraint bool2int(b0,x0);\n");
    fzn.append("constraint jacop_short_table_int([y0,x0,y1,y2,y3],")
        .append(table)
        .append(",-1);\n");
    fzn.append("solve satisfy;\n");
    return fzn.toString();
  }

  @Test
  void diagramsKeepAllSolutions() throws IOException {
    Random random = new Random(71);
    int compiled = 0;
    int trials = Integer.getInteger("tablemdd.trials", 200);
    for (int trial = 0; trial < trials; trial++) {
      String model = randomModel(random, false);
      String on = run(model, true, "-a", "-debug");
      compiled += on.matches("(?s).*as diagram: \\d+ edges.*") ? 1 : 0;
      String off = run(model, false, "-a");
      assertEquals(solutions(off), solutions(on), "trial " + trial + "\n" + model + "\n" + on);
    }
    assertTrue(compiled > trials / 3, "compiled " + compiled);
  }

  @Test
  void diagramsKeepOptima() throws IOException {
    Random random = new Random(72);
    int trials = Integer.getInteger("tablemdd.trials", 200) / 2;
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
  void connectivityRuleCompilesSmall() throws IOException {
    String model = connectivityModel(5);
    String on = run(model, true, "-a", "-debug");
    String off = run(model, false, "-a");
    assertEquals(solutions(off), solutions(on));
    // 1,000-odd rows, a diagram of a few dozen edges
    String line =
        Arrays.stream(on.split("\\R")).filter(l -> l.contains(" edges")).findFirst().orElseThrow();
    int edges = Integer.parseInt(line.replaceAll(".*: (\\d+) edges.*", "$1"));
    assertTrue(edges < 100, line);
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

  private String run(String model, boolean compile, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    System.setProperty(ROWS, compile ? "1" : "0");
    System.setProperty(RATIO, "1");
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.clearProperty(ROWS);
      System.clearProperty(RATIO);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
