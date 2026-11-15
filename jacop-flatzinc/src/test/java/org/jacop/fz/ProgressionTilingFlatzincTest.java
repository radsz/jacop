/*
 * ProgressionTilingFlatzincTest.java
 * <p>
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
import static org.junit.jupiter.api.Assertions.assertNotEquals;
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tilings of 0..n-1 by m arithmetic progressions of k terms with ordered starts and all different
 * gaps (XCSP3 PerfectRythmicTiling) are found by {@code ProgressionTilingDetector} in the three
 * forms MiniZinc flattens them to, and its search finds tilings and proves their absence.
 */
class ProgressionTilingFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.progressionTiling";

  @TempDir Path tmp;

  /** The forms of the progressions. */
  private enum Form {
    /** x_{i,j+1} = x_{i,j} + g_i, all terms all different. */
    CHAIN,
    /** t_{i,j} = s_i + j g_i, the terms indexing an array of the progression of each value. */
    OFFSETS,
    /** a table of the tuples (s, s + g, ..., s + (k - 1) g, g), all terms all different. */
    TABLE
  }

  private static String model(Form form, int k, int m, boolean gapsDifferent) {
    int n = k * m;
    int maxGap = (n - 1) / (k - 1);
    StringBuilder fzn = new StringBuilder();
    List<String> constraints = new ArrayList<>();
    List<String> starts = new ArrayList<>();
    List<String> gaps = new ArrayList<>();
    List<String> terms = new ArrayList<>();
    for (int i = 0; i < m; i++) {
      starts.add("s" + i);
      gaps.add("g" + i);
      fzn.append("var 0..").append(n - 1).append(": s").append(i).append(";\n");
      fzn.append("var 1..").append(maxGap).append(": g").append(i).append(";\n");
      terms.add("s" + i);
      for (int j = 1; j < k; j++) {
        String t = "t" + i + "_" + j;
        fzn.append("var ").append(j).append("..").append(n - 1).append(": ").append(t);
        fzn.append(":: var_is_introduced :: is_defined_var;\n");
        terms.add(t);
        switch (form) {
          case CHAIN -> {
            String prev = j == 1 ? "s" + i : "t" + i + "_" + (j - 1);
            constraints.add("int_lin_eq([1,-1,-1],[" + t + ",g" + i + "," + prev + "],0)");
          }
          case OFFSETS ->
              constraints.add("int_lin_eq([1,-1,-" + j + "],[" + t + ",s" + i + ",g" + i + "],0)");
          case TABLE -> {
            // the table below
          }
        }
      }
      if (form == Form.TABLE) {
        List<Integer> tuples = new ArrayList<>();
        for (int g = 1; g <= maxGap; g++) {
          for (int s = 0; s + (k - 1) * g < n; s++) {
            for (int j = 0; j < k; j++) {
              tuples.add(s + j * g);
            }
            tuples.add(g);
          }
        }
        List<String> vars = new ArrayList<>(terms.subList(terms.size() - k, terms.size()));
        vars.add("g" + i);
        constraints.add("jacop_table_int(" + vars + "," + tuples + ")");
      }
    }
    if (form == Form.OFFSETS) {
      // which progression covers each value: element(t, cover) = i
      for (int p = 0; p < n; p++) {
        fzn.append("var 0..").append(m - 1).append(": c").append(p).append(";\n");
      }
      List<String> cover = new ArrayList<>();
      for (int p = 0; p < n; p++) {
        cover.add("c" + p);
      }
      for (String t : terms) {
        int i = Integer.parseInt(t.substring(1).split("_")[0]);
        constraints.add(
            "jacop_array_var_int_element_nonshifted(" + t + "," + cover + "," + i + ",0)");
      }
    } else {
      constraints.add("jacop_alldiff(" + terms + ")");
    }
    if (gapsDifferent) {
      constraints.add("jacop_alldiff(" + gaps + ")");
    }
    constraints.add("jacop_strictly_increasing(" + starts + ")");
    array(fzn, "s", starts);
    array(fzn, "g", gaps);
    constraints.forEach(c -> fzn.append("constraint ").append(c.replace(" ", "")).append(";\n"));
    fzn.append("solve satisfy;\n");
    return fzn.toString();
  }

  private static void array(StringBuilder fzn, String name, List<String> vars) {
    fzn.append("array [1..").append(vars.size()).append("] of var int: ").append(name);
    fzn.append(":: output_array([1..")
        .append(vars.size())
        .append("]) = ")
        .append(vars.toString().replace(" ", ""));
    fzn.append(";\n");
  }

  @Test
  void findsTheTilingsInEveryForm() throws IOException {
    for (Form form : Form.values()) {
      // K(8, 3) and K(10, 3) exist (Tom Johnson's perfect rhythmic tilings)
      for (int[] km : new int[][] {{3, 8}, {3, 10}}) {
        String out = run(model(form, km[0], km[1], true), null, "-s", "-debug");
        assertTrue(
            out.contains("% progression tiling: " + km[1] + " progressions of " + km[0] + " terms"),
            form + "\n" + out);
        assertTrue(out.contains("%% progression tiling search"), form + "\n" + out);
        assertTiling(out, km[0], km[1]);
      }
    }
  }

  @Test
  void provesThatNoTilingExists() throws IOException {
    // no perfect rhythmic tiling of 3-term progressions with 2, 3, 4 or 6 progressions
    for (int m : new int[] {3, 4, 6}) {
      for (Form form : Form.values()) {
        String out = run(model(form, 3, m, true), null);
        assertTrue(out.contains("%% progression tiling search"), out);
        assertTrue(out.contains("=====UNSATISFIABLE====="), form + " m=" + m + "\n" + out);
      }
    }
  }

  @Test
  void needsAllDifferentGapsAndCanBeTurnedOff() throws IOException {
    String out = run(model(Form.CHAIN, 3, 8, false), null, "-debug");
    assertTrue(out.contains("% progression tiling: none"), out);
    out = run(model(Form.CHAIN, 3, 8, true), "false", "-debug");
    assertFalse(out.contains("progression tiling"), out);
    assertTiling(out, 3, 8);
  }

  @Test
  void allSolutionsKeepTheirSearch() throws IOException {
    // -a: the search of the model, the same solutions with and without the detector
    String fzn = model(Form.CHAIN, 3, 5, true);
    String on = run(fzn, null, "-a");
    assertFalse(on.contains("%% progression tiling search"), on);
    assertEquals(run(fzn, "false", "-a"), on);
  }

  /** The output's starts and gaps form a tiling of 0..k m - 1 with all different gaps. */
  private static void assertTiling(String out, int k, int m) {
    int[] s = values(out, "s");
    int[] g = values(out, "g");
    assertEquals(m, s.length, out);
    boolean[] covered = new boolean[k * m];
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < i; j++) {
        assertNotEquals(g[i], g[j], out);
      }
      for (int j = 0; j < k; j++) {
        int p = s[i] + j * g[i];
        assertTrue(p < k * m && !covered[p], out);
        covered[p] = true;
      }
    }
  }

  private static int[] values(String out, String name) {
    Matcher matcher =
        Pattern.compile("(?m)^" + name + " = array1d\\(1\\.\\.\\d+, \\[([^]]*)]\\);").matcher(out);
    assertTrue(matcher.find(), out);
    return Arrays.stream(matcher.group(1).split(","))
        .map(String::strip)
        .mapToInt(Integer::parseInt)
        .toArray();
  }

  private String run(String model, String property, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    if (property != null) {
      System.setProperty(PROPERTY, property);
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
