/*
 * MddLinearSumFlatzincTest.java
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
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import org.jacop.fz.constraints.MddLinearSum;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * A diagram that states exactly x_1 + ... + x_n = S is posted as the sum ({@link MddLinearSum}); a
 * diagram that misses one tuple of the sum keeps the diagram. The solutions must stay the same.
 */
class MddLinearSumFlatzincTest {

  private static final String PROPERTY = "org.jacop.fz.mddLinear";

  @TempDir Path tmp;

  /**
   * The partial-sum diagram of x_1 + ... + x_n = s over the values vals, optionally with one edge
   * on a path to the terminal removed. Labels may also hold values outside the variable domains.
   */
  private static String model(
      Random random, int n, int[] vals, int lo, int hi, int s, boolean cut) {
    // nodes per level by partial sum, kept only when the terminal stays reachable
    int minV = Arrays.stream(vals).min().getAsInt();
    int maxV = Arrays.stream(vals).max().getAsInt();
    List<Map<Integer, Integer>> levels = new ArrayList<>();
    List<Integer> level = new ArrayList<>();
    List<int[]> edges = new ArrayList<>();
    Map<Integer, Integer> current = new LinkedHashMap<>();
    current.put(0, 1);
    level.add(1);
    levels.add(current);
    for (int l = 0; l < n; l++) {
      Map<Integer, Integer> next = new LinkedHashMap<>();
      int rest = n - l - 1;
      for (Map.Entry<Integer, Integer> node : current.entrySet()) {
        for (int v : vals) {
          int p = node.getKey() + v;
          if (p + rest * minV > s || p + rest * maxV < s) {
            continue;
          }
          int target = 0;
          if (rest > 0) {
            Integer t = next.get(p);
            if (t == null) {
              t = level.size() + 1;
              level.add(l + 2);
              next.put(p, t);
            }
            target = t;
          }
          edges.add(new int[] {node.getValue(), v, target});
        }
      }
      current = next;
    }
    if (cut && edges.size() > 2) {
      // the last edge into the terminal goes
      edges.remove(edges.size() - 1 - random.nextInt(2));
    }
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var ").append(lo).append("..").append(hi).append(": x").append(i);
      fzn.append(":: output_var;\n");
    }
    fzn.append("constraint jacop_mdd([");
    for (int i = 0; i < n; i++) {
      fzn.append(i > 0 ? "," : "").append("x").append(i);
    }
    fzn.append("],").append(level.toString().replace(" ", "")).append(",[");
    for (int e = 0; e < edges.size(); e++) {
      fzn.append(e > 0 ? "," : "").append(edges.get(e)[0]);
    }
    fzn.append("],[");
    for (int e = 0; e < edges.size(); e++) {
      fzn.append(e > 0 ? "," : "").append('{').append(edges.get(e)[1]).append('}');
    }
    fzn.append("],[");
    for (int e = 0; e < edges.size(); e++) {
      fzn.append(e > 0 ? "," : "").append(edges.get(e)[2]);
    }
    fzn.append("]);\nsolve satisfy;\n");
    return fzn.toString();
  }

  @Test
  void sumDiagramsKeepAllSolutions() throws IOException {
    Random random = new Random(7);
    int posted = 0;
    for (int trial = 0; trial < 40; trial++) {
      int n = 2 + random.nextInt(3);
      // the label values: an interval of 1..5, or the domain with a hole, or wider than the domain
      int lo = 1 + random.nextInt(2);
      int hi = lo + 1 + random.nextInt(3);
      int kind = random.nextInt(3);
      List<Integer> vs = new ArrayList<>();
      for (int v = lo - (kind == 2 ? 1 : 0); v <= hi + (kind == 2 ? 1 : 0); v++) {
        if (kind != 1 || v != lo + 1) {
          vs.add(v);
        }
      }
      int[] vals = vs.stream().mapToInt(Integer::intValue).toArray();
      // a reachable sum of label values inside the domains
      int s = 0;
      for (int i = 0; i < n; i++) {
        s += Math.max(lo, Math.min(hi, vals[random.nextInt(vals.length)]));
      }
      boolean cut = random.nextInt(3) == 0;
      String fzn = model(random, n, vals, lo, hi, s, cut);
      String on = run(fzn, null, "-a", "-debug");
      Set<String> expected = solutions(run(fzn, "false", "-a"));
      assertEquals(expected, solutions(on), "trial " + trial + "\n" + fzn);
      boolean sum = on.contains("SumInt");
      posted += sum ? 1 : 0;
      String lcg = run(fzn, null, "-f", "--lcg", "on");
      assertEquals(expected.isEmpty(), solutions(lcg).isEmpty(), "trial " + trial + " lcg\n" + fzn);
      assertTrue(solutions(lcg).isEmpty() || expected.containsAll(solutions(lcg)), fzn);
    }
    assertTrue(posted >= 10, "posted " + posted);
  }

  @Test
  void magicSquareRowIsASum() throws IOException {
    // x0 + x1 + x2 = 15 over 1..9: the diagram of all its tuples is the sum
    String fzn = model(new Random(1), 3, new int[] {1, 2, 3, 4, 5, 6, 7, 8, 9}, 1, 9, 15, false);
    String out = run(fzn, null, "-a", "-debug");
    assertTrue(out.contains("SumInt"), out);
    assertEquals(solutions(run(fzn, "false", "-a")), solutions(out));
    String cut = model(new Random(1), 3, new int[] {1, 2, 3, 4, 5, 6, 7, 8, 9}, 1, 9, 15, true);
    String kept = run(cut, null, "-a", "-debug");
    assertFalse(kept.contains("SumInt"), kept);
    assertEquals(solutions(run(cut, "false", "-a")), solutions(kept));
  }

  private String run(String model, String property, String... options) throws IOException {
    MddLinearSum.reset();
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

  private static Set<String> solutions(String out) {
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(out.split("----------"))
        .map(
            s ->
                String.join(
                    " ",
                    Arrays.stream(s.strip().split("\\R"))
                        .filter(l -> !l.isBlank() && !l.startsWith("%"))
                        .toList()))
        .filter(s -> !s.isEmpty() && !s.startsWith("==========") && !s.contains("UNSATISFIABLE"))
        .forEach(solutions::add);
    return solutions;
  }
}
