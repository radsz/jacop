/*
 * SlotDiveFlatzincTest.java
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
import java.util.Arrays;
import java.util.Random;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the dive of free search through the slots of a cardinality with fixed counts ({@code
 * Solve.slotDive}) on the slot model of bin packing of XCSP 2024 BinPacking: {@code x[i][j]} is the
 * weight of the j-th item in bin i (0 for none), the rows are ordered and within the capacity,
 * every weight occurs its fixed number of times, and the number of bins in use is minimised. The
 * optimum of random models must match a brute-force packing, with the dive on and off, and every
 * printed solution must be a packing.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class SlotDiveFlatzincTest {

  @TempDir Path tmp;

  private record Model(String fzn, int[] weights, int capacity, int bins, int optimum) {}

  private static Model randomModel(Random random) {
    int n = 3 + random.nextInt(4);
    int capacity = 8 + random.nextInt(8);
    int[] w = new int[n];
    for (int i = 0; i < n; i++) {
      w[i] = 1 + random.nextInt(capacity);
    }
    int bins = n;
    int slots = n;
    TreeMap<Integer, Integer> counts = new TreeMap<>();
    for (int v : w) {
      counts.merge(v, 1, Integer::sum);
    }
    StringBuilder domain = new StringBuilder("{0");
    for (int v : counts.keySet()) {
      domain.append(',').append(v);
    }
    domain.append('}');
    StringBuilder fzn = new StringBuilder();
    StringBuilder all = new StringBuilder();
    for (int i = 0; i < bins; i++) {
      for (int j = 0; j < slots; j++) {
        fzn.append("var ").append(domain).append(": x_").append(i).append('_').append(j);
        fzn.append(":: output_var;\n");
        all.append(all.isEmpty() ? "" : ",").append("x_").append(i).append('_').append(j);
      }
    }
    StringBuilder cover = new StringBuilder();
    StringBuilder counters = new StringBuilder();
    int k = 0;
    for (var e : counts.entrySet()) {
      fzn.append("var ").append(e.getValue()).append("..").append(e.getValue());
      fzn.append(": c").append(k).append(";\n");
      cover.append(k == 0 ? "" : ",").append(e.getKey());
      counters.append(k == 0 ? "" : ",").append('c').append(k);
      k++;
    }
    StringBuilder used = new StringBuilder();
    for (int i = 0; i < bins; i++) {
      fzn.append("var bool: b").append(i).append(":: var_is_introduced :: is_defined_var;\n");
      fzn.append("var 0..1: u").append(i).append(":: var_is_introduced :: is_defined_var;\n");
      used.append(i == 0 ? "" : ",").append('u').append(i);
    }
    fzn.append("var 0..").append(bins).append(": z:: output_var :: is_defined_var;\n");
    fzn.append("array [1..")
        .append(bins * slots)
        .append("] of var int: slots = [")
        .append(all)
        .append("];\n");
    for (int i = 0; i < bins; i++) {
      StringBuilder row = new StringBuilder();
      StringBuilder ones = new StringBuilder();
      for (int j = 0; j < slots; j++) {
        row.append(j == 0 ? "" : ",").append("x_").append(i).append('_').append(j);
        ones.append(j == 0 ? "" : ",").append(1);
        if (j + 1 < slots) {
          fzn.append("constraint int_lin_le([-1,1],[x_")
              .append(i)
              .append('_')
              .append(j)
              .append(",x_")
              .append(i)
              .append('_')
              .append(j + 1)
              .append("],0);\n");
        }
      }
      fzn.append("constraint int_lin_le([")
          .append(ones)
          .append("],[")
          .append(row)
          .append("],")
          .append(capacity)
          .append(");\n");
      fzn.append("constraint int_ne_reif(x_").append(i).append("_0,0,b").append(i);
      fzn.append("):: defines_var(b").append(i).append(");\n");
      fzn.append("constraint bool2int(b").append(i).append(",u").append(i);
      fzn.append("):: defines_var(u").append(i).append(");\n");
    }
    fzn.append("constraint jacop_count_values(slots,[")
        .append(cover)
        .append("],[")
        .append(counters)
        .append("]);\n");
    StringBuilder coefficients = new StringBuilder("-1");
    for (int i = 0; i < bins; i++) {
      coefficients.append(",1");
    }
    fzn.append("constraint int_lin_eq([")
        .append(coefficients)
        .append("],[z,")
        .append(used)
        .append("],0):: defines_var(z);\n");
    fzn.append("solve minimize z;\n");
    return new Model(fzn.toString(), w, capacity, bins, fewestBins(w, capacity));
  }

  // the fewest bins of the capacity that hold the weights, by enumeration of the assignments
  private static int fewestBins(int[] w, int capacity) {
    int n = w.length;
    int best = n;
    int[] bin = new int[n];
    int total = (int) Math.pow(n, n);
    for (int code = 0; code < total; code++) {
      int c = code;
      int[] load = new int[n];
      boolean fits = true;
      for (int i = 0; i < n && fits; i++) {
        bin[i] = c % n;
        c /= n;
        load[bin[i]] += w[i];
        fits = load[bin[i]] <= capacity;
      }
      if (fits) {
        best = Math.min(best, (int) Arrays.stream(load).filter(l -> l > 0).count());
      }
    }
    return best;
  }

  @Test
  void slotDiveKeepsTheOptimum() throws IOException {
    Random random = new Random(41);
    int dived = 0;
    for (int trial = 0; trial < 40; trial++) {
      Model model = randomModel(random);
      String on = run(model.fzn(), "--lcg", "on", "-f", "-debug");
      String off = run(model.fzn(), "--lcg", "on", "-f", "--free-config", "slot-dive=off");
      if (on.contains("% slot dive: " + model.bins() * model.bins() + " slots, a solution")) {
        dived++;
      }
      for (String out : new String[] {on, off}) {
        assertTrue(out.contains("=========="), "trial " + trial + "\n" + out);
        assertEquals(model.optimum(), lastCost(out), "trial " + trial + "\n" + model.fzn());
        checkPackings(model, out, trial);
      }
    }
    assertEquals(40, dived, "the dive fills the slots of every model");
  }

  // the cost of the last solution printed
  private static int lastCost(String out) {
    Matcher m = Pattern.compile("(?m)^z = (\\d+);").matcher(out);
    int cost = -1;
    while (m.find()) {
      cost = Integer.parseInt(m.group(1));
    }
    return cost;
  }

  // every printed solution is a packing of the weights whose cost is the number of bins in use
  private static void checkPackings(Model model, String out, int trial) {
    int n = model.bins();
    for (String solution : out.split("----------")) {
      if (!solution.contains("z = ")) {
        continue;
      }
      int[][] x = new int[n][n];
      Matcher m = Pattern.compile("(?m)^x_(\\d+)_(\\d+) = (\\d+);").matcher(solution);
      while (m.find()) {
        x[Integer.parseInt(m.group(1))][Integer.parseInt(m.group(2))] =
            Integer.parseInt(m.group(3));
      }
      int[] packed = Arrays.stream(x).flatMapToInt(Arrays::stream).filter(v -> v > 0).toArray();
      int[] weights = model.weights().clone();
      Arrays.sort(packed);
      Arrays.sort(weights);
      assertTrue(Arrays.equals(weights, packed), "trial " + trial + " packs " + solution);
      int inUse = 0;
      for (int[] row : x) {
        assertTrue(Arrays.stream(row).sum() <= model.capacity(), "trial " + trial + solution);
        inUse += row[0] > 0 ? 1 : 0;
      }
      assertEquals(inUse, lastCost(solution), "trial " + trial + solution);
    }
  }

  private String run(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 3);
    args[options.length] = "-t";
    args[options.length + 1] = "20000";
    args[options.length + 2] = fzn.toString();
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
