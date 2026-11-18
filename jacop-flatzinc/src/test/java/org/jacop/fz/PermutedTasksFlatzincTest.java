/*
 * PermutedTasksFlatzincTest.java
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
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks {@code PermutedTasksDetector} on the open shop model of XCSP 2025 SchedulingOS: operation
 * j of job i starts at {@code s[i][j]}, runs on machine {@code mc[i][j]} for {@code d[i][j]} (a
 * table of the job's processing times), the operations of a job follow each other, its machines are
 * all different, {@code s[i][j] = sd[i][mc[i][j]]}, and the machines are unary resources over
 * {@code sd}. The optimum of random small instances must match a brute force over the orders of the
 * operations, with the detector on and off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class PermutedTasksFlatzincTest {

  @TempDir Path tmp;

  private static String openShop(int[][] p, int horizon) {
    int jobs = p.length;
    int machines = p[0].length;
    StringBuilder fzn = new StringBuilder();
    fzn.append("predicate jacop_alldiff(array [int] of var int: x);\n");
    fzn.append("predicate jacop_table_int(array [int] of var int: x,array [int] of int: t);\n");
    fzn.append(
        "predicate jacop_array_var_int_element_nonshifted(var int: idx,"
            + "array [int] of var int: xs,var int: y,int: min_index);\n");
    fzn.append(
        "predicate jacop_cumulative(array [int] of var int: s,array [int] of var int: d,"
            + "array [int] of var int: r,var int: b);\n");
    for (int i = 0; i < jobs; i++) {
      for (int j = 0; j < machines; j++) {
        fzn.append("var 0..").append(horizon).append(": s_").append(i).append('_').append(j);
        fzn.append(";\nvar 0..").append(machines - 1).append(": mc_").append(i).append('_');
        fzn.append(j).append(";\nvar 0..").append(horizon).append(": d_").append(i).append('_');
        fzn.append(j).append(";\nvar 0..").append(horizon).append(": sd_").append(i);
        fzn.append('_').append(j).append(";\n");
      }
    }
    fzn.append("var 0..").append(horizon).append(": z:: output_var;\n");
    for (int i = 0; i < jobs; i++) {
      StringBuilder mc = new StringBuilder();
      StringBuilder sd = new StringBuilder();
      StringBuilder table = new StringBuilder();
      for (int k = 0; k < machines; k++) {
        mc.append(k == 0 ? "" : ",").append("mc_").append(i).append('_').append(k);
        sd.append(k == 0 ? "" : ",").append("sd_").append(i).append('_').append(k);
        table.append(k == 0 ? "" : ",").append(k).append(',').append(p[i][k]);
      }
      fzn.append("constraint jacop_alldiff([").append(mc).append("]);\n");
      for (int j = 0; j < machines; j++) {
        String s = "s_" + i + "_" + j;
        String d = "d_" + i + "_" + j;
        String next = j + 1 < machines ? "s_" + i + "_" + (j + 1) : "z";
        fzn.append("constraint int_lin_le([1,1,-1],[").append(s).append(',').append(d);
        fzn.append(',').append(next).append("],0);\n");
        fzn.append("constraint jacop_table_int([mc_").append(i).append('_').append(j);
        fzn.append(',').append(d).append("],[").append(table).append("]);\n");
        fzn.append("constraint jacop_array_var_int_element_nonshifted(mc_").append(i);
        fzn.append('_').append(j).append(",[").append(sd).append("],").append(s);
        fzn.append(",0);\n");
      }
    }
    for (int k = 0; k < machines; k++) {
      StringBuilder sd = new StringBuilder();
      StringBuilder d = new StringBuilder();
      StringBuilder r = new StringBuilder();
      for (int i = 0; i < jobs; i++) {
        sd.append(i == 0 ? "" : ",").append("sd_").append(i).append('_').append(k);
        d.append(i == 0 ? "" : ",").append(p[i][k]);
        r.append(i == 0 ? "" : ",").append(1);
      }
      fzn.append("constraint jacop_cumulative([").append(sd).append("],[").append(d);
      fzn.append("],[").append(r).append("],1);\n");
    }
    fzn.append("solve minimize z;\n");
    return fzn.toString();
  }

  /**
   * The least makespan of the open shop, by enumeration of the order of the operations of every job
   * and every machine (semi-active schedules: each operation as early as its job and machine let
   * it, in the order of a topological sort of the two orders).
   */
  private static int bruteForce(int[][] p) {
    int jobs = p.length;
    int machines = p[0].length;
    int[][] jobOrders = permutations(machines);
    int[][] machineOrders = permutations(jobs);
    int best = Integer.MAX_VALUE;
    int[] jobChoice = new int[jobs];
    int[] machineChoice = new int[machines];
    long total =
        (long) Math.pow(jobOrders.length, jobs) * (long) Math.pow(machineOrders.length, machines);
    for (long code = 0; code < total; code++) {
      long c = code;
      for (int i = 0; i < jobs; i++) {
        jobChoice[i] = (int) (c % jobOrders.length);
        c /= jobOrders.length;
      }
      for (int k = 0; k < machines; k++) {
        machineChoice[k] = (int) (c % machineOrders.length);
        c /= machineOrders.length;
      }
      int makespan = schedule(p, jobOrders, machineOrders, jobChoice, machineChoice);
      if (makespan >= 0) {
        best = Math.min(best, makespan);
      }
    }
    return best;
  }

  // the makespan of the orders, or -1 when they contradict each other
  private static int schedule(
      int[][] p, int[][] jobOrders, int[][] machineOrders, int[] jobChoice, int[] machineChoice) {
    int jobs = p.length;
    int machines = p[0].length;
    int[] jobPos = new int[jobs];
    int[] machinePos = new int[machines];
    int[] jobEnd = new int[jobs];
    int[] machineEnd = new int[machines];
    int done = 0;
    boolean progress = true;
    while (progress) {
      progress = false;
      for (int i = 0; i < jobs; i++) {
        if (jobPos[i] == machines) {
          continue;
        }
        int k = jobOrders[jobChoice[i]][jobPos[i]];
        if (machinePos[k] < jobs && machineOrders[machineChoice[k]][machinePos[k]] == i) {
          int start = Math.max(jobEnd[i], machineEnd[k]);
          jobEnd[i] = start + p[i][k];
          machineEnd[k] = start + p[i][k];
          jobPos[i]++;
          machinePos[k]++;
          done++;
          progress = true;
        }
      }
    }
    return done == jobs * machines ? Arrays.stream(jobEnd).max().getAsInt() : -1;
  }

  private static int[][] permutations(int n) {
    if (n == 1) {
      return new int[][] {{0}};
    }
    int[][] smaller = permutations(n - 1);
    int[][] all = new int[smaller.length * n][];
    int k = 0;
    for (int[] q : smaller) {
      for (int pos = 0; pos < n; pos++) {
        int[] r = new int[n];
        for (int i = 0, j = 0; i < n; i++) {
          r[i] = i == pos ? n - 1 : q[j++];
        }
        all[k++] = r;
      }
    }
    return all;
  }

  @Test
  void permutedTasksKeepTheOptimum() throws IOException {
    Random random = new Random(7);
    for (int trial = 0; trial < 12; trial++) {
      int jobs = 2 + random.nextInt(2);
      int machines = 3;
      int[][] p = new int[jobs][machines];
      int horizon = 0;
      for (int[] row : p) {
        for (int k = 0; k < machines; k++) {
          row[k] = 1 + random.nextInt(6);
          horizon += row[k];
        }
      }
      String fzn = openShop(p, horizon);
      int optimum = bruteForce(p);
      String on = run(fzn, "-debug");
      assertTrue(
          on.contains("% permuted tasks: unary resource on " + machines + " resource starts"),
          "trial " + trial + "\n" + on);
      String previous = System.getProperty("org.jacop.fz.permutedTasks");
      System.setProperty("org.jacop.fz.permutedTasks", "false");
      String off;
      try {
        off = run(fzn);
      } finally {
        if (previous == null) {
          System.clearProperty("org.jacop.fz.permutedTasks");
        } else {
          System.setProperty("org.jacop.fz.permutedTasks", previous);
        }
      }
      for (String out : new String[] {on, off}) {
        assertTrue(out.contains("=========="), "trial " + trial + "\n" + out);
        assertEquals(optimum, lastCost(out), "trial " + trial + " " + Arrays.deepToString(p));
      }
    }
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
