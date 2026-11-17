/*
 * FreeFirstFlatzincTest.java
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
import java.util.List;
import java.util.Random;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Free search without learning before LCG free search for objectives that are sums of squares
 * (Solve.freeSearchFirst): small balanced-curriculum models, whose optimum is found by enumeration,
 * must end optimal with every printed cost lower than the one before, whether free search proves
 * the optimum itself or LCG goes on from its best solution.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class FreeFirstFlatzincTest {

  @TempDir Path tmp;

  private static final Pattern COST = Pattern.compile("cost = (\\d+);");

  /** A random model: n courses with loads placed in p periods, curricula of courses, target t. */
  private record Model(String fzn, int optimum) {}

  private static Model randomModel(Random random) {
    int n = 4 + random.nextInt(3);
    int p = 2 + random.nextInt(2);
    int[] size = new int[n];
    for (int i = 0; i < n; i++) {
      size[i] = 1 + random.nextInt(6);
    }
    List<int[]> curricula = new ArrayList<>();
    int m = 2 + random.nextInt(2);
    for (int c = 0; c < m; c++) {
      List<Integer> members = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        if (random.nextInt(3) != 0) {
          members.add(i);
        }
      }
      if (members.isEmpty()) {
        members.add(random.nextInt(n));
      }
      curricula.add(members.stream().mapToInt(Integer::intValue).toArray());
    }
    int[] target = new int[m];
    int maxLoad = 0;
    for (int c = 0; c < m; c++) {
      int total = 0;
      for (int i : curricula.get(c)) {
        total += size[i];
      }
      target[c] = total / p;
      maxLoad = Math.max(maxLoad, total);
    }
    // a precedence between the first two courses, as the prerequisites of the curricula
    boolean precedence = random.nextBoolean();

    StringBuilder s = new StringBuilder();
    for (int i = 0; i < n; i++) {
      s.append("var 0..").append(p - 1).append(": x").append(i).append(":: output_var;\n");
    }
    StringBuilder terms = new StringBuilder();
    StringBuilder ones = new StringBuilder();
    StringBuilder con = new StringBuilder();
    for (int c = 0; c < m; c++) {
      for (int k = 0; k < p; k++) {
        String load = "l" + c + "_" + k;
        String d = "d" + c + "_" + k;
        String q = "q" + c + "_" + k;
        s.append("var 0..").append(maxLoad).append(": ").append(load).append(";\n");
        s.append("var 0..").append(maxLoad).append(": ").append(d).append(";\n");
        s.append("var 0..").append(maxLoad * maxLoad).append(": ").append(q).append(";\n");
        StringBuilder coefs = new StringBuilder();
        StringBuilder bs = new StringBuilder();
        for (int i : curricula.get(c)) {
          String b = "b" + c + "_" + k + "_" + i;
          s.append("var 0..1: ").append(b).append(";\n");
          con.append("constraint int_eq_reif(x")
              .append(i)
              .append(",")
              .append(k)
              .append(",")
              .append("bb")
              .append(b)
              .append(");\n");
          s.append("var bool: bb").append(b).append(";\n");
          con.append("constraint bool2int(bb").append(b).append(",").append(b).append(");\n");
          coefs.append(size[i]).append(',');
          bs.append(b).append(',');
        }
        con.append("constraint int_lin_eq([")
            .append(coefs)
            .append("-1],[")
            .append(bs)
            .append(load)
            .append("],0);\n");
        // d = |load - target|
        String diff = "e" + c + "_" + k;
        s.append("var ").append(-maxLoad).append("..").append(maxLoad).append(": ");
        s.append(diff).append(";\n");
        con.append("constraint int_lin_eq([1,-1],[")
            .append(load)
            .append(",")
            .append(diff)
            .append("],")
            .append(target[c])
            .append(");\n");
        con.append("constraint int_abs(").append(diff).append(",").append(d).append(");\n");
        con.append("constraint int_times(")
            .append(d)
            .append(",")
            .append(d)
            .append(",")
            .append(q)
            .append(");\n");
        terms.append(q).append(',');
        ones.append("1,");
      }
    }
    if (precedence) {
      con.append("constraint int_lin_le([1,-1],[x0,x1],-1);\n");
    }
    s.append("var int: cost:: output_var:: is_defined_var;\n");
    s.append(con);
    s.append("constraint int_lin_eq([")
        .append(ones)
        .append("-1],[")
        .append(terms)
        .append("cost],0):: defines_var(cost);\n");
    s.append("solve minimize cost;\n");

    // the optimum by enumeration of the periods
    int best = Integer.MAX_VALUE;
    int[] x = new int[n];
    int count = 1;
    for (int i = 0; i < n; i++) {
      count *= p;
    }
    for (int code = 0; code < count; code++) {
      int r = code;
      for (int i = 0; i < n; i++) {
        x[i] = r % p;
        r /= p;
      }
      if (precedence && x[0] >= x[1]) {
        continue;
      }
      int cost = 0;
      for (int c = 0; c < m; c++) {
        for (int k = 0; k < p; k++) {
          int load = 0;
          for (int i : curricula.get(c)) {
            load += x[i] == k ? size[i] : 0;
          }
          cost += (load - target[c]) * (load - target[c]);
        }
      }
      best = Math.min(best, cost);
    }
    return new Model(s.toString(), best);
  }

  @Test
  void optimumOfRandomBalancingModels() throws IOException {
    Random random = new Random(Long.getLong("freefirst.seed", 20261116L));
    int trials = Integer.getInteger("freefirst.trials", 12);
    // a model that the root or the linear relaxation already solves never reaches the search
    int fired = 0;
    for (int t = 0; t < trials; t++) {
      Model model = randomModel(random);
      // with and without -a: the replay of the XCSP competition prints every better solution
      for (boolean all : new boolean[] {true, false}) {
        String out = run(model.fzn(), all, "");
        String context = "trial " + t + " all=" + all + "\n" + model.fzn() + "\n" + out;
        fired += out.contains("freeFirstSquares=") ? 1 : 0;
        List<Integer> costs = costs(out);
        assertTrue(!costs.isEmpty(), context);
        for (int k = 1; k < costs.size(); k++) {
          assertTrue(costs.get(k) < costs.get(k - 1), context);
        }
        assertEquals(model.optimum(), costs.get(costs.size() - 1), context);
        assertTrue(out.contains("=========="), context);
      }
    }
    assertTrue(
        fired >= trials, "free search ran first in " + fired + " of " + 2 * trials + " runs");
  }

  @Test
  void offLeavesLcgAlone() throws IOException {
    Model model = randomModel(new Random(7));
    String out = run(model.fzn(), false, "free-first=0");
    assertTrue(!out.contains("freeFirstSquares="), out);
    List<Integer> costs = costs(out);
    assertEquals(model.optimum(), costs.get(costs.size() - 1), out);
  }

  private static List<Integer> costs(String out) {
    List<Integer> costs = new ArrayList<>();
    Matcher m = COST.matcher(out);
    while (m.find()) {
      costs.add(Integer.parseInt(m.group(1)));
    }
    return costs;
  }

  private String run(String model, boolean all, String config) throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    List<String> args = new ArrayList<>(List.of("--lcg", "-f", "-s", "-t", "20000"));
    if (all) {
      args.add("-a");
    }
    if (!config.isEmpty()) {
      args.add("--free-config");
      args.add(config);
    }
    args.add(fzn.toString());
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args.toArray(new String[0]));
    } finally {
      System.setOut(originalOut);
    }
    return out.toString(StandardCharsets.UTF_8);
  }
}
