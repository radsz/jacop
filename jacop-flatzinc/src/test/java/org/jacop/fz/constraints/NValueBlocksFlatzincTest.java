/*
 * NValueBlocksFlatzincTest.java
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
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.constraints;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.fz.Fz2jacop;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * jacop_nvalue over variables whose domains fall into blocks that share no value is posted as one
 * count per block and their sum (org.jacop.fz.nvalueBlocks): random models, as the items of each
 * kind take their group from a range of their own in MiniZinc Challenge gfd-schedule, must keep the
 * optimum found by enumeration, under LCG and without it, in fixed and free search.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class NValueBlocksFlatzincTest {

  @TempDir Path tmp;

  private static final Pattern COST = Pattern.compile("cost = (-?\\d+);");

  private record Model(String fzn, int optimum) {}

  private static Model randomModel(Random random) {
    int blocks = 2 + random.nextInt(2);
    List<int[]> domains = new ArrayList<>();
    int base = random.nextInt(3);
    for (int b = 0; b < blocks; b++) {
      int width = 2 + random.nextInt(3);
      int items = 2 + random.nextInt(2);
      for (int i = 0; i < items; i++) {
        int lo = base + random.nextInt(width - 1);
        int hi = lo + 1 + random.nextInt(base + width - lo);
        domains.add(new int[] {lo, Math.min(hi, base + width)});
      }
      // a gap or none between blocks: touching ranges still share no value
      base += width + 1 + random.nextInt(2);
    }
    int n = domains.size();
    // random disequalities and equalities, each between two variables
    List<int[]> ne = new ArrayList<>();
    List<int[]> eq = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        int r = random.nextInt(8);
        if (r == 0) {
          ne.add(new int[] {i, j});
        } else if (r == 1) {
          eq.add(new int[] {i, j});
        }
      }
    }
    int[] weight = new int[n];
    for (int i = 0; i < n; i++) {
      weight[i] = random.nextInt(3) - 1;
    }

    StringBuilder s = new StringBuilder();
    StringBuilder xs = new StringBuilder();
    for (int i = 0; i < n; i++) {
      s.append("var ")
          .append(domains.get(i)[0])
          .append("..")
          .append(domains.get(i)[1])
          .append(": x")
          .append(i)
          .append(":: output_var;\n");
      xs.append(i == 0 ? "" : ",").append('x').append(i);
    }
    s.append("var 0..").append(n).append(": k;\n");
    s.append("var -1000..1000: cost:: output_var;\n");
    for (int[] p : ne) {
      s.append("constraint int_ne(x").append(p[0]).append(",x").append(p[1]).append(");\n");
    }
    for (int[] p : eq) {
      s.append("constraint int_eq(x").append(p[0]).append(",x").append(p[1]).append(");\n");
    }
    s.append("constraint jacop_nvalue(k,[").append(xs).append("]);\n");
    StringBuilder coefs = new StringBuilder("[10");
    StringBuilder vars = new StringBuilder("[k");
    for (int i = 0; i < n; i++) {
      coefs.append(',').append(weight[i]);
      vars.append(",x").append(i);
    }
    s.append("constraint int_lin_eq(")
        .append(coefs)
        .append(",-1],")
        .append(vars)
        .append(",cost],0);\n");
    s.append("solve minimize cost;\n");

    // the optimum by enumeration
    int best = Integer.MAX_VALUE;
    int[] x = new int[n];
    for (int i = 0; i < n; i++) {
      x[i] = domains.get(i)[0];
    }
    while (true) {
      boolean ok = true;
      for (int[] p : ne) {
        ok &= x[p[0]] != x[p[1]];
      }
      for (int[] p : eq) {
        ok &= x[p[0]] == x[p[1]];
      }
      if (ok) {
        Set<Integer> values = new HashSet<>();
        int cost = 0;
        for (int i = 0; i < n; i++) {
          values.add(x[i]);
          cost += weight[i] * x[i];
        }
        best = Math.min(best, cost + 10 * values.size());
      }
      int i = 0;
      while (i < n && x[i] == domains.get(i)[1]) {
        x[i] = domains.get(i)[0];
        i++;
      }
      if (i == n) {
        break;
      }
      x[i]++;
    }
    return new Model(s.toString(), best);
  }

  @Test
  void optimumOfRandomBlockModels() throws IOException {
    Random random = new Random(Long.getLong("nvalueblocks.seed", 20261119L));
    int trials = Integer.getInteger("nvalueblocks.trials", 30);
    for (int t = 0; t < trials; t++) {
      Model model = randomModel(random);
      for (String[] opts : new String[][] {{}, {"--lcg"}, {"-f"}, {"--lcg", "-f", "-t", "20000"}}) {
        String out = run(model.fzn(), opts);
        String context = "trial " + t + " " + String.join(" ", opts) + "\n" + model.fzn() + out;
        if (model.optimum() == Integer.MAX_VALUE) {
          assertEquals(true, out.contains("=====UNSATISFIABLE====="), context);
          continue;
        }
        List<Integer> costs = new ArrayList<>();
        Matcher m = COST.matcher(out);
        while (m.find()) {
          costs.add(Integer.parseInt(m.group(1)));
        }
        assertEquals(model.optimum(), costs.get(costs.size() - 1), context);
        assertEquals(true, out.contains("=========="), context);
      }
    }
  }

  @Test
  void blocksOfDisjointRanges() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 1, 3);
    IntVar b = new IntVar(store, "b", 2, 4);
    IntVar c = new IntVar(store, "c", 5, 6);
    IntVar d = new IntVar(store, "d", 7, 7);
    IntVar e = new IntVar(store, "e", 6, 8);
    // a, b overlap; c and e overlap through 6 and d lies inside e
    List<IntVar[]> blocks = GlobalConstraints.valueBlocks(new IntVar[] {e, a, d, c, b});
    assertEquals(2, blocks.size());
    assertEquals(Set.of(a, b), Set.of(blocks.get(0)));
    assertEquals(Set.of(c, d, e), Set.of(blocks.get(1)));
    assertEquals(1, GlobalConstraints.valueBlocks(new IntVar[] {a, b}).size());
  }

  private String run(String model, String... opts) throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    List<String> args = new ArrayList<>(List.of(opts));
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
