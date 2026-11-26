/*
 * FixedFirstFlatzincTest.java
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
 * The annotation's search without learning before LCG fixed search on optimisation models
 * (Solve.fixedSearchFirst), and LCG giving way to it, and diffn posted as pairwise disjunctions
 * under LCG fixed search: every printed cost must be lower than the one before, and the last one
 * the optimum that search without learning proves.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class FixedFirstFlatzincTest {

  @TempDir Path tmp;

  private static final Pattern COST = Pattern.compile("cost = (-?\\d+);");

  /**
   * Points on a grid placed to match given distances, the model of city-position (MiniZinc
   * Challenge 2017) with Manhattan distances: cost = sum |(|xa - xb| + |ya - yb|) - d|, under a
   * first_fail annotation.
   */
  private static String cityModel(Random random, int points, int size) {
    StringBuilder s = new StringBuilder();
    StringBuilder con = new StringBuilder();
    StringBuilder search = new StringBuilder();
    StringBuilder terms = new StringBuilder();
    StringBuilder ones = new StringBuilder();
    for (int i = 0; i < points; i++) {
      s.append("var 0..").append(size).append(": x").append(i).append(":: output_var;\n");
      s.append("var 0..").append(size).append(": y").append(i).append(":: output_var;\n");
    }
    for (int i = 0; i < points; i++) {
      search.append(i == 0 ? "" : ",").append('x').append(i);
    }
    for (int i = 0; i < points; i++) {
      search.append(",y").append(i);
    }
    int pair = 0;
    for (int a = 0; a < points; a++) {
      for (int b = a + 1; b < points; b++) {
        int d = random.nextInt(2 * size + 1);
        String p = "p" + pair++;
        for (String c : new String[] {"x", "y"}) {
          s.append("var ").append(-size).append("..").append(size).append(": d");
          s.append(c).append(p).append(";\n");
          s.append("var 0..").append(size).append(": a").append(c).append(p).append(";\n");
          con.append("constraint int_lin_eq([1,-1,-1],[")
              .append(c)
              .append(a)
              .append(',')
              .append(c)
              .append(b)
              .append(",d")
              .append(c)
              .append(p)
              .append("],0);\n");
          con.append("constraint int_abs(d")
              .append(c)
              .append(p)
              .append(",a")
              .append(c)
              .append(p)
              .append(");\n");
        }
        s.append("var ").append(-4 * size).append("..").append(4 * size).append(": e");
        s.append(p).append(";\n");
        s.append("var 0..").append(4 * size).append(": f").append(p).append(";\n");
        con.append("constraint int_lin_eq([1,1,-1],[ax")
            .append(p)
            .append(",ay")
            .append(p)
            .append(",e")
            .append(p)
            .append("],")
            .append(d)
            .append(");\n");
        con.append("constraint int_abs(e").append(p).append(",f").append(p).append(");\n");
        terms.append('f').append(p).append(',');
        ones.append("1,");
      }
    }
    s.append("var 0..").append(4 * size * pair).append(": cost:: output_var:: is_defined_var;\n");
    s.append(con);
    s.append("constraint int_lin_eq([")
        .append(ones)
        .append("-1],[")
        .append(terms)
        .append("cost],0):: defines_var(cost);\n");
    s.append("solve :: int_search([")
        .append(search)
        .append("],first_fail,indomain_min,complete) minimize cost;\n");
    return s.toString();
  }

  /**
   * Squares of random sizes placed without overlap in a strip of fixed width, the height of the
   * highest one minimised, under an input_order annotation on their positions.
   */
  private static String stripModel(Random random, int squares, int width) {
    StringBuilder s = new StringBuilder();
    StringBuilder con = new StringBuilder();
    StringBuilder xs = new StringBuilder();
    StringBuilder ys = new StringBuilder();
    StringBuilder sizes = new StringBuilder();
    int total = 0;
    for (int i = 0; i < squares; i++) {
      int size = 1 + random.nextInt(3);
      total += size;
      s.append("var 0..").append(width - size).append(": x").append(i).append(":: output_var;\n");
      xs.append(i == 0 ? "" : ",").append('x').append(i);
      sizes.append(i == 0 ? "" : ",").append(size);
      ys.append(i == 0 ? "" : ",").append('y').append(i);
      con.append("constraint int_lin_le([1,-1],[y")
          .append(i)
          .append(",cost],")
          .append(-size)
          .append(");\n");
    }
    for (int i = 0; i < squares; i++) {
      // a tall strip, so that the squares fill little of it, as diffnByPairs requires
      s.append("var 0..").append(20 * total).append(": y").append(i).append(":: output_var;\n");
    }
    s.append("var 0..").append(21 * total).append(": cost:: output_var;\n");
    s.append(con);
    s.append("constraint jacop_diff2_strict([")
        .append(xs)
        .append("],[")
        .append(ys)
        .append("],[")
        .append(sizes)
        .append("],[")
        .append(sizes)
        .append("]);\n");
    s.append("solve :: seq_search([int_search([")
        .append(xs)
        .append("],input_order,indomain_min,complete),int_search([")
        .append(ys)
        .append("],input_order,indomain_min,complete)]) minimize cost;\n");
    return s.toString();
  }

  @Test
  void optimumAfterSearchWithoutLearningFirst() throws IOException {
    Random random = new Random(Long.getLong("fixedfirst.seed", 20261121L));
    int trials = Integer.getInteger("fixedfirst.trials", 4);
    int gaveWay = 0;
    int kept = 0;
    int handedBack = 0;
    for (int t = 0; t < trials; t++) {
      String model = cityModel(random, 5, 4 + random.nextInt(2));
      int optimum = optimum(model);
      // the default; a first search of a millisecond after which LCG gives way at once; the same
      // with LCG back as soon as the search without learning goes a millisecond without a better
      // solution; LCG kept
      for (String config :
          new String[] {
            "",
            "fixed-first=0.0005,fixed-first-lcg=0,fixed-first-lcg-min=0,fixed-first-rate=0",
            "fixed-first=0.0005,fixed-first-lcg=0,fixed-first-lcg-min=0,fixed-first-rate=0,"
                + "fixed-first-stall=0.000001,fixed-first-stall-min=0",
            "fixed-first=0.0005,fixed-first-lcg-min=60000"
          }) {
        String out = run(model, config, "");
        String context = "trial " + t + " config " + config + "\n" + model + "\n" + out;
        checkCosts(out, optimum, context);
        gaveWay += out.contains("fixedFirst=cp") ? 1 : 0;
        kept += out.contains("fixedFirst=lcg") ? 1 : 0;
        handedBack += out.contains("fixedFirst=cp-lcg") ? 1 : 0;
      }
    }
    assertTrue(gaveWay > 0, "LCG never gave way");
    assertTrue(kept > 0, "LCG never went on");
    assertTrue(handedBack > 0, "the search without learning never handed back to LCG");
  }

  @Test
  void offLeavesLcgAlone() throws IOException {
    String model = cityModel(new Random(7), 4, 4);
    String out = run(model, "fixed-first=0", "");
    assertTrue(!out.contains("fixedFirst="), out);
    checkCosts(out, optimum(model), out);
  }

  @Test
  void diffnByPairsUnderLcg() throws IOException {
    Random random = new Random(Long.getLong("fixedfirst.seed", 20261121L));
    int trials = Integer.getInteger("fixedfirst.trials", 4);
    for (int t = 0; t < trials; t++) {
      String model = stripModel(random, 4 + random.nextInt(4), 3 + random.nextInt(3));
      // Diffn without learning gives the optimum; LCG with the pairwise disjunctions, and with
      // Diffn, must end at it
      int optimum = optimum(model);
      for (String pairs : new String[] {"30", "0"}) {
        String out = run(model, "fixed-first=0", pairs);
        checkCosts(out, optimum, "trial " + t + " pairs " + pairs + "\n" + model + "\n" + out);
      }
    }
  }

  private static void checkCosts(String out, int optimum, String context) {
    List<Integer> costs = costs(out);
    assertTrue(!costs.isEmpty(), context);
    for (int k = 1; k < costs.size(); k++) {
      assertTrue(costs.get(k) < costs.get(k - 1), context);
    }
    assertEquals(optimum, costs.get(costs.size() - 1), context);
    assertTrue(out.contains("=========="), context);
  }

  private int optimum(String model) throws IOException {
    String out = runWith(model, List.of("--lcg", "off"), "", "");
    List<Integer> costs = costs(out);
    assertTrue(out.contains("==========") && !costs.isEmpty(), out);
    return costs.get(costs.size() - 1);
  }

  private static List<Integer> costs(String out) {
    List<Integer> costs = new ArrayList<>();
    Matcher m = COST.matcher(out);
    while (m.find()) {
      costs.add(Integer.parseInt(m.group(1)));
    }
    return costs;
  }

  private String run(String model, String config, String diffnPairs) throws IOException {
    // the build turns LCG off by default (see the parent pom)
    return runWith(model, List.of("--lcg"), config, diffnPairs);
  }

  private String runWith(String model, List<String> extra, String config, String diffnPairs)
      throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    List<String> args = new ArrayList<>(List.of("-a", "-s", "-t", "20000"));
    args.addAll(extra);
    if (!config.isEmpty()) {
      args.add("--free-config");
      args.add(config);
    }
    args.add(fzn.toString());
    String old = System.getProperty("org.jacop.fz.diffnPairs");
    if (!diffnPairs.isEmpty()) {
      System.setProperty("org.jacop.fz.diffnPairs", diffnPairs);
    }
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args.toArray(new String[0]));
    } finally {
      System.setOut(originalOut);
      if (old == null) {
        System.clearProperty("org.jacop.fz.diffnPairs");
      } else {
        System.setProperty("org.jacop.fz.diffnPairs", old);
      }
    }
    return out.toString(StandardCharsets.UTF_8);
  }
}
