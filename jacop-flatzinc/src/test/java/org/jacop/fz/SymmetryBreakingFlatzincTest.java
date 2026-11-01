/*
 * SymmetryBreakingFlatzincTest.java
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

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.IntUnaryOperator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks symmetry breaking in presolve on random models built to have symmetries: a random
 * permutation of the variables, and constraints closed under it. With symmetry breaking a model
 * must stay satisfiable or unsatisfiable, and keep its optimum; presolve runs in checking mode, so
 * every solution is also checked against the loaded model.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
class SymmetryBreakingFlatzincTest {

  private static final Pattern GENERATORS = Pattern.compile("symmetryGenerators=(\\d+)");
  private static final Pattern OBJECTIVE = Pattern.compile("obj = (-?\\d+);");

  @TempDir Path tmp;

  @Test
  void pigeonholeIsRefutedWithFewFailures() throws IOException {
    int holes = 7;
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i <= holes; i++) {
      for (int h = 0; h < holes; h++) {
        fzn.append("var bool: p_").append(i).append('_').append(h).append(";\n");
      }
    }
    for (int i = 0; i <= holes; i++) {
      List<String> row = new ArrayList<>();
      for (int h = 0; h < holes; h++) {
        row.add("p_" + i + "_" + h);
      }
      fzn.append("constraint bool_clause([").append(String.join(",", row)).append("],[]);\n");
    }
    for (int h = 0; h < holes; h++) {
      for (int i = 0; i <= holes; i++) {
        for (int j = i + 1; j <= holes; j++) {
          fzn.append("constraint bool_clause([],[p_")
              .append(i)
              .append('_')
              .append(h)
              .append(",p_")
              .append(j)
              .append('_')
              .append(h)
              .append("]);\n");
        }
      }
    }
    fzn.append("solve satisfy;\n");
    String model = fzn.toString();

    String off =
        FlatzincTestRunner.run(
            tmp, model, "--search-statistics", "--presolve", "on", "--symmetry", "off");
    String on = FlatzincTestRunner.run(tmp, model, "--search-statistics", "--presolve", "check");
    assertTrue(off.contains("=====UNSATISFIABLE====="), off);
    assertTrue(on.contains("=====UNSATISFIABLE====="), on);
    // the pigeons and the holes are interchangeable: 7 + 6 generators
    assertEquals(13, generators(on));
    assertTrue(failures(on) * 10 < failures(off), on + "\n" + off);
  }

  @Test
  void readingTheModelCountsInTheTimeGiven() throws IOException {
    // building the graph of a large model took several times the second given to the
    // automorphism search (groupsplitter: 7 s); it now stops when the time is up
    String model =
        """
        array [1..4] of var 1..4: x :: output_array([1..4]);
        constraint jacop_alldiff(x);
        solve satisfy;
        """;
    String on = FlatzincTestRunner.run(tmp, model, "--search-statistics", "--symmetry", "on");
    assertTrue(on.contains("symmetryConstraints=2"), on);
    String time = System.setProperty("org.jacop.fz.symmetryTime", "0");
    try {
      String out = FlatzincTestRunner.run(tmp, model, "--search-statistics", "--symmetry", "on");
      assertTrue(out.contains("symmetryConstraints=0"), out);
      assertTrue(out.contains("symmetrySearchComplete=false"), out);
      assertTrue(out.contains("time limit"), out);
      assertTrue(out.contains("----------"), out);
    } finally {
      if (time == null) {
        System.clearProperty("org.jacop.fz.symmetryTime");
      } else {
        System.setProperty("org.jacop.fz.symmetryTime", time);
      }
    }
  }

  @Test
  void aSearchForTheLargestValuesMeetsTheLargestSolutionFirst() throws IOException {
    // any two of the four may be 1; the search tries 1 first, so it meets x = [1, 1, 0, 0] first,
    // which the lex-leader constraints must keep
    String model =
        """
        array [1..4] of var 0..1: x :: output_array([1..4]);
        constraint int_lin_le([1,1,1,1], x, 2);
        constraint int_lin_le([-1,-1,-1,-1], x, -2);
        solve :: int_search(x, input_order, indomain_max, complete) satisfy;
        """;
    String out = FlatzincTestRunner.run(tmp, model, "--search-statistics", "--symmetry", "on");
    assertTrue(out.contains("x = array1d(1..4, [1, 1, 0, 0]);"), out);
    assertTrue(out.contains("failures=0"), out);
    assertTrue(generators(out) > 0, out);
  }

  /**
   * The model with a search annotation over its x variables that tries the largest values first.
   */
  private static String largestFirst(String model) {
    List<String> xs = new ArrayList<>();
    Matcher m = Pattern.compile("var [^:]+: (x\\d+)").matcher(model);
    while (m.find()) {
      xs.add(m.group(1));
    }
    return model.replace(
        "solve ",
        "solve :: int_search(["
            + String.join(",", xs)
            + "], input_order, indomain_max, complete) ");
  }

  @Test
  void freeSearchLeavesTheMachinesOfAMakespanUnordered() throws IOException {
    // identical machines with the largest load minimized (P||Cmax): value precedence on the
    // machines multiplied the failures of --lcg -f, so free search leaves it out
    String model =
        """
        array [1..6] of var 1..3: mc :: output_array([1..6]);
        array [1..3] of var 0..30: load;
        var 0..30: makespan :: output_var;
        constraint jacop_bin_packing(mc, load, [7, 6, 5, 4, 3, 3], 1);
        constraint jacop_maximum(makespan, load);
        solve :: int_search(mc, first_fail, indomain_min, complete) minimize makespan;
        """;
    String annotated =
        FlatzincTestRunner.run(tmp, model, "--search-statistics", "--symmetry", "on");
    assertTrue(annotated.contains("symmetryValuePrecedences=1"), annotated);
    for (String[] options :
        new String[][] {
          {"--search-statistics", "-f", "--symmetry", "on"},
          {"--search-statistics", "-f", "--lcg", "--symmetry", "on"}
        }) {
      String free = FlatzincTestRunner.run(tmp, model, options);
      assertTrue(free.contains("symmetryValuePrecedences=0"), free);
      assertEquals(10, objective(free, "makespan"), free);
    }
    assertEquals(10, objective(annotated, "makespan"), annotated);
  }

  @Test
  void allSolutionsOfASatisfactionProblemAreKept() throws IOException {
    String model =
        """
        var 1..3: x :: output_var;
        var 1..3: y :: output_var;
        constraint int_ne(x, y);
        solve satisfy;
        """;
    String out =
        FlatzincTestRunner.run(tmp, model, "-a", "--search-statistics", "--presolve", "check");
    assertEquals(6, FlatzincTestRunner.solutions(out).size(), out);
    assertFalse(out.contains("symmetryGenerators"), out);
  }

  @Test
  void randomSymmetricModelsKeepSatisfiabilityAndOptimum() throws IOException {
    Random random = new Random(5);
    int trials = Integer.getInteger("symmetry.trials", 300);
    int broken = 0;
    for (int trial = 0; trial < trials; trial++) {
      boolean optimise = random.nextBoolean();
      String model = randomModel(random, optimise);
      String off = FlatzincTestRunner.run(tmp, model, "--presolve", "off");
      String on = FlatzincTestRunner.run(tmp, model, "--search-statistics", "--presolve", "check");
      String what = "trial " + trial + "\n" + model + "\n" + on;
      boolean unsat = off.contains("=====UNSATISFIABLE=====");
      assertEquals(unsat, on.contains("=====UNSATISFIABLE====="), what);
      if (optimise && !unsat) {
        assertEquals(objective(off), objective(on), what);
      }
      // without presolve, as fzn-jacop runs by default; compared with LCG without symmetry
      // breaking, since LCG rejects some of these models (array_int_maximum) that CP refutes
      String lcgOff = FlatzincTestRunner.run(tmp, model, "--symmetry", "off", "--lcg");
      String lcgOn = FlatzincTestRunner.run(tmp, model, "--symmetry", "on", "--lcg");
      // a search for the largest values first keeps the largest solution of each orbit
      if (trial % 2 == 0) {
        lcgOn = FlatzincTestRunner.run(tmp, largestFirst(model), "--symmetry", "on", "--lcg");
      }
      boolean lcgUnsat = lcgOff.contains("=====UNSATISFIABLE=====");
      assertEquals(lcgUnsat, lcgOn.contains("=====UNSATISFIABLE====="), what + "\n" + lcgOn);
      if (optimise && !lcgUnsat) {
        assertEquals(objective(lcgOff), objective(lcgOn), what + "\n" + lcgOn);
      }
      if (generators(on) > 0) {
        broken++;
      }
    }
    assertTrue(broken > trials / 3, "broken " + broken);
  }

  @Test
  void interchangeableValuesNeedEveryPermutationFixingTheRest() {
    // the symmetric group of 4 points, from a 4-cycle and a swap
    assertEquals(
        List.of("[0, 1, 2, 3]"), classes(4, new int[] {1, 2, 3, 0}, new int[] {1, 0, 2, 3}));
    // the symmetries of a square permute its corners, but not in every way
    assertEquals(List.of(), classes(4, new int[] {1, 2, 3, 0}, new int[] {3, 2, 1, 0}));
    // the alternating group of 4 points
    assertEquals(List.of(), classes(4, new int[] {1, 2, 0, 3}, new int[] {0, 2, 3, 1}));
    // 0 and 1 swap together with 2 and 3; never alone
    assertEquals(List.of(), classes(4, new int[] {1, 0, 3, 2}));
    // the product of a 3-cycle and a swap of 3 and 4, with the swap of 0 and 1
    assertEquals(
        List.of("[0, 1, 2]", "[3, 4]"),
        classes(5, new int[] {1, 2, 0, 4, 3}, new int[] {1, 0, 2, 3, 4}));
    // (0 1)(2 3) and (0 1) generate (2 3) too, which a stabilizer chain finds
    assertEquals(
        List.of("[0, 1]", "[2, 3]"), classes(4, new int[] {1, 0, 3, 2}, new int[] {1, 0, 2, 3}));
  }

  private static List<String> classes(int n, int[]... generators) {
    return SymmetryBreaking.symmetricClasses(List.of(generators), n).stream()
        .map(Arrays::toString)
        .toList();
  }

  @Test
  void colouringValuesAreInterchangeable() throws IOException {
    // a 5-cycle with 3 colours: 30 colourings, 5 up to colour permutations
    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < 5; i++) {
      fzn.append("var 1..3: x").append(i).append(" :: output_var;\n");
    }
    for (int i = 0; i < 5; i++) {
      fzn.append("constraint int_lin_ne([1,-1],[x")
          .append(i)
          .append(",x")
          .append((i + 1) % 5)
          .append("],0);\n");
    }
    fzn.append("solve satisfy;\n");
    String on =
        FlatzincTestRunner.run(tmp, fzn.toString(), "--search-statistics", "--presolve", "check");
    assertEquals(1, precedences(on), on);
    // value precedence: x0 = 1, and the first other colour is 2
    assertTrue(on.contains("x0 = 1;"), on);
  }

  @Test
  void fewestColoursKeepValuePrecedence() throws IOException {
    // the number of colours bounds every colour, which breaks their symmetry; relabelling the
    // colours by first use never raises the largest one, so the precedence chain is still posted
    StringBuilder fzn = new StringBuilder("var 1..4: colours :: output_var;\n");
    for (int i = 0; i < 5; i++) {
      fzn.append("var 1..4: x").append(i).append(" :: output_var;\n");
    }
    for (int i = 0; i < 5; i++) {
      fzn.append("constraint int_lin_ne([1,-1],[x")
          .append(i)
          .append(",x")
          .append((i + 1) % 5)
          .append("],0);\n");
      fzn.append("constraint int_lin_le([1,-1],[x").append(i).append(",colours],0);\n");
    }
    fzn.append("solve minimize colours;\n");
    String on =
        FlatzincTestRunner.run(tmp, fzn.toString(), "--search-statistics", "--presolve", "check");
    assertEquals(1, precedences(on), on);
    assertEquals(3, objective(on, "colours"), on);
  }

  @Test
  void identicalBinsAreInterchangeable() throws IOException {
    String model =
        """
        array [1..5] of int: w = [5,4,4,3,2];
        var 1..4: b1 :: output_var;
        var 1..4: b2 :: output_var;
        var 1..4: b3 :: output_var;
        var 1..4: b4 :: output_var;
        var 1..4: b5 :: output_var;
        var 0..8: l1;
        var 0..8: l2;
        var 0..8: l3;
        var 0..8: l4;
        var bool: u1;
        var bool: u2;
        var bool: u3;
        var bool: u4;
        var 0..4: used :: output_var;
        constraint jacop_bin_packing([b1,b2,b3,b4,b5],[l1,l2,l3,l4],w,1);
        constraint int_lt_reif(0,l1,u1);
        constraint int_lt_reif(0,l2,u2);
        constraint int_lt_reif(0,l3,u3);
        constraint int_lt_reif(0,l4,u4);
        constraint bool_lin_eq([1,1,1,1],[u1,u2,u3,u4],used);
        solve minimize used;
        """;
    String off =
        FlatzincTestRunner.run(
            tmp, model, "--search-statistics", "--presolve", "on", "--symmetry", "off");
    String on = FlatzincTestRunner.run(tmp, model, "--search-statistics", "--presolve", "check");
    assertEquals(objective(off, "used"), objective(on, "used"), on);
    assertEquals(3, objective(on, "used"), on);
    assertEquals(1, precedences(on), on);
    assertTrue(on.contains("b1 = 1;"), on);
  }

  @Test
  void presolveNarrowsDomainsAtTheLevelPropagationRaised() throws IOException {
    // Alldistinct raises the level before its consistency; with the precedence chain posted,
    // presolve propagated it inside a round of rules and dual reductions then narrowed a load at
    // the level before (an assertion with jacop.asserts.enabled)
    String model =
        """
        var 1..3: x0 :: output_var;
        var bool: e0_1;
        var bool: e0_2;
        var bool: e0_3;
        var 1..3: x1 :: output_var;
        var bool: e1_1;
        var bool: e1_2;
        var bool: e1_3;
        var 1..3: x2 :: output_var;
        var bool: e2_1;
        var bool: e2_2;
        var bool: e2_3;
        var 1..3: x3 :: output_var;
        var bool: e3_1;
        var bool: e3_2;
        var bool: e3_3;
        var 1..3: x4 :: output_var;
        var bool: e4_1;
        var bool: e4_2;
        var bool: e4_3;
        var 0..5: c1;
        var 0..15: l1;
        var 0..5: c2;
        var 0..15: l2;
        var 0..5: c3;
        var 0..15: l3;
        constraint int_ne(x2,x4);
        constraint bool_clause([e1_3,e4_3],[e3_3]);
        constraint bool_clause([e1_1,e4_1],[e3_1]);
        constraint bool_clause([e1_2,e4_2],[e3_2]);
        constraint jacop_alldiff([x4,x1,x0]);
        constraint int_ne(x4,x2);
        constraint int_le(c2,l2);
        constraint int_le(c3,l3);
        constraint int_le(c1,l1);
        constraint int_eq_reif(x0,1,e0_1);
        constraint int_eq_reif(x0,2,e0_2);
        constraint int_eq_reif(x0,3,e0_3);
        constraint int_eq_reif(x1,1,e1_1);
        constraint int_eq_reif(x1,2,e1_2);
        constraint int_eq_reif(x1,3,e1_3);
        constraint int_eq_reif(x2,1,e2_1);
        constraint int_eq_reif(x2,2,e2_2);
        constraint int_eq_reif(x2,3,e2_3);
        constraint int_eq_reif(x3,1,e3_1);
        constraint int_eq_reif(x3,2,e3_2);
        constraint int_eq_reif(x3,3,e3_3);
        constraint int_eq_reif(x4,1,e4_1);
        constraint int_eq_reif(x4,2,e4_2);
        constraint int_eq_reif(x4,3,e4_3);
        constraint jacop_count([x0,x1,x2,x3,x4],1,c1);
        constraint jacop_count([x0,x1,x2,x3,x4],2,c2);
        constraint jacop_count([x0,x1,x2,x3,x4],3,c3);
        solve satisfy;
        """;
    String on = FlatzincTestRunner.run(tmp, model, "--search-statistics", "--presolve", "check");
    assertEquals(1, precedences(on), on);
    assertTrue(on.contains("x0 = 1;"), on);
  }

  @Test
  void randomValueSymmetricModelsKeepSatisfiabilityAndOptimum() throws IOException {
    Random random = new Random(Long.getLong("symmetry.seed", 11));
    int trials = Integer.getInteger("symmetry.trials", 300);
    int broken = 0;
    for (int trial = 0; trial < trials; trial++) {
      boolean optimise = random.nextBoolean();
      String model = randomValueModel(random, optimise);
      String off = FlatzincTestRunner.run(tmp, model, "--presolve", "off");
      String what = "trial " + trial + "\n" + model;
      boolean unsat = off.contains("=====UNSATISFIABLE=====");
      for (String[] options :
          new String[][] {
            {"--search-statistics", "--presolve", "check"},
            {"--search-statistics", "--presolve", "check", "--lcg"},
            // without presolve, as fzn-jacop runs by default, and with the annotation search
            {"--search-statistics", "--lcg", "--symmetry", "on"},
            {"--search-statistics", "-f", "--symmetry", "on"},
          }) {
        String on;
        try {
          on = FlatzincTestRunner.run(tmp, model, options);
        } catch (RuntimeException e) {
          throw new AssertionError(what + "\n" + String.join(" ", options), e);
        }
        String why = what + "\n" + String.join(" ", options) + "\n" + on;
        assertEquals(unsat, on.contains("=====UNSATISFIABLE====="), why);
        if (optimise && !unsat) {
          assertEquals(objective(off, "obj"), objective(on, "obj"), why);
        }
        if (options.length == 3 && precedences(on) > 0) {
          broken++;
        } else if (options.length == 3 && Boolean.getBoolean("dumpnp") && trial < 60) {
          java.nio.file.Files.writeString(
              java.nio.file.Path.of("/tmp/claude-0/np" + trial + ".fzn"), model);
        }
      }
    }
    assertTrue(broken > trials / 8, "broken " + broken);
  }

  @Test
  void randomMatrixModelsKeepSatisfiabilityAndOptimum() throws IOException {
    Random random = new Random(Long.getLong("symmetry.seed", 13));
    int trials = Integer.getInteger("symmetry.trials", 300) / 2;
    int chains = 0;
    for (int trial = 0; trial < trials; trial++) {
      boolean optimise = random.nextBoolean();
      String model = randomMatrixModel(random, optimise);
      String off = FlatzincTestRunner.run(tmp, model, "--presolve", "off");
      String what = "trial " + trial + "\n" + model;
      boolean unsat = off.contains("=====UNSATISFIABLE=====");
      for (String[] options :
          new String[][] {
            {"--search-statistics", "--presolve", "check"},
            {"--search-statistics", "--presolve", "check", "--lcg"},
            // without presolve, as fzn-jacop runs by default, and with the annotation search
            {"--search-statistics", "--lcg", "--symmetry", "on"},
            {"--search-statistics", "-f", "--symmetry", "on"},
          }) {
        String on;
        try {
          on = FlatzincTestRunner.run(tmp, model, options);
        } catch (RuntimeException e) {
          throw new AssertionError(what + "\n" + String.join(" ", options), e);
        }
        String why = what + "\n" + String.join(" ", options) + "\n" + on;
        assertEquals(unsat, on.contains("=====UNSATISFIABLE====="), why);
        if (optimise && !unsat) {
          assertEquals(objective(off, "obj"), objective(on, "obj"), why);
        }
        Matcher m = Pattern.compile("symmetryOrbitopes=(\\d+)").matcher(on);
        if (options.length == 3 && m.find() && Integer.parseInt(m.group(1)) > 0) {
          chains++;
        }
      }
    }
    assertTrue(chains > trials / 8, "orbitopes " + chains);
  }

  /**
   * A 0/1 matrix x_r_c with a flag o_c per column, closed under every permutation of the columns (a
   * cycle and a swap) and, in some models, a random permutation of the rows.
   */
  private static String randomMatrixModel(Random random, boolean optimise) {
    int rows = 3 + random.nextInt(3);
    int cols = 3 + random.nextInt(2);
    int[] w = random.ints(rows, 1, 5).toArray();
    int cap = 3 + random.nextInt(5);
    int[] cycle = new int[cols];
    for (int i = 0; i < cols; i++) {
      cycle[i] = (i + 1) % cols;
    }
    int[] swap = identityOf(cols);
    swap[0] = 1;
    swap[1] = 0;
    int[] pi = random.nextBoolean() ? permutation(rows, random) : identityOf(rows);
    // rows that the permutation maps to each other have the same weight
    for (int i = 0; i < rows; i++) {
      int j = pi[i];
      while (j != i) {
        w[j] = w[i];
        j = pi[j];
      }
    }
    Set<String> constraints = new LinkedHashSet<>();
    for (int c = 0; c < cols; c++) {
      StringBuilder ws = new StringBuilder();
      StringBuilder xs = new StringBuilder();
      for (int r = 0; r < rows; r++) {
        ws.append(w[r]).append(',');
        xs.append("x_").append(r).append('_').append(c).append(',');
        constraints.add("bool_clause([o_" + c + "],[x_" + r + "_" + c + "])");
      }
      constraints.add(
          "bool_lin_le(["
              + ws.substring(0, ws.length() - 1)
              + "],["
              + xs.substring(0, xs.length() - 1)
              + "],"
              + cap
              + ")");
    }
    for (int r = 0; r < rows; r++) {
      StringBuilder xs = new StringBuilder();
      for (int c = 0; c < cols; c++) {
        xs.append(c > 0 ? "," : "").append("x_").append(r).append('_').append(c);
      }
      constraints.add("bool_clause([" + xs + "],[])");
    }
    int base = 1 + random.nextInt(3);
    for (int t = 0; t < base; t++) {
      // a clause over cells, and its images
      int[] rs = random.ints(2, 0, rows).toArray();
      int[] cs = random.ints(2, 0, cols).toArray();
      boolean[] neg = {random.nextBoolean(), random.nextBoolean()};
      List<int[][]> queue = new ArrayList<>();
      Set<String> seen = new LinkedHashSet<>();
      queue.add(new int[][] {rs, cs});
      for (int head = 0; head < queue.size() && head < 400; head++) {
        int[] r = queue.get(head)[0];
        int[] c = queue.get(head)[1];
        if (!seen.add(Arrays.toString(r) + Arrays.toString(c))) {
          continue;
        }
        List<String> pos = new ArrayList<>();
        List<String> ngs = new ArrayList<>();
        for (int i = 0; i < 2; i++) {
          (neg[i] ? ngs : pos).add("x_" + r[i] + "_" + c[i]);
        }
        if (!(pos.size() == 1 && pos.equals(ngs))) {
          constraints.add(
              "bool_clause([" + String.join(",", pos) + "],[" + String.join(",", ngs) + "])");
        }
        queue.add(new int[][] {Arrays.stream(r).map(i -> pi[i]).toArray(), c});
        for (int[] g : List.of(cycle, swap)) {
          queue.add(new int[][] {r, Arrays.stream(c).map(i -> g[i]).toArray()});
        }
      }
    }
    StringBuilder fzn = new StringBuilder();
    for (int r = 0; r < rows; r++) {
      for (int c = 0; c < cols; c++) {
        fzn.append("var bool: x_").append(r).append('_').append(c).append(" :: output_var;\n");
      }
    }
    List<String> flags = new ArrayList<>();
    for (int c = 0; c < cols; c++) {
      fzn.append("var bool: o_").append(c).append(";\n");
      flags.add("o_" + c);
    }
    if (optimise) {
      fzn.append("var 0..").append(cols).append(": obj :: output_var;\n");
    }
    for (String c : constraints) {
      fzn.append("constraint ").append(c).append(";\n");
    }
    if (optimise) {
      fzn.append("constraint bool_lin_eq([")
          .append(String.join(",", Collections.nCopies(cols, "1")))
          .append("],[")
          .append(String.join(",", flags))
          .append("],obj);\n");
      fzn.append(random.nextBoolean() ? "solve minimize obj;\n" : "solve maximize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  private static int precedences(String out) {
    Matcher m = Pattern.compile("symmetryValuePrecedences=(\\d+)").matcher(out);
    return m.find() ? Integer.parseInt(m.group(1)) : 0;
  }

  private static int objective(String out, String name) {
    Matcher m = Pattern.compile(name + " = (-?\\d+);").matcher(out);
    int last = Integer.MIN_VALUE;
    while (m.find()) {
      last = Integer.parseInt(m.group(1));
    }
    return last;
  }

  /**
   * A model over variables x0.. with values 1..k, their indicators e_i_v (x_i = v), their counts
   * c_v and the loads l_v of a bin packing, closed under a random permutation of the values and of
   * the variables x: a constraint is posted with its images until they repeat. Some models also
   * compare x by number, which leaves them without value symmetry.
   */
  private static String randomValueModel(Random random, boolean optimise) {
    int n = 3 + random.nextInt(4);
    int k = 2 + random.nextInt(3);
    // the values are permuted by a random permutation, or in every way (a k-cycle and a swap)
    List<int[]> sigmas = new ArrayList<>();
    if (random.nextBoolean()) {
      sigmas.add(permutation(k, random));
    } else {
      int[] cycle = new int[k];
      for (int i = 0; i < k; i++) {
        cycle[i] = (i + 1) % k;
      }
      int[] swap = identityOf(k);
      swap[0] = 1;
      swap[1] = 0;
      sigmas.add(cycle);
      sigmas.add(swap);
    }
    int[] pi = random.nextBoolean() ? permutation(n, random) : identityOf(n);

    Set<String> constraints = new LinkedHashSet<>();
    int base = 2 + random.nextInt(4);
    for (int t = 0; t < base; t++) {
      ValueTemplate tmpl = valueTemplate(random, n, k);
      // the images of the constraint under the permutations, breadth first
      List<int[][]> queue = new ArrayList<>();
      Set<String> seen = new LinkedHashSet<>();
      queue.add(new int[][] {tmpl.x, tmpl.v});
      for (int head = 0; head < queue.size() && head < 200; head++) {
        int[] x = queue.get(head)[0];
        int[] v = queue.get(head)[1];
        if (!seen.add(Arrays.toString(x) + Arrays.toString(v))) {
          continue;
        }
        constraints.add(tmpl.text.of(x, v));
        queue.add(new int[][] {Arrays.stream(x).map(i -> pi[i]).toArray(), v});
        for (int[] sigma : sigmas) {
          queue.add(new int[][] {x, Arrays.stream(v).map(i -> sigma[i]).toArray()});
        }
      }
    }

    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < n; i++) {
      fzn.append("var 1..").append(k).append(": x").append(i).append(" :: output_var;\n");
      for (int c = 1; c <= k; c++) {
        fzn.append("var bool: e").append(i).append('_').append(c).append(";\n");
        constraints.add("int_eq_reif(x" + i + "," + c + ",e" + i + "_" + c + ")");
      }
    }
    for (int c = 1; c <= k; c++) {
      fzn.append("var 0..").append(n).append(": c").append(c).append(";\n");
      fzn.append("var 0..").append(3 * n).append(": l").append(c).append(";\n");
      constraints.add("jacop_count([" + xs(n) + "]," + c + ",c" + c + ")");
    }
    if (optimise) {
      fzn.append("var 0..").append(3 * n * k).append(": obj :: output_var;\n");
    }
    StringBuilder loads = new StringBuilder();
    StringBuilder weights = new StringBuilder();
    for (int c = 1; c <= k; c++) {
      loads.append(c > 1 ? "," : "").append('l').append(c);
    }
    for (int i = 0; i < n; i++) {
      weights.append(i > 0 ? "," : "").append(1 + random.nextInt(3));
    }
    if (random.nextBoolean()) {
      // the weights follow the permutation of the items, so they are the same along its cycles
      int[] w = new int[n];
      for (int i = 0; i < n; i++) {
        int j = i;
        int min = i;
        do {
          j = pi[j];
          min = Math.min(min, j);
        } while (j != i);
        w[i] = 1 + min % 3;
      }
      constraints.add(
          "jacop_bin_packing(["
              + xs(n)
              + "],["
              + loads
              + "],"
              + Arrays.toString(w).replace(" ", "")
              + ",1)");
    }
    for (String c : constraints) {
      fzn.append("constraint ").append(c).append(";\n");
    }
    int form = random.nextInt(4);
    if (optimise && form > 0) {
      // the largest value of the x, of all of them (a dominance keeps value precedence) or of some
      int bounded = form == 3 ? n - 1 : n;
      if (form == 1) {
        List<String> xs = new ArrayList<>();
        for (int i = 0; i < bounded; i++) {
          xs.add("x" + i);
        }
        fzn.append("constraint array_int_maximum(obj,[")
            .append(String.join(",", xs))
            .append("]);\n");
      } else {
        for (int i = 0; i < bounded; i++) {
          fzn.append(
              random.nextBoolean()
                  ? "constraint int_le(x" + i + ",obj);\n"
                  : "constraint int_lin_le([1,-1],[x" + i + ",obj],0);\n");
        }
      }
    } else if (optimise) {
      List<String> ones = new ArrayList<>();
      List<String> terms = new ArrayList<>();
      for (int c = 1; c <= k; c++) {
        ones.add("1");
        terms.add("l" + c);
      }
      for (int c = 1; c <= k; c++) {
        ones.add("2");
        terms.add("c" + c);
      }
      ones.add("-1");
      terms.add("obj");
      fzn.append("constraint int_lin_eq([")
          .append(String.join(",", ones))
          .append("],[")
          .append(String.join(",", terms))
          .append("],0);\n");
    }
    if (optimise) {
      fzn.append(random.nextBoolean() ? "solve minimize obj;\n" : "solve maximize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  private static String xs(int n) {
    List<String> xs = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      xs.add("x" + i);
    }
    return String.join(",", xs);
  }

  private static int[] identityOf(int n) {
    int[] p = new int[n];
    for (int i = 0; i < n; i++) {
      p[i] = i;
    }
    return p;
  }

  /** A constraint over variables x and values v (0-based, value v + 1), written by text. */
  private static final class ValueTemplate {
    final int[] x;
    final int[] v;
    final ValueText text;

    ValueTemplate(int[] x, int[] v, ValueText text) {
      this.x = x;
      this.v = v;
      this.text = text;
    }
  }

  private interface ValueText {
    String of(int[] x, int[] v);
  }

  private static ValueTemplate valueTemplate(Random r, int n, int k) {
    int[] x = r.ints(0, n).distinct().limit(3).toArray();
    int[] v = r.ints(3, 0, k).toArray();
    int bound = 1 + r.nextInt(3);
    ValueText text =
        switch (r.nextInt(20)) {
          case 0, 14, 15, 16 -> (xs, vs) -> "int_ne(x" + xs[0] + ",x" + xs[1] + ")";
          case 1 -> (xs, vs) -> "int_lin_ne([1,-1],[x" + xs[0] + ",x" + xs[1] + "],0)";
          case 2 -> (xs, vs) -> "int_ne(x" + xs[0] + "," + (vs[0] + 1) + ")";
          case 3 -> (xs, vs) -> "jacop_alldiff([x" + xs[0] + ",x" + xs[1] + ",x" + xs[2] + "])";
          case 4 ->
              (xs, vs) ->
                  "bool_clause([e"
                      + xs[0]
                      + "_"
                      + (vs[0] + 1)
                      + ",e"
                      + xs[1]
                      + "_"
                      + (vs[1] + 1)
                      + "],[e"
                      + xs[2]
                      + "_"
                      + (vs[0] + 1)
                      + "])";
          case 5 -> (xs, vs) -> "int_le(c" + (vs[0] + 1) + "," + bound + ")";
          case 6 -> (xs, vs) -> "int_le(l" + (vs[0] + 1) + "," + (bound + 2) + ")";
          case 7 -> (xs, vs) -> "int_le(c" + (vs[0] + 1) + ",l" + (vs[1] + 1) + ")";
          case 8 ->
              (xs, vs) ->
                  "array_int_element(c"
                      + (vs[2] + 1)
                      + ",["
                      + (vs[0] + 1)
                      + ","
                      + (vs[1] + 1)
                      + ","
                      + (vs[0] + 1)
                      + "],x"
                      + xs[0]
                      + ")";
          case 9 ->
              (xs, vs) ->
                  "int_eq_reif(x" + xs[0] + ",x" + xs[1] + ",e" + xs[2] + "_" + (vs[0] + 1) + ")";
          case 10 ->
              (xs, vs) -> "jacop_atmost([x" + xs[0] + ",x" + xs[1] + "]," + (vs[0] + 1) + ",1)";
          case 11 ->
              (xs, vs) -> "jacop_nvalue(c" + (vs[0] + 1) + ",[x" + xs[0] + ",x" + xs[1] + "])";
          case 12 -> (xs, vs) -> "int_le(x" + xs[0] + ",x" + xs[1] + ")";
          case 17, 18 ->
              (xs, vs) -> "jacop_alldiff([x" + xs[0] + ",x" + xs[1] + ",x" + xs[2] + "])";
          default ->
              (xs, vs) ->
                  "jacop_count([x"
                      + xs[0]
                      + ",x"
                      + xs[1]
                      + "],"
                      + (vs[0] + 1)
                      + ",c"
                      + (vs[1] + 1)
                      + ")";
        };
    return new ValueTemplate(x, v, text);
  }

  private static int generators(String out) {
    Matcher m = GENERATORS.matcher(out);
    return m.find() ? Integer.parseInt(m.group(1)) : 0;
  }

  private static long failures(String out) {
    Matcher m = Pattern.compile("failures=(\\d+)").matcher(out);
    long last = -1;
    while (m.find()) {
      last = Long.parseLong(m.group(1));
    }
    return last;
  }

  private static int objective(String out) {
    Matcher m = OBJECTIVE.matcher(out);
    int last = Integer.MIN_VALUE;
    while (m.find()) {
      last = Integer.parseInt(m.group(1));
    }
    return last;
  }

  /**
   * A model over integer variables x0.. and Boolean variables b0.., with random constraints and
   * their images under a random permutation of each kind of variables.
   */
  private static String randomModel(Random random, boolean optimise) {
    int ints = 4 + random.nextInt(4);
    int bools = 3 + random.nextInt(3);
    int max = 2 + random.nextInt(2);
    int[] pi = permutation(ints, random);
    int[] pb = permutation(bools, random);

    Set<String> constraints = new LinkedHashSet<>();
    int base = 2 + random.nextInt(4);
    for (int k = 0; k < base; k++) {
      Template t = template(random, ints, bools, max);
      // the constraint and its images under the permutations until they repeat
      int[] x = t.x;
      int[] b = t.b;
      for (int step = 0; step < 60; step++) {
        constraints.add(t.text(x, b));
        x = Arrays.stream(x).map(v -> pi[v]).toArray();
        b = Arrays.stream(b).map(v -> pb[v]).toArray();
      }
    }

    StringBuilder fzn = new StringBuilder();
    for (int i = 0; i < ints; i++) {
      fzn.append("var 0..").append(max).append(": x").append(i).append(" :: output_var;\n");
    }
    for (int i = 0; i < bools; i++) {
      fzn.append("var bool: b").append(i).append(" :: output_var;\n");
    }
    if (optimise) {
      fzn.append("var 0..").append(ints * max).append(": obj :: output_var;\n");
    }
    for (String c : constraints) {
      fzn.append("constraint ").append(c).append(";\n");
    }
    if (optimise) {
      List<String> ones = new ArrayList<>(Collections.nCopies(ints, "1"));
      ones.add("-1");
      List<String> xs = new ArrayList<>();
      for (int i = 0; i < ints; i++) {
        xs.add("x" + i);
      }
      xs.add("obj");
      fzn.append("constraint int_lin_eq([")
          .append(String.join(",", ones))
          .append("],[")
          .append(String.join(",", xs))
          .append("],0);\n");
      fzn.append(random.nextBoolean() ? "solve minimize obj;\n" : "solve maximize obj;\n");
    } else {
      fzn.append("solve satisfy;\n");
    }
    return fzn.toString();
  }

  /** A random permutation made of a few cycles. */
  private static int[] permutation(int n, Random random) {
    List<Integer> order = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      order.add(i);
    }
    Collections.shuffle(order, random);
    int[] p = new int[n];
    for (int i = 0; i < n; i++) {
      p[i] = i;
    }
    int i = 0;
    while (i < n) {
      int len = Math.min(n - i, 1 + random.nextInt(3));
      for (int k = 0; k < len; k++) {
        p[order.get(i + k)] = order.get(i + (k + 1) % len);
      }
      i += len;
    }
    return p;
  }

  /** A constraint over integer variables x and Boolean variables b, written by text. */
  private static final class Template {
    final int[] x;
    final int[] b;
    final Text text;

    Template(int[] x, int[] b, Text text) {
      this.x = x;
      this.b = b;
      this.text = text;
    }

    String text(int[] xs, int[] bs) {
      return text.of(i -> xs[i], i -> bs[i]);
    }
  }

  private interface Text {
    String of(IntUnaryOperator x, IntUnaryOperator b);
  }

  private static Template template(Random r, int ints, int bools, int max) {
    int[] x = r.ints(4, 0, ints).toArray();
    int[] b = r.ints(3, 0, bools).toArray();
    int c0 = r.nextInt(5) - 2;
    int c1 = r.nextInt(5) - 2;
    int c2 = r.nextInt(5) - 2;
    int k = r.nextInt(2 * max + 1) - max / 2;
    int v = r.nextInt(max + 1);
    Text text =
        switch (r.nextInt(18)) {
          case 0 -> (xs, bs) -> "int_le(" + xv(xs, 0) + "," + xv(xs, 1) + ")";
          case 1 -> (xs, bs) -> "int_ne(" + xv(xs, 0) + "," + xv(xs, 1) + ")";
          case 2 ->
              (xs, bs) ->
                  "int_lin_le(["
                      + c0
                      + ","
                      + c1
                      + ","
                      + c2
                      + "],["
                      + xv(xs, 0)
                      + ","
                      + xv(xs, 1)
                      + ","
                      + xv(xs, 2)
                      + "],"
                      + k
                      + ")";
          case 3 -> (xs, bs) -> "int_plus(" + xv(xs, 0) + "," + xv(xs, 1) + "," + xv(xs, 2) + ")";
          case 4 -> (xs, bs) -> "int_max(" + xv(xs, 0) + "," + xv(xs, 1) + "," + xv(xs, 2) + ")";
          case 5 ->
              (xs, bs) -> "jacop_alldiff([" + xv(xs, 0) + "," + xv(xs, 1) + "," + xv(xs, 2) + "])";
          case 6 ->
              (xs, bs) ->
                  "jacop_count(["
                      + xv(xs, 0)
                      + ","
                      + xv(xs, 1)
                      + ","
                      + xv(xs, 2)
                      + "],"
                      + v
                      + ","
                      + xv(xs, 3)
                      + ")";
          case 7 ->
              (xs, bs) ->
                  "array_int_maximum("
                      + xv(xs, 3)
                      + ",["
                      + xv(xs, 0)
                      + ","
                      + xv(xs, 1)
                      + ","
                      + xv(xs, 2)
                      + "])";
          case 8 ->
              (xs, bs) -> "int_eq_reif(" + xv(xs, 0) + "," + xv(xs, 1) + "," + bv(bs, 0) + ")";
          case 9 ->
              (xs, bs) -> "bool_clause([" + bv(bs, 0) + "," + bv(bs, 1) + "],[" + bv(bs, 2) + "])";
          case 10 ->
              (xs, bs) -> "array_bool_or([" + bv(bs, 0) + "," + bv(bs, 1) + "]," + bv(bs, 2) + ")";
          case 11 ->
              (xs, bs) ->
                  "int_lin_le_reif(["
                      + c0
                      + ","
                      + c1
                      + "],["
                      + xv(xs, 0)
                      + ","
                      + xv(xs, 1)
                      + "],"
                      + k
                      + ","
                      + bv(bs, 0)
                      + ")";
          case 12 ->
              (xs, bs) ->
                  "jacop_cumulative(["
                      + xv(xs, 0)
                      + ","
                      + xv(xs, 1)
                      + ","
                      + xv(xs, 2)
                      + "],[1,"
                      + (1 + v)
                      + ",2],["
                      + (1 + v)
                      + ",1,1],2)";
          case 13 ->
              (xs, bs) -> "jacop_nvalue(" + xv(xs, 3) + ",[" + xv(xs, 0) + "," + xv(xs, 1) + "])";
          case 14 -> (xs, bs) -> "bool_xor(" + bv(bs, 0) + "," + bv(bs, 1) + "," + bv(bs, 2) + ")";
          case 15 -> (xs, bs) -> "int_times(" + xv(xs, 0) + "," + xv(xs, 1) + "," + xv(xs, 2) + ")";
          case 16 ->
              (xs, bs) ->
                  "int_lin_eq(["
                      + c0
                      + ","
                      + c1
                      + "],["
                      + xv(xs, 0)
                      + ","
                      + xv(xs, 1)
                      + "],"
                      + k
                      + ")";
          default -> (xs, bs) -> "bool2int(" + bv(bs, 0) + "," + xv(xs, 0) + ")";
        };
    return new Template(x, b, text);
  }

  private static String xv(IntUnaryOperator xs, int i) {
    return "x" + xs.applyAsInt(i);
  }

  private static String bv(IntUnaryOperator bs, int i) {
    return "b" + bs.applyAsInt(i);
  }
}
