/*
 * GoalsFlatzincTest.java
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
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tests of several objectives in FlatZinc: MiniZinc's goal_hierarchy annotation (lexicographic
 * optimum) and JaCoP's pareto annotation (Pareto front), on random small models against a
 * brute-force enumeration and with the search options that solve each subproblem.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class GoalsFlatzincTest {

  @TempDir Path tmp;

  private static final int N = 4;
  private static final int MAX_VALUE = 3;
  private static final Pattern X = Pattern.compile("x = array1d\\(1\\.\\.\\d+, \\[([^]]*)]\\);");

  /** The model of MiniZinc's goal_hierarchy documentation, compiled by MiniZinc 2.9.4. */
  private static final String HIERARCHY =
      """
      array [1..3] of int: X_INTRODUCED_6_ = [-1,-1,-1];
      array [1..2] of int: X_INTRODUCED_7_ = [1,-1];
      var 0..10: X_INTRODUCED_0_;
      var 0..10: X_INTRODUCED_1_;
      var 0..10: X_INTRODUCED_2_;
      var 0..30: s:: is_defined_var;
      var 0..20: X_INTRODUCED_9_ ::var_is_introduced :: is_defined_var;
      array [1..3] of var int: x:: output_array([1..3]) = [X_INTRODUCED_0_,X_INTRODUCED_1_,\
      X_INTRODUCED_2_];
      constraint int_lin_le(X_INTRODUCED_6_,[X_INTRODUCED_1_,X_INTRODUCED_0_,X_INTRODUCED_2_],-12);
      constraint int_lin_ne(X_INTRODUCED_7_,[X_INTRODUCED_0_,X_INTRODUCED_1_],0);
      constraint int_lin_eq([2,1,-1],[X_INTRODUCED_0_,X_INTRODUCED_2_,s],0):: defines_var(s);
      constraint int_lin_eq([1,1,-1],[X_INTRODUCED_0_,X_INTRODUCED_1_,X_INTRODUCED_9_],0)\
      :: defines_var(X_INTRODUCED_9_);
      solve :: int_search(x,input_order,indomain_min,complete)\
      :: goal_hierarchy([int_min_goal(X_INTRODUCED_9_),max_goal(s),min_goal(X_INTRODUCED_2_)]) \
      satisfy;
      """;

  @Test
  void goalHierarchyGivesLexicographicOptimum() throws IOException {
    // x1 + x2 = 2 at least (x1 != x2 and x3 <= 10), then 2 x1 + x3 = 14 at most
    String out = run(HIERARCHY);
    assertEquals("x = array1d(1..3, [2, 0, 10]);\n----------\n==========\n", out);
    String all = run(HIERARCHY, "-a");
    List<int[]> solutions = solutions(all);
    assertTrue(solutions.size() > 1, all);
    assertTrue(all.endsWith("x = array1d(1..3, [2, 0, 10]);\n----------\n==========\n"), all);
  }

  @Test
  void annotationOrderAndBooleanGoals() throws IOException {
    String model =
        """
        var 0..3: a:: output_var;
        var 0..3: b:: output_var;
        var bool: p:: output_var;
        constraint int_lin_le([1,1],[a,b],4);
        constraint int_le_reif(3,a,p);
        solve :: pareto([sat_goal(p), max_goal(b)]) :: int_search([a,b],input_order,indomain_min,\
        complete) satisfy;
        """;
    // p (a >= 3) and then b <= 1, or not p and b = 3
    String out = run(model);
    assertEquals(
        Set.of("a = 3;\nb = 1;\np = true;\n", "a = 0;\nb = 3;\np = false;\n"),
        Set.copyOf(Arrays.asList(out.replace("==========\n", "").split("----------\n"))),
        out);
    assertTrue(out.endsWith("----------\n==========\n"), out);
  }

  @Test
  void unsatisfiableModel() throws IOException {
    String model =
        """
        var 0..3: a:: output_var;
        constraint int_lt(a,0);
        solve :: goal_hierarchy([min_goal(a)]) satisfy;
        """;
    assertEquals("=====UNSATISFIABLE=====\n", run(model));
    assertEquals("=====UNSATISFIABLE=====\n", run(model.replace("goal_hierarchy", "pareto")));
  }

  @Test
  void floatGoalIsIgnored() throws IOException {
    String model =
        """
        var 0.0..1.0: f:: output_var;
        solve :: goal_hierarchy([float_min_goal(f)]) satisfy;
        """;
    // solved as the satisfaction problem it is without the goal
    assertTrue(run(model).contains("----------\n"));
  }

  @Test
  void randomModelsMatchEnumeration() throws IOException {
    Random rnd = new Random(20261030L);
    String[][] options = {{}, {"-f"}, {"--lcg"}, {"--presolve", "on"}};
    for (int t = 0; t < 16; t++) {
      Instance in = Instance.random(rnd);
      String[] opt = options[t % options.length];
      List<int[]> all = in.enumerate();

      String lex = run(in.model("goal_hierarchy"), opt);
      String pareto = run(in.model("pareto"), opt);
      String message = in + " " + Arrays.toString(opt);
      if (all.isEmpty()) {
        assertEquals("=====UNSATISFIABLE=====\n", lex, message);
        assertEquals("=====UNSATISFIABLE=====\n", pareto, message);
        continue;
      }
      List<int[]> best = solutions(lex);
      assertEquals(1, best.size(), message + lex);
      assertTrue(lex.endsWith("==========\n"), message + lex);
      int[] optimum = all.stream().min(in::compare).orElseThrow();
      assertEquals(
          Arrays.toString(optimum), Arrays.toString(in.objectives(best.get(0))), message + lex);

      assertTrue(pareto.endsWith("==========\n"), message + pareto);
      Set<String> front = new TreeSet<>();
      for (int[] a : all) {
        if (all.stream().noneMatch(b -> in.dominates(b, a))) {
          front.add(Arrays.toString(a));
        }
      }
      Set<String> found = new TreeSet<>();
      for (int[] x : solutions(pareto)) {
        assertTrue(found.add(Arrays.toString(in.objectives(x))), message + pareto);
      }
      assertEquals(front, found, message + pareto);
    }
  }

  /** Binary constraints between four variables and two or three weighted-sum goals. */
  private record Instance(String constraints, int[][] neq, int[][] weights, boolean[] maximize) {

    @Override
    public String toString() {
      return constraints + Arrays.deepToString(weights) + Arrays.toString(maximize);
    }

    @Override
    public boolean equals(Object o) {
      return o instanceof Instance i && toString().equals(i.toString());
    }

    @Override
    public int hashCode() {
      return toString().hashCode();
    }

    static Instance random(Random rnd) {
      StringBuilder c = new StringBuilder();
      List<int[]> neq = new ArrayList<>();
      for (int i = 0; i < N; i++) {
        for (int j = i + 1; j < N; j++) {
          if (rnd.nextInt(10) < 4) {
            neq.add(new int[] {i, j});
            c.append("constraint int_ne(x").append(i).append(",x").append(j).append(");\n");
          }
        }
      }
      if (rnd.nextInt(10) == 0) {
        c.append("constraint int_lt(x0,0);\n");
        neq.add(new int[] {-1, -1});
      }
      int m = 2 + rnd.nextInt(2);
      int[][] weights = new int[m][N];
      boolean[] maximize = new boolean[m];
      for (int o = 0; o < m; o++) {
        for (int i = 0; i < N; i++) {
          weights[o][i] = rnd.nextInt(7) - 3;
        }
        maximize[o] = rnd.nextBoolean();
      }
      return new Instance(c.toString(), neq.toArray(new int[0][]), weights, maximize);
    }

    String model(String annotation) {
      StringBuilder s = new StringBuilder();
      for (int i = 0; i < N; i++) {
        s.append("var 0..").append(MAX_VALUE).append(": x").append(i).append(";\n");
      }
      for (int o = 0; o < weights.length; o++) {
        s.append("var -100..100: o").append(o).append(";\n");
      }
      s.append("array [1..").append(N).append("] of var int: x:: output_array([1..").append(N);
      s.append("]) = [x0");
      for (int i = 1; i < N; i++) {
        s.append(",x").append(i);
      }
      s.append("];\n").append(constraints);
      StringBuilder goals = new StringBuilder();
      for (int o = 0; o < weights.length; o++) {
        s.append("constraint int_lin_eq([");
        for (int i = 0; i < N; i++) {
          s.append(weights[o][i]).append(',');
        }
        s.append("-1],[x0,x1,x2,x3,o").append(o).append("],0);\n");
        goals.append(o == 0 ? "" : ",").append(maximize[o] ? "max_goal(o" : "int_min_goal(o");
        goals.append(o).append(')');
      }
      return s.append("solve :: ")
          .append(annotation)
          .append("([")
          .append(goals)
          .append("]) satisfy;\n")
          .toString();
    }

    List<int[]> enumerate() {
      List<int[]> all = new ArrayList<>();
      int[] x = new int[N];
      for (int c = 0; c < (int) Math.pow(MAX_VALUE + 1.0, N); c++) {
        int r = c;
        for (int i = 0; i < N; i++) {
          x[i] = r % (MAX_VALUE + 1);
          r /= MAX_VALUE + 1;
        }
        if (satisfied(x)) {
          all.add(objectives(x));
        }
      }
      return all;
    }

    boolean satisfied(int[] x) {
      for (int[] c : neq) {
        if (c[0] < 0 || x[c[0]] == x[c[1]]) {
          return false;
        }
      }
      return true;
    }

    int[] objectives(int[] x) {
      int[] v = new int[weights.length];
      for (int o = 0; o < v.length; o++) {
        for (int i = 0; i < N; i++) {
          v[o] += weights[o][i] * x[i];
        }
      }
      return v;
    }

    // lexicographic order, better first
    int compare(int[] a, int[] b) {
      for (int o = 0; o < a.length; o++) {
        if (a[o] != b[o]) {
          return maximize[o] ? Integer.compare(b[o], a[o]) : Integer.compare(a[o], b[o]);
        }
      }
      return 0;
    }

    boolean dominates(int[] a, int[] b) {
      boolean strictly = false;
      for (int o = 0; o < a.length; o++) {
        int d = maximize[o] ? a[o] - b[o] : b[o] - a[o];
        if (d < 0) {
          return false;
        }
        strictly |= d > 0;
      }
      return strictly;
    }
  }

  private static List<int[]> solutions(String out) {
    List<int[]> solutions = new ArrayList<>();
    Matcher m = X.matcher(out);
    while (m.find()) {
      solutions.add(
          Arrays.stream(m.group(1).split(","))
              .map(String::strip)
              .mapToInt(Integer::parseInt)
              .toArray());
    }
    return solutions;
  }

  private String run(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("goals.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      assertEquals(0, new Fz2jacop().callMain(args));
    } finally {
      System.setOut(originalOut);
    }
    return out.toString(StandardCharsets.UTF_8);
  }
}
