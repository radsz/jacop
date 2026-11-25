/*
 * LcgSlowFallbackFlatzincTest.java
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
import java.lang.reflect.Field;
import java.lang.reflect.RecordComponent;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.LongSupplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.jacop.jasat.lcg.LcgSolver;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tests of LCG free search giving way to free search without learning (--free-config
 * lcg-slow-rate). The store must get back the clauses of the model, which under LCG went to the SAT
 * solver only, and free search must improve on the solutions printed before it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class LcgSlowFallbackFlatzincTest {

  @TempDir Path tmp;

  private static final int N = 21;

  private static final Pattern COST = Pattern.compile("cost = (\\d+);");

  // a smallest set of vertices of a cycle of N with one in every three consecutive ones, N / 3, as
  // clauses
  private static String cover() {
    StringBuilder s = new StringBuilder();
    StringBuilder xs = new StringBuilder();
    StringBuilder ones = new StringBuilder();
    for (int i = 1; i <= N; i++) {
      s.append("var bool: x").append(i).append(":: output_var;\n");
      xs.append(i == 1 ? "" : ",").append('x').append(i);
      ones.append(i == 1 ? "" : ",").append('1');
    }
    s.append("var 0..").append(N).append(": cost:: output_var:: is_defined_var;\n");
    for (int i = 1; i <= N; i++) {
      s.append("constraint bool_clause([x")
          .append(i)
          .append(",x")
          .append(i % N + 1)
          .append(",x")
          .append((i + 1) % N + 1)
          .append("],[]);\n");
    }
    s.append("constraint bool_lin_eq([").append(ones).append("],[").append(xs);
    s.append("],cost):: defines_var(cost);\nsolve minimize cost;\n");
    return s.toString();
  }

  @Test
  void optimumAfterGivingWayAtOnce() throws IOException {
    // without the MaxSAT local search, whose optimal first solution leaves LCG nothing to give way
    // on
    String out = run("lcg-slow-rate=1,lcg-slow-at=0,maxsat=0");
    // LCG gives way at its first test; only the core-guided probe's trimming of its first cores
    // can have made a few conflicts by then
    Matcher conflicts = Pattern.compile("lcgSlowConflicts=(\\d+)").matcher(out);
    assertTrue(conflicts.find(), out);
    assertTrue(Long.parseLong(conflicts.group(1)) < 10, out);
    checkOptimum(out);
  }

  // a Golomb ruler of 9 marks below 81, shortest 44: LCG finds solutions within a tenth of a
  // second, and proves the optimum alone in about 3 s, long after its speed check
  private static String golomb() {
    int n = 9;
    StringBuilder vars = new StringBuilder();
    StringBuilder cons = new StringBuilder();
    StringBuilder ds = new StringBuilder();
    for (int i = 1; i <= n; i++) {
      vars.append("var 0..80: m").append(i).append(":: output_var;\n");
    }
    cons.append("constraint int_eq(m1,0);\n");
    for (int i = 1; i < n; i++) {
      cons.append("constraint int_lt(m").append(i).append(",m").append(i + 1).append(");\n");
    }
    for (int i = 1; i <= n; i++) {
      for (int j = i + 1; j <= n; j++) {
        String d = "d" + i + "_" + j;
        vars.append("var 1..80: ").append(d).append(";\n");
        cons.append("constraint int_lin_eq([1,-1,-1],[m")
            .append(j)
            .append(",m")
            .append(i)
            .append(',')
            .append(d)
            .append("],0);\n");
        ds.append(ds.length() == 0 ? "" : ",").append(d);
      }
    }
    cons.append("constraint jacop_alldiff([").append(ds).append("]);\n");
    cons.append("constraint int_lt(d1_2,d").append(n - 1).append('_').append(n).append(");\n");
    return vars + cons.toString() + "solve minimize m" + n + ";\n";
  }

  @Test
  void optimumProvedAcrossOptimisationSlices() throws IOException {
    // LCG gives way with a solution at its speed check, free search without learning runs in
    // slices of a store level the solver lends, and LCG gets the search back under the best cost.
    // The core-guided phase is off: a core found since the last speed check keeps a slow LCG, and
    // whether one falls between two checks depends on the timing.
    String out =
        run(
            golomb(),
            "lcg-slow-rate=1000000000,lcg-slow-at=0.01,lcg-slow-stall=0,maxsat=0,lcg-core=0,"
                + "lcg-cop-slices=1");
    Matcher slices = Pattern.compile("lcgCopSlices=(\\d+)").matcher(out);
    assertTrue(slices.find(), out);
    assertTrue(Long.parseLong(slices.group(1)) >= 1, out);
    List<Integer> costs = new ArrayList<>();
    Matcher m = Pattern.compile("m9 = (\\d+);").matcher(out);
    while (m.find()) {
      costs.add(Integer.parseInt(m.group(1)));
    }
    assertTrue(costs.size() > 1, out);
    for (int k = 1; k < costs.size(); k++) {
      assertTrue(costs.get(k) < costs.get(k - 1), out);
    }
    assertEquals(44, costs.get(costs.size() - 1), out);
    assertTrue(out.contains("=========="), out);
  }

  @Test
  void solverThatGaveWayIsNotKept() {
    // free search keeps only the conflicts, deadline and clock of the LCG solver that gave way: the
    // solver, with its clauses and three literal maps per variable, held 2.35 million variables'
    // worth while the clauses were posted again (rcpsp-wet-diverse j90_48_4 -f out of 4 GB)
    // the running solver, and the early prober (dropped when search starts)
    Set<String> solvers = Set.of("lcg", "earlyProber");
    for (Field f : Solve.class.getDeclaredFields()) {
      if (LcgSolver.class.isAssignableFrom(f.getType())) {
        assertTrue(solvers.contains(f.getName()), f.toString());
      }
    }
    for (RecordComponent c : Solve.SlowLcg.class.getRecordComponents()) {
      assertTrue(c.getType().isPrimitive() || c.getType() == LongSupplier.class, c.toString());
    }
  }

  @Test
  void optimumAfterGivingWayToLocalSearchSolution() throws IOException {
    // local search prints a solution first, which LCG at its root, or free search without learning,
    // must improve on or prove optimal
    checkOptimum(run("lcg-slow-rate=1,lcg-slow-at=0,ls=0.5,ls-patience=0"));
  }

  private static final int REGULAR_N = 40;

  private static int weight(int i) {
    return 1 + i * 7 % 5;
  }

  // REGULAR_N variables 0..1 with no two consecutive zeros as a regular constraint, minimizing the
  // weighted ones. Under LCG the regular constraint becomes clauses and leaves the store, so free
  // search without learning must get it back, or it prints solutions with consecutive zeros.
  private static String noTwoZeros() {
    StringBuilder s = new StringBuilder();
    s.append("predicate jacop_regular(array[int] of var int: x, int: Q, int: S, ");
    s.append("array[int] of int: d, int: q0, set of int: F, int: min_index);\n");
    StringBuilder xs = new StringBuilder();
    StringBuilder weights = new StringBuilder();
    int total = 0;
    for (int i = 1; i <= REGULAR_N; i++) {
      s.append("var 0..1: x").append(i).append(":: output_var;\n");
      xs.append(i == 1 ? "" : ",").append('x').append(i);
      weights.append(i == 1 ? "" : ",").append(weight(i));
      total += weight(i);
    }
    s.append("var 0..").append(total).append(": cost:: output_var:: is_defined_var;\n");
    // state 1: the last value was 1 (or there is none yet), state 2: it was 0
    s.append("constraint jacop_regular([").append(xs).append("],2,2,[2,1,0,1],1,1..2,0);\n");
    s.append("constraint int_lin_eq([").append(weights).append(",-1],[").append(xs);
    s.append(",cost],0):: defines_var(cost);\nsolve minimize cost;\n");
    return s.toString();
  }

  // the optimum of noTwoZeros by dynamic programming over the last value
  private static int noTwoZerosOptimum() {
    int lastZero = 0;
    int lastOne = weight(1);
    for (int i = 2; i <= REGULAR_N; i++) {
      int zero = lastOne;
      int one = Math.min(lastZero, lastOne) + weight(i);
      lastZero = zero;
      lastOne = one;
    }
    return Math.min(lastZero, lastOne);
  }

  @Test
  void regularKeptAfterGivingWayAtOnce() throws IOException {
    String out = run(noTwoZeros(), "lcg-slow-rate=1,lcg-slow-at=0");
    assertTrue(out.contains("lcgSlowConflicts=0"), out);
    Pattern value = Pattern.compile("x(\\d+) = (\\d);");
    int cost = -1;
    for (String solution : out.split("----------")) {
      Matcher c = COST.matcher(solution);
      if (!c.find()) {
        continue;
      }
      int[] x = new int[REGULAR_N + 1];
      Matcher m = value.matcher(solution);
      while (m.find()) {
        x[Integer.parseInt(m.group(1))] = Integer.parseInt(m.group(2));
      }
      for (int i = 1; i < REGULAR_N; i++) {
        assertTrue(x[i] + x[i + 1] > 0, "x" + i + " and x" + (i + 1) + " are 0:\n" + out);
      }
      cost = Integer.parseInt(c.group(1));
    }
    assertEquals(noTwoZerosOptimum(), cost, out);
    assertTrue(out.contains("=========="), out);
  }

  @Test
  void slowLcgGoesOnWhileItMakesProgress() {
    long s = 1_000_000_000L;
    long none = Long.MIN_VALUE;
    int noCost = Integer.MAX_VALUE;
    // a bound raised inside the window keeps LCG, one raised before it does not
    assertTrue(Solve.stillProgressing(100 * s, 10 * s, 0.01, 95 * s, 500, 500));
    assertFalse(Solve.stillProgressing(100 * s, 10 * s, 0.01, 80 * s, 500, 500));
    // the best cost fell by 1 % of itself over the window (ma-path-finding), or by less
    // (unit-commitment improves by under 0.5 % in 30 s and gives way)
    assertTrue(Solve.stillProgressing(100 * s, 10 * s, 0.01, none, 500, 495));
    assertFalse(Solve.stillProgressing(100 * s, 10 * s, 0.01, none, 4_683_690, 4_661_990));
    // a maximised cost is negated: -500 to -505 is a gain of 1 %
    assertTrue(Solve.stillProgressing(100 * s, 10 * s, 0.01, none, -500, -505));
    // the first solution inside the window counts as progress, none at all does not
    assertTrue(Solve.stillProgressing(100 * s, 10 * s, 0.01, none, noCost, 700));
    assertFalse(Solve.stillProgressing(100 * s, 10 * s, 0.01, none, noCost, noCost));
  }

  @Test
  void theWindowSeesSolutionsFoundBeforeTheFirstCheck() {
    long s = 1_000_000_000L;
    int noCost = Integer.MAX_VALUE;
    // the checks sample the best cost from the first one on: a cost improved from 4,100 to 3,900
    // at 20 s, and the check at 24 s, whose only sample was 3,900, saw no gain over its 12 s
    // window (celar graph11, MiniZinc Challenge 2013, gave way and ended at 13,387, not 3,080)
    List<long[]> improvements = List.of(new long[] {5 * s, noCost}, new long[] {20 * s, 4_100});
    long before = Solve.costAt(improvements, 12 * s, 3_900);
    assertEquals(4_100, before);
    assertTrue(Solve.stillProgressing(24 * s, 12 * s, 0.005, Long.MIN_VALUE, before, 3_900));
    assertFalse(Solve.stillProgressing(24 * s, 12 * s, 0.005, Long.MIN_VALUE, 3_900, 3_900));
    // the first solution inside the window
    assertEquals(noCost, Solve.costAt(improvements, 4 * s, 3_900));
    // nothing improved since the start of the window: the sampled cost
    assertEquals(3_900, Solve.costAt(improvements, 21 * s, 3_900));
    // a sample taken after the improvement inside the window was already the higher cost
    assertEquals(4_500, Solve.costAt(improvements, 12 * s, 4_500));
  }

  @Test
  void aBoundRaiseCountsOnlyWhenItClosesAShareOfTheGap() {
    // CVRPLIB X-n110-k13: the bound rose from 4 to 5 against a best cost of 59,211
    assertFalse(Solve.boundClosesGap(4, 5, 0.005, 59_211));
    assertTrue(Solve.boundClosesGap(4, 400, 0.005, 59_211));
    assertFalse(Solve.boundClosesGap(5, 5, 0.005, 59_211));
    // without a solution any raise counts
    assertTrue(Solve.boundClosesGap(4, 5, 0.005, Integer.MAX_VALUE));
  }

  @Test
  void slowRateGrowsWithLearntClauseLength() {
    // short learnt clauses keep lcg-slow-rate; ttppv circ20 learns about 400 literals a conflict,
    // so 530 conflicts/s counts as slow at 5 conflicts/s per literal (2000)
    assertEquals(300, Solve.slowRate(1000, 20_000, 300, 5), 1e-9);
    assertEquals(2000, Solve.slowRate(1000, 400_000, 300, 5), 1e-9);
    // off, and no conflicts yet
    assertEquals(300, Solve.slowRate(1000, 400_000, 300, 0), 1e-9);
    assertEquals(300, Solve.slowRate(0, 0, 300, 5), 1e-9);
  }

  @Test
  void slowLcgKeptWhenTheWindowCoversTheRun() throws IOException {
    // every check finds LCG slow (rate far above any solver), but the window is the whole time
    // limit and the first solution counts as progress until it is that old: LCG never gives way
    String out = run("lcg-slow-rate=1000000000,lcg-slow-at=0.01,lcg-slow-stall=1,lcg-slow-gain=0");
    assertTrue(!out.contains("lcgSlowConflicts="), out);
    checkOptimum(out);
  }

  @Test
  void optimumWhenLcgIsFastEnough() throws IOException {
    String out = run("lcg-slow-rate=0.001,lcg-slow-at=0.5");
    assertTrue(!out.contains("lcgSlowConflicts="), out);
    checkOptimum(out);
  }

  @Test
  void satisfactionProbeTellsWeakLearning() {
    // costas-array 17: conflicts at depth 22 jump back 1.17 levels, LBD 11
    assertTrue(Solve.learningCutsLittle(430_606, 21.8, 1.169, 10.7, 1.3, 0.35));
    // Dominoes-table-45-286 (XCSP 2026): 1.38 levels is too long a jump, learning finds it in 60 s
    assertFalse(Solve.learningCutsLittle(1_844, 18.7, 1.377, 14.2, 1.3, 0.35));
    // nmseq 395: conflicts at depth 1
    assertTrue(Solve.learningCutsLittle(316, 1.0, 0.997, 1.0, 1.3, 0.35));
    // whirlpool d29 and PegSolitaire: long jumps, short clauses
    assertFalse(Solve.learningCutsLittle(7_288, 792.2, 19.8, 63.1, 1.3, 0.35));
    assertFalse(Solve.learningCutsLittle(42_078, 262.0, 12.3, 23.8, 1.3, 0.35));
    // short jumps but clauses far shorter than the depth: learning generalises
    assertFalse(Solve.learningCutsLittle(31_000, 90.8, 1.2, 23.5, 1.3, 0.35));
    // no conflict yet: nothing to tell
    assertFalse(Solve.learningCutsLittle(0, 0, 0, 0, 1.3, 0.35));
  }

  @Test
  void satisfactionSolvedAfterGivingWay() throws IOException {
    // lazy clause generation is under test: the model is not compiled to clauses
    ClausalOff.run(this::satisfactionSolvedAfterGivingWayBody);
  }

  private void satisfactionSolvedAfterGivingWayBody() throws IOException {
    // 40 queens (8 are solved before LCG starts); lcg-sat-at=0 gives way after LCG's root
    // propagation, and search without learning
    // must print a solution of the model
    int n = 40;
    StringBuilder s = new StringBuilder();
    for (int i = 1; i <= n; i++) {
      s.append("var 1..").append(n).append(": q").append(i).append(":: output_var;\n");
    }
    for (int i = 1; i <= n; i++) {
      for (int j = i + 1; j <= n; j++) {
        s.append("constraint int_ne(q").append(i).append(", q").append(j).append(");\n");
        // q_i - q_j != j - i and q_i - q_j != i - j
        for (int d : new int[] {j - i, i - j}) {
          s.append("constraint int_lin_ne([1, -1], [q")
              .append(i)
              .append(", q")
              .append(j)
              .append("], ")
              .append(d)
              .append(");\n");
        }
      }
    }
    s.append("solve satisfy;\n");
    String out = runSatisfaction(s.toString(), "lcg-sat-at=0");
    assertTrue(out.contains("lcgSlowUnsolved=true"), out);
    int[] q = new int[n + 1];
    for (int i = 1; i <= n; i++) {
      Matcher m = Pattern.compile("q" + i + " = (\\d+);").matcher(out);
      assertTrue(m.find(), out);
      q[i] = Integer.parseInt(m.group(1));
    }
    for (int i = 1; i <= n; i++) {
      for (int j = i + 1; j <= n; j++) {
        assertTrue(q[i] != q[j] && Math.abs(q[i] - q[j]) != j - i, out);
      }
    }
  }

  @Test
  void satisfactionSolvedInASliceWithoutLearning() throws IOException {
    // 40 queens with a clause that only the SAT solver holds under LCG: exactly one of q1 and q2 is
    // at most 20. The probe fires at its first conflicts (any jump counts as weak) and search
    // without learning gets a thousand times LCG's time, so it finds the solution in its slice,
    // where the clauses must be posted in the store
    int n = 40;
    StringBuilder s = new StringBuilder();
    for (int i = 1; i <= n; i++) {
      s.append("var 1..").append(n).append(": q").append(i).append(":: output_var;\n");
    }
    s.append("var bool: b1;\nvar bool: b2;\n");
    for (int i = 1; i <= n; i++) {
      for (int j = i + 1; j <= n; j++) {
        s.append("constraint int_ne(q").append(i).append(", q").append(j).append(");\n");
        for (int d : new int[] {j - i, i - j}) {
          s.append("constraint int_lin_ne([1, -1], [q")
              .append(i)
              .append(", q")
              .append(j)
              .append("], ")
              .append(d)
              .append(");\n");
        }
      }
    }
    s.append("constraint int_le_reif(q1, 20, b1);\n");
    s.append("constraint int_le_reif(q2, 20, b2);\n");
    s.append("constraint bool_clause([b1, b2], []);\n");
    s.append("constraint bool_clause([], [b1, b2]);\n");
    s.append("solve satisfy;\n");
    String out =
        runSatisfaction(
            s.toString(),
            "lcg-sat-at=0.0001,lcg-sat-jump=1000,lcg-sat-lbd=0,lcg-sat-cp-share=1000");
    // LCG may find the solution before its first conflict, when the probe cannot fire yet
    assertFalse(out.contains("lcgSlowUnsolved"), out);
    int[] q = new int[n + 1];
    for (int i = 1; i <= n; i++) {
      Matcher m = Pattern.compile("q" + i + " = (\\d+);").matcher(out);
      assertTrue(m.find(), out);
      q[i] = Integer.parseInt(m.group(1));
    }
    for (int i = 1; i <= n; i++) {
      for (int j = i + 1; j <= n; j++) {
        assertTrue(q[i] != q[j] && Math.abs(q[i] - q[j]) != j - i, out);
      }
    }
    assertTrue(q[1] <= 20 != q[2] <= 20, out);
  }

  @Test
  void satisfactionProvedUnsatisfiableAcrossSlices() throws IOException {
    // lazy clause generation is under test: the model is not compiled to clauses
    ClausalOff.run(this::satisfactionProvedUnsatisfiableAcrossSlicesBody);
  }

  private void satisfactionProvedUnsatisfiableAcrossSlicesBody() throws IOException {
    // 9 pigeons in 8 holes, each difference a variable without 0, which presolve does not read as
    // an all-different: the proof needs search. Slices of 1 ms of search without learning
    // alternate with LCG from the first probe, and the answer must be unsatisfiable whichever of
    // them finishes
    int n = 9;
    StringBuilder decl = new StringBuilder();
    StringBuilder cons = new StringBuilder();
    StringBuilder nonZero = new StringBuilder();
    for (int v = 2 - n; v <= n - 2; v++) {
      if (v != 0) {
        nonZero.append(nonZero.isEmpty() ? "" : ",").append(v);
      }
    }
    for (int i = 1; i <= n; i++) {
      decl.append("var 1..").append(n - 1).append(": p").append(i).append(":: output_var;\n");
    }
    for (int i = 1; i <= n; i++) {
      for (int j = i + 1; j <= n; j++) {
        String d = "d" + i + "_" + j;
        decl.append("var {").append(nonZero).append("}: ").append(d).append(";\n");
        cons.append("constraint int_lin_eq([1,-1,-1],[p").append(i).append(",p").append(j);
        cons.append(",").append(d).append("],0);\n");
      }
    }
    String out =
        runSatisfaction(
            decl.toString() + cons + "solve satisfy;\n",
            "lcg-sat-at=0.0001,lcg-sat-jump=1000,lcg-sat-lbd=0,lcg-sat-cp-share=0.0001");
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
    assertFalse(out.contains("----------"), out);
    assertTrue(out.contains("lcgSatSlices="), out);
  }

  // n queens, the columns searched in input order, smallest row first
  private static String queensInputOrder(int n) {
    StringBuilder s = new StringBuilder();
    StringBuilder qs = new StringBuilder();
    for (int i = 1; i <= n; i++) {
      s.append("var 1..").append(n).append(": q").append(i).append(":: output_var;\n");
      qs.append(i == 1 ? "" : ",").append('q').append(i);
    }
    for (int i = 1; i <= n; i++) {
      for (int j = i + 1; j <= n; j++) {
        s.append("constraint int_ne(q").append(i).append(", q").append(j).append(");\n");
        for (int d : new int[] {j - i, i - j}) {
          s.append("constraint int_lin_ne([1, -1], [q")
              .append(i)
              .append(", q")
              .append(j)
              .append("], ")
              .append(d)
              .append(");\n");
        }
      }
    }
    s.append("solve :: int_search([").append(qs).append("], input_order, indomain_min, complete)");
    s.append(" satisfy;\n");
    return s.toString();
  }

  // 10 pigeons in 9 holes as in satisfactionProvedUnsatisfiableAcrossSlices, searched in input
  // order
  private static String pigeonsInputOrder() {
    int n = 10;
    StringBuilder decl = new StringBuilder();
    StringBuilder cons = new StringBuilder();
    StringBuilder nonZero = new StringBuilder();
    StringBuilder ps = new StringBuilder();
    for (int v = 2 - n; v <= n - 2; v++) {
      if (v != 0) {
        nonZero.append(nonZero.isEmpty() ? "" : ",").append(v);
      }
    }
    for (int i = 1; i <= n; i++) {
      decl.append("var 1..").append(n - 1).append(": p").append(i).append(":: output_var;\n");
      ps.append(i == 1 ? "" : ",").append('p').append(i);
    }
    for (int i = 1; i <= n; i++) {
      for (int j = i + 1; j <= n; j++) {
        String d = "d" + i + "_" + j;
        decl.append("var {").append(nonZero).append("}: ").append(d).append(";\n");
        cons.append("constraint int_lin_eq([1,-1,-1],[p").append(i).append(",p").append(j);
        cons.append(",").append(d).append("],0);\n");
      }
    }
    return decl.toString()
        + cons
        + "solve :: int_search(["
        + ps
        + "], input_order, indomain_min, complete) satisfy;\n";
  }

  private static void checkQueens(String out, int n) {
    int[] q = new int[n + 1];
    for (int i = 1; i <= n; i++) {
      Matcher m = Pattern.compile("q" + i + " = (\\d+);").matcher(out);
      assertTrue(m.find(), out);
      q[i] = Integer.parseInt(m.group(1));
    }
    for (int i = 1; i <= n; i++) {
      for (int j = i + 1; j <= n; j++) {
        assertTrue(q[i] != q[j] && Math.abs(q[i] - q[j]) != j - i, out);
      }
    }
  }

  @Test
  void fixedSatisfactionKeepsTheSearchWithoutLearning() throws IOException {
    // fixed search: the taste at its first decisions, kept whatever the positions (ratio -1), must
    // print a solution of the model from the search without learning, which runs on to the end
    String out = runFixed(queensInputOrder(20), "lcg-fixed-at=0.0001,lcg-fixed-ratio=-1");
    checkQueens(out, 20);
    assertTrue(out.contains("lcgFixedTaste=cp"), out);
  }

  @Test
  void fixedSatisfactionProvedUnsatisfiableWithoutLearning() throws IOException {
    // the search without learning kept explores the whole tree: unsatisfiable
    String out = runFixed(pigeonsInputOrder(), "lcg-fixed-at=0.0001,lcg-fixed-ratio=-1");
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
    assertFalse(out.contains("----------"), out);
    assertTrue(out.contains("lcgFixedTaste=cp"), out);
  }

  @Test
  void fixedSatisfactionGoesOnWithLcgAfterTheTaste() throws IOException {
    // never kept: the search without learning stops after the taste and LCG, given back its
    // solver, proves the model unsatisfiable
    String out = runFixed(pigeonsInputOrder(), "lcg-fixed-at=0.0001,lcg-fixed-ratio=1e300");
    assertTrue(out.contains("=====UNSATISFIABLE====="), out);
    assertFalse(out.contains("----------"), out);
    assertTrue(out.contains("lcgFixedTaste=lcg"), out);
  }

  private String runFixed(String model, String config) throws IOException {
    Path fzn = tmp.resolve("fixed.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    String[] args = {
      "--lcg",
      "-s",
      "--search-statistics",
      "--lp",
      "off",
      "-t",
      "30000",
      "--free-config",
      config,
      fzn.toString()
    };
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return out.toString(StandardCharsets.UTF_8);
  }

  private String runSatisfaction(String model, String config) throws IOException {
    Path fzn = tmp.resolve("sat.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    String[] args = {
      "--lcg",
      "-f",
      "-s",
      "-v",
      "--lp",
      "off",
      "-t",
      "30000",
      "--free-config",
      config,
      fzn.toString()
    };
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return out.toString(StandardCharsets.UTF_8);
  }

  private static void checkOptimum(String out) {
    List<Integer> costs = new ArrayList<>();
    Matcher m = COST.matcher(out);
    while (m.find()) {
      costs.add(Integer.parseInt(m.group(1)));
    }
    assertTrue(!costs.isEmpty(), out);
    for (int k = 1; k < costs.size(); k++) {
      assertTrue(costs.get(k) < costs.get(k - 1), out);
    }
    assertEquals(N / 3, costs.get(costs.size() - 1), out);
    assertTrue(out.contains("=========="), out);
  }

  private String run(String config) throws IOException {
    return run(cover(), config);
  }

  private String run(String model, String config) throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    String[] args = {
      // without the linear relaxation, whose rows of the clauses would enforce them
      "--lcg",
      "-f",
      "-a",
      "-s",
      "-v",
      "--lp",
      "off",
      "-t",
      "10000",
      "--free-config",
      config,
      fzn.toString()
    };
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return out.toString(StandardCharsets.UTF_8);
  }
}
