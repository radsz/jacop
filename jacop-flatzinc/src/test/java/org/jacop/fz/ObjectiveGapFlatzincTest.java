/*
 * ObjectiveGapFlatzincTest.java
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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
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
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

/**
 * --gap stops an optimisation once the best solution is within the given percentage of the proved
 * bound, and -s prints each better bound as the statistic objectiveBound.
 */
@Timeout(120)
class ObjectiveGapFlatzincTest {

  // the root's bound is 100; the annotation finds 110, 109, ..., 100 in that order
  private static final String MINIMISE =
      """
      var 0..10: x :: output_var;
      var 90..200: obj :: output_var;
      constraint int_lin_eq([1,-1],[obj,x],100);
      solve :: int_search([x], input_order, indomain_max, complete) minimize obj;
      """;

  // the root's bound is 100; the annotation finds 90, 91, ..., 100 in that order
  private static final String MAXIMISE =
      """
      var 0..10: x :: output_var;
      var 0..200: obj :: output_var;
      constraint int_lin_eq([1,1],[obj,x],100);
      solve :: int_search([x], input_order, indomain_max, complete) maximize obj;
      """;

  // ten disjoint pairs of which one each must be true: optimum 10, which cores prove
  private static final String PAIRS;

  static {
    StringBuilder s = new StringBuilder();
    s.append("array [1..20] of var bool: b :: output_array([1..20]);\n");
    s.append("array [1..20] of var 0..1: x;\n");
    s.append("var 0..20: obj :: output_var;\n");
    for (int i = 1; i <= 20; i++) {
      s.append("constraint bool2int(b[").append(i).append("],x[").append(i).append("]);\n");
    }
    for (int i = 1; i <= 20; i += 2) {
      s.append("constraint bool_clause([b[").append(i).append("],b[").append(i + 1);
      s.append("]],[]);\n");
    }
    s.append("constraint int_lin_eq([");
    for (int i = 1; i <= 20; i++) {
      s.append("1,");
    }
    s.append("-1],[");
    for (int i = 1; i <= 20; i++) {
      s.append("x[").append(i).append("],");
    }
    s.append("obj],0);\nsolve minimize obj;\n");
    PAIRS = s.toString();
  }

  // four different values up to obj: optimum 3, which the root does not see; the annotation
  // refutes obj = 0, 1 and 2 in turn
  private static final String RISING =
      """
      var 0..10: obj :: output_var;
      array [1..4] of var 0..10: y :: output_array([1..4]);
      constraint int_ne(y[1],y[2]);
      constraint int_ne(y[1],y[3]);
      constraint int_ne(y[1],y[4]);
      constraint int_ne(y[2],y[3]);
      constraint int_ne(y[2],y[4]);
      constraint int_ne(y[3],y[4]);
      constraint int_le(y[1],obj);
      constraint int_le(y[2],obj);
      constraint int_le(y[3],obj);
      constraint int_le(y[4],obj);
      solve :: int_search([obj,y[1],y[2],y[3],y[4]], input_order, indomain_min, complete)
        minimize obj;
      """;

  private static final Pattern OBJECTIVE = Pattern.compile("(?m)^obj = (-?\\d+);");
  private static final Pattern BOUND = Pattern.compile("%%%mzn-stat: objectiveBound=(-?\\d+)");

  @TempDir Path tmp;

  @Test
  void minimisationStopsWithinTheGap() throws IOException {
    for (String engine : new String[] {"--lcg=off", "--lcg=on"}) {
      // 110 is 9.1 % above the bound 100
      String out = solve(MINIMISE, engine, "--gap", "10");
      assertEquals(110, lastObjective(out), out);
      assertFalse(out.contains("=========="), out);
      // 105 is the first within 5 %: 5/105 = 4.8 %, 6/106 = 5.7 %
      out = solve(MINIMISE, engine, "--gap=5");
      assertEquals(105, lastObjective(out), out);
      assertFalse(out.contains("=========="), out);
      // without --gap the search proves 100
      out = solve(MINIMISE, engine);
      assertEquals(100, lastObjective(out), out);
      assertTrue(out.contains("=========="), out);
    }
  }

  @Test
  void gapIsRelativeToTheBestSolution() throws IOException {
    for (String engine : new String[] {"--lcg=off", "--lcg=on"}) {
      // 90 is 10 below the bound 100: 10/90 = 11.1 %; 91: 9/91 = 9.9 %
      String out = solve(MAXIMISE, engine, "--gap", "10");
      assertEquals(91, lastObjective(out), out);
      assertFalse(out.contains("=========="), out);
    }
  }

  @Test
  void aBoundAtTheBestSolutionIsAProof() throws IOException {
    for (String engine : new String[] {"--lcg=off", "--lcg=on"}) {
      String out = solve(MINIMISE, engine, "--gap", "0");
      assertEquals(100, lastObjective(out), out);
      assertTrue(out.contains("=========="), out);
    }
  }

  @Test
  void allSolutionsAreKeptUntilTheGap() throws IOException {
    String out = solve(MINIMISE, "--lcg=off", "-a", "--gap", "7");
    assertEquals(List.of(110L, 109L, 108L, 107L), all(OBJECTIVE, out), out);
    assertFalse(out.contains("=========="), out);
  }

  @Test
  void boundIsPrintedWithStatisticsInTheModelsObjective() throws IOException {
    String out = solve(MINIMISE, "--lcg=off", "-s");
    assertEquals(List.of(100L), all(BOUND, out), out);
    out = solve(MAXIMISE, "--lcg=off", "-s");
    assertEquals(List.of(100L), all(BOUND, out), out);
    out = solve(MINIMISE, "--lcg=off");
    assertTrue(all(BOUND, out).isEmpty(), out);
  }

  @Test
  void boundsRiseDuringTheSearchWithoutRestarts() throws IOException {
    // depth-first search: each refuted obj = v leaves the subtree obj > v, whose minimum is a bound
    String out = solve(RISING, "--lcg=off", "-s");
    assertEquals(3, lastObjective(out), out);
    assertEquals(List.of(0L, 1L, 2L, 3L), all(BOUND, out), out);
    // LCG under the annotation, without restarts: the backjumps to the root raise the bound
    out = solve(RISING, "--lcg=on", "-s");
    assertEquals(3, lastObjective(out), out);
    List<Long> bounds = all(BOUND, out);
    for (int k = 0; k < bounds.size(); k++) {
      assertTrue(bounds.get(k) <= 3, out);
      assertTrue(k == 0 || bounds.get(k) > bounds.get(k - 1), out);
    }
    assertEquals(3L, bounds.get(bounds.size() - 1), out);
    assertTrue(bounds.size() > 2, out);
    // the bound comes with the time it was proved
    assertTrue(out.contains("%%%mzn-stat: objectiveBoundTime="), out);
    // free search without LCG: refuted probes and nogoods raise the root's bound between runs
    for (String seed : new String[] {"1", "2", "3"}) {
      out = solve(RISING, "--lcg=off", "-f", "-s", "-r", seed);
      assertEquals(3, lastObjective(out), out);
      bounds = all(BOUND, out);
      for (int k = 0; k < bounds.size(); k++) {
        assertTrue(bounds.get(k) <= 3, out);
        assertTrue(k == 0 || bounds.get(k) > bounds.get(k - 1), out);
      }
      assertEquals(3L, bounds.get(bounds.size() - 1), out);
    }
  }

  @Test
  void anOptimalEndPrintsTheOptimumAsTheBound() throws IOException {
    // maximise 100 + x: the root's bound 110 is reached only by the last solution
    String model =
        """
        var 0..10: x :: output_var;
        var 0..200: obj :: output_var;
        constraint int_lin_eq([1,-1],[obj,x],100);
        constraint int_ne(x,10);
        solve :: int_search([x], input_order, indomain_min, complete) maximize obj;
        """;
    for (String engine : new String[] {"--lcg=off", "--lcg=on"}) {
      String out = solve(model, engine, "-s");
      assertEquals(109, lastObjective(out), out);
      assertTrue(out.contains("=========="), out);
      List<Long> bounds = all(BOUND, out);
      assertEquals(109L, bounds.get(bounds.size() - 1), out);
    }
  }

  @Test
  void learntBoundsHoldAndRise() throws IOException {
    for (String seed : new String[] {"1", "2", "3"}) {
      String out = solve(PAIRS, "-f", "-s", "-r", seed);
      assertEquals(10, lastObjective(out), out);
      assertTrue(out.contains("=========="), out);
      List<Long> bounds = all(BOUND, out);
      for (int k = 0; k < bounds.size(); k++) {
        assertTrue(bounds.get(k) <= 10, out);
        assertTrue(k == 0 || bounds.get(k) > bounds.get(k - 1), out);
      }
      // the last bound printed and the answer satisfy the gap
      out = solve(PAIRS, "-f", "-s", "-r", seed, "--gap", "40");
      assertGapHolds(out, 0.4, false);
    }
  }

  @Test
  void portfolioStopsWithinTheGap() throws IOException {
    assertGapHolds(solve(MINIMISE, "-p", "3", "-s", "--gap", "10"), 0.1, false);
    assertGapHolds(solve(MAXIMISE, "-p", "3", "-s", "--gap", "10"), 0.1, true);
    assertGapHolds(solve(PAIRS, "-p", "3", "-s", "--gap", "10"), 0.1, false);
  }

  @Test
  void wrongGapIsRejected() {
    for (String bad : new String[] {"-1", "abc", "NaN", "Infinity"}) {
      assertThrows(
          IllegalArgumentException.class, () -> new Options(new String[] {"--gap", bad, "m.fzn"}));
    }
    assertEquals(0.125, new Options(new String[] {"--gap", "12.5", "m.fzn"}).gap());
    assertTrue(new Options(new String[] {"m.fzn"}).gap() < 0);
  }

  @Test
  void gapArithmetic() {
    List<String> printed = new ArrayList<>();
    ObjectiveGap gap = new ObjectiveGap(0.1, false, printed::add);
    assertNull(gap.objectiveBound());
    assertFalse(gap.solution(200));
    assertFalse(gap.bound(150));
    assertFalse(gap.bound(120)); // a weaker bound is not printed
    assertEquals(1, printed.size());
    assertTrue(printed.get(0).startsWith("%%%mzn-stat: objectiveBound=150\n"), printed.toString());
    assertTrue(gap.solution(165)); // 15/165 = 9.1 %
    assertFalse(gap.proved());
    assertTrue(gap.reached());

    // maximisation: cost -91 against bound -100, 9 <= 9.1
    printed.clear();
    ObjectiveGap max = new ObjectiveGap(0.1, true, printed::add);
    assertFalse(max.bound(-100));
    assertEquals(100L, max.objectiveBound());
    assertTrue(
        printed
            .get(0)
            .matches(
                "%%%mzn-stat: objectiveBound=100\n%%%mzn-stat: objectiveBoundTime=[0-9.]+\n%%%mzn-stat-end"),
        printed.get(0));
    assertFalse(max.solution(-90));
    assertTrue(max.solution(-91));

    // exactly at the gap stops; no gap never stops, but still prints
    assertTrue(gapAt(0.25, 75, 100));
    assertFalse(gapAt(0.25, 74, 100));
    ObjectiveGap none = new ObjectiveGap(-1, false, printed::add);
    none.solution(5);
    assertFalse(none.bound(5));
    assertTrue(none.proved());

    // a zero best needs a bound of zero
    assertFalse(gapAt(0.5, -1, 0));
    assertTrue(gapAt(0, 0, 0));
  }

  private static boolean gapAt(double gap, long bound, long best) {
    ObjectiveGap g = new ObjectiveGap(gap, false, null);
    g.bound(bound);
    return g.solution(best);
  }

  private static void assertGapHolds(String out, double gap, boolean maximise) {
    long obj = lastObjective(out);
    if (!out.contains("==========")) {
      List<Long> bounds = all(BOUND, out);
      assertFalse(bounds.isEmpty(), out);
      // the bound is the model's own: below the objective for minimisation, above for maximisation
      long b =
          maximise
              ? bounds.stream().min(Long::compare).orElseThrow()
              : bounds.stream().max(Long::compare).orElseThrow();
      assertTrue(Math.abs(obj - b) <= gap * Math.abs(obj), obj + " vs " + b + "\n" + out);
    }
  }

  private static long lastObjective(String out) {
    List<Long> all = all(OBJECTIVE, out);
    assertFalse(all.isEmpty(), out);
    return all.getLast();
  }

  private static List<Long> all(Pattern p, String out) {
    List<Long> values = new ArrayList<>();
    Matcher m = p.matcher(out);
    while (m.find()) {
      values.add(Long.parseLong(m.group(1)));
    }
    return values;
  }

  private String solve(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }
}
