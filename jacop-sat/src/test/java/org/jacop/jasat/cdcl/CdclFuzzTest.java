/*
 * CdclFuzzTest.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.cdcl;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * In-process fuzzing of {@link CdclSolver}, run on demand (no Maven profile includes it). Every
 * answer is checked without a reference solver: a SAT answer by its model, an UNSAT answer by
 * checking its DRAT proof with {@link RupChecker}, and an UNSAT answer under assumptions by solving
 * the formula with the failed assumptions as units and checking that proof.
 *
 * <pre>
 * mvn -Pmin -pl jacop-sat test -Dtest=CdclFuzzTest -Dfuzz.runs=1000000 -Dfuzz.seed=1
 * </pre>
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class CdclFuzzTest {

  /** A failure with what is needed to reproduce it. */
  private static void check(boolean condition, long seed, String what, List<int[]> formula) {
    if (!condition) {
      StringBuilder cnf = new StringBuilder("p cnf ? " + formula.size() + "\n");
      for (int[] c : formula) {
        for (int l : c) {
          cnf.append(l).append(' ');
        }
        cnf.append("0\n");
      }
      fail("seed " + seed + ": " + what + "\n" + (formula.size() <= 200 ? cnf : ""));
    }
  }

  /** Random formulas of several shapes; mostly near the satisfiability threshold. */
  static List<int[]> randomFormula(Random rnd, int[] varsOut) {
    int shape = rnd.nextInt(4);
    int vars;
    int clauses;
    int minLen;
    int maxLen;
    switch (shape) {
      case 0 -> { // small, mixed lengths, with units and duplicates
        vars = 1 + rnd.nextInt(15);
        clauses = 1 + rnd.nextInt(6 * vars);
        minLen = 1;
        maxLen = 4;
      }
      case 1 -> { // random 3-SAT near the threshold
        vars = 20 + rnd.nextInt(130);
        clauses = (int) (vars * (3.9 + 0.7 * rnd.nextDouble()));
        minLen = 3;
        maxLen = 3;
      }
      case 2 -> { // mixed 2..5, many binaries
        vars = 10 + rnd.nextInt(80);
        clauses = (int) (vars * (2.0 + 4.0 * rnd.nextDouble()));
        minLen = 2;
        maxLen = 5;
      }
      default -> { // layered (cnfuzz-like): clauses over a sliding window of variables
        vars = 30 + rnd.nextInt(150);
        clauses = 0;
        minLen = 2;
        maxLen = 4;
      }
    }
    List<int[]> f = new ArrayList<>();
    if (shape == 3) {
      int width = 8 + rnd.nextInt(20);
      double ratio = 3.5 + rnd.nextDouble();
      for (int low = 1; low + width - 1 <= vars; low += 1 + rnd.nextInt(width / 2)) {
        for (int k = 0; k < (int) (width * ratio / 2); k++) {
          int[] c = new int[2 + rnd.nextInt(3)];
          for (int i = 0; i < c.length; i++) {
            int v = low + rnd.nextInt(width);
            c[i] = rnd.nextBoolean() ? v : -v;
          }
          f.add(c);
        }
      }
    } else {
      for (int k = 0; k < clauses; k++) {
        int[] c = new int[minLen + rnd.nextInt(maxLen - minLen + 1)];
        for (int i = 0; i < c.length; i++) {
          int v = 1 + rnd.nextInt(vars);
          c[i] = rnd.nextBoolean() ? v : -v;
        }
        f.add(c);
      }
    }
    varsOut[0] = vars;
    return f;
  }

  private static boolean satisfiedBy(List<int[]> f, CdclSolver s) {
    for (int[] c : f) {
      boolean sat = false;
      for (int l : c) {
        sat |= s.modelValue(Math.abs(l)) == l > 0;
      }
      if (!sat) {
        return false;
      }
    }
    return true;
  }

  /** Chronological backtracking always, by default, or never, so small formulas exercise it. */
  private static int chronoLimit(long seed) {
    long mode = Math.floorMod(seed, 3L);
    return mode == 0 ? 0 : mode == 1 ? 100 : -1;
  }

  /** Solves with a DRAT proof and checks the answer; returns the answer. */
  private static int solveChecked(List<int[]> f, int vars, long seed) throws IOException {
    CdclSolver s = new CdclSolver();
    ByteArrayOutputStream proof = new ByteArrayOutputStream();
    DratWriter drat = new DratWriter(proof);
    s.setProof(drat);
    s.setChronoLimit(chronoLimit(seed));
    s.ensureVars(vars);
    for (int[] c : f) {
      s.addClause(c);
    }
    int result = s.solve();
    drat.close();
    if (result == CdclSolver.SAT) {
      check(satisfiedBy(f, s), seed, "model does not satisfy the formula", f);
    } else {
      check(result == CdclSolver.UNSAT, seed, "answer " + result, f);
      String error = RupChecker.check(vars, f, proof.toString(StandardCharsets.US_ASCII));
      check(error == null, seed, "proof rejected: " + error, f);
    }
    return result;
  }

  /** Incremental use: clauses added in batches, solved under random assumptions in between. */
  private static void incremental(Random rnd, List<int[]> f, int vars, long seed)
      throws IOException {
    CdclSolver s = new CdclSolver();
    s.setChronoLimit(chronoLimit(seed));
    s.ensureVars(vars);
    List<int[]> added = new ArrayList<>();
    int next = 0;
    while (next < f.size()) {
      int batch = 1 + rnd.nextInt(Math.max(1, f.size() / 3));
      for (int k = 0; k < batch && next < f.size(); k++, next++) {
        s.addClause(f.get(next));
        added.add(f.get(next));
      }
      int[] assumed = new int[rnd.nextInt(4)];
      for (int i = 0; i < assumed.length; i++) {
        int v = 1 + rnd.nextInt(vars);
        assumed[i] = rnd.nextBoolean() ? v : -v;
      }
      int result = s.solve(assumed);
      if (result == CdclSolver.SAT) {
        check(satisfiedBy(added, s), seed, "incremental model does not satisfy the formula", added);
        for (int a : assumed) {
          check(s.modelValue(Math.abs(a)) == a > 0, seed, "model violates assumption " + a, added);
        }
      } else {
        check(result == CdclSolver.UNSAT, seed, "incremental answer " + result, added);
        int[] core = s.failedAssumptions();
        List<int[]> withCore = new ArrayList<>(added);
        for (int a : core) {
          check(Arrays.stream(assumed).anyMatch(x -> x == a), seed, "core is not a subset", added);
          withCore.add(new int[] {a});
        }
        check(
            solveChecked(withCore, vars, seed) == CdclSolver.UNSAT,
            seed,
            "formula with the failed assumptions " + Arrays.toString(core) + " is satisfiable",
            added);
        if (core.length == 0) {
          return; // unsatisfiable without assumptions
        }
      }
    }
  }

  @Test
  void fuzz() throws IOException {
    long runs = Long.getLong("fuzz.runs", 2000);
    long base = Long.getLong("fuzz.seed", 1);
    long unsat = 0;
    for (long run = 0; run < runs; run++) {
      long seed = base * 1_000_003L + run;
      Random rnd = new Random(seed);
      int[] vars = new int[1];
      List<int[]> f = randomFormula(rnd, vars);
      if (solveChecked(f, vars[0], seed) == CdclSolver.UNSAT) {
        unsat++;
      }
      if (rnd.nextInt(4) == 0) {
        incremental(rnd, f, vars[0], seed);
      }
      if ((run + 1) % 100_000 == 0) {
        System.out.println("fuzz: " + (run + 1) + " runs, " + unsat + " UNSAT");
      }
    }
    System.out.println("fuzz: " + runs + " runs, " + unsat + " UNSAT, all answers checked");
    assertTrue(runs == 0 || unsat > 0, "no UNSAT instance was generated");
  }

  @Test
  void rupCheckerRejectsWrongProofs() {
    List<int[]> f =
        List.of(new int[] {1, 2}, new int[] {-1, 2}, new int[] {1, -2}, new int[] {-1, -2});
    assertEquals(null, RupChecker.check(2, f, "2 0\nd 1 2 0\n0\n"));
    assertTrue(RupChecker.check(2, f, "0\n") != null, "empty clause is not RUP here");
    assertEquals(null, RupChecker.check(2, f, "2 0\n"), "the formula fails by propagation after 2");
    List<int[]> satisfiable = List.of(new int[] {1, 2}, new int[] {-1, 2});
    assertTrue(RupChecker.check(2, satisfiable, "2 0\n") != null, "no refutation");
    assertTrue(RupChecker.check(2, List.of(new int[] {1, 2}), "1 0\n0\n") != null, "1 is not RUP");
  }
}
