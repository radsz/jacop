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

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
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
 * the formula with the failed assumptions as units and checking that proof. The solver checks its
 * propagation at every decision as well ({@link CdclSolver#setChecking}).
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

  /**
   * A random circuit of AND, XOR and ITE gates in which some gates are copies of others over
   * equivalent inputs (permuted, with negations that cancel, through equivalence chains), so that
   * congruence closure and substitution have work; with random clauses and sometimes a miter that
   * asks two equivalent outputs to differ.
   */
  static List<int[]> circuitFormula(Random rnd, int[] varsOut) {
    List<int[]> f = new ArrayList<>();
    int inputs = 2 + rnd.nextInt(8);
    int gates = 2 + rnd.nextInt(30);
    // per node (variable), the variable of its class's first member
    int[] canon = new int[inputs + 3 * gates + 2];
    List<int[]> specs = new ArrayList<>(); // kind, output, inputs...
    int next = inputs + 1;
    for (int v = 1; v <= inputs; v++) {
      canon[v] = v;
    }
    for (int g = 0; g < gates; g++) {
      int out = next++;
      int[] spec;
      if (!specs.isEmpty() && rnd.nextInt(3) == 0) {
        // a copy of an earlier gate over members of the same classes
        int[] old = specs.get(rnd.nextInt(specs.size()));
        spec = old.clone();
        spec[1] = out;
        canon[out] = canon[old[1]];
        for (int i = 2; i < spec.length; i++) {
          int c = canon[Math.abs(spec[i])];
          int member = c;
          for (int v = 1; v < next; v++) {
            if (canon[v] == c && rnd.nextInt(3) == 0) {
              member = v;
            }
          }
          spec[i] = spec[i] > 0 ? member : -member;
        }
        if (spec[0] != 2 && spec.length > 3) {
          // AND and XOR: permute the inputs
          for (int i = spec.length - 1; i > 2; i--) {
            int j = 2 + rnd.nextInt(i - 1);
            int t = spec[i];
            spec[i] = spec[j];
            spec[j] = t;
          }
        }
        if (spec[0] == 1 && rnd.nextBoolean()) {
          spec[2] = -spec[2]; // XOR: two negations cancel
          spec[3] = -spec[3];
        }
        if (spec[0] == 2 && rnd.nextBoolean()) {
          spec[2] = -spec[2]; // ITE: c ? t : e = -c ? e : t
          int t = spec[3];
          spec[3] = spec[4];
          spec[4] = t;
        }
      } else {
        int kind = rnd.nextInt(3); // 0 AND, 1 XOR, 2 ITE
        int arity = kind == 2 ? 3 : 2 + rnd.nextInt(2);
        spec = new int[2 + arity];
        spec[0] = kind;
        spec[1] = out;
        if (out - 1 < arity) {
          next--;
          continue;
        }
        int[] picked = rnd.ints(1, out).distinct().limit(arity).toArray();
        for (int i = 0; i < arity; i++) {
          spec[2 + i] = rnd.nextBoolean() ? picked[i] : -picked[i];
        }
        canon[out] = out;
      }
      specs.add(spec);
      encodeGate(f, spec);
      if (rnd.nextInt(6) == 0) {
        // an equivalence chain node: e = out through binary clauses
        int e = next++;
        canon[e] = canon[out];
        f.add(new int[] {-e, out});
        f.add(new int[] {e, -out});
      }
    }
    int vars = next - 1;
    int extra = rnd.nextInt(Math.max(1, vars / 2));
    for (int k = 0; k < extra; k++) {
      int[] c = new int[1 + rnd.nextInt(3)];
      for (int i = 0; i < c.length; i++) {
        int v = 1 + rnd.nextInt(vars);
        c[i] = rnd.nextBoolean() ? v : -v;
      }
      f.add(c);
    }
    if (rnd.nextBoolean()) {
      // a miter on two members of one class
      for (int tries = 0; tries < 20; tries++) {
        int a = 1 + rnd.nextInt(vars);
        int b = 1 + rnd.nextInt(vars);
        if (a != b && canon[a] == canon[b]) {
          f.add(new int[] {a, b});
          f.add(new int[] {-a, -b});
          break;
        }
      }
    }
    java.util.Collections.shuffle(f, rnd);
    varsOut[0] = vars;
    return f;
  }

  // the clauses of a gate: kind (0 AND, 1 XOR, 2 ITE), output, inputs
  private static void encodeGate(List<int[]> f, int[] spec) {
    int o = spec[1];
    int[] in = Arrays.copyOfRange(spec, 2, spec.length);
    if (spec[0] == 0) {
      int[] big = new int[in.length + 1];
      big[0] = o;
      for (int i = 0; i < in.length; i++) {
        f.add(new int[] {-o, in[i]});
        big[i + 1] = -in[i];
      }
      f.add(big);
    } else if (spec[0] == 1) {
      // forbid every assignment of inputs and output with o != xor of the inputs
      int n = in.length;
      for (int m = 0; m < 1 << n; m++) {
        boolean x = false;
        int[] c = new int[n + 1];
        for (int i = 0; i < n; i++) {
          boolean bit = (m >> i & 1) != 0;
          x ^= bit;
          c[i] = bit ? -in[i] : in[i];
        }
        c[n] = x ? o : -o; // the assignment with output !x is forbidden
        f.add(c);
      }
    } else {
      int c = in[0];
      int t = in[1];
      int e = in[2];
      f.add(new int[] {-o, -c, t});
      f.add(new int[] {-o, c, e});
      f.add(new int[] {o, -c, -t});
      f.add(new int[] {o, c, -e});
    }
  }

  /** Random formulas of several shapes; mostly near the satisfiability threshold. */
  // the formula of a seed: a circuit for one seed in five, chosen apart from the seed's stream so
  // the other seeds keep the formulas they had before circuits were added (and replay as before)
  static List<int[]> formula(long seed, Random rnd, int[] varsOut) {
    if (new Random(~seed).nextInt(5) == 0) {
      return circuitFormula(rnd, varsOut);
    }
    return randomFormula(rnd, varsOut);
  }

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

  /**
   * Connects an external propagator that decides the variables in input order, each with a phase
   * fixed by the seed, as a fixed search annotation does under LCG, and backtracks one level
   * instead of backjumping always or above a few levels ({@link CdclSolver#setLazyChronoLimit}).
   */
  private static void inputOrderDecisions(CdclSolver s, int vars, long seed) {
    Random phases = new Random(seed);
    boolean[] positive = new boolean[vars + 1];
    for (int v = 1; v <= vars; v++) {
      positive[v] = phases.nextBoolean();
      s.observe(v);
    }
    s.setLazyChronoLimit(Math.floorMod(seed, 2L) == 0 ? 0 : 3);
    s.connect(
        new ExternalPropagator() {
          @Override
          public int decide() {
            for (int v = 1; v <= vars; v++) {
              if (s.value(v) == 0) {
                return positive[v] ? v : -v;
              }
            }
            return 0;
          }
        });
  }

  /** Solves with a DRAT proof and checks the answer; returns the answer. */
  private static int solveChecked(List<int[]> f, int vars, long seed) throws IOException {
    CdclSolver s = new CdclSolver();
    s.setChecking(true);
    ByteArrayOutputStream proof = new ByteArrayOutputStream();
    DratWriter drat = new DratWriter(proof);
    s.setProof(drat);
    s.setChronoLimit(chronoLimit(seed));
    if (seed % 2 == 0) {
      s.setReduceBase(10);
    }
    s.ensureVars(vars);
    for (int[] c : f) {
      s.addClause(c);
    }
    if (Math.floorMod(seed, 5L) == 3) {
      inputOrderDecisions(s, vars, seed);
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
    s.setChecking(true);
    s.setChronoLimit(chronoLimit(seed));
    if (seed % 2 == 0) {
      s.setReduceBase(10);
    }
    s.setAssumptionsOnOneLevel(Math.floorMod(seed, 5L) != 0);
    s.ensureVars(vars);
    List<int[]> added = new ArrayList<>();
    int next = 0;
    while (next < f.size()) {
      int batch = 1 + rnd.nextInt(Math.max(1, f.size() / 3));
      for (int k = 0; k < batch && next < f.size(); k++, next++) {
        s.addClause(f.get(next));
        added.add(f.get(next));
      }
      int[] assumed = new int[rnd.nextInt(Math.floorMod(seed, 4L) == 1 ? 24 : 4)];
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

  /**
   * Solves, with every check, the first formula of the given fuzz seed.
   *
   * @param seed the seed, as a failure prints it
   * @return the answer
   */
  static int replay(long seed) throws IOException {
    Random rnd = new Random(seed);
    int[] vars = new int[1];
    List<int[]> f = formula(seed, rnd, vars);
    return solveChecked(f, vars[0], seed);
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
      List<int[]> f = formula(seed, rnd, vars);
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
    assertNull(RupChecker.check(2, f, "2 0\nd 1 2 0\n0\n"));
    assertNotNull(RupChecker.check(2, f, "0\n"), "empty clause is not RUP here");
    assertNull(RupChecker.check(2, f, "2 0\n"), "the formula fails by propagation after 2");
    List<int[]> satisfiable = List.of(new int[] {1, 2}, new int[] {-1, 2});
    assertNotNull(RupChecker.check(2, satisfiable, "2 0\n"), "no refutation");
    assertNotNull(RupChecker.check(2, List.of(new int[] {1, 2}), "1 0\n0\n"), "1 is not RUP");
  }
}
