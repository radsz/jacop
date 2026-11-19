/*
 * CdclSolverTest.java
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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.lang.reflect.Field;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.locks.LockSupport;
import java.util.function.LongSupplier;
import org.junit.jupiter.api.Test;

/**
 * Tests of {@link CdclSolver}: answers compared with brute force on random formulas, models
 * checked, assumptions and incremental use, and DIMACS/DRAT input and output.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class CdclSolverTest {

  private static List<int[]> randomFormula(Random rnd, int vars, int clauses, int maxLen) {
    List<int[]> f = new ArrayList<>();
    for (int i = 0; i < clauses; i++) {
      int len = 1 + rnd.nextInt(maxLen);
      int[] c = new int[len];
      for (int k = 0; k < len; k++) {
        int v = 1 + rnd.nextInt(vars);
        c[k] = rnd.nextBoolean() ? v : -v;
      }
      f.add(c);
    }
    return f;
  }

  private static boolean satisfies(List<int[]> f, boolean[] value) {
    for (int[] c : f) {
      boolean sat = false;
      for (int l : c) {
        if (value[Math.abs(l)] == l > 0) {
          sat = true;
          break;
        }
      }
      if (!sat) {
        return false;
      }
    }
    return true;
  }

  private static boolean bruteForce(List<int[]> f, int vars, int[] assumptions) {
    boolean[] value = new boolean[vars + 1];
    for (long m = 0; m < 1L << vars; m++) {
      for (int v = 1; v <= vars; v++) {
        value[v] = (m >> (v - 1) & 1) != 0;
      }
      boolean ok = true;
      for (int a : assumptions) {
        ok &= value[Math.abs(a)] == a > 0;
      }
      if (ok && satisfies(f, value)) {
        return true;
      }
    }
    return false;
  }

  private static boolean[] model(CdclSolver s, int vars) {
    boolean[] value = new boolean[vars + 1];
    for (int v = 1; v <= vars; v++) {
      value[v] = s.modelValue(v);
    }
    return value;
  }

  /** Pigeons into holes: each pigeon in some hole, at most one pigeon per hole. */
  private static List<int[]> pigeons(int pigeons, int holes) {
    List<int[]> f = new ArrayList<>();
    for (int p = 0; p < pigeons; p++) {
      int[] c = new int[holes];
      for (int h = 0; h < holes; h++) {
        c[h] = p * holes + h + 1;
      }
      f.add(c);
    }
    for (int h = 0; h < holes; h++) {
      for (int p = 0; p < pigeons; p++) {
        for (int q = p + 1; q < pigeons; q++) {
          f.add(new int[] {-(p * holes + h + 1), -(q * holes + h + 1)});
        }
      }
    }
    return f;
  }

  @Test
  void boundedVariableAdditionKeepsAnswersAndProofs() throws IOException {
    List<int[]> unsat = pigeons(7, 6);
    CdclSolver s = new CdclSolver();
    s.setChecking(true);
    s.setFactoring(true);
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    DratWriter drat = new DratWriter(out);
    s.setProof(drat);
    unsat.forEach(s::addClause);
    assertEquals(CdclSolver.UNSAT, s.solve());
    drat.close();
    assertTrue(s.factoredVars > 0, "the at-most-one cliques are factored");
    assertEquals(42, s.numInputVars());
    assertNull(RupChecker.check(42, unsat, out.toString(StandardCharsets.US_ASCII)));

    List<int[]> sat = pigeons(6, 6);
    CdclSolver t = new CdclSolver();
    t.setChecking(true);
    t.setFactoring(true);
    // the forward lucky pass satisfies the pigeons before factoring would run
    t.setLucky(false);
    sat.forEach(t::addClause);
    assertEquals(CdclSolver.SAT, t.solve());
    assertTrue(t.factoredVars > 0);
    for (int[] c : sat) {
      boolean holds = false;
      for (int l : c) {
        holds |= t.modelValue(Math.abs(l)) == l > 0;
      }
      assertTrue(holds, "the model satisfies the input clauses");
    }
    // the fresh variables are not the caller's
    assertThrows(IllegalStateException.class, () -> t.addClause(t.numInputVars() + 1));
    // a clause on an eliminated input variable brings back the removed clauses, the ones on fresh
    // variables included
    assertTrue(t.eliminatedCount() > 0, "elimination ran after the factoring");
    for (int h = 1; h <= 6; h++) {
      t.addClause(-h);
    }
    assertEquals(CdclSolver.UNSAT, t.solve(), "pigeon 1 has no hole left");
  }

  @Test
  void vivificationDoesNotLeaveADeletedClauseAsAReason() throws IOException {
    // A clause that vivification shortened was deleted but kept its watches until the end of the
    // round, so the propagations of the round could still make it the reason of a literal: the
    // self-check reported "reason of -36 deleted" (CdclFuzzTest, seed 7263191).
    assertEquals(CdclSolver.SAT, CdclFuzzTest.replay(7_263_191L));
  }

  @Test
  void randomFormulasAgreeWithBruteForce() {
    Random rnd = new Random(42);
    for (int run = 0; run < 3000; run++) {
      int vars = 3 + rnd.nextInt(10);
      List<int[]> f = randomFormula(rnd, vars, 1 + rnd.nextInt(5 * vars), 1 + rnd.nextInt(4));
      CdclSolver s = new CdclSolver();
      s.setChecking(true);
      s.ensureVars(vars);
      for (int[] c : f) {
        s.addClause(c);
      }
      int result = s.solve();
      boolean expected = bruteForce(f, vars, new int[0]);
      assertEquals(expected ? CdclSolver.SAT : CdclSolver.UNSAT, result, "run " + run);
      if (expected) {
        assertTrue(satisfies(f, model(s, vars)), "model of run " + run);
      }
    }
  }

  @Test
  void assumptionsAndFailedCores() {
    assumptionsAndFailedCores(7, true, 3);
  }

  @Test
  void assumptionsOnTheirOwnLevels() {
    assumptionsAndFailedCores(7, false, 3);
  }

  @Test
  void manyAssumptionsOnOneLevel() {
    // more assumptions than variables: duplicates and complementary pairs on level 1
    assumptionsAndFailedCores(13, true, 14);
  }

  @Test
  void complementaryAssumptions() {
    CdclSolver s = new CdclSolver();
    s.ensureVars(3);
    s.addClause(new int[] {1, 2, 3});
    assertEquals(CdclSolver.UNSAT, s.solve(2, 1, -2));
    Set<Integer> core = new HashSet<>();
    for (int a : s.failedAssumptions()) {
      core.add(a);
    }
    assertEquals(Set.of(2, -2), core);
    assertTrue(s.isOk());
    assertEquals(CdclSolver.SAT, s.solve(-1, -2));
  }

  @Test
  void conflictOfTheAssumptionLevel() {
    // the assumptions -1 and -2 force 3 and 4, which clash: the core is {-1, -2}, not -5
    CdclSolver s = new CdclSolver();
    s.ensureVars(5);
    s.addClause(new int[] {1, 2, 3});
    s.addClause(new int[] {1, 2, 4});
    s.addClause(new int[] {-3, -4});
    assertEquals(CdclSolver.UNSAT, s.solve(-5, -1, -2));
    Set<Integer> core = new HashSet<>();
    for (int a : s.failedAssumptions()) {
      core.add(a);
    }
    assertEquals(Set.of(-1, -2), core);
    assertEquals(CdclSolver.SAT, s.solve(-5, -1));
  }

  private void assumptionsAndFailedCores(long seed, boolean oneLevel, int maxAssumptions) {
    Random rnd = new Random(seed);
    for (int run = 0; run < 1000; run++) {
      int vars = 4 + rnd.nextInt(8);
      List<int[]> f = randomFormula(rnd, vars, vars + rnd.nextInt(3 * vars), 3);
      CdclSolver s = new CdclSolver();
      s.setChecking(true);
      s.setAssumptionsOnOneLevel(oneLevel);
      s.ensureVars(vars);
      for (int[] c : f) {
        s.addClause(c);
      }
      // several calls on the same solver: learnt clauses must stay valid across assumptions
      for (int call = 0; call < 4; call++) {
        int k = 1 + rnd.nextInt(maxAssumptions);
        int[] assumed = new int[k];
        for (int i = 0; i < k; i++) {
          int v = 1 + rnd.nextInt(vars);
          assumed[i] = rnd.nextBoolean() ? v : -v;
        }
        int result = s.solve(assumed);
        boolean expected = bruteForce(f, vars, assumed);
        assertEquals(expected ? CdclSolver.SAT : CdclSolver.UNSAT, result, "run " + run);
        if (expected) {
          boolean[] value = model(s, vars);
          assertTrue(satisfies(f, value));
          for (int a : assumed) {
            assertEquals(a > 0, value[Math.abs(a)]);
          }
        } else if (s.isOk()) {
          int[] core = s.failedAssumptions();
          Set<Integer> given = new HashSet<>();
          for (int a : assumed) {
            given.add(a);
          }
          for (int a : core) {
            assertTrue(given.contains(a), "core literal " + a + " is an assumption");
          }
          assertFalse(bruteForce(f, vars, core), "core of run " + run + " is unsatisfiable");
        }
      }
    }
  }

  @Test
  void incrementalClauseAddition() {
    Random rnd = new Random(11);
    for (int run = 0; run < 500; run++) {
      int vars = 5 + rnd.nextInt(7);
      List<int[]> f = new ArrayList<>();
      CdclSolver s = new CdclSolver();
      s.setChecking(true);
      for (int step = 0; step < 6; step++) {
        for (int[] c : randomFormula(rnd, vars, 2 + rnd.nextInt(vars), 3)) {
          f.add(c);
          s.addClause(c);
        }
        s.ensureVars(vars);
        int result = s.solve();
        boolean expected = bruteForce(f, vars, new int[0]);
        assertEquals(expected ? CdclSolver.SAT : CdclSolver.UNSAT, result, "run " + run);
        if (!expected) {
          break;
        }
        assertTrue(satisfies(f, model(s, vars)));
      }
    }
  }

  private static void pigeonhole(CdclSolver s, int holes) {
    int pigeons = holes + 1;
    for (int p = 0; p < pigeons; p++) {
      int[] c = new int[holes];
      for (int h = 0; h < holes; h++) {
        c[h] = p * holes + h + 1;
      }
      s.addClause(c);
    }
    for (int h = 0; h < holes; h++) {
      for (int p = 0; p < pigeons; p++) {
        for (int q = p + 1; q < pigeons; q++) {
          s.addClause(-(p * holes + h + 1), -(q * holes + h + 1));
        }
      }
    }
  }

  @Test
  void analysedVariablesAreNotifiedOncePerConflictAndNotLearnt() {
    for (boolean on : new boolean[] {false, true}) {
      CdclSolver s = new CdclSolver();
      s.setChecking(true);
      pigeonhole(s, 6);
      s.setAnalysedNotify(on);
      Set<Integer> learnt = new HashSet<>();
      Set<Integer> analysed = new HashSet<>();
      boolean[] inAnalysed = {false};
      int[] count = {0};
      s.connect(
          new ExternalPropagator() {
            @Override
            public void notifyLearntLiteral(int lit) {
              if (inAnalysed[0]) {
                learnt.clear();
                analysed.clear();
                inAnalysed[0] = false;
              }
              learnt.add(Math.abs(lit));
            }

            @Override
            public void notifyAnalysedLiteral(int var) {
              inAnalysed[0] = true;
              count[0]++;
              assertFalse(learnt.contains(var), "a learnt variable is notified as analysed");
              assertTrue(analysed.add(var), "an analysed variable is notified twice");
              assertTrue(s.levelOf(var) > 0, "a root variable is notified as analysed");
            }
          });
      assertEquals(CdclSolver.UNSAT, s.solve());
      assertEquals(on, count[0] > 0);
    }
  }

  /**
   * Solves x1 or PH(4), the pigeonhole clauses each with x1 added, deciding x1 false, then 30 free
   * variables, then the pigeonhole variables, in that order (a fixed search under LCG). Each
   * conflict of the pigeonhole part backjumps to x1's level, and the free variables between are
   * decided again after it, unless the solver backtracks one level instead.
   */
  private static long fixedOrderDecisions(int lazyChronoLimit) {
    CdclSolver s = new CdclSolver();
    s.setChecking(true);
    int free = 30;
    int holes = 4;
    int first = free + 2; // the pigeonhole variables follow x1 and the free ones
    int vars = first - 1 + (holes + 1) * holes;
    s.ensureVars(vars);
    for (int p = 0; p <= holes; p++) {
      int[] c = new int[holes + 1];
      c[holes] = 1;
      for (int h = 0; h < holes; h++) {
        c[h] = first + p * holes + h;
      }
      s.addClause(c);
    }
    for (int h = 0; h < holes; h++) {
      for (int p = 0; p <= holes; p++) {
        for (int q = p + 1; q <= holes; q++) {
          s.addClause(1, -(first + p * holes + h), -(first + q * holes + h));
        }
      }
    }
    for (int v = 1; v <= vars; v++) {
      s.observe(v);
    }
    s.setLazyChronoLimit(lazyChronoLimit);
    s.connect(
        new ExternalPropagator() {
          @Override
          public int decide() {
            for (int v = 1; v <= vars; v++) {
              if (s.value(v) == 0) {
                return v >= first ? v : -v; // x1 and the free variables false
              }
            }
            return 0;
          }
        });
    assertEquals(CdclSolver.SAT, s.solve());
    assertTrue(s.modelValue(1), "x1 must be true: PH(4) is unsatisfiable");
    return s.decisions;
  }

  @Test
  void lazyChronologicalBacktrackingKeepsTheDecisionsBetween() {
    long backjumping = fixedOrderDecisions(-1);
    long lazy = fixedOrderDecisions(0);
    assertTrue(
        lazy * 2 < backjumping,
        "decisions with one-level backtracking " + lazy + ", with backjumping " + backjumping);
    assertTrue(fixedOrderDecisions(10) < backjumping, "a backjump of 31 levels is over 10");
  }

  @Test
  void pigeonholeIsUnsatisfiable() {
    CdclSolver s = new CdclSolver();
    pigeonhole(s, 7);
    assertEquals(CdclSolver.UNSAT, s.solve());
    assertFalse(s.isOk());
  }

  @Test
  void conflictLimitStopsTheSearch() {
    CdclSolver s = new CdclSolver();
    s.setChecking(true);
    pigeonhole(s, 10);
    s.setConflictLimit(100);
    assertEquals(CdclSolver.UNKNOWN, s.solve());
  }

  @Test
  void workLimitStopsTheSearchAtTheSameConflictInEveryRun() {
    // the core-guided phase of LcgSolver stops by the solver's work, not by the clock, so that a
    // run
    // repeats whatever the load of the machine
    long[] conflicts = new long[2];
    for (int run = 0; run < 2; run++) {
      CdclSolver s = new CdclSolver();
      s.setChecking(true);
      pigeonhole(s, 10);
      s.setWorkLimit(20_000);
      assertEquals(CdclSolver.UNKNOWN, s.solve());
      assertTrue(s.work() >= 20_000, "work " + s.work());
      conflicts[run] = s.conflicts;
    }
    assertTrue(conflicts[0] > 0);
    assertEquals(conflicts[0], conflicts[1]);
  }

  @Test
  void virtualClockDeadlineStopsTheSearchAtTheSameConflictInEveryRun() {
    // under the virtual clock a time limit is a work limit: -f under jacop.virtualClock repeats
    // its phases, neighbourhoods and stops whatever the load of the machine
    long[] conflicts = new long[2];
    for (int run = 0; run < 2; run++) {
      CdclSolver s = new CdclSolver();
      s.setVirtualClock(true);
      pigeonhole(s, 10);
      long start = s.now();
      assertEquals(s.work() * 1_000_000L / CdclSolver.VIRTUAL_WORK_PER_MS, start);
      s.setDeadline(start + 10 * 1_000_000L);
      assertEquals(CdclSolver.UNKNOWN, s.solve());
      assertTrue(s.now() > s.deadline(), "stopped before the deadline");
      conflicts[run] = s.conflicts;
    }
    assertTrue(conflicts[0] > 0);
    assertEquals(conflicts[0], conflicts[1]);
  }

  @Test
  void stoppedClockReadsLikeTheSolverWithoutHoldingIt() {
    // free search keeps this clock of the LCG solver that gave way, and drops the solver and its
    // clauses (rcpsp-wet-diverse j90_48_4 under -f ran out of 4 GB while it kept them)
    CdclSolver s = new CdclSolver();
    s.setVirtualClock(true);
    long[] external = {1_000};
    s.setExternalWork(() -> external[0]);
    pigeonhole(s, 8);
    s.setDeadline(s.now() + 2 * 1_000_000L);
    assertEquals(CdclSolver.UNKNOWN, s.solve());
    LongSupplier clock = s.stoppedClock();
    assertEquals(s.now(), clock.getAsLong());
    external[0] += CdclSolver.VIRTUAL_WORK_PER_MS;
    // the store's propagations after the hand-over still count
    assertEquals(s.now(), clock.getAsLong());
    assertEquals(s.deadline() - s.now(), s.deadline() - clock.getAsLong());
    // the clock holds the work done, not the solver
    for (Field f : clock.getClass().getDeclaredFields()) {
      assertFalse(CdclSolver.class.isAssignableFrom(f.getType()), f.toString());
    }
    CdclSolver wall = new CdclSolver();
    long before = System.nanoTime();
    long now = wall.stoppedClock().getAsLong();
    assertTrue(now >= before && now <= System.nanoTime());
  }

  @Test
  void alarmRunsOnceAndCanStopTheSearch() {
    // the check of LCG's speed runs as an alarm under the virtual clock, in place of a thread
    long[] conflicts = new long[2];
    for (int run = 0; run < 2; run++) {
      CdclSolver s = new CdclSolver();
      s.setVirtualClock(true);
      pigeonhole(s, 10);
      int[] calls = new int[1];
      s.setAlarm(
          s.now() + 5 * 1_000_000L,
          () -> {
            calls[0]++;
            s.interrupt();
          });
      assertEquals(CdclSolver.UNKNOWN, s.solve());
      assertEquals(1, calls[0]);
      conflicts[run] = s.conflicts;
    }
    assertEquals(conflicts[0], conflicts[1]);
  }

  @Test
  void deadlineStopsTheSearchOnExternalDecisions() {
    // The deadline was checked only on conflicts and on the solver's own decisions, so a search
    // driven by the external propagator's decisions ran past it.
    CdclSolver s = new CdclSolver();
    s.setChecking(true);
    int vars = 5000;
    s.ensureVars(vars);
    s.connect(
        new ExternalPropagator() {
          private int next = 1;

          @Override
          public void notifyBacktrack(int level) {
            next = 1;
          }

          @Override
          public int decide() {
            while (next <= vars && s.value(next) != 0) {
              next++;
            }
            return next <= vars ? next : 0;
          }
        });
    for (int v = 1; v <= vars; v++) {
      s.observe(v);
    }
    s.setDeadline(System.nanoTime() - 1);
    assertEquals(CdclSolver.UNKNOWN, s.solve());
  }

  @Test
  void deadlineStopsAPropagationThatTakesManyRounds() {
    // The deadline was checked only on conflicts and decisions, so an external propagator that
    // took many rounds to reach its fixpoint (bounds creeping one value at a time) ran past it.
    CdclSolver s = new CdclSolver();
    int vars = 100_000;
    s.ensureVars(vars);
    int[] implied = {0};
    s.connect(
        new ExternalPropagator() {
          @Override
          public int propagate() {
            return implied[0] < vars ? ++implied[0] : 0;
          }

          @Override
          public int[] reason(int lit) {
            return new int[] {lit};
          }
        });
    s.setDeadline(System.nanoTime() - 1);
    assertEquals(CdclSolver.UNKNOWN, s.solve());
    assertTrue(implied[0] < 5000, "rounds after the deadline: " + implied[0]);
  }

  @Test
  void deadlineStopsAPropagationOfSlowRoundsSoon() {
    // The clock was read every 1,024 rounds of the external propagator. Rounds of a creeping
    // fixpoint can each take long (vrp-submission toy_D under the core-guided probe), so the
    // search ran minutes past the deadline; now it stops within 64 rounds.
    CdclSolver s = new CdclSolver();
    int vars = 10_000;
    s.ensureVars(vars);
    int[] implied = {0};
    s.connect(
        new ExternalPropagator() {
          @Override
          public int propagate() {
            LockSupport.parkNanos(100_000); // a slow round
            return implied[0] < vars ? ++implied[0] : 0;
          }

          @Override
          public int[] reason(int lit) {
            return new int[] {lit};
          }
        });
    s.setDeadline(System.nanoTime() - 1);
    assertEquals(CdclSolver.UNKNOWN, s.solve());
    assertTrue(implied[0] <= 64, "rounds after the deadline: " + implied[0]);
  }

  @Test
  void probeAfterTheDeadlineDecidesNothingBeforeTheRootFixpoint() {
    // The root propagation of a probe stops at the deadline without its fixpoint, and the probe
    // still decided its literal: the external propagator then pushed the rest of its root
    // consequences at level 1, and they were undone with the probe while the propagator kept them,
    // so later reasons cited unassigned literals (ma-path-finding under --lcg -f)
    CdclSolver s = new CdclSolver();
    int vars = 100_000;
    s.ensureVars(vars + 1);
    int[] implied = {0};
    boolean[] early = {false};
    s.connect(
        new ExternalPropagator() {
          @Override
          public int propagate() {
            return implied[0] < vars ? ++implied[0] : 0;
          }

          @Override
          public int[] reason(int lit) {
            return new int[] {lit};
          }

          @Override
          public void notifyNewDecisionLevel() {
            early[0] |= implied[0] < vars;
          }
        });
    s.setDeadline(System.nanoTime() - 1);
    assertNotNull(s.probe(vars + 1));
    assertFalse(early[0], "a decision with " + (vars - implied[0]) + " root consequences to come");
  }

  @Test
  void subsumptionCountsTheOccurrencesItScans() {
    // The triples {x, y, x^y} of nonzero vectors of GF(2)^6 (a Steiner triple system on 63
    // variables, each in 31 triples, two triples sharing at most one variable): every clause's
    // signature rejects every other one, so the effort counted only compared clauses and stayed
    // 0 however long the scanned lists were (DiamondFree-70 of XCSP 2022, 917,000 clauses over
    // 4,830 variables, scanned for the whole 300 s run under LCG)
    int[][] triples = new int[651][];
    int n = 0;
    for (int x = 1; x < 64; x++) {
      for (int y = x + 1; y < 64; y++) {
        if ((x ^ y) > y) {
          triples[n++] = new int[] {2 * (x - 1), 2 * (y - 1), 2 * ((x ^ y) - 1)};
        }
      }
    }
    assertEquals(651, n);
    boolean[] frozen = new boolean[63];
    Arrays.fill(frozen, true);
    Eliminator e = new Eliminator(63, triples, n, frozen, null);
    assertTrue(e.run());
    // each clause scans the 31 occurrences of one of its literals
    assertTrue(e.effort() >= 651 * 31, "effort " + e.effort());
  }

  @Test
  void eliminationResolvesOnlyGateClausesAgainstTheOthers() {
    // x (variable 0) = a (variable 1), and x occurs in 4 other clauses of each sign. The 24
    // resolvents of all clauses exceed the 10 clauses they replace, but only the 8 of a defining
    // clause with another clause are needed (Een and Biere, SAT 2005)
    int numVars = 18;
    int x = 0;
    int a = 2;
    int[][] clauses = new int[10][];
    clauses[0] = new int[] {x + 1, a};
    clauses[1] = new int[] {x, a + 1};
    for (int i = 0; i < 4; i++) {
      clauses[2 + i] = new int[] {x, 4 * (1 + i), 4 * (1 + i) + 2};
      clauses[6 + i] = new int[] {x + 1, 4 * (1 + i) + 1, 4 * (1 + i) + 3};
    }
    boolean[] frozen = new boolean[numVars];
    Arrays.fill(frozen, true);
    frozen[0] = false;
    for (boolean gates : new boolean[] {false, true}) {
      Eliminator e =
          new Eliminator(
              numVars,
              clauses,
              clauses.length,
              frozen,
              null,
              new Eliminator.Limits(0, 0, 100, gates));
      assertTrue(e.run());
      assertEquals(gates, e.eliminated()[0], "x eliminated with gates " + gates);
      assertEquals(gates ? 1 : 0, e.numGateEliminations());
      assertEquals(gates ? 8 : 10, e.clauses().length);
    }
  }

  @Test
  void eliminationBoundAllowsMoreResolventsThanClauses() {
    // x (variable 0) occurs in 3 clauses of each sign over distinct other variables: 9 resolvents
    // replace 6 clauses, so x is eliminated from bound 3 on, and the bound rises to it when a
    // round finds nothing
    int numVars = 13;
    int[][] clauses = new int[6][];
    for (int i = 0; i < 3; i++) {
      clauses[i] = new int[] {0, 2 * (1 + i)};
      clauses[3 + i] = new int[] {1, 2 * (4 + i)};
    }
    boolean[] frozen = new boolean[numVars];
    Arrays.fill(frozen, true);
    frozen[0] = false;
    for (int max : new int[] {0, 2, 4, 16}) {
      Eliminator e =
          new Eliminator(
              numVars,
              clauses,
              clauses.length,
              frozen,
              null,
              new Eliminator.Limits(0, max, 100, false));
      assertTrue(e.run());
      assertEquals(max >= 3, e.eliminated()[0], "x eliminated with largest bound " + max);
    }
    Eliminator minisat = new Eliminator(numVars, clauses, clauses.length, frozen, null);
    assertTrue(minisat.run());
    assertFalse(minisat.eliminated()[0], "MiniSat elimination adds no clauses");
    assertEquals(1, Eliminator.nextBound(0, 16));
    assertEquals(8, Eliminator.nextBound(4, 16));
    assertEquals(16, Eliminator.nextBound(16, 16));
    assertEquals(5, Eliminator.nextBound(4, 5));
  }

  @Test
  void probeKeepsARootConflictFoundAfterAnExternalClauseUndidItsLevel() {
    // The probe of 1 sets 3 false at level 1; the external clause (3 or 4), with 4 false at the
    // root, then asserts 3 at level 0, which undoes the probe's level, and 3 at the root falsifies
    // (-3 or 2) and (-3 or -2). The probe took that root conflict for a failure of its literal and
    // returned with the formula still open, so variable elimination later met an empty clause
    // (ArrayIndexOutOfBoundsException in Eliminator.subsume, XorSystemFuzzTest without XorSystem)
    for (boolean elimination : new boolean[] {true, false}) {
      CdclSolver s = new CdclSolver();
      s.setChecking(true);
      s.setElimination(elimination);
      s.addClause(-4);
      s.addClause(-1, -3);
      s.addClause(-3, 2);
      s.addClause(-3, -2);
      boolean[] given = {false};
      s.connect(
          new ExternalPropagator() {
            @Override
            public int[] externalClause() {
              if (given[0] || s.value(1) <= 0) {
                return null;
              }
              given[0] = true;
              return new int[] {3, 4};
            }
          });
      for (int v = 1; v <= 4; v++) {
        s.observe(v);
      }
      assertNull(s.probe(1));
      assertTrue(given[0], "the external clause was not asked for");
      assertEquals(CdclSolver.UNSAT, s.solve());
    }
  }

  private static CdclSolver luckySolver(int vars, int[]... clauses) {
    CdclSolver s = new CdclSolver();
    s.setChecking(true);
    s.ensureVars(vars);
    for (int[] c : clauses) {
      s.addClause(c);
    }
    return s;
  }

  @Test
  void luckyAssignmentsFindTrivialModelsWithoutSearch() {
    // every clause has a positive literal: all true
    CdclSolver s = luckySolver(3, new int[] {1, -2}, new int[] {2, 3}, new int[] {-1, -3, 2});
    assertEquals(CdclSolver.SAT, s.solve());
    assertEquals("all-true", s.luckyFound);
    assertEquals(0, s.conflicts);
    // every clause has a negative literal: all false
    s = luckySolver(3, new int[] {-1, 2}, new int[] {-2, -3}, new int[] {1, 2, -3});
    assertEquals(CdclSolver.SAT, s.solve());
    assertEquals("all-false", s.luckyFound);
    // forward false fails at x2 whichever value it takes, forward true flips nothing
    int[][] f = {{1, 2, 3}, {1, 2, -3}, {1, -2, 3}, {1, -2, -3}, {-1, -2, -3}};
    s = luckySolver(3, f);
    s.setElimination(false);
    assertEquals(CdclSolver.SAT, s.solve());
    assertEquals("forward-true", s.luckyFound);
    assertEquals(0, s.conflicts);
    assertTrue(satisfies(List.of(f), model(s, 3)));
    s = luckySolver(3, f);
    s.setElimination(false);
    s.setLucky(false);
    assertEquals(CdclSolver.SAT, s.solve());
    assertNull(s.luckyFound);
    assertTrue(satisfies(List.of(f), model(s, 3)));
  }

  @Test
  void failedLuckyAssignmentsLeaveTheSearchAsWithoutThem() {
    Random rnd = new Random(11);
    int compared = 0;
    for (int run = 0; run < 40; run++) {
      int vars = 60 + rnd.nextInt(40);
      List<int[]> f = new ArrayList<>();
      for (int i = 0; i < (int) (4.2 * vars); i++) {
        int[] c = new int[3];
        for (int k = 0; k < 3; k++) {
          int v = 1 + rnd.nextInt(vars);
          c[k] = rnd.nextBoolean() ? v : -v;
        }
        f.add(c);
      }
      CdclSolver on = luckySolver(vars, f.toArray(new int[0][]));
      CdclSolver off = luckySolver(vars, f.toArray(new int[0][]));
      off.setLucky(false);
      int result = on.solve();
      assertEquals(off.solve(), result, "run " + run);
      if (on.luckyFound == null) {
        compared++;
        assertEquals(off.conflicts, on.conflicts, "conflicts of run " + run);
        assertEquals(off.decisions, on.decisions, "decisions of run " + run);
        assertEquals(off.propagations, on.propagations, "propagations of run " + run);
      }
    }
    assertTrue(compared > 20, "compared " + compared);
  }

  @Test
  void luckyAssignmentsKeepRandomAnswersAndProofs() throws IOException {
    Random rnd = new Random(7);
    for (int run = 0; run < 2000; run++) {
      int vars = 3 + rnd.nextInt(10);
      List<int[]> f = randomFormula(rnd, vars, 1 + rnd.nextInt(5 * vars), 1 + rnd.nextInt(4));
      CdclSolver s = luckySolver(vars, f.toArray(new int[0][]));
      s.setElimination(rnd.nextBoolean());
      ByteArrayOutputStream proof = new ByteArrayOutputStream();
      DratWriter drat = new DratWriter(proof);
      s.setProof(drat);
      int result = s.solve();
      drat.close();
      boolean expected = bruteForce(f, vars, new int[0]);
      assertEquals(expected ? CdclSolver.SAT : CdclSolver.UNSAT, result, "run " + run);
      if (expected) {
        assertTrue(satisfies(f, model(s, vars)), "model of run " + run);
      } else {
        String text = proof.toString(StandardCharsets.US_ASCII);
        assertNull(RupChecker.check(vars, f, text), "proof of run " + run);
      }
    }
  }

  @Test
  void lubySequence() {
    long[] expected = {1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8};
    for (int i = 0; i < expected.length; i++) {
      assertEquals(expected[i], CdclSolver.luby(i + 1));
    }
  }

  @Test
  void readsDimacsAndWritesDrat() throws IOException {
    String cnf = "c example\np cnf 3 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n";
    CdclSolver s = new CdclSolver();
    s.setChecking(true);
    ByteArrayOutputStream proof = new ByteArrayOutputStream();
    DratWriter drat = new DratWriter(proof);
    s.setProof(drat);
    DimacsReader.read(new ByteArrayInputStream(cnf.getBytes(StandardCharsets.US_ASCII)), s);
    assertEquals(3, s.numVars());
    assertEquals(CdclSolver.UNSAT, s.solve());
    drat.close();
    String text = proof.toString(StandardCharsets.US_ASCII);
    assertTrue(text.endsWith("0\n") && text.lines().anyMatch("0"::equals), text);
  }

  /** A depth-first search driven from outside, like the CP solver drives the SAT core. */
  private static final class ExternalSearch {
    final CdclSolver s;
    final int vars;
    final List<int[]> late;
    int nextLate;
    long steps;

    ExternalSearch(CdclSolver s, int vars, List<int[]> late) {
      this.s = s;
      this.vars = vars;
      this.late = late;
    }

    /** Learns the pending clause if it is no longer false; false when this node must fail. */
    private boolean settle() {
      if (!s.isOk()) {
        return false;
      }
      while (s.hasPendingClause()) {
        if (s.pendingFalsified()) {
          return false;
        }
        s.addPendingClause();
      }
      return true;
    }

    boolean dfs() {
      while (true) {
        if (++steps > 1_000_000) {
          throw new IllegalStateException("external search does not terminate");
        }
        if (!settle()) {
          return false;
        }
        if (nextLate < late.size() && steps % 3 == 0) {
          int[] c = late.get(nextLate++);
          if (s.addClauseLive(c, c.length)) {
            s.propagateUnits();
          }
          continue;
        }
        int v = 1;
        while (v <= vars && s.value(v) != 0) {
          v++;
        }
        if (v > vars) {
          if (nextLate < late.size()) {
            int[] c = late.get(nextLate++);
            if (s.addClauseLive(c, c.length)) {
              s.propagateUnits();
            }
            continue;
          }
          return true;
        }
        int lvl = s.decisionLevel();
        for (int lit : new int[] {v, -v}) {
          if (s.value(lit) != 0) {
            break; // forced by a clause learnt in the first branch
          }
          s.newLevel();
          s.assume(lit);
          s.propagateUnits();
          if (dfs()) {
            return true;
          }
          s.backtrackTo(lvl);
          if (!settle()) {
            return false;
          }
        }
        if (s.value(v) == 0 && !s.hasPendingClause()) {
          return false;
        }
      }
    }
  }

  /**
   * A propagator that holds part of the formula as its theory: it propagates and adds those clauses
   * lazily, and checks that its view of the assignment (from the notifications) matches the
   * solver's.
   */
  private static final class TheoryPropagator implements ExternalPropagator {
    final CdclSolver s;
    final List<int[]> theory;
    final Random rnd;
    final int vars;
    final int[] view;
    final List<Integer> trail = new ArrayList<>();
    final List<Integer> levelStart = new ArrayList<>();
    int[] clause;
    final Map<Integer, int[]> reasons = new HashMap<>();
    int calls;
    // lazy: skips some propagations (found again at a later level, so reasons reach lower levels)
    // and gives theory clauses as clauses at random times, also satisfied or unit ones
    boolean lazy;

    TheoryPropagator(CdclSolver s, List<int[]> theory, int vars, Random rnd) {
      this.s = s;
      this.theory = theory;
      this.vars = vars;
      this.rnd = rnd;
      view = new int[vars + 1];
    }

    private int value(int lit) {
      return lit > 0 ? view[lit] : -view[-lit];
    }

    private void checkView() {
      for (int v = 1; v <= vars; v++) {
        assertEquals(s.value(v), view[v], "view of variable " + v);
      }
    }

    @Override
    public void notifyAssignment(int lit, boolean fixed) {
      assertEquals(0, view[Math.abs(lit)], "variable " + lit + " notified twice");
      view[Math.abs(lit)] = lit > 0 ? 1 : -1;
      trail.add(lit);
    }

    @Override
    public void notifyNewDecisionLevel() {
      levelStart.add(trail.size());
    }

    @Override
    public void notifyBacktrack(int level) {
      int keep = levelStart.get(level);
      while (trail.size() > keep) {
        view[Math.abs(trail.remove(trail.size() - 1))] = 0;
      }
      levelStart.subList(level, levelStart.size()).clear();
    }

    @Override
    public boolean checkModel(int[] model) {
      for (int[] c : theory) {
        boolean sat = false;
        for (int l : c) {
          sat |= model[Math.abs(l) - 1] == l;
        }
        if (!sat) {
          clause = c;
          return false;
        }
      }
      return true;
    }

    @Override
    public int decide() {
      if (rnd.nextInt(3) != 0) {
        return 0;
      }
      int v = 1 + rnd.nextInt(vars);
      if (view[v] != 0) {
        return 0;
      }
      return rnd.nextBoolean() ? v : -v;
    }

    @Override
    public int propagate() {
      checkView();
      if (lazy && rnd.nextInt(3) == 0) {
        return 0;
      }
      for (int[] c : theory) {
        int unassigned = 0;
        int open = 0;
        boolean sat = false;
        for (int l : c) {
          sat |= value(l) > 0;
          if (value(l) == 0) {
            unassigned = l;
            open++;
          }
        }
        if (!sat && open == 1) {
          clause = c;
          reasons.put(unassigned, c);
          return unassigned;
        }
      }
      return 0;
    }

    @Override
    public int[] reason(int lit) {
      // asked lazily, possibly after other propagations
      return reasons.get(lit);
    }

    @Override
    public int[] externalClause() {
      checkView();
      if (clause != null && calls++ % 2 == 0) {
        // the clause of a rejected model, or the last reason given again as a plain clause
        int[] c = clause;
        clause = null;
        return c;
      }
      if (lazy && !theory.isEmpty() && rnd.nextInt(4) == 0) {
        return theory.get(rnd.nextInt(theory.size()));
      }
      for (int[] c : theory) {
        boolean open = false;
        for (int l : c) {
          open |= value(l) >= 0;
        }
        if (!open) {
          return c; // falsified
        }
      }
      return null;
    }
  }

  @Test
  void externalPropagatorAgreesWithBruteForce() {
    externalPropagatorAgreesWithBruteForce(false);
  }

  /**
   * A lazy propagator: its clauses and reasons can be unit at a lower level than the current one,
   * and must still propagate after a backtrack to that level (checked at every decision).
   */
  @Test
  void lazyExternalPropagatorAgreesWithBruteForce() {
    externalPropagatorAgreesWithBruteForce(true);
  }

  private static void externalPropagatorAgreesWithBruteForce(boolean lazy) {
    Random rnd = new Random(lazy ? 17 : 13);
    for (int run = 0; run < 3000; run++) {
      int vars = 3 + rnd.nextInt(10);
      List<int[]> f = randomFormula(rnd, vars, 1 + rnd.nextInt(5 * vars), 1 + rnd.nextInt(4));
      CdclSolver s = new CdclSolver();
      s.setChecking(true);
      s.ensureVars(vars);
      s.setChronoLimit(0);
      if (run % 2 == 0) {
        s.setReduceBase(10);
      }
      // reasons above this size are temporary: deleted on backtracking, moved by compaction
      s.setExternalReasonKeep(run % 3 == 0 ? Integer.MAX_VALUE : 2 + run % 3);
      List<int[]> theory = new ArrayList<>();
      for (int[] c : f) {
        if (rnd.nextInt(2) == 0) {
          theory.add(c);
        } else {
          s.addClause(c);
        }
      }
      TheoryPropagator p = new TheoryPropagator(s, theory, vars, rnd);
      p.lazy = lazy;
      s.connect(p);
      for (int v = 1; v <= vars; v++) {
        s.observe(v);
      }
      int result = s.solve();
      boolean expected = bruteForce(f, vars, new int[0]);
      assertEquals(expected ? CdclSolver.SAT : CdclSolver.UNSAT, result, "run " + run);
      if (expected) {
        assertTrue(satisfies(f, model(s, vars)), "model of run " + run);
      }
    }
  }

  @Test
  void externalSearchAgreesWithBruteForce() {
    Random rnd = new Random(5);
    for (int run = 0; run < 3000; run++) {
      int vars = 3 + rnd.nextInt(10);
      List<int[]> f = randomFormula(rnd, vars, 1 + rnd.nextInt(5 * vars), 1 + rnd.nextInt(4));
      CdclSolver s = new CdclSolver();
      s.setChecking(true);
      s.ensureVars(vars);
      List<int[]> late = new ArrayList<>();
      for (int[] c : f) {
        if (rnd.nextInt(3) == 0) {
          late.add(c);
        } else {
          s.addClause(c);
        }
      }
      ExternalSearch search = new ExternalSearch(s, vars, late);
      boolean found = search.dfs();
      boolean expected = bruteForce(f, vars, new int[0]);
      assertEquals(expected, found, "run " + run);
      if (found) {
        boolean[] value = new boolean[vars + 1];
        for (int v = 1; v <= vars; v++) {
          value[v] = s.value(v) > 0;
        }
        assertTrue(satisfies(f, value), "model of run " + run);
      }
    }
  }

  /** Decides 1..n true, each at its own level, under the external search. */
  private static CdclSolver decidedInOrder(int n) {
    CdclSolver s = new CdclSolver();
    s.setChecking(true);
    s.ensureVars(n);
    for (int v = 1; v <= n; v++) {
      s.newLevel();
      s.assume(v);
      assertTrue(s.propagateUnits());
    }
    return s;
  }

  @Test
  void clauseAddedSatisfiedAboveItsUnitLevelPropagatesAfterBacktrack() {
    CdclSolver s = decidedInOrder(6);
    // satisfied by 6 (level 6), false at levels 2 and 4: unit at level 4
    assertTrue(s.addClauseLive(new int[] {-4, -2, 6}, 3));
    s.backtrackTo(4);
    assertTrue(s.propagateUnits());
    assertEquals(1, s.value(6));
  }

  @Test
  void binaryAddedUnitAboveItsUnitLevelPropagatesAfterBacktrack() {
    CdclSolver s = decidedInOrder(4);
    // unit at level 2, asserted at level 4
    assertTrue(s.addClauseLive(new int[] {-2, 5}, 2));
    assertTrue(s.propagateUnits());
    assertEquals(1, s.value(5));
    s.backtrackTo(3);
    assertTrue(s.propagateUnits());
    assertEquals(1, s.value(5));
  }

  @Test
  void clauseRevisitedAfterBacktrackWithBothWatchesFalseIsNotAConflict() {
    CdclSolver s = decidedInOrder(6);
    // watched by 6 (true at level 6) and -4 (false at level 4); -2 false at level 2
    assertTrue(s.addClauseLive(new int[] {-4, -2, 6}, 3));
    s.backtrackTo(1);
    // both watches false before the next propagation; -2 is free, so the clause is unit
    assertTrue(s.addClauseLive(new int[] {-6}, 1));
    assertTrue(s.addClauseLive(new int[] {4}, 1));
    assertTrue(s.propagateUnits());
    assertEquals(-1, s.value(2));
  }

  @Test
  void unitAssertedAgainByBacktrackPropagatesAtLevelZero() {
    CdclSolver s = new CdclSolver();
    s.setChecking(true);
    s.ensureVars(3);
    s.addClause(5, -3);
    s.newLevel();
    s.assume(1);
    assertTrue(s.propagateUnits());
    assertTrue(s.addClauseLive(new int[] {-5}, 1));
    assertTrue(s.propagateUnits());
    // the unit is assigned again at level 0 and propagated only after the next level is opened
    s.backtrackTo(0);
    s.newLevel();
    s.assume(2);
    assertTrue(s.propagateUnits());
    s.backtrackTo(0);
    assertTrue(s.propagateUnits());
    assertEquals(-1, s.value(3));
  }

  @Test
  void varHeapRemoveKeepsTheOrder() {
    Random rnd = new Random(5);
    for (int run = 0; run < 200; run++) {
      int n = 1 + rnd.nextInt(40);
      double[] activity = new double[n];
      VarHeap heap = new VarHeap();
      heap.grow(n, activity);
      Set<Integer> in = new HashSet<>();
      for (int v = 0; v < n; v++) {
        activity[v] = rnd.nextInt(10);
        heap.insert(v);
        in.add(v);
      }
      for (int step = 0; step < 3 * n; step++) {
        int v = rnd.nextInt(n);
        if (rnd.nextBoolean()) {
          heap.remove(v);
          in.remove(v);
        } else {
          heap.insert(v);
          in.add(v);
        }
        assertEquals(in.contains(v), heap.contains(v));
      }
      double last = Double.MAX_VALUE;
      int count = 0;
      while (!heap.isEmpty()) {
        int v = heap.removeMax();
        assertTrue(in.contains(v) && activity[v] <= last, "run " + run);
        last = activity[v];
        count++;
      }
      assertEquals(in.size(), count, "run " + run);
    }
  }

  /** Solves with sweeping and probing on or off, checks a model or the DRAT proof. */
  private static CdclSolver solveInprocessing(List<int[]> f, int vars, boolean on)
      throws IOException {
    CdclSolver s = new CdclSolver();
    s.setChecking(true);
    s.setSweeping(on);
    s.setProbing(on);
    // lucky assignments solve these small formulas before the elimination round
    s.setLucky(false);
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    DratWriter drat = new DratWriter(out);
    s.setProof(drat);
    s.ensureVars(vars);
    for (int[] c : f) {
      s.addClause(c);
    }
    int result = s.solve();
    drat.close();
    if (result == CdclSolver.SAT) {
      assertTrue(satisfies(f, model(s, vars)), "model");
    } else {
      assertEquals(CdclSolver.UNSAT, result);
      assertNull(RupChecker.check(vars, f, out.toString(StandardCharsets.US_ASCII), true));
    }
    return s;
  }

  @Test
  void sweepingRefutesMitersOfEquivalentCircuits() throws IOException {
    // two differently built copies of a circuit and a miter: sweeping finds the equivalent signals,
    // substitutes them and often refutes the miter before any conflict
    int refutedBySweeping = 0;
    for (int run = 0; run < 300; run++) {
      int[] vars = new int[1];
      List<int[]> f = CdclFuzzTest.circuitFormula(new Random(run), vars);
      CdclSolver on = solveInprocessing(f, vars[0], true);
      CdclSolver off = solveInprocessing(f, vars[0], false);
      assertEquals(off.isOk(), on.isOk(), "run " + run);
      if (!on.isOk() && on.conflicts == 0 && on.sweepEquivalences > 0) {
        refutedBySweeping++;
      }
    }
    assertTrue(refutedBySweeping > 0, "no miter refuted by sweeping alone");
  }

  @Test
  void probingFindsAFailedLiteral() throws IOException {
    // 1 implies 2 and 3 through binary clauses, which clash: probing 1 gives the unit -1
    List<int[]> f = new ArrayList<>();
    f.add(new int[] {-1, 2});
    f.add(new int[] {-1, 3});
    f.add(new int[] {-2, -3});
    f.add(new int[] {1, 4, 5});
    f.add(new int[] {1, -4, 5});
    f.add(new int[] {1, 4, -5});
    CdclSolver s = solveInprocessing(f, 5, true);
    assertTrue(s.failedLiterals > 0);
    assertFalse(s.modelValue(1));
    assertTrue(s.modelValue(4) && s.modelValue(5));
  }

  @Test
  void sweptEquivalencesExtendModels() throws IOException {
    // x1 = x2 AND x3 twice (x4 the copy); sweeping substitutes one copy, and the model of the
    // reduced formula gives the substituted variable its value back
    List<int[]> f = new ArrayList<>();
    f.add(new int[] {-1, 2});
    f.add(new int[] {-1, 3});
    f.add(new int[] {1, -2, -3});
    f.add(new int[] {-4, 2});
    f.add(new int[] {-4, 3});
    f.add(new int[] {4, -2, -3});
    f.add(new int[] {1, 4, 5});
    f.add(new int[] {2, 6});
    f.add(new int[] {3, -6});
    CdclSolver s = solveInprocessing(f, 6, true);
    assertTrue(s.isOk());
    assertTrue(s.sweepEquivalences > 0);
    assertEquals(s.modelValue(1), s.modelValue(4));
  }
}
