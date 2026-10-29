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
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
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
    Random rnd = new Random(7);
    for (int run = 0; run < 1000; run++) {
      int vars = 4 + rnd.nextInt(8);
      List<int[]> f = randomFormula(rnd, vars, vars + rnd.nextInt(3 * vars), 3);
      CdclSolver s = new CdclSolver();
      s.setChecking(true);
      s.ensureVars(vars);
      for (int[] c : f) {
        s.addClause(c);
      }
      // several calls on the same solver: learnt clauses must stay valid across assumptions
      for (int call = 0; call < 4; call++) {
        int k = 1 + rnd.nextInt(3);
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
}
