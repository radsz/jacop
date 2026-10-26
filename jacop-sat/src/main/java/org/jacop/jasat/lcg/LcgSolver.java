/*
 * LcgSolver.java
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

package org.jacop.jasat.lcg;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.jasat.cdcl.ExternalPropagator;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.ExplanationChecker;

/**
 * Lazy clause generation with JaSAT: the constraints of a store propagate as an external propagator
 * of {@link CdclSolver}, whose conflict analysis learns from their explanations.
 *
 * <p>The atoms of the store's {@link AtomicTrail} are the solver's literals {@code [x >= v]} and
 * {@code [x = v]}, created lazily when an atom, a reason or a decision first needs one. Each new
 * {@code [x >= v]} is linked by clauses to the nearest ones of its variable and each {@code [x =
 * v]} to {@code [x >= v]} and {@code [x >= v + 1]}. The store level follows the solver's decision
 * level. When the solver assigns literals they are applied to the domains and the store propagates;
 * every atom it records goes back to the solver with its explanation as reason, and a failure
 * becomes a conflict clause of the explanations. When every literal is assigned and a variable is
 * not fixed, the solver branches on {@code [x <= min]} of the unfixed variable with the smallest
 * domain.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LcgSolver implements ExternalPropagator {

  private static final int GE_KIND = 0;
  private static final int EQ_KIND = 1;

  private final Store store;
  private final CdclSolver sat = new CdclSolver();
  private final AtomicTrail trail;
  private final int baseLevel;
  private boolean rootFailed;

  // per variable (by trail id): the root domain and the literals created so far (value -> variable)
  private IntVar[] vars = new IntVar[0];
  private IntDomain[] root = new IntDomain[0];
  private final LiteralMap[] ge;
  private final LiteralMap[] eq;

  // per DIMACS variable: its variable's trail id, kind and value
  private int[] litVar = new int[16];
  private byte[] litKind = new byte[16];
  private int[] litValue = new int[16];

  // clauses linking new literals, added through externalClause
  private final ArrayDeque<int[]> structural = new ArrayDeque<>();

  // SAT assignments not yet applied to the domains
  private int[] pending = new int[64];
  private int numPending;

  // per trail entry recorded while applying a solver literal: that literal
  private int[] cause = new int[64];

  private int pushed; // trail entries below are true in the solver
  private boolean failed;
  private int[] pushedReason;
  private int[] propagated = new int[16]; // per DIMACS variable pushed as an atom: its entry
  private boolean lazyAtoms = !Boolean.getBoolean("jacop.lcg.eagerAtoms");
  // literals created after an entry implying them: pushed out of order, and again after a
  // backtrack while the solver level is above the entry's
  private int[] lateLit = new int[16];
  private int[] lateEntry = new int[16];
  private int numLate;
  private int lateNext;
  // atoms a reason needed and had no literal for, as (variable, kind, value): created next
  private int[] wanted = new int[48];
  private int numWanted;
  private boolean[] explained; // per variable: an atom of it was in a reason; its atoms are eager
  private int[] seen = new int[64]; // per entry: the stamp of the last expansion that met it
  private int stamp;
  private int[] solution;
  private Runnable onSolution;
  private ExplanationChecker checker;
  private final Map<String, long[]> explanationCounts = new TreeMap<>();

  /** Statistics: reasons the solver asked for. */
  public long reasons;

  /** Statistics: literals of those reasons. */
  public long reasonLiterals;

  /** Statistics: solutions found by {@link #minimize}. */
  public long solutions;

  /** Statistics: entries no literal stood for, so not pushed. */
  public long atomsSkipped;

  /** Statistics: literals pushed after the entries that implied them, once they were created. */
  public long atomsLate;

  /** Statistics: atoms propagated to the solver. */
  public long atomsPropagated;

  /** Statistics: distinct literals pushed as atoms. */
  public long atomLiterals;

  /** Statistics: distinct literals pushed as atoms that occur in a learnt clause. */
  public long atomLiteralsLearnt;

  // per DIMACS variable: 1 once pushed as an atom, 2 once it also occurred in a learnt clause
  private byte[] atomUse = new byte[16];

  /** Statistics: failures of the constraints turned into conflict clauses. */
  public long constraintConflicts;

  /** Statistics: decisions made on unfixed variables when every literal was assigned. */
  public long searchDecisions;

  /**
   * Builds the solver for the constraints imposed in a store. The store is propagated first; its
   * domains then are the root facts.
   *
   * @param store the store with its variables and constraints
   */
  public LcgSolver(Store store) {
    this.store = store;
    rootFailed = !store.consistency();
    this.baseLevel = store.level; // consistency may raise the level after impositions
    trail = new AtomicTrail(store);
    sat.setExternalReasonKeep(Integer.getInteger("jacop.lcg.reasonKeep", 2));
    if (Boolean.getBoolean("jacop.lcg.check")) {
      checker = new ExplanationChecker(trail);
    }
    List<IntVar> all = new ArrayList<>();
    for (int i = 0; i < store.size(); i++) {
      if (store.vars[i] instanceof IntVar x) {
        all.add(x);
      }
    }
    for (Var v : store.variablesHashMap.values()) {
      if (v instanceof BooleanVar b) {
        all.add(b);
      }
    }
    int n = 0;
    for (IntVar x : all) {
      n = Math.max(n, trail.id(x) + 1);
    }
    vars = new IntVar[n];
    root = new IntDomain[n];
    ge = new LiteralMap[n];
    eq = new LiteralMap[n];
    explained = new boolean[n];
    for (IntVar x : all) {
      int i = trail.id(x);
      vars[i] = x;
      root[i] = x.dom().cloneLight();
      ge[i] = new LiteralMap();
      eq[i] = new LiteralMap();
    }
    sat.connect(this);
  }

  // ------------------------------------------------------------------------------- literals

  private int newLiteral(int i, int kind, int value) {
    int d = sat.newVariables(1);
    sat.observe(d);
    if (d >= litVar.length) {
      int n = 2 * d;
      litVar = Arrays.copyOf(litVar, n);
      litKind = Arrays.copyOf(litKind, n);
      litValue = Arrays.copyOf(litValue, n);
    }
    litVar[d] = i;
    litKind[d] = (byte) kind;
    litValue[d] = value;
    if (lazyAtoms) {
      queueIfImplied(d);
    }
    return d;
  }

  /** Queues a new literal for a push when an entry implies it or its negation. */
  private void queueIfImplied(int d) {
    IntVar x = vars[litVar[d]];
    int v = litValue[d];
    int lit = -d;
    int e;
    if (litKind[d] == GE_KIND) {
      e = trail.firstImplying(x, AtomicTrail.GE, v);
      if (e >= 0) {
        lit = d;
      } else {
        e = trail.firstImplying(x, AtomicTrail.LE, v - 1);
      }
    } else {
      e = trail.firstImplying(x, AtomicTrail.NE, v);
    }
    if (e < 0) {
      return;
    }
    if (numLate == lateLit.length) {
      lateLit = Arrays.copyOf(lateLit, 2 * numLate);
      lateEntry = Arrays.copyOf(lateEntry, 2 * numLate);
    }
    lateLit[numLate] = lit;
    lateEntry[numLate++] = e;
  }

  /** The variable of [x >= v] for v in (root min, root max], created when missing. */
  private int geVar(int i, int v) {
    int d = ge[i].get(v);
    if (d != LiteralMap.NONE) {
      return d;
    }
    int lit = newLiteral(i, GE_KIND, v);
    int below = ge[i].lower(v);
    int above = ge[i].higher(v);
    if (below != LiteralMap.NONE) {
      structural.add(new int[] {-lit, below}); // [x >= v] -> [x >= below]
    }
    if (above != LiteralMap.NONE) {
      structural.add(new int[] {-above, lit}); // [x >= above] -> [x >= v]
    }
    ge[i].put(v, lit);
    return lit;
  }

  /** The literal [x >= v]; 0 stands for a constant, which callers rule out. */
  private int geLit(int i, int v) {
    if (v <= root[i].min() || v > root[i].max()) {
      throw new IllegalStateException("[" + vars[i].id() + " >= " + v + "] is a constant");
    }
    return geVar(i, v);
  }

  /** The variable of [x = v] for v in the root domain, created when missing. */
  private int eqVar(int i, int v) {
    int d = eq[i].get(v);
    if (d != LiteralMap.NONE) {
      return d;
    }
    int lit = newLiteral(i, EQ_KIND, v);
    boolean atMin = v == root[i].min();
    boolean atMax = v == root[i].max();
    int geV = atMin ? 0 : geVar(i, v);
    int geNext = atMax ? 0 : geVar(i, v + 1);
    if (!atMin) {
      structural.add(new int[] {-lit, geV});
    }
    if (!atMax) {
      structural.add(new int[] {-lit, -geNext});
    }
    if (atMin && atMax) {
      structural.add(new int[] {lit});
    } else if (atMin) {
      structural.add(new int[] {lit, geNext});
    } else if (atMax) {
      structural.add(new int[] {lit, -geV});
    } else {
      structural.add(new int[] {lit, -geV, geNext});
    }
    eq[i].put(v, lit);
    return lit;
  }

  /** The DIMACS literal that is true when a trail entry's atom holds. */
  private int atomLit(int entry) {
    int i = trail.id(trail.variable(entry));
    int v = trail.value(entry);
    return switch (trail.kind(entry)) {
      case AtomicTrail.GE -> geLit(i, v);
      case AtomicTrail.LE -> -geLit(i, v + 1);
      default -> -eqVar(i, v);
    };
  }

  /** The literal of an entry's own atom, or 0 when it has none. */
  private int existingAtomLit(int entry) {
    int i = trail.id(trail.variable(entry));
    int v = trail.value(entry);
    return switch (trail.kind(entry)) {
      case AtomicTrail.GE -> ge[i].get(v);
      case AtomicTrail.LE -> -ge[i].get(v + 1);
      default -> -eq[i].get(v);
    };
  }

  /** The literal of the strongest atom with a literal that an entry implies, or 0. */
  private int impliedLit(int entry) {
    int i = trail.id(trail.variable(entry));
    int v = trail.value(entry);
    int d;
    switch (trail.kind(entry)) {
      case AtomicTrail.GE -> {
        d = ge[i].get(v);
        return d != LiteralMap.NONE ? d : ge[i].lower(v);
      }
      case AtomicTrail.LE -> {
        d = ge[i].get(v + 1);
        return -(d != LiteralMap.NONE ? d : ge[i].higher(v + 1));
      }
      default -> {
        return -eq[i].get(v);
      }
    }
  }

  /** Notes that an entry's atom needs a literal, created at the next {@link #propagate}. */
  private void want(int entry) {
    if (numWanted + 3 > wanted.length) {
      wanted = Arrays.copyOf(wanted, 2 * wanted.length);
    }
    int i = trail.id(trail.variable(entry));
    explained[i] = true;
    wanted[numWanted++] = i;
    wanted[numWanted++] = trail.kind(entry);
    wanted[numWanted++] = trail.value(entry);
  }

  private void createWanted() {
    while (numWanted > 0) {
      numWanted -= 3;
      int i = wanted[numWanted];
      int v = wanted[numWanted + 2];
      switch (wanted[numWanted + 1]) {
        case AtomicTrail.GE -> geVar(i, v);
        case AtomicTrail.LE -> geVar(i, v + 1);
        default -> eqVar(i, v);
      }
    }
  }

  /**
   * Returns the next queued literal, created after an entry that implies it, that is not true yet,
   * or 0. A literal pushed at a level not above its entry's stays true while the entry stays, so it
   * leaves the queue; the others are pushed again after a backtrack.
   */
  private int nextLate() {
    while (lateNext < numLate) {
      int k = lateNext;
      int lit = lateLit[k];
      int e = lateEntry[k];
      if (store.level <= trail.level(e)) {
        numLate--;
        lateLit[k] = lateLit[numLate];
        lateEntry[k] = lateEntry[numLate];
      } else {
        lateNext++;
      }
      if (sat.value(lit) <= 0) {
        atomsLate++;
        pushedAs(lit, e);
        return lit;
      }
    }
    return 0;
  }

  /** Records that a literal is pushed for an entry. */
  private void pushedAs(int lit, int e) {
    int dimacsVar = Math.abs(lit);
    if (dimacsVar >= propagated.length) {
      propagated = Arrays.copyOf(propagated, Math.max(dimacsVar + 1, 2 * propagated.length));
    }
    propagated[dimacsVar] = e;
    if (dimacsVar >= atomUse.length) {
      atomUse = Arrays.copyOf(atomUse, propagated.length);
    }
    if (atomUse[dimacsVar] == 0) {
      atomUse[dimacsVar] = 1;
      atomLiterals++;
    }
    atomsPropagated++;
  }

  /**
   * Returns the solver, for its settings and statistics.
   *
   * @return the CDCL solver
   */
  public CdclSolver sat() {
    return sat;
  }

  /**
   * Solves the store's constraints.
   *
   * @return {@link CdclSolver#SAT}, {@link CdclSolver#UNSAT} or {@link CdclSolver#UNKNOWN}
   */
  public int solve() {
    if (rootFailed) {
      return CdclSolver.UNSAT;
    }
    solution = null;
    int result = sat.solve();
    // the solver leaves its last assignment without notifying; the store goes back to the root
    notifyBacktrack(0);
    return result;
  }

  /**
   * Minimises a variable: solves, then requires a smaller value than the solution's, until no
   * solution is left. {@link #value} then gives the best solution found.
   *
   * @param objective the variable to minimise
   * @return {@link CdclSolver#SAT} when the best solution is optimal, {@link CdclSolver#UNSAT} when
   *     there is no solution, or {@link CdclSolver#UNKNOWN} when a limit stopped the search
   */
  public int minimize(IntVar objective) {
    int i = trail.id(objective);
    int[] best = null;
    while (true) {
      int result = solve();
      if (result != CdclSolver.SAT) {
        solution = best;
        if (result == CdclSolver.UNSAT) {
          return best == null ? CdclSolver.UNSAT : CdclSolver.SAT;
        }
        return CdclSolver.UNKNOWN;
      }
      best = solution;
      solutions++;
      int v = best[i];
      if (v <= root[i].min()) {
        return CdclSolver.SAT;
      }
      sat.addClause(-geLit(i, v)); // objective <= v - 1
    }
  }

  /**
   * Adds a clause over 0/1 variables: one of the positive variables is 1 or one of the negative
   * ones is 0. It goes to the SAT solver as a clause of {@code [x >= 1]} literals, so it is
   * propagated and explained by the solver itself. Add clauses before solving.
   *
   * @param positive variables of which one may be 1
   * @param negative variables of which one may be 0
   */
  public void addClause(IntVar[] positive, IntVar[] negative) {
    List<Integer> clause = new ArrayList<>();
    for (int sign = 1; sign >= -1; sign -= 2) {
      for (IntVar x : sign > 0 ? positive : negative) {
        int i = trail.id(x);
        if (root[i].min() < 0 || root[i].max() > 1) {
          throw new IllegalArgumentException(x + " is not a 0/1 variable");
        }
        if (root[i].singleton()) {
          if (root[i].min() == (sign > 0 ? 1 : 0)) {
            return; // satisfied at the root
          }
          continue; // false at the root
        }
        clause.add(sign * geLit(i, 1));
      }
    }
    if (clause.isEmpty()) {
      rootFailed = true;
      return;
    }
    if (!sat.addClause(clause.stream().mapToInt(Integer::intValue).toArray())) {
      rootFailed = true;
    }
  }

  /**
   * Turns the explanation checker on or off: every explanation is then derived again in a scratch
   * store, and a wrong one stops the solver with an {@link IllegalStateException}. The system
   * property {@code jacop.lcg.check=true} turns it on for every solver.
   *
   * @param on true to check explanations
   */
  public void setChecking(boolean on) {
    checker = on ? new ExplanationChecker(trail) : null;
  }

  /**
   * Chooses how atoms reach the solver. Lazily (the default), an entry is pushed as the strongest
   * atom it implies that has a literal, and is skipped when there is none; an atom of a reason gets
   * a literal when it has none, and is replaced by its own reason meanwhile. Eagerly, every entry
   * is pushed as its own atom, with a literal created for it; the system property {@code
   * jacop.lcg.eagerAtoms=true} chooses that for every solver.
   *
   * @param on true for lazy atoms
   */
  public void setLazyAtoms(boolean on) {
    lazyAtoms = on;
  }

  /**
   * Returns the explanation checker, for its statistics.
   *
   * @return the checker, or null when checking is off
   */
  public ExplanationChecker checker() {
    return checker;
  }

  /**
   * Sets an action run at every solution while the store's domains are fixed to it, for example to
   * print the solution.
   *
   * @param action the action, or null for none
   */
  public void onSolution(Runnable action) {
    onSolution = action;
  }

  /**
   * Returns the value of a variable in the last solution.
   *
   * @param x a variable of the store
   * @return its value
   */
  public int value(IntVar x) {
    if (solution == null) {
      throw new IllegalStateException("no solution");
    }
    return solution[trail.id(x)];
  }

  // ------------------------------------------------------------------ the external propagator

  @Override
  public void notifyLearntLiteral(int lit) {
    int dimacsVar = Math.abs(lit);
    if (dimacsVar < atomUse.length && atomUse[dimacsVar] == 1) {
      atomUse[dimacsVar] = 2;
      atomLiteralsLearnt++;
    }
  }

  @Override
  public void notifyAssignment(int lit, boolean fixed) {
    if (numPending == pending.length) {
      pending = Arrays.copyOf(pending, 2 * numPending);
    }
    pending[numPending++] = lit;
  }

  @Override
  public void notifyNewDecisionLevel() {
    store.setLevel(store.level + 1);
  }

  @Override
  public void notifyBacktrack(int level) {
    while (store.level > baseLevel + level) {
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
    }
    numPending = 0;
    failed = false;
    pushed = Math.min(pushed, trail.size());
    int kept = 0;
    for (int k = 0; k < numLate; k++) {
      if (lateEntry[k] < trail.size()) {
        lateLit[kept] = lateLit[k];
        lateEntry[kept++] = lateEntry[k];
      }
    }
    numLate = kept;
    lateNext = 0;
  }

  @Override
  public int[] externalClause() {
    return structural.poll();
  }

  /**
   * Pushes the atoms the store recorded to the solver one at a time, each with its explanation as
   * reason; once all are in, applies the solver's new assignments to the domains and propagates the
   * store. A failure is returned as a false literal whose reason is the conflict clause, which the
   * solver takes as a conflict.
   */
  @Override
  public int propagate() {
    if (failed) {
      return 0;
    }
    while (true) {
      createWanted();
      int late = nextLate();
      if (late != 0) {
        return late;
      }
      while (pushed < trail.size()) {
        int e = pushed++;
        int lit =
            lazyAtoms && !explained[trail.id(trail.variable(e))] ? impliedLit(e) : atomLit(e);
        if (lit == 0) {
          atomsSkipped++;
          continue;
        }
        if (sat.value(lit) > 0) {
          continue;
        }
        pushedAs(lit, e);
        return lit;
      }
      if (numPending == 0) {
        return 0;
      }
      int from = trail.size();
      for (int k = 0; k < numPending; k++) {
        int lit = pending[k];
        try {
          apply(lit);
        } catch (FailException _) {
          IntVar x = vars[litVar[Math.abs(lit)]];
          EntryList atoms = new EntryList();
          trail.atomsBefore(x, trail.size(), atoms);
          return conflict(atoms, lit);
        }
        if (trail.size() > cause.length) {
          cause = Arrays.copyOf(cause, Math.max(trail.size(), 2 * cause.length));
        }
        for (; from < trail.size(); from++) {
          cause[from] = lit;
        }
      }
      numPending = 0;
      if (!store.consistency()) {
        constraintConflicts++;
        EntryList atoms = new EntryList();
        boolean own = trail.explainFailure(store.recentlyFailedConstraint, atoms);
        count(store.recentlyFailedConstraint, own, atoms.size(), 3);
        if (checker != null) {
          verify(checker.checkFailure(store.recentlyFailedConstraint, atoms));
        }
        return conflict(atoms, 0);
      }
    }
  }

  /**
   * Adds the reason entries of an entry to {@code out}; an entry recorded while applying a solver
   * literal is explained by its variable's atoms before it and that literal, which is returned.
   *
   * @return the solver literal that is part of the reason, or 0
   */
  private int explainEntry(int e, EntryList out) {
    if (trail.reason(e) == null) {
      trail.atomsBefore(trail.variable(e), e, out);
      return cause[e];
    }
    int mark = out.size();
    boolean own = trail.explain(e, out);
    count(trail.reason(e), own, out.size() - mark, 0);
    if (checker != null) {
      EntryList reason = new EntryList();
      for (int k = mark; k < out.size(); k++) {
        reason.add(out.get(k));
      }
      verify(checker.checkReason(e, reason));
    }
    return 0;
  }

  // per constraint class: reasons, generic reasons and atoms in them, then the same for failures
  private void count(Constraint c, boolean own, int atoms, int at) {
    long[] counts =
        explanationCounts.computeIfAbsent(
            c == null ? "none" : c.getClass().getSimpleName(), k -> new long[6]);
    counts[at]++;
    if (!own) {
      counts[at + 1]++;
    }
    counts[at + 2] += atoms;
  }

  /**
   * Returns the explanation statistics per constraint class (simple name): reasons asked, those
   * given by the generic reason, and the atoms in them; then failures explained, those explained
   * generically, and their atoms.
   *
   * @return six counts per class, in the order above
   */
  public Map<String, long[]> explanationStatistics() {
    return explanationCounts;
  }

  private static void verify(String problem) {
    if (problem != null) {
      throw new IllegalStateException("wrong explanation: " + problem);
    }
  }

  /**
   * Turns a failure into a conflict: the negated atoms, each one not yet in the solver replaced by
   * its own explanation, and the negated solver literal extra unless 0. Returns a false literal of
   * the clause, whose reason is the clause.
   */
  private int conflict(EntryList atoms, int extra) {
    numPending = 0;
    failed = true;
    EntryList lits = new EntryList();
    if (extra != 0) {
      lits.add(-extra);
    }
    negatedAtoms(atoms, Integer.MAX_VALUE, lits);
    int[] clause = new int[lits.size()];
    for (int k = 0; k < lits.size(); k++) {
      clause[k] = lits.get(k);
    }
    clause = Arrays.stream(clause).distinct().toArray();
    if (clause.length == 0) {
      throw new IllegalStateException(
          "the constraints failed on the root domains: " + store.recentlyFailedConstraint);
    }
    pushedReason = clause;
    return clause[0];
  }

  /**
   * Adds to {@code lits} the negations of atoms: of each atom whose literal was made true in the
   * solver before trail position {@code limit}; any other atom is replaced by its explanation. The
   * atoms given that have no literal get one for the next time, but not the atoms of their
   * explanations. Uses {@code atoms} as a stack.
   */
  private void negatedAtoms(EntryList atoms, int limit, EntryList lits) {
    if (seen.length < trail.size()) {
      seen = new int[Math.max(trail.size(), 2 * seen.length)];
    }
    if (++stamp == 0) {
      Arrays.fill(seen, 0);
      stamp = 1;
    }
    if (lazyAtoms) {
      for (int k = 0; k < atoms.size(); k++) {
        if (existingAtomLit(atoms.get(k)) == 0) {
          want(atoms.get(k));
        }
      }
    }
    while (atoms.size() > 0) {
      int e = atoms.get(atoms.size() - 1);
      atoms.truncate(atoms.size() - 1);
      if (seen[e] == stamp) {
        continue;
      }
      seen[e] = stamp;
      int lit = lazyAtoms ? existingAtomLit(e) : atomLit(e);
      if (lit != 0 && sat.value(lit) > 0 && sat.trailPosition(lit) < limit) {
        lits.add(-lit);
        continue;
      }
      int more = explainEntry(e, atoms);
      if (more != 0) {
        lits.add(-more);
      }
    }
  }

  private void apply(int lit) {
    int dimacsVar = Math.abs(lit);
    IntVar x = vars[litVar[dimacsVar]];
    int v = litValue[dimacsVar];
    store.currentConstraint = null;
    if (litKind[dimacsVar] == GE_KIND) {
      if (lit > 0) {
        x.domain.inMin(store.level, x, v);
      } else {
        x.domain.inMax(store.level, x, v - 1);
      }
    } else if (lit > 0) {
      x.domain.in(store.level, x, v, v);
    } else if (x.domain.contains(v)) {
      x.domain.inComplement(store.level, x, v);
    }
  }

  /**
   * Returns the reason of a literal: the conflict clause just returned by {@link #propagate}, or
   * the explanation of the atom pushed as that literal, computed now.
   */
  @Override
  public int[] reason(int lit) {
    if (pushedReason != null && pushedReason[0] == lit) {
      int[] r = pushedReason;
      pushedReason = null;
      return r;
    }
    int e = propagated[Math.abs(lit)];
    EntryList atoms = new EntryList();
    EntryList lits = new EntryList();
    lits.add(lit);
    int extra = explainEntry(e, atoms);
    if (extra != 0) {
      lits.add(-extra);
    }
    negatedAtoms(atoms, sat.trailPosition(lit), lits);
    int[] clause = new int[lits.size()];
    for (int k = 0; k < lits.size(); k++) {
      clause[k] = lits.get(k);
    }
    reasons++;
    reasonLiterals += clause.length;
    return clause;
  }

  /**
   * When every literal is assigned, branches on {@code [x <= min]} of the unfixed variable with the
   * smallest domain; otherwise leaves the decision to the solver.
   */
  @Override
  public int decide() {
    if (sat.trailSize() < sat.numVars() || !structural.isEmpty()) {
      return 0;
    }
    int best = -1;
    int bestSize = Integer.MAX_VALUE;
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] != null && !vars[i].singleton() && vars[i].getSize() < bestSize) {
        best = i;
        bestSize = vars[i].getSize();
      }
    }
    if (best < 0) {
      return 0;
    }
    searchDecisions++;
    return -geLit(best, vars[best].min() + 1);
  }

  @Override
  public boolean checkModel(int[] model) {
    solution = new int[vars.length];
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] != null) {
        if (!vars[i].singleton()) {
          throw new IllegalStateException(vars[i] + " is not fixed in a model");
        }
        solution[i] = vars[i].value();
      }
    }
    if (onSolution != null) {
      onSolution.run();
    }
    return true;
  }
}
