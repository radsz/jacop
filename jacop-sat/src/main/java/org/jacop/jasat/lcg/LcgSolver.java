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
import java.util.HashMap;
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
  private final TreeMap<Integer, Integer>[] ge;
  private final Map<Integer, Integer>[] eq;

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

  /** Statistics: atoms propagated to the solver. */
  public long atomsPropagated;

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
    ge = newTreeMaps(n);
    eq = newHashMaps(n);
    for (IntVar x : all) {
      int i = trail.id(x);
      vars[i] = x;
      root[i] = x.dom().cloneLight();
      ge[i] = new TreeMap<>();
      eq[i] = new HashMap<>();
    }
    sat.connect(this);
  }

  @SuppressWarnings("unchecked")
  private static TreeMap<Integer, Integer>[] newTreeMaps(int n) {
    return new TreeMap[n];
  }

  @SuppressWarnings("unchecked")
  private static Map<Integer, Integer>[] newHashMaps(int n) {
    return new Map[n];
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
    return d;
  }

  /** The variable of [x >= v] for v in (root min, root max], created when missing. */
  private int geVar(int i, int v) {
    Integer d = ge[i].get(v);
    if (d != null) {
      return d;
    }
    int lit = newLiteral(i, GE_KIND, v);
    Map.Entry<Integer, Integer> below = ge[i].lowerEntry(v);
    Map.Entry<Integer, Integer> above = ge[i].higherEntry(v);
    if (below != null) {
      structural.add(new int[] {-lit, below.getValue()}); // [x >= v] -> [x >= below]
    }
    if (above != null) {
      structural.add(new int[] {-above.getValue(), lit}); // [x >= above] -> [x >= v]
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
    Integer d = eq[i].get(v);
    if (d != null) {
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
      while (pushed < trail.size()) {
        int e = pushed++;
        int lit = atomLit(e);
        if (sat.value(lit) > 0) {
          continue;
        }
        int dimacsVar = Math.abs(lit);
        if (dimacsVar >= propagated.length) {
          propagated = Arrays.copyOf(propagated, Math.max(dimacsVar + 1, 2 * propagated.length));
        }
        propagated[dimacsVar] = e;
        atomsPropagated++;
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
    boolean[] seen = new boolean[trail.size()];
    EntryList inSolver = new EntryList();
    EntryList lits = new EntryList();
    if (extra != 0) {
      lits.add(-extra);
    }
    EntryList stack = atoms;
    while (stack.size() > 0) {
      int e = stack.get(stack.size() - 1);
      stack.truncate(stack.size() - 1);
      if (seen[e]) {
        continue;
      }
      seen[e] = true;
      int lit = atomLit(e);
      if (sat.value(lit) > 0) {
        inSolver.add(e);
      } else {
        int more = explainEntry(e, stack);
        if (more != 0) {
          lits.add(-more);
        }
      }
    }
    int[] clause = new int[inSolver.size() + lits.size()];
    for (int k = 0; k < inSolver.size(); k++) {
      clause[k] = -atomLit(inSolver.get(k));
    }
    for (int k = 0; k < lits.size(); k++) {
      clause[inSolver.size() + k] = lits.get(k);
    }
    clause = Arrays.stream(clause).distinct().toArray();
    if (clause.length == 0) {
      throw new IllegalStateException(
          "the constraints failed on the root domains: " + store.recentlyFailedConstraint);
    }
    pushedReason = clause;
    return clause[0];
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
    EntryList reason = new EntryList();
    int extra = explainEntry(e, reason);
    int[] clause = new int[reason.size() + (extra == 0 ? 1 : 2)];
    clause[0] = lit;
    for (int k = 0; k < reason.size(); k++) {
      clause[k + 1] = -atomLit(reason.get(k));
    }
    if (extra != 0) {
      clause[clause.length - 1] = -extra;
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
