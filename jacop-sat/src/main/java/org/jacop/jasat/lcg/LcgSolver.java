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
import java.util.function.IntSupplier;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.jasat.cdcl.ExternalPropagator;
import org.jacop.jasat.cdcl.VarHeap;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.ExplanationChecker;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.Mirrored;
import org.jacop.search.SelectChoicePoint;

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

  /**
   * Runs the store to its fixpoint before clauses propagate again; false returns to the clauses
   * after each pruning.
   */
  private static final boolean FULL_FIXPOINT =
      Boolean.parseBoolean(System.getProperty("jacop.lcg.fullFixpoint", "true"));

  // per variable (by trail id): the root domain and the literals created so far (value -> variable)
  private IntVar[] vars = new IntVar[0];
  private IntDomain[] root = new IntDomain[0];
  private final LiteralMap[] ge;
  private final LiteralMap[] eq;

  // per DIMACS variable: its variable's trail id, kind and value
  private int[] litVar = new int[16];
  private byte[] litKind = new byte[16];
  private int[] litValue = new int[16];
  // semantic minimisation: learnt literals sorted by variable, and those removed
  private long[] minimizeKeys = new long[16];
  private boolean[] minimizeRemoved = new boolean[16];

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

  /** Statistics: distinct literals pushed as atoms. */
  public long atomLiterals;

  /** Statistics: distinct literals pushed as atoms that occur in a learnt clause. */
  public long atomLiteralsLearnt;

  // per DIMACS variable: 1 once pushed as an atom, 2 once it also occurred in a learnt clause
  private byte[] atomUse = new byte[16];

  /** Statistics: failures of the constraints turned into conflict clauses. */
  public long constraintConflicts;

  /**
   * Statistics: decisions made on integer variables, by activity or when every literal was
   * assigned.
   */
  public long searchDecisions;

  /** Statistics: activity decisions on late variables (see {@link #setLateVariables}). */
  public long lateDecisions;

  /** Statistics: the late variables (see {@link #setLateVariables}). */
  public long lateVariables;

  /** Statistics: the unfixed 0/1 variables at the start, late ones included. */
  public long booleanVariables;

  /** Statistics: the unfixed variables at the start that are not 0/1, late ones included. */
  public long wideVariables;

  /** Statistics: decisions taken from the model's search annotation. */
  public long annotationDecisions;

  /** How decisions are made outside the runs of the search annotation. */
  public enum Branching {
    /** On the most active integer variable, by the activity of its literals in learnt clauses. */
    ACTIVITY,
    /** The SAT solver's own decisions on literals, by their activity and saved phases. */
    LITERALS,
    /**
     * As LITERALS, but as ACTIVITY from {@link #AUTO_CONFLICTS} conflicts to the first solution.
     */
    AUTO,
    /**
     * Runs take turns at each restart: with an annotation under free search, the annotation
     * (completed by ACTIVITY), then LITERALS, then ACTIVITY; without one, LITERALS and ACTIVITY.
     */
    ALTERNATE
  }

  /** Conflicts without a solution after which {@link Branching#AUTO} uses activity branching. */
  public static final long AUTO_CONFLICTS = 1000;

  private Branching branching =
      Branching.valueOf(System.getProperty("jacop.lcg.branching", "activity").toUpperCase());
  // whether decisions are on the most active variable, now
  private boolean activityBranching = branching == Branching.ACTIVITY;
  private long runs; // restarts so far, for the turns of Branching.ALTERNATE
  private final String valueChoice = System.getProperty("jacop.lcg.value", "split");
  // last-conflict branching, on unless -Djacop.lcg.lastConflict=false
  private final boolean lastConflict =
      !"false".equals(System.getProperty("jacop.lcg.lastConflict"));
  private int decisionVar = -1; // the variable of the last activity decision
  private int conflictVar = -1; // the variable to branch on next, after a conflict
  private long backtrackConflicts;
  // semantic minimisation of learnt clauses, on unless -Djacop.lcg.semantic=false
  private final boolean semantic = !"false".equals(System.getProperty("jacop.lcg.semantic"));
  // semantic UIPs in conflict analysis, on unless -Djacop.lcg.semanticUip=false
  private final boolean semanticUip = !"false".equals(System.getProperty("jacop.lcg.semanticUip"));
  private double[] activity;
  // the variables by activity; with Booleans first only the 0/1 ones, the others in wide, which
  // is branched on only once every 0/1 variable is fixed, as in CP-SAT's default search
  private final VarHeap heap = new VarHeap();
  private final VarHeap wide = new VarHeap();
  // Booleans first unless -Djacop.lcg.booleansFirst=false, which keeps every variable in heap
  private boolean split = !"false".equals(System.getProperty("jacop.lcg.booleansFirst"));
  // whether the runs of activity branching take turns with and without Booleans first
  private boolean booleansFirstTurns;
  // variables branched on only when every variable of heap and wide is fixed (defined variables)
  private final VarHeap lateHeap = new VarHeap();
  private boolean[] late;
  private double activityInc = 1;
  private long activityConflicts;
  // variables taken off the heap because they were fixed, with the decision level at the time
  private int[] popped = new int[16];
  private int[] poppedLevel = new int[16];
  private int numPopped;
  // the values of the last solution, preferred in decisions
  private int[] phase;

  // the model's search annotation: used in every run, or in every other run when free
  private SelectChoicePoint<? extends Var> annotation;
  private boolean freeSearch;
  private boolean annotationRun;

  private double lowerBoundShare;
  private long lowerBoundBudget;

  /** Statistics: runs of objective lower-bound search. */
  public long lowerBoundRuns;

  /** Statistics: lower-bound runs that raised the lower bound. */
  public long lowerBoundRaised;

  // the variable minimised by branch and bound, or -1
  private int objective = -1;
  private int[] best;
  // after the core phase, branch and bound starts from the activity before it, unless
  // -Djacop.lcg.coreRestore=false
  private static final boolean CORE_RESTORE =
      !"false".equals(System.getProperty("jacop.lcg.coreRestore"));
  // the core phase gives its time to branch and bound when it has no solution by this share of
  // its time; 0 turns it off. With the restore it scored 21.3 against 14.7 and 24.3 against 12.7 on
  // the Challenge sample in two pairings, and 21.8 against 22.2 and 22.9 against 21.1 on the
  // OR-Tools set; either alone lost.
  private static final double CORE_NO_SOLUTION =
      Double.parseDouble(System.getProperty("jacop.lcg.coreNoSolution", "0.33"));
  private double coreShare;
  private long coreBudget;
  private long coreCallLimit;
  private boolean coreMode; // solutions under assumptions end the search instead of bounding it
  private CoreSearch coreSearch;
  // the objective value of the best solution found outside this solver, and the last one imported
  private IntSupplier sharedBound;
  private int importedBound = Integer.MAX_VALUE;
  // a shared bound at or below the objective's smallest value: no better solution exists
  private boolean sharedBoundUnreachable;

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
    // reasons of up to three literals stay as clauses; with the full fixpoint this scored 22.8
    // against 20.2 on the OR-Tools set and 18.9 against 19.1 on the Challenge sample, and proved
    // one more instance in each
    sat.setExternalReasonKeep(Integer.getInteger("jacop.lcg.reasonKeep", 3));
    // learnt clauses keep longer in LCG, where a level holds many atoms: core up to LBD 3, middle
    // up to 8 scored 19.4 against 15.6 for 2 and 6 on the Challenge sample, in four pairings
    sat.setTierLimits(3, 8);
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
    activity = new double[n];
    heap.grow(n, activity);
    wide.grow(n, activity);
    lateHeap.grow(n, activity);
    late = new boolean[n];
    for (IntVar x : all) {
      int i = trail.id(x);
      vars[i] = x;
      root[i] = x.dom().cloneLight();
      ge[i] = new LiteralMap();
      eq[i] = new LiteralMap();
      if (!root[i].singleton()) {
        heapOf(i).insert(i);
        if (root[i].min() < 0 || root[i].max() > 1) {
          wideVariables++;
        } else {
          booleanVariables++;
        }
      }
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
    return d;
  }

  /** A new solver variable that is not an atom, such as an output of a cardinality encoding. */
  int newAuxiliary() {
    int d = sat.newVariables(1);
    if (d >= litVar.length) {
      int n = 2 * d;
      litVar = Arrays.copyOf(litVar, n);
      litKind = Arrays.copyOf(litKind, n);
      litValue = Arrays.copyOf(litValue, n);
    }
    litVar[d] = -1;
    return d;
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
    return solve(new int[0]);
  }

  private int solve(int... assumed) {
    if (rootFailed) {
      return CdclSolver.UNSAT;
    }
    solution = null;
    // clauses propagate between constraints: each consistency() returns after a pruning constraint
    store.setReturnAfterPruning(!FULL_FIXPOINT);
    int result;
    try {
      result = sat.solve(assumed);
    } finally {
      store.setReturnAfterPruning(false);
    }
    // the solver leaves its last assignment without notifying; the store goes back to the root
    notifyBacktrack(0);
    return result;
  }

  /**
   * Minimises a variable by branch and bound inside one search: at each solution the solver gets
   * the clause that the objective is smaller and backjumps, keeping its learnt clauses, until no
   * solution is left. {@link #value} then gives the best solution found.
   *
   * @param objective the variable to minimise
   * @return {@link CdclSolver#SAT} when the best solution is optimal, {@link CdclSolver#UNSAT} when
   *     there is no solution, or {@link CdclSolver#UNKNOWN} when a limit stopped the search
   */
  public int minimize(IntVar objective) {
    this.objective = trail.id(objective);
    best = null;
    coreSearch = coreShare > 0 ? CoreSearch.of(this, objective) : null;
    int result;
    try {
      if (coreSearch != null) {
        result = minimizeWithCores();
      } else {
        result = lowerBoundShare > 0 ? minimizeWithLowerBoundSearch() : solve();
      }
    } finally {
      this.objective = -1;
      sat.setConflictLimit(Long.MAX_VALUE);
    }
    solution = best;
    if (result == CdclSolver.UNKNOWN && !sharedBoundUnreachable) {
      return CdclSolver.UNKNOWN;
    }
    // SAT when the solution has the smallest value of the objective, UNSAT when none is better
    return best == null ? CdclSolver.UNSAT : CdclSolver.SAT;
  }

  /**
   * Runs core-guided search, then branch and bound from its best solution and lower bound. The
   * core-guided search takes at most its share of the time left (its budget of conflicts when there
   * is no deadline), and stops early when one call of the solver needs more than its limit of
   * conflicts: a sign that it no longer finds cores or solutions quickly. It also stops when it has
   * no solution after a third of its time. Under a solution bound, every solution the core-guided
   * search finds would have to improve, which makes its strata hard, so the bound comes only after
   * it. Branch and bound then starts from the variables' activity before the core-guided search.
   */
  private int minimizeWithCores() {
    long deadline = sat.deadline();
    long now = System.nanoTime();
    long phaseLimit = Long.MAX_VALUE;
    if (deadline != Long.MAX_VALUE) {
      sat.setDeadline(now + (long) (coreShare * Math.max(0, deadline - now)));
    } else {
      phaseLimit = sat.conflicts + coreBudget;
    }
    double[] saved = CORE_RESTORE ? activity.clone() : null;
    double savedInc = activityInc;
    coreMode = true;
    int result;
    try {
      long full = sat.deadline();
      if (CORE_NO_SOLUTION > 0 && full != Long.MAX_VALUE) {
        // without a solution by this share of the phase, branch and bound gets the time
        long first = now + (long) (CORE_NO_SOLUTION * (full - now));
        sat.setDeadline(first);
        result = coreSearch.run(phaseLimit, coreCallLimit);
        if (result == CdclSolver.UNKNOWN && best != null && System.nanoTime() >= first) {
          sat.setDeadline(full);
          result = coreSearch.run(phaseLimit, coreCallLimit);
        }
      } else {
        result = coreSearch.run(phaseLimit, coreCallLimit);
      }
    } finally {
      coreMode = false;
      sat.setDeadline(deadline);
      sat.setConflictLimit(Long.MAX_VALUE);
    }
    if (result != CdclSolver.UNKNOWN) {
      return result;
    }
    if (saved != null) {
      // the core phase bumped the variables of conflicts under its assumptions, which mislead
      // branch and bound: harmony-brother reached the optimum's bound in 8 s and then did not find
      // the optimum, which branch and bound alone proves in 35 s
      System.arraycopy(saved, 0, activity, 0, Math.min(saved.length, activity.length));
      activityInc = savedInc;
      rebuildHeap(heap);
      rebuildHeap(wide);
      rebuildHeap(lateHeap);
    }
    if (!requireBetter()) {
      return CdclSolver.SAT;
    }
    return lowerBoundShare > 0 ? minimizeWithLowerBoundSearch() : solve();
  }

  /**
   * Adds the clause that the objective is below its value in the best solution, if there is one.
   * Returns false when that value is the objective's smallest, so the best solution is optimal.
   */
  boolean requireBetter() {
    if (best == null) {
      return true;
    }
    int v = best[objective];
    if (v <= vars[objective].min()) {
      return false;
    }
    sat.addClause(-geLit(objective, v)); // objective <= v - 1
    return true;
  }

  /**
   * Turns on core-guided search in {@link #minimize} when the objective is a linear sum: before
   * branch and bound, it finds unsatisfiable cores of the assumptions that each term of the sum
   * stays at its lower bound and relaxes them (OLL), raising the objective's lower bound, until it
   * proves a solution optimal, its time is up, or one call of the solver needs too many conflicts.
   *
   * @param share the share of the time left that it may take; 0 turns it off
   * @param conflicts the conflicts it may take when there is no deadline
   * @param callLimit the conflicts one call of the solver may take before it stops
   */
  public void setCoreSearch(double share, long conflicts, long callLimit) {
    coreShare = share;
    coreBudget = Math.max(1, conflicts);
    coreCallLimit = Math.max(1, callLimit);
  }

  /**
   * Returns the core-guided phase of the last {@link #minimize}, for its statistics.
   *
   * @return the phase, or null when it did not run
   */
  public CoreSearch coreSearch() {
    return coreSearch;
  }

  // ------------------------------------------------- access for the core-guided phase

  CdclSolver solver() {
    return sat;
  }

  /** The index of a variable of the store, or -1 when it is not one of the solver's variables. */
  int index(IntVar x) {
    int i = trail.id(x);
    return i >= 0 && i < vars.length && vars[i] == x ? i : -1;
  }

  IntVar variable(int i) {
    return vars[i];
  }

  /** The literal {@code [x >= v]} of variable i, for v in (root min, root max]. */
  int geLiteral(int i, int v) {
    return geLit(i, v);
  }

  /** The literal {@code [x = v]} of variable i, for v in its root domain. */
  int eqLiteral(int i, int v) {
    return eqVar(i, v);
  }

  /** Whether literal lit of variable i's atoms holds when the variable takes value v. */
  boolean holds(int lit, int i, int v) {
    int d = Math.abs(lit);
    if (litVar[d] != i) {
      throw new IllegalArgumentException(lit + " is not an atom of variable " + i);
    }
    boolean atom = litKind[d] == GE_KIND ? v >= litValue[d] : v == litValue[d];
    return atom == lit > 0;
  }

  int solveUnder(int... assumed) {
    return solve(assumed);
  }

  /** The objective's value in the best solution so far, or {@link Long#MAX_VALUE}. */
  long bestObjective() {
    return best == null ? Long.MAX_VALUE : best[objective];
  }

  /**
   * Alternates branch and bound with objective lower-bound search: runs of branch and bound end
   * after a number of conflicts, and each is followed by a run under the assumption that the
   * objective is at its lower bound, with a share of those conflicts. When that run proves the
   * assumption impossible, the lower bound goes up by a clause; when it finds a solution, the
   * solution is optimal. The budget of conflicts grows by half at each round.
   */
  private int minimizeWithLowerBoundSearch() {
    long budget = lowerBoundBudget;
    while (true) {
      long limit = sat.conflicts + budget;
      sat.setConflictLimit(limit);
      int result = solve();
      if (result != CdclSolver.UNKNOWN || sat.conflicts < limit) {
        return result; // done, or stopped by the deadline
      }
      int lb = vars[objective].min(); // after solve the domains are those of level 0
      if (best != null && lb < best[objective]) {
        int lit = -geLit(objective, lb + 1); // objective <= lb
        limit = sat.conflicts + (long) (budget * lowerBoundShare);
        sat.setConflictLimit(limit);
        lowerBoundRuns++;
        result = solve(lit);
        if (result == CdclSolver.SAT) {
          return result; // a solution at the smallest value of the objective
        }
        if (result == CdclSolver.UNSAT) {
          if (sat.failedAssumptions().length == 0) {
            return result; // no better solution at all
          }
          sat.addClause(-lit); // objective >= lb + 1
          lowerBoundRaised++;
        } else if (sat.conflicts < limit) {
          return result;
        }
      }
      budget += budget / 2;
    }
  }

  /**
   * Turns on objective lower-bound search in {@link #minimize}: runs of branch and bound alternate
   * with runs that assume the objective at its lower bound, which take the given share of the
   * conflicts of the runs before them.
   *
   * @param share the conflicts of a lower-bound run per conflict of branch and bound; 0 for none
   * @param firstRun the conflicts of the first run of branch and bound, growing by half each round
   */
  public void setLowerBoundSearch(double share, long firstRun) {
    lowerBoundShare = share;
    lowerBoundBudget = Math.max(1, firstRun);
  }

  /**
   * Sets how decisions are made outside the runs of the annotation. Set it before solving.
   *
   * @param branching the branching
   */
  public void setBranching(Branching branching) {
    this.branching = branching;
    activityBranching = branching == Branching.ACTIVITY;
  }

  /**
   * Sets whether activity branching decides the 0/1 variables first, before any other variable is
   * decided, as CP-SAT's default search does, or takes all variables in one order of activity. The
   * default is the first, unless the system property {@code jacop.lcg.booleansFirst} is false. Set
   * it before solving.
   *
   * @param booleansFirst true for the 0/1 variables first
   */
  public void setBooleansFirst(boolean booleansFirst) {
    if (booleansFirst == split) {
      return;
    }
    split = booleansFirst;
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] != null && !late[i] && (heap.contains(i) || wide.contains(i))) {
        (heap.contains(i) ? heap : wide).remove(i);
        heapOf(i).insert(i);
      }
    }
  }

  /**
   * Sets whether the runs of activity branching take turns at restarts with and without the 0/1
   * variables first (see {@link #setBooleansFirst}), starting with the current setting. Neither
   * order is better on most models, and the one that is differs between models of one kind. Set it
   * before solving.
   *
   * @param turns true for turns
   */
  public void setBooleansFirstTurns(boolean turns) {
    booleansFirstTurns = turns;
  }

  /**
   * Returns whether activity branching decides the 0/1 variables first.
   *
   * @return true for the 0/1 variables first
   */
  public boolean booleansFirst() {
    return split;
  }

  /**
   * Sets the model's search annotation as the branching. Under fixed search every run follows it;
   * under free search the runs alternate between it and the activity of the variables, starting
   * with it. When it has fixed all its variables, the activity completes the assignment.
   *
   * @param select the annotation's variable and value selection, or null for none
   * @param free true for free search
   */
  public void setAnnotation(SelectChoicePoint<? extends Var> select, boolean free) {
    annotation = select;
    freeSearch = free;
    annotationRun = select != null;
    if (annotationRun && branching == Branching.ALTERNATE) {
      activityBranching = true;
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
  public void notifyLearntLiteral(int lit) {
    int dimacsVar = Math.abs(lit);
    if (litVar[dimacsVar] < 0) {
      return; // not an atom
    }
    if (branching != Branching.LITERALS) {
      bump(litVar[dimacsVar]);
    }
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
    if (sat.conflicts != backtrackConflicts) {
      // a conflict led here: its last decision was on decisionVar
      backtrackConflicts = sat.conflicts;
      conflictVar = decisionVar;
    }
    while (store.level > baseLevel + level) {
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
    }
    // a variable fixed at the decision level it was taken off at, or below, may be free again
    while (numPopped > 0 && poppedLevel[numPopped - 1] > level) {
      int v = popped[--numPopped];
      heapOf(v).insert(v);
    }
    numPending = 0;
    failed = false;
    pushed = Math.min(pushed, trail.size());
  }

  @Override
  public void notifyRestart() {
    if (branching == Branching.ALTERNATE && annotation != null && freeSearch) {
      // the annotation, the literals and the activity in turn, with the activity completing the
      // annotation's runs
      runs++;
      annotationRun = runs % 3 == 0;
      activityBranching = runs % 3 != 1;
    } else if (branching == Branching.ALTERNATE) {
      activityBranching = !activityBranching;
    } else if (annotation != null && freeSearch) {
      annotationRun = !annotationRun;
    }
    if (booleansFirstTurns && activityBranching) {
      setBooleansFirst(!split);
    }
  }

  /**
   * Semantic minimisation (Feydy, Schutt and Stuckey 2013): a learnt literal whose set of values of
   * its variable is inside the set of another learnt literal on the same variable implies that
   * literal, so the clause holds without it; for example {@code [x <= 2]} next to {@code [x <= 4]},
   * or {@code [x = 3]} next to {@code [x != 5]}.
   */
  @Override
  public int minimizeLearnt(int[] clause, int size) {
    if (!semantic) {
      return size;
    }
    if (minimizeKeys.length < size) {
      minimizeKeys = new long[2 * size];
      minimizeRemoved = new boolean[2 * size];
    }
    for (int k = 0; k < size; k++) {
      minimizeKeys[k] = (long) litVar[Math.abs(clause[k])] << 32 | k;
      minimizeRemoved[k] = false;
    }
    Arrays.sort(minimizeKeys, 0, size);
    int removed = 0;
    for (int from = 0, to; from < size; from = to) {
      long var = minimizeKeys[from] >>> 32;
      to = from + 1;
      while (to < size && minimizeKeys[to] >>> 32 == var) {
        to++;
      }
      if (to - from > 16 && var <= Integer.MAX_VALUE) {
        removed += minimizeGroup(clause, from, to);
        continue;
      }
      for (int a = from; a < to; a++) {
        int i = (int) minimizeKeys[a];
        if (i == 0 || litVar[Math.abs(clause[i])] < 0) {
          continue; // the asserting literal stays, and so do literals that are not atoms
        }
        for (int b = from; b < to; b++) {
          int j = (int) minimizeKeys[b];
          if (j != i && !minimizeRemoved[j] && implies(clause[i], clause[j])) {
            minimizeRemoved[i] = true;
            removed++;
            break;
          }
        }
      }
    }
    if (removed == 0) {
      return size;
    }
    int kept = 0;
    for (int k = 0; k < size; k++) {
      if (!minimizeRemoved[k]) {
        clause[kept++] = clause[k];
      }
    }
    return kept;
  }

  /**
   * Semantic minimisation of the literals of one variable, keys {@code from} to {@code to}, in
   * linear time for long groups: of the {@code [x >= v]} literals only the weakest can stay, and so
   * of the {@code [x < v]} ones, while an {@code [x = v]} literal goes when it implies another
   * literal of the group. Returns the number of literals removed.
   */
  private int minimizeGroup(int[] clause, int from, int to) {
    int lo = -1; // the [x >= v] literal with the smallest v
    int hi = -1; // the [x < v] literal with the largest v
    int holeMin = Integer.MAX_VALUE;
    int holeMax = Integer.MIN_VALUE;
    int holes = 0;
    for (int a = from; a < to; a++) {
      int i = (int) minimizeKeys[a];
      int l = clause[i];
      int d = Math.abs(l);
      if (litKind[d] == GE_KIND) {
        if (l > 0 && (lo < 0 || litValue[d] < litValue[Math.abs(clause[lo])])) {
          lo = i;
        } else if (l < 0 && (hi < 0 || litValue[d] > litValue[Math.abs(clause[hi])])) {
          hi = i;
        }
      } else if (l < 0) {
        holes++;
        holeMin = Math.min(holeMin, litValue[d]);
        holeMax = Math.max(holeMax, litValue[d]);
      }
    }
    // the weakest bounds go when they imply a hole: [x >= v] that x != w for w < v
    if (lo > 0 && holeMin < litValue[Math.abs(clause[lo])]) {
      minimizeRemoved[lo] = true;
    }
    if (hi > 0 && holeMax >= litValue[Math.abs(clause[hi])]) {
      minimizeRemoved[hi] = true;
    }
    int removed = (lo > 0 && minimizeRemoved[lo] ? 1 : 0) + (hi > 0 && minimizeRemoved[hi] ? 1 : 0);
    for (int a = from; a < to; a++) {
      int i = (int) minimizeKeys[a];
      if (i == 0 || i == lo || i == hi) {
        continue;
      }
      int l = clause[i];
      int d = Math.abs(l);
      boolean drop;
      if (litKind[d] == GE_KIND) {
        // implies the weakest bound of its side, or the hole the weakest one implies
        drop = true;
      } else if (l > 0) {
        long v = litValue[d];
        // x = v implies the weakest bound of a side it is on, or a hole at another value
        drop =
            lo >= 0 && v >= litValue[Math.abs(clause[lo])]
                || hi >= 0 && v < litValue[Math.abs(clause[hi])]
                || holes > 1
                || holes == 1 && holeMin != v;
      } else {
        drop = false; // x != v implies nothing else
      }
      if (drop) {
        minimizeRemoved[i] = true;
        removed++;
      }
    }
    return removed;
  }

  // whether literal a implies literal b, both on the same variable, by their sets of values
  private boolean implies(int a, int b) {
    int va = Math.abs(a);
    int vb = Math.abs(b);
    boolean aEq = litKind[va] == EQ_KIND;
    boolean bEq = litKind[vb] == EQ_KIND;
    if (aEq && a < 0) {
      return false; // x != v implies no other atom's literal on x
    }
    long aLo = a > 0 ? litValue[va] : Long.MIN_VALUE;
    long aHi = aEq || a < 0 ? litValue[va] - (aEq ? 0L : 1L) : Long.MAX_VALUE;
    if (bEq && b < 0) {
      return litValue[vb] < aLo || litValue[vb] > aHi;
    }
    long bLo = b > 0 ? litValue[vb] : Long.MIN_VALUE;
    long bHi = bEq || b < 0 ? litValue[vb] - (bEq ? 0L : 1L) : Long.MAX_VALUE;
    return bLo <= aLo && aHi <= bHi;
  }

  @Override
  public int integerVariable(int var) {
    return semanticUip && var < litVar.length ? litVar[var] : -1;
  }

  /**
   * The atom equal to a conjunction of true atoms of one variable, when one exists: the values they
   * leave form one interval, after the {@code x != v} atoms at its ends, that touches a root bound
   * ({@code [x >= v]} or {@code [x <= v]}) or holds one value ({@code [x = v]}).
   */
  @Override
  public int semanticUip(int[] lits, int size) {
    int i = litVar[Math.abs(lits[0])];
    long lo = Long.MIN_VALUE;
    long hi = Long.MAX_VALUE;
    for (int k = 0; k < size; k++) {
      int d = Math.abs(lits[k]);
      long v = litValue[d];
      if (litKind[d] == GE_KIND) {
        if (lits[k] > 0) {
          lo = Math.max(lo, v);
        } else {
          hi = Math.min(hi, v - 1);
        }
      } else if (lits[k] > 0) {
        lo = Math.max(lo, v);
        hi = Math.min(hi, v);
      }
    }
    for (boolean moved = true; moved; ) {
      moved = false;
      for (int k = 0; k < size; k++) {
        int d = Math.abs(lits[k]);
        if (litKind[d] == EQ_KIND && lits[k] < 0 && (litValue[d] == lo || litValue[d] == hi)) {
          lo += litValue[d] == lo ? 1 : 0;
          hi -= litValue[d] == hi ? 1 : 0;
          moved = true;
        }
      }
    }
    for (int k = 0; k < size; k++) {
      int d = Math.abs(lits[k]);
      if (litKind[d] == EQ_KIND && lits[k] < 0 && lo < litValue[d] && litValue[d] < hi) {
        return 0; // a hole inside the interval
      }
    }
    int min = root[i].min();
    int max = root[i].max();
    if (lo > hi || lo <= min && hi >= max) {
      return 0;
    }
    int d = LiteralMap.NONE;
    if (lo == hi) {
      d = eq[i].get((int) lo);
    }
    if (d == LiteralMap.NONE && hi >= max) {
      return orZero(ge[i].get((int) lo), 1);
    }
    if (d == LiteralMap.NONE && lo <= min) {
      return orZero(ge[i].get((int) hi + 1), -1);
    }
    return orZero(d, 1);
  }

  private static int orZero(int d, int sign) {
    return d == LiteralMap.NONE ? 0 : sign * d;
  }

  /**
   * Makes {@link #minimize} look only for solutions better than the best one found outside this
   * solver, for example by another search of the same model in a parallel portfolio. The supplier
   * is read from the solver's thread whenever it takes clauses, and gives {@link Integer#MAX_VALUE}
   * as long as there is no such solution. When {@link #minimize} then ends without a better
   * solution, the best solution found outside is optimal.
   *
   * @param bound the objective value of the best solution found elsewhere
   */
  public void setSharedBound(IntSupplier bound) {
    sharedBound = bound;
  }

  /** Stops {@link #solve} and {@link #minimize}, also when called from another thread. */
  public void stop() {
    sat.cancel();
  }

  @Override
  public int[] externalClause() {
    if (structural.isEmpty() && sharedBound != null && objective >= 0 && !coreMode) {
      importBound();
    }
    return structural.poll();
  }

  /** Adds the clause that the objective is below a better bound found elsewhere. */
  private void importBound() {
    int shared = sharedBound.getAsInt();
    if (shared >= importedBound || (best != null && shared >= best[objective])) {
      return;
    }
    importedBound = shared;
    if (shared <= root[objective].min()) {
      sharedBoundUnreachable = true;
      sat.cancel();
    } else if (shared <= root[objective].max()) {
      // the literal first, so that its linking clauses come before the bound
      int lit = geLit(objective, shared);
      structural.add(new int[] {-lit}); // objective <= shared - 1
    }
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
        if (dimacsVar >= atomUse.length) {
          atomUse = Arrays.copyOf(atomUse, propagated.length);
        }
        if (atomUse[dimacsVar] == 0) {
          atomUse[dimacsVar] = 1;
          atomLiterals++;
        }
        atomsPropagated++;
        return lit;
      }
      if (numPending == 0 && !store.hasPendingConstraints()) {
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
      // the explanations, stronger than propagation at the root, prove the model unsatisfiable:
      // the empty clause follows, and so does any clause, here one false literal; the solver
      // backjumps to the root on it and then takes the empty clause
      int any = extra == 0 ? trueAtom() : extra;
      if (any == 0) {
        throw new IllegalStateException(
            "the constraints failed on the root domains: " + store.recentlyFailedConstraint);
      }
      structural.add(new int[0]);
      clause = new int[] {-any};
    }
    pushedReason = clause;
    return clause[0];
  }

  // a literal the solver has true, or 0 when it has assigned nothing
  private int trueAtom() {
    int n = sat.trailSize();
    return n == 0 ? 0 : sat.trailLiteral(n - 1);
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
   * Decides on the model's annotation in its runs while it has unfixed variables; otherwise, with
   * activity branching, on the most active unfixed variable, a 0/1 one while any is unfixed (unless
   * the system property {@code jacop.lcg.booleansFirst} is false, which branches on all variables
   * in one order of activity): its value in the last solution when still possible, else the lower
   * half of its domain (the system property {@code jacop.lcg.value} = {@code min} or {@code max}
   * picks its smallest or largest value instead). Without activity branching, leaves the decision
   * to the solver's VSIDS until every literal is assigned, then branches on {@code [x <= min]} of
   * the unfixed variable with the smallest domain.
   */
  @Override
  public int decide() {
    if (branching == Branching.AUTO
        && best == null
        && !activityBranching
        && sat.conflicts >= AUTO_CONFLICTS) {
      activityBranching = true; // no solution yet from the literals: activity until the first one
    }
    if (annotationRun) {
      int lit = annotationDecision();
      if (lit != 0) {
        annotationDecisions++;
        return lit;
      }
    }
    if (activityBranching) {
      return activityDecision();
    }
    return 0;
  }

  /**
   * Without activity branching, once the solver has assigned every literal, branches on {@code [x
   * <= min]} of the unfixed variable with the smallest domain.
   */
  @Override
  public int decideLast() {
    if (activityBranching || !structural.isEmpty()) {
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

  // the heap of a variable: lateHeap for a late variable, else wide for one that is not 0/1
  private void rebuildHeap(VarHeap h) {
    int[] members = new int[activity.length];
    int n = 0;
    for (int i = 0; i < activity.length; i++) {
      if (h.contains(i)) {
        members[n++] = i;
      }
    }
    h.rebuild(members, n);
  }

  private VarHeap heapOf(int i) {
    if (late[i]) {
      return lateHeap;
    }
    return split && (root[i].min() < 0 || root[i].max() > 1) ? wide : heap;
  }

  // takes the fixed variables off the top of a heap, to be put back on backtracking
  private void popFixed(VarHeap h) {
    while (!h.isEmpty() && vars[h.max()].singleton()) {
      if (numPopped == popped.length) {
        popped = Arrays.copyOf(popped, 2 * numPopped);
        poppedLevel = Arrays.copyOf(poppedLevel, 2 * numPopped);
      }
      popped[numPopped] = h.removeMax();
      poppedLevel[numPopped++] = sat.decisionLevel();
    }
  }

  private int activityDecision() {
    popFixed(heap);
    popFixed(wide);
    VarHeap h = heap.isEmpty() ? wide : heap;
    if (h.isEmpty()) {
      popFixed(lateHeap);
      h = lateHeap;
      if (h.isEmpty()) {
        return 0;
      }
    }
    int i = h.max();
    if (lastConflict
        && conflictVar >= 0
        && !vars[conflictVar].singleton()
        && heapOf(conflictVar) == h) {
      i = conflictVar; // last-conflict branching (Lecoutre et al. 2009)
    }
    conflictVar = -1;
    decisionVar = i;
    if (late[i]) {
      lateDecisions++;
    }
    IntVar x = vars[i];
    searchDecisions++;
    if (phase != null && x.domain.contains(phase[i])) {
      return eqVar(i, phase[i]);
    }
    return switch (valueChoice) {
      case "max" -> geLit(i, x.max());
      case "split" -> -geLit(i, x.min() + (x.max() - x.min()) / 2 + 1);
      default -> -geLit(i, x.min() + 1);
    };
  }

  /**
   * Sets the variables branched on by activity only after every other variable is fixed, such as
   * variables defined by a constraint from the others. Set them before solving.
   *
   * @param defined the variables to branch on last
   */
  public void setLateVariables(Iterable<? extends Var> defined) {
    for (Var v : defined) {
      int i = idOf(v);
      if (i >= 0 && !late[i]) {
        VarHeap h = heapOf(i);
        late[i] = true;
        lateVariables++;
        if (h.contains(i)) {
          h.remove(i);
          lateHeap.insert(i);
        }
      }
    }
  }

  private void bump(int i) {
    if (sat.conflicts != activityConflicts) {
      activityConflicts = sat.conflicts;
      activityInc /= 0.95;
    }
    if ((activity[i] += activityInc) > 1e100) {
      for (int k = 0; k < activity.length; k++) {
        activity[k] *= 1e-100;
      }
      activityInc *= 1e-100;
    }
    heapOf(i).increased(i);
  }

  /**
   * The annotation's next decision as a literal, or 0 when it has fixed all its variables or
   * chooses something that is not an atom of the store's integer variables.
   */
  private int annotationDecision() {
    Var v = annotation.getChoiceVariable(0);
    if (v instanceof Mirrored m) {
      // the left branch on a set variable's element is that the element is in the set
      int i = idOf(m.decisionVariable(annotation.getChoiceValue()));
      return i < 0 ? 0 : eqVar(i, 1);
    }
    if (v != null) {
      int i = idOf(v);
      if (i < 0) {
        return 0;
      }
      int value = annotation.getChoiceValue();
      return vars[i].domain.contains(value) ? eqVar(i, value) : 0;
    }
    PrimitiveConstraint c = annotation.getChoiceConstraint(0);
    if (!(c instanceof LinearExplainable l)) {
      return 0;
    }
    LinearForm f = l.linearForm();
    if (f == null || f.vars().length != 1 || Math.abs(f.weights()[0]) != 1) {
      return 0;
    }
    int i = idOf(f.vars()[0]);
    if (i < 0) {
      return 0;
    }
    long w = f.weights()[0];
    long bound = w * f.c(); // the relation on x itself, with LE and GE swapped for -x
    int relation = f.relation();
    if (w < 0 && relation == LinearForm.LE) {
      relation = LinearForm.GE;
    } else if (w < 0 && relation == LinearForm.GE) {
      relation = LinearForm.LE;
    }
    IntDomain d = vars[i].domain;
    if (bound < d.min() || bound > d.max()) {
      return 0;
    }
    int b = (int) bound;
    return switch (relation) {
      case LinearForm.LE -> b < d.max() ? -geLit(i, b + 1) : 0;
      case LinearForm.GE -> b > d.min() ? geLit(i, b) : 0;
      case LinearForm.EQ -> d.contains(b) ? eqVar(i, b) : 0;
      default -> d.contains(b) ? -eqVar(i, b) : 0;
    };
  }

  private int idOf(Var v) {
    if (!(v instanceof IntVar x) || x.singleton()) {
      return -1;
    }
    int i = trail.id(x);
    return i >= 0 && i < vars.length && vars[i] == x ? i : -1;
  }

  /**
   * Records a solution. When minimising, it then rejects the model with the clause that the
   * objective is smaller, unless the objective is at its smallest value.
   */
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
    // under core-guided search a solution need not improve on the best one
    boolean improving = objective < 0 || best == null || solution[objective] < best[objective];
    if (onSolution != null && improving) {
      onSolution.run();
    }
    if (objective < 0) {
      return true;
    }
    if (improving) {
      best = solution;
      phase = solution;
      if (branching == Branching.AUTO) {
        activityBranching = false; // the solver's saved phases now hold this solution
      }
      solutions++;
    }
    if (coreMode) {
      return true;
    }
    int v = solution[objective];
    if (v <= root[objective].min()) {
      return true;
    }
    // the literal first, so that its linking clauses come before the bound
    int lit = geLit(objective, v);
    structural.add(new int[] {-lit}); // objective <= v - 1
    return false;
  }
}
