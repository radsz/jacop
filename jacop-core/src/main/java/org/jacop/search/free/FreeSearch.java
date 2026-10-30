/*
 * FreeSearch.java
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

package org.jacop.search.free;

import java.time.Duration;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.IntSupplier;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DomainOperationHandler;
import org.jacop.search.IndomainMin;
import org.jacop.search.SearchHandlerRegistry;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.lns.AdaptiveLns;
import org.jacop.search.restart.Calculator;
import org.jacop.search.restart.GeometricCalculator;
import org.jacop.search.restart.RestartHook;

/**
 * A search engine for free search: depth-first search with binary branching, restarts,
 * branch-and-bound and hooks for learning heuristics.
 *
 * <p>Unlike {@link org.jacop.search.DepthFirstSearch} it keeps the decisions on an explicit stack,
 * so the depth of the search is not limited by the Java stack, and it sends every decision,
 * failure, restart and solution to its {@link SearchMonitor}s. It branches with any {@link
 * SelectChoicePoint}: a variable and a value ({@code x = v}, then {@code x != v}) or a primitive
 * constraint (the constraint, then its negation).
 *
 * <p>Restarts are counted in failures and follow a restart {@link Calculator}. For optimisation the
 * bound on the objective is imposed at the root after each solution, so the search is complete with
 * restarts: when a run explores its whole tree before its fail limit, the last solution is optimal,
 * or the problem has no solution.
 *
 * <p>With {@link Builder#probeObjective(double, long)} some runs are probes: they look for a
 * solution with the objective close to its lower bound ({@code cost <= lb + d} when minimising),
 * with a fail limit of their own. A probe that explores its whole tree proves that no such solution
 * exists and raises the lower bound for good; a probe that finds a solution finds one close to the
 * optimum. The offset {@code d} starts at 0 (objective lower-bound search) and doubles after each
 * refuted probe and halves after a probe that ran out of failures (objective shaving), as in the
 * {@code objective_lb_search} and {@code objective_shaving} workers of OR-Tools CP-SAT.
 *
 * <pre>{@code
 * FreeSearch search = FreeSearch.builder(store, select)
 *     .minimize(cost)
 *     .restarts(new LubyCalculator(100))
 *     .onSolution(s -> System.out.println(cost))
 *     .timeLimit(Duration.ofSeconds(10))
 *     .build();
 * FreeSearch.Status status = search.solve();
 * }</pre>
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class FreeSearch {

  /** How a search ended. */
  public enum Status {
    /** No solution exists. */
    UNSATISFIABLE,
    /** A solution was found; for optimisation it is not proven optimal. */
    SATISFIED,
    /** The search explored the whole space: the last solution is optimal, or all were found. */
    OPTIMAL,
    /** A limit was reached before any solution was found. */
    UNKNOWN
  }

  /** When a search with two branchings uses the alternative one. */
  public enum Alternation {
    /** Runs alternate between the two branchings, starting with the alternative one. */
    EVERY_RESTART,
    /** The alternative branching is used until the first solution, the main one afterwards. */
    UNTIL_FIRST_SOLUTION
  }

  /** The reason a run ended. */
  private enum RunEnd {
    EXHAUSTED,
    RESTART,
    STOP
  }

  /** A decision on the stack. */
  private static final class Frame {
    Var var;
    int value;
    PrimitiveConstraint choice;
    int firstIndex;
    int level;
    boolean right;
    boolean projected;
  }

  /** The fail limit of the first run of {@link #withDefaults(Store, IntVar[])}. */
  public static final int DEFAULT_RESTART_SCALE = 100;

  /** The growth of the fail limit from one run to the next in {@link #withDefaults}. */
  public static final double DEFAULT_RESTART_BASE = 1.5;

  /** The failures of a run that replays a solution found elsewhere. */
  public static final long IMPORT_FAIL_LIMIT = 100;

  private final Store store;
  private final SelectChoicePoint<? extends Var> mainSelect;
  private final SelectChoicePoint<? extends Var> alternative;
  private final Alternation alternation;
  private final boolean mainFirst;
  private SelectChoicePoint<? extends Var> select;
  private final IntVar cost;
  private final boolean maximize;
  private final Calculator restarts;
  private final boolean restartOnSolution;
  private final boolean resetRestartsOnSolution;
  private boolean runEndedBySolution;
  private final boolean allSolutions;
  private final long solutionLimit;
  private final long failLimit;
  private final long timeLimitMillis;
  private final Var[] recorded;
  private final Set<Var> projection;
  private final List<SearchMonitor> monitors;
  private final Consumer<FreeSearch> solutionHandler;
  private final IntSupplier sharedBound;
  // a better solution found elsewhere is replayed in a run of its own, with the bound at its value
  private final SharedSolution sharedSolution;
  private int importedObjective;
  private boolean importing;
  private long importRuns;
  private final boolean learnNogoods;
  private final int maxNogoods;
  private final int maxNogoodLength;
  private RestartNoGoods nogoods;
  private boolean runEndedByFailure;
  private IntVar[] nogoodVars = new IntVar[16];
  private int[] nogoodValues = new int[16];

  // large neighbourhood search: runs that fix variables to their values in the best solution
  private final AdaptiveLns lns;
  private final double lnsShare;
  private final long lnsFailLimit;
  private long lnsNanos;
  private long searchNanos;
  private long lnsRuns;
  // MiniZinc's on_restart: code that fixes variables at the root of every run
  private final RestartHook hook;
  private int hookStatus = RestartHook.START;
  // the run fixes variables at its root, so what it explores holds only under them
  private boolean conditionalRun;
  private long runSolutions;

  private final List<Frame> stack = new ArrayList<>();
  private int stackSize;
  private int rootLevel;
  private long deadline;
  // set by stop(), possibly from another thread
  private volatile boolean stopRequested;
  private boolean limitReached;

  private boolean hasBound;
  private int bound;

  // objective probing (lower-bound search and shaving); probeShare 0 turns it off
  private final double probeShare;
  private long probeLimit;
  private int probeOffset;
  private boolean probing;
  private int probeTarget;
  private long probeFailures;
  private long probeRuns;
  private long probesRefuted;
  private long regularRuns;
  private int[] lastSolution;
  private int lastCost;

  private long nodes;
  private long decisions;
  private long failures;
  private long runFailures;
  private long restartCount;
  private long solutions;
  private int maxDepth;

  private FreeSearch(Builder builder) {
    store = builder.store;
    mainSelect = builder.select;
    alternative = builder.alternative;
    alternation = builder.alternation;
    mainFirst = builder.mainFirst;
    select = mainSelect;
    cost = builder.cost;
    maximize = builder.maximize;
    allSolutions = builder.allSolutions && cost == null;
    // restarts would find the same solutions again
    restarts = allSolutions ? null : builder.restarts;
    restartOnSolution = builder.restartOnSolution && restarts != null;
    resetRestartsOnSolution = builder.resetRestartsOnSolution;
    solutionLimit = builder.solutionLimit;
    failLimit = builder.failLimit;
    timeLimitMillis = builder.timeLimitMillis;
    recorded = builder.recorded == null ? new Var[0] : builder.recorded;
    projection =
        builder.projection == null ? null : Collections.newSetFromMap(new IdentityHashMap<>());
    if (projection != null) {
      projection.addAll(Arrays.asList(builder.projection));
    }
    monitors = List.copyOf(builder.monitors);
    solutionHandler = builder.solutionHandler;
    sharedBound = cost == null ? null : builder.sharedBound;
    importedObjective = maximize ? Integer.MIN_VALUE : Integer.MAX_VALUE;
    learnNogoods = builder.nogoods && restarts != null;
    maxNogoods = builder.maxNogoods;
    maxNogoodLength = builder.maxNogoodLength;
    hook = builder.hook;
    // the model's own neighbourhoods replace those of large neighbourhood search and probes
    lns = hook == null && cost != null && restarts != null ? builder.lns : null;
    lnsShare = builder.lnsShare;
    lnsFailLimit = builder.lnsFailLimit;
    probeShare = hook == null && cost != null && restarts != null ? builder.probeShare : 0;
    probeLimit = builder.probeFailLimit;
    // the model's own runs fix their variables at the root of each run
    sharedSolution =
        hook == null && cost != null && restarts != null ? builder.sharedSolution : null;
  }

  /**
   * Starts building a search.
   *
   * @param store the store with the model.
   * @param select the branching: variable and value selection, or constraint choices.
   * @return the builder.
   */
  public static Builder builder(Store store, SelectChoicePoint<? extends Var> select) {
    return new Builder(store, select);
  }

  /**
   * Starts building a search with the default free search heuristics: dom/wdeg over the given
   * variables with last conflict, the value of the last solution or else the minimum, geometric
   * restarts counted in failures with nogoods learned at each restart, and a restart after each
   * solution for optimisation. For optimisation, leave the objective out of the variables when it
   * is defined by them.
   *
   * @param store the store with the model.
   * @param vars the variables to branch on.
   * @return the builder, to which an objective, limits and a solution handler can be added.
   */
  public static Builder withDefaults(Store store, IntVar[] vars) {
    IndomainLastSolution values = new IndomainLastSolution(vars, new IndomainMin<>());
    DomWdeg domWdeg = new DomWdeg(vars, values);
    LastConflict lastConflict = new LastConflict(domWdeg, values, 1);
    return builder(store, lastConflict)
        .monitor(values)
        .monitor(domWdeg)
        .monitor(lastConflict)
        .restarts(new GeometricCalculator(DEFAULT_RESTART_BASE, DEFAULT_RESTART_SCALE))
        .restartOnSolution(true)
        .nogoodsFromRestarts(true);
  }

  /**
   * Runs the search. The store is left at the level it was at before the call; the values of the
   * recorded variables in the last solution are available from {@link #getSolution()}.
   *
   * @return how the search ended.
   */
  public Status solve() {
    deadline = timeLimitMillis > 0 ? System.currentTimeMillis() + timeLimitMillis : Long.MAX_VALUE;
    int startLevel = store.level;
    boolean exhausted = false;
    try {
      // changes made at the root stay in a level of their own, removed at the end
      store.setLevel(startLevel + 1);
      rootLevel = store.level;
      if (learnNogoods) {
        nogoods = new RestartNoGoods(store, maxNogoods, maxNogoodLength);
        store.impose(nogoods);
      }
      if (!store.consistency()) {
        exhausted = true;
      } else {
        for (SearchMonitor m : monitors) {
          m.onStart(this);
        }
        exhausted = runs();
      }
    } finally {
      unwind();
      // the level where a conditional run fixed its variables
      while (store.level > rootLevel) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }
      if (nogoods != null) {
        nogoods.detach();
      }
      store.removeLevel(rootLevel);
      store.setLevel(startLevel);
    }
    if (exhausted) {
      return solutions > 0 ? Status.OPTIMAL : Status.UNSATISFIABLE;
    }
    return solutions > 0 ? Status.SATISFIED : Status.UNKNOWN;
  }

  /** Runs until a run explores its whole tree (returns true) or the search stops (false). */
  private boolean runs() {
    while (true) {
      runFailures = 0;
      runSolutions = 0;
      if (hook != null && hook.completeMarked()) {
        return true;
      }
      // a probe propagates above the root, so what the nogoods and bounds just added there must be
      // propagated at the root first; otherwise the end of the probe would undo it
      if (probeShare > 0 && !store.consistency()) {
        return true;
      }
      importing = startImport();
      boolean importRun = importing;
      probing = !importRun && startProbe();
      boolean probe = probing;
      select = probe || importRun ? mainSelect : branchingOfRun();
      // the time before the first solution is not shared with neighbourhoods, nor that of probes
      boolean afterSolution = !probe && !importRun && lns != null && lns.ready();
      boolean lnsRun = afterSolution && lnsNanos < lnsShare * searchNanos;
      conditionalRun = !probe && (importRun || lnsRun || hook != null);
      long start = System.nanoTime();
      RunEnd end;
      if (conditionalRun) {
        end = conditionalRun(lnsRun);
      } else {
        end = run();
      }
      if (lnsRun) {
        lnsNanos += System.nanoTime() - start;
      } else if (afterSolution) {
        searchNanos += System.nanoTime() - start;
      }
      if (probe) {
        if (endProbe(end)) {
          return true;
        }
        if (end == RunEnd.EXHAUSTED) {
          continue;
        }
      }
      if (end == RunEnd.EXHAUSTED && !conditionalRun) {
        return true;
      }
      if (end == RunEnd.STOP) {
        return false;
      }
      restartCount++;
      int depth = stackSize;
      unwind();
      if (importRun) {
        // like a probe, it is not a run of the restart policy nor of the heuristics
        importing = false;
        store.removeLevel(rootLevel + 1);
        store.setLevel(rootLevel);
        continue;
      }
      if (probe) {
        // the nogoods of a probe hold only under its bound on the objective, and the monitors
        // count restarts of the regular runs (dom/wdeg flushes its weights every k of them)
        continue;
      }
      if (conditionalRun) {
        store.removeLevel(rootLevel + 1);
        store.setLevel(rootLevel);
        endConditionalRun(lnsRun, end);
      } else if (nogoods != null) {
        // the decisions of a conditional run hold only under the variables fixed at its root
        learnNogoods(depth);
      }
      for (SearchMonitor m : monitors) {
        m.onRestart(this);
      }
      regularRuns++;
      if (restarts != null) {
        if (runEndedBySolution && resetRestartsOnSolution) {
          restarts.reset();
        } else if (!lnsRun) {
          restarts.newLimit();
        }
      }
    }
  }

  /**
   * Decides whether the next run replays a solution found elsewhere: one better than the best of
   * this search and not replayed before. Its run looks for solutions as good as it, not better, so
   * that the replayed solution becomes the best of this search.
   */
  private boolean startImport() {
    if (sharedSolution == null) {
      return false;
    }
    int shared = sharedSolution.objective();
    if (shared == (maximize ? Integer.MIN_VALUE : Integer.MAX_VALUE)
        || shared == importedObjective
        || (solutions > 0 && (maximize ? shared <= lastCost : shared >= lastCost))) {
      return false;
    }
    importedObjective = shared;
    importRuns++;
    hasBound = true;
    bound = shared;
    return true;
  }

  /**
   * Decides whether the next run is a probe and, if so, sets its target and opens the level of its
   * bound. A probe runs when the failures spent in probes are below their share of the others and
   * the target is tighter than the bound of a regular run.
   */
  private boolean startProbe() {
    if (probeShare <= 0 || probeFailures > probeShare * (failures - probeFailures)) {
      return false;
    }
    // the best value the objective can still take, a bound proven at the root
    long target;
    if (maximize) {
      target = (long) cost.max() - probeOffset;
      if (target <= (hasBound ? bound : cost.min())) {
        return false;
      }
    } else {
      target = (long) cost.min() + probeOffset;
      if (target >= (hasBound ? bound : cost.max())) {
        return false;
      }
    }
    probeTarget = (int) target;
    probeRuns++;
    // the bound of the probe is imposed at a level of its own, removed when the probe ends
    store.setLevel(rootLevel + 1);
    return true;
  }

  /**
   * Ends a probe: removes its level and, when it explored its whole tree, raises the lower bound of
   * the objective at the root. Adapts the offset and the fail limit of the next probe. Returns true
   * when raising the bound left no solution, so the search is complete.
   */
  private boolean endProbe(RunEnd end) {
    int limit = probeLimit();
    probing = false;
    unwind();
    store.removeLevel(rootLevel + 1);
    store.setLevel(rootLevel);
    store.recentlyFailedConstraint = null;
    if (end == RunEnd.EXHAUSTED) {
      // no solution has the objective within the probe's limit
      probesRefuted++;
      probeOffset = probeOffset >= (1 << 29) ? probeOffset : 2 * probeOffset + 1;
      try {
        if (maximize) {
          cost.domain.inMax(rootLevel, cost, limit - 1);
        } else {
          cost.domain.inMin(rootLevel, cost, limit + 1);
        }
        return !store.consistency();
      } catch (FailException e) {
        store.recentlyFailedConstraint = null;
        return true;
      }
    }
    if (end == RunEnd.RESTART && !runEndedBySolution) {
      probeOffset /= 2;
      probeLimit += probeLimit / 2;
    }
    return false;
  }

  /** The limit on the objective in the current probe: its target, or the bound if tighter. */
  private int probeLimit() {
    if (!hasBound) {
      return probeTarget;
    }
    return maximize ? Math.max(probeTarget, bound) : Math.min(probeTarget, bound);
  }

  /**
   * Runs at a level above the root where the hook or a neighbourhood fixes variables. The root is
   * propagated first, at its own level: nogoods learned at the last restart prune there, and
   * constraints that trail their state (tables) would lose what they learn from those prunings if
   * they first saw them at the run's level, which is removed. A failure there proves that no better
   * solution exists.
   */
  private RunEnd conditionalRun(boolean lnsRun) {
    if (!propagate()) {
      store.recentlyFailedConstraint = null;
      conditionalRun = false;
      return RunEnd.EXHAUSTED;
    }
    store.setLevel(rootLevel + 1);
    try {
      if (importing) {
        sharedSolution.impose(store);
      } else if (lnsRun) {
        lnsRuns++;
        IntVar[] xs = lns.variables();
        for (int k : lns.neighbourhood()) {
          if (xs[k].domain.contains(lns.value(k))) {
            xs[k].domain.inValue(store.level, xs[k], lns.value(k));
          }
        }
      } else {
        hook.restart(store, hookStatus);
      }
    } catch (FailException _) {
      store.recentlyFailedConstraint = null;
      runEndedBySolution = false;
      runEndedByFailure = false;
      return RunEnd.EXHAUSTED;
    }
    return run();
  }

  /** Tells the neighbourhoods or the hook how a conditional run ended. */
  private void endConditionalRun(boolean lnsRun, RunEnd end) {
    if (lnsRun) {
      AdaptiveLns.Outcome outcome;
      if (runSolutions > 0) {
        outcome = AdaptiveLns.Outcome.IMPROVED;
      } else if (end == RunEnd.EXHAUSTED) {
        outcome = AdaptiveLns.Outcome.EXHAUSTED;
      } else {
        outcome = AdaptiveLns.Outcome.LIMIT;
      }
      lns.outcome(outcome);
    } else if (hook != null) {
      // until the first solution the status stays START, as in Chuffed
      if (runSolutions > 0) {
        hookStatus = RestartHook.SAT;
      } else if (solutions > 0) {
        hookStatus = end == RunEnd.EXHAUSTED ? RestartHook.UNSAT : RestartHook.UNKNOWN;
      }
    }
  }

  /**
   * Turns the decisions of the run that just ended into reduced nld-nogoods (Lecoutre et al. 2007)
   * and adds them at the root. Each refuted left branch {@code x = v}, the frames whose right
   * branch was taken and the top frame when the run ended on a failure, gives the nogood made of
   * the positive decisions above it and {@code x = v}. Constraint decisions cannot be expressed: a
   * positive one ends the nogoods of the path, a negative one gives no nogood.
   */
  private void learnNogoods(int depth) {
    int positives = 0;
    try {
      for (int i = 0; i < depth; i++) {
        Frame f = stack.get(i);
        boolean refuted = f.right || (i == depth - 1 && runEndedByFailure);
        if (!(f.var instanceof IntVar x)) {
          if (refuted) {
            continue;
          }
          return;
        }
        if (positives == nogoodVars.length) {
          nogoodVars = Arrays.copyOf(nogoodVars, 2 * positives + 16);
          nogoodValues = Arrays.copyOf(nogoodValues, 2 * positives + 16);
        }
        nogoodVars[positives] = x;
        nogoodValues[positives] = f.value;
        if (refuted) {
          nogoods.add(nogoodVars, nogoodValues, positives + 1);
        } else {
          positives++;
        }
      }
    } catch (FailException _) {
      // a nogood emptied a domain at the root: the next run fails at once and ends the search
      store.recentlyFailedConstraint = null;
      nogoods.add(nogoodVars, nogoodValues, 0);
    }
  }

  private SelectChoicePoint<? extends Var> branchingOfRun() {
    if (alternative == null) {
      return mainSelect;
    }
    boolean useAlternative =
        alternation == Alternation.EVERY_RESTART
            ? (regularRuns + (mainFirst ? 1 : 0)) % 2 == 0
            : solutions == 0 && !mainFirst;
    return useAlternative ? alternative : mainSelect;
  }

  private RunEnd run() {
    runEndedByFailure = false;
    runEndedBySolution = false;
    int nextIndex = 0;
    boolean consistent = propagate();
    Frame failedFrame = null;
    while (true) {
      if (consistent) {
        if (outOfLimits()) {
          return RunEnd.STOP;
        }
        Frame frame = choose(nextIndex);
        if (frame == null) {
          RunEnd end = solution();
          if (end != null) {
            return end;
          }
          // backtrack from the solution without counting a failure
          skipUnprojected();
          if (backtrack()) {
            return RunEnd.EXHAUSTED;
          }
          failedFrame = top();
          consistent = rightBranch();
          nextIndex = failedFrame.firstIndex;
          continue;
        }
        consistent = leftBranch(frame);
        nextIndex = select.getIndex();
        failedFrame = frame;
        continue;
      }
      failures++;
      runFailures++;
      if (probing) {
        probeFailures++;
      }
      Var decision = failedFrame == null ? null : failedFrame.var;
      // failures under the alternative branching would teach the heuristics of the main one
      // about a search they do not make, and so would the failures of a probe, whose bound on
      // the objective is not part of the problem
      if (select == mainSelect && !probing) {
        for (SearchMonitor m : monitors) {
          m.onFailure(store.recentlyFailedConstraint, decision);
        }
      }
      store.recentlyFailedConstraint = null;
      if (outOfLimits()) {
        return RunEnd.STOP;
      }
      // a run whose tree is explored is a proof, even at its fail limit
      if (backtrack()) {
        return RunEnd.EXHAUSTED;
      }
      if (restarts != null && runFailures >= runFailLimit()) {
        runEndedByFailure = true;
        return RunEnd.RESTART;
      }
      failedFrame = top();
      consistent = rightBranch();
      nextIndex = failedFrame.firstIndex;
    }
  }

  private long runFailLimit() {
    if (probing) {
      return probeLimit;
    }
    if (importing) {
      return IMPORT_FAIL_LIMIT;
    }
    return conditionalRun && hook == null ? lnsFailLimit : restarts.getFailLimit();
  }

  /**
   * Undoes decisions until the top frame has a right branch to explore. Returns true when there is
   * none left, so the run explored its whole tree.
   */
  private boolean backtrack() {
    while (stackSize > 0) {
      Frame f = top();
      store.removeLevel(f.level);
      if (!f.right && (f.choice != null || !f.var.singleton())) {
        return false;
      }
      stackSize--;
      store.setLevel(f.level - 1);
    }
    return true;
  }

  /**
   * After a solution, removes the decisions on variables outside the projection: other values of
   * them would only repeat the solution.
   */
  private void skipUnprojected() {
    while (stackSize > 0 && !top().projected) {
      Frame f = stack.get(--stackSize);
      store.removeLevel(f.level);
      store.setLevel(f.level - 1);
    }
  }

  /** Removes all decisions, back to the root level. */
  private void unwind() {
    while (stackSize > 0) {
      Frame f = stack.get(--stackSize);
      store.removeLevel(f.level);
      store.setLevel(f.level - 1);
    }
  }

  private Frame top() {
    return stack.get(stackSize - 1);
  }

  /** Selects the next decision, or returns null when all variables of the branching are fixed. */
  private Frame choose(int firstIndex) {
    Var var = select.getChoiceVariable(firstIndex);
    PrimitiveConstraint choice = null;
    int value = 0;
    if (var != null) {
      value = select.getChoiceValue();
    } else {
      choice = select.getChoiceConstraint(firstIndex);
      if (choice == null) {
        return null;
      }
    }
    if (stackSize == stack.size()) {
      stack.add(new Frame());
    }
    Frame f = stack.get(stackSize++);
    f.var = var;
    f.value = value;
    f.choice = choice;
    f.firstIndex = firstIndex;
    f.right = false;
    f.projected =
        projection == null
            || (var != null
                ? projection.contains(var)
                : projection.containsAll(choice.arguments()));
    store.setLevel(store.level + 1);
    f.level = store.level;
    maxDepth = Math.max(maxDepth, stackSize);
    return f;
  }

  private boolean leftBranch(Frame f) {
    decisions++;
    try {
      if (f.var != null) {
        if (f.var instanceof IntVar v) {
          v.domain.inValue(store.level, v, f.value);
        } else {
          handler(f.var).inValue(store, f.var, f.value, true);
        }
        for (SearchMonitor m : monitors) {
          m.onDecision(f.var, f.value, true);
        }
      } else {
        store.impose(f.choice);
        for (SearchMonitor m : monitors) {
          m.onDecision(f.choice, true);
        }
      }
    } catch (FailException e) {
      return false;
    }
    return propagate();
  }

  /** Explores the right branch of the top frame, at the frame's level. */
  private boolean rightBranch() {
    Frame f = top();
    f.right = true;
    store.setLevel(f.level);
    try {
      if (f.var != null) {
        if (f.var instanceof IntVar v) {
          v.domain.inComplement(store.level, v, f.value);
        } else {
          handler(f.var).inComplement(store, f.var, f.value, true);
        }
        for (SearchMonitor m : monitors) {
          m.onDecision(f.var, f.value, false);
        }
      } else {
        store.impose(new Not(f.choice));
        for (SearchMonitor m : monitors) {
          m.onDecision(f.choice, false);
        }
      }
    } catch (FailException e) {
      return false;
    }
    return propagate();
  }

  private static DomainOperationHandler handler(Var v) {
    DomainOperationHandler h = SearchHandlerRegistry.getInstance().findDomainHandler(v);
    if (h == null) {
      throw new IllegalArgumentException("No domain operation handler for variable " + v);
    }
    return h;
  }

  /** Imposes the objective bound and propagates the current node. */
  private boolean propagate() {
    nodes++;
    if (sharedBound != null && !importing) {
      importBound();
    }
    if (hasBound || probing) {
      int limit = probing ? probeLimit() : bound;
      try {
        if (maximize) {
          if (cost.min() < limit) {
            cost.domain.inMin(store.level, cost, limit);
          }
        } else if (cost.max() > limit) {
          cost.domain.inMax(store.level, cost, limit);
        }
      } catch (FailException e) {
        store.recentlyFailedConstraint = null;
        return false;
      }
    }
    return store.consistency();
  }

  /** Takes the objective value of a better solution found elsewhere as the bound. */
  private void importBound() {
    int shared = sharedBound.getAsInt();
    if (maximize) {
      if (shared != Integer.MIN_VALUE && (!hasBound || shared >= bound)) {
        hasBound = true;
        bound = shared + 1;
      }
    } else if (shared != Integer.MAX_VALUE && (!hasBound || shared <= bound)) {
      hasBound = true;
      bound = shared - 1;
    }
  }

  /**
   * Handles a solution. Returns how the run ends, or null when the search continues by
   * backtracking.
   */
  private RunEnd solution() {
    solutions++;
    if (lastSolution == null) {
      lastSolution = new int[recorded.length];
    }
    for (int i = 0; i < recorded.length; i++) {
      lastSolution[i] = recorded[i] instanceof IntVar v ? v.min() : 0;
    }
    if (cost != null) {
      lastCost = maximize ? cost.max() : cost.min();
      hasBound = true;
      bound = maximize ? lastCost + 1 : lastCost - 1;
    }
    runSolutions++;
    if (lns != null) {
      lns.solution();
    }
    if (hook != null) {
      hook.solution();
    }
    for (SearchMonitor m : monitors) {
      m.onSolution(this);
    }
    if (solutionHandler != null) {
      solutionHandler.accept(this);
    }
    if (stopRequested || (solutionLimit > 0 && solutions >= solutionLimit)) {
      return RunEnd.STOP;
    }
    if (cost == null && !allSolutions) {
      return RunEnd.STOP;
    }
    if (cost != null && restartOnSolution) {
      runEndedBySolution = true;
      return RunEnd.RESTART;
    }
    return null;
  }

  private boolean outOfLimits() {
    if (stopRequested) {
      return true;
    }
    if ((failLimit > 0 && failures >= failLimit)
        // the clock is read at every node: one node can take seconds when propagation is costly
        || System.currentTimeMillis() > deadline) {
      limitReached = true;
      return true;
    }
    return false;
  }

  /**
   * Asks the search to stop at the next node; it can be called from a solution handler or from
   * another thread.
   */
  public void stop() {
    stopRequested = true;
  }

  /**
   * Imposes the values of the last solution on the recorded variables, at the current store level.
   *
   * @return false if there is no solution or imposing it fails.
   */
  public boolean assignSolution() {
    if (lastSolution == null) {
      return false;
    }
    try {
      for (int i = 0; i < recorded.length; i++) {
        if (recorded[i] instanceof IntVar v) {
          v.domain.in(store.level, v, lastSolution[i], lastSolution[i]);
        }
      }
    } catch (FailException e) {
      return false;
    }
    return store.consistency();
  }

  /**
   * Returns the values of the recorded integer variables in the last solution, in the order given
   * to {@link Builder#record(Var...)}.
   *
   * @return the values, or null if no solution was found.
   */
  public int[] getSolution() {
    return lastSolution == null ? null : lastSolution.clone();
  }

  /**
   * Returns the objective value of the last solution.
   *
   * @return the objective value; meaningless if there is no objective or no solution.
   */
  public int getCostValue() {
    return lastCost;
  }

  /**
   * Returns the store the search works on.
   *
   * @return the store.
   */
  public Store getStore() {
    return store;
  }

  /**
   * Returns whether a time or fail limit stopped the search.
   *
   * @return true if a limit was reached.
   */
  public boolean limitReached() {
    return limitReached;
  }

  /**
   * Returns the number of nodes (propagations of a search node).
   *
   * @return the number of nodes.
   */
  public long getNodes() {
    return nodes;
  }

  /**
   * Returns the number of decisions (left branches).
   *
   * @return the number of decisions.
   */
  public long getDecisions() {
    return decisions;
  }

  /**
   * Returns the number of failures.
   *
   * @return the number of failures.
   */
  public long getFailures() {
    return failures;
  }

  /**
   * Returns the number of restarts.
   *
   * @return the number of restarts.
   */
  public long getRestarts() {
    return restartCount;
  }

  /**
   * Returns the number of solutions found.
   *
   * @return the number of solutions.
   */
  public long getSolutions() {
    return solutions;
  }

  /**
   * Returns the number of nogoods learned from restarts, including those that pruned at the root at
   * once.
   *
   * @return the number of nogoods.
   */
  public long getNogoods() {
    return nogoods == null ? 0 : nogoods.getAdded();
  }

  /**
   * Returns the number of probe runs of {@link Builder#probeObjective(double, long)}.
   *
   * @return the number of probes.
   */
  public long getProbes() {
    return probeRuns;
  }

  /**
   * Returns the number of probes that explored their whole tree and so raised the lower bound of
   * the objective.
   *
   * @return the number of refuted probes.
   */
  public long getProbesRefuted() {
    return probesRefuted;
  }

  /**
   * Returns the number of failures spent in probe runs.
   *
   * @return the failures of probes.
   */
  public long getProbeFailures() {
    return probeFailures;
  }

  /**
   * Returns the number of runs that replayed a solution found elsewhere.
   *
   * @return the number of runs.
   */
  public long getImportRuns() {
    return importRuns;
  }

  /**
   * Returns the number of runs in large neighbourhoods.
   *
   * @return the number of runs.
   */
  public long getLnsRuns() {
    return lnsRuns;
  }

  /**
   * Returns the largest number of decisions on the stack.
   *
   * @return the peak depth.
   */
  public int getMaxDepth() {
    return maxDepth;
  }

  /**
   * Returns the current number of decisions on the stack.
   *
   * @return the depth.
   */
  public int getDepth() {
    return stackSize;
  }

  /** Builds a {@link FreeSearch}. */
  public static final class Builder {

    private final Store store;
    private final SelectChoicePoint<? extends Var> select;
    private SelectChoicePoint<? extends Var> alternative;
    private boolean mainFirst;
    private Alternation alternation;
    private IntVar cost;
    private boolean maximize;
    private Calculator restarts;
    private boolean restartOnSolution;
    private boolean resetRestartsOnSolution;
    private boolean allSolutions;
    private long solutionLimit;
    private long failLimit;
    private long timeLimitMillis;
    private Var[] recorded;
    private Var[] projection;
    private final List<SearchMonitor> monitors = new ArrayList<>();
    private Consumer<FreeSearch> solutionHandler;
    private IntSupplier sharedBound;
    private SharedSolution sharedSolution;
    private boolean nogoods;
    private int maxNogoods = RestartNoGoods.DEFAULT_MAX_NOGOODS;
    private int maxNogoodLength = RestartNoGoods.DEFAULT_MAX_LENGTH;
    private double probeShare;
    private long probeFailLimit;
    private AdaptiveLns lns;
    private double lnsShare;
    private long lnsFailLimit;
    private RestartHook hook;

    private Builder(Store store, SelectChoicePoint<? extends Var> select) {
      this.store = store;
      this.select = select;
    }

    /**
     * Minimises the given variable.
     *
     * @param cost the objective.
     * @return this builder.
     */
    public Builder minimize(IntVar cost) {
      this.cost = cost;
      this.maximize = false;
      return this;
    }

    /**
     * Maximises the given variable.
     *
     * @param cost the objective.
     * @return this builder.
     */
    public Builder maximize(IntVar cost) {
      this.cost = cost;
      this.maximize = true;
      return this;
    }

    /**
     * Interleaves another branching with the main one across restarts, for example the search
     * annotation of a model with free search. The alternative branching must fix all the variables
     * that the main one fixes. Monitors see the failures of runs with the main branching only, so
     * learning heuristics are not trained on the alternative one; they see all solutions.
     *
     * @param select the alternative branching.
     * @param when when the alternative branching is used.
     * @return this builder.
     */
    public Builder alternateWith(SelectChoicePoint<? extends Var> select, Alternation when) {
      this.alternative = select;
      this.alternation = when;
      return this;
    }

    /**
     * Makes the first run use the main branching even when there is an alternative one, for example
     * when its value heuristic has been given a solution as a hint.
     *
     * @param main true to start with the main branching.
     * @return this builder.
     */
    public Builder mainBranchingFirst(boolean main) {
      this.mainFirst = main;
      return this;
    }

    /**
     * Restarts the search when a run reaches the fail limit given by the calculator; null (the
     * default) means no restarts.
     *
     * @param calculator the restart policy, for example a Luby or geometric calculator.
     * @return this builder.
     */
    public Builder restarts(Calculator calculator) {
      this.restarts = calculator;
      return this;
    }

    /**
     * Learns nogoods from the decisions of each run when it restarts, so later runs do not explore
     * the refuted parts of the search again. It needs restarts and works on decisions {@code x = v}
     * on integer variables.
     *
     * @param learn true to learn nogoods.
     * @return this builder.
     */
    public Builder nogoodsFromRestarts(boolean learn) {
      this.nogoods = learn;
      return this;
    }

    /**
     * Sets the limits of the nogood store of {@link #nogoodsFromRestarts(boolean)}.
     *
     * @param max the largest number of nogoods kept; the oldest half is deleted beyond it.
     * @param maxLength the largest number of literals of a nogood; longer ones are not kept.
     * @return this builder.
     */
    public Builder nogoodLimits(int max, int maxLength) {
      this.maxNogoods = max;
      this.maxNogoodLength = maxLength;
      return this;
    }

    /**
     * For optimisation with restarts, spends a share of the time in runs in large neighbourhoods of
     * the best solution: from the first solution on, a run fixes the variables outside a
     * neighbourhood to their values in the best solution, and ends at its own fail limit or at an
     * improvement. Such runs learn no nogoods and prove nothing when they explore their whole tree.
     * A {@link #restartHook(RestartHook)} turns them off.
     *
     * @param neighbourhoods the neighbourhoods.
     * @param share the time of runs in neighbourhoods per unit of time of the other runs.
     * @param failLimit the failures of one run in a neighbourhood.
     * @return this builder.
     */
    public Builder lns(AdaptiveLns neighbourhoods, double share, long failLimit) {
      this.lns = neighbourhoods;
      this.lnsShare = share;
      this.lnsFailLimit = Math.max(1, failLimit);
      return this;
    }

    /**
     * Runs code at the root of every run, for MiniZinc's on_restart: it fixes variables that depend
     * on the outcome of the last run and on the best solution. Every run is then conditional on
     * what the hook fixed, so it learns no nogoods, and the search ends when the hook marks it
     * complete, when the bound on the objective fails at the root, or at a limit.
     *
     * @param restartHook the hook.
     * @return this builder.
     */
    public Builder restartHook(RestartHook restartHook) {
      this.hook = restartHook;
      return this;
    }

    /**
     * For optimisation with restarts, restarts after each solution.
     *
     * @param restart true to restart after each solution.
     * @return this builder.
     */
    public Builder restartOnSolution(boolean restart) {
      this.restartOnSolution = restart;
      return this;
    }

    /**
     * With {@link #restartOnSolution(boolean)}, starts the sequence of fail limits again after each
     * solution, so the runs after an improvement are short again (as in Choco).
     *
     * @param reset true to reset the restart limits after each solution.
     * @return this builder.
     */
    public Builder resetRestartsOnSolution(boolean reset) {
      this.resetRestartsOnSolution = reset;
      return this;
    }

    /**
     * For optimisation with restarts, makes some runs probes that look for a solution with the
     * objective at its lower bound, or a growing offset above it (below the upper bound when
     * maximising). A probe that explores its whole tree raises the lower bound for good. Probes
     * take about {@code share} failures per failure of the regular runs.
     *
     * @param share failures of probes per failure of regular runs; 0 (the default) turns probes
     *     off.
     * @param failLimit the fail limit of the first probe, growing by half after each probe that
     *     reaches it.
     * @return this builder.
     */
    public Builder probeObjective(double share, long failLimit) {
      if (share < 0 || failLimit < 1) {
        throw new IllegalArgumentException("The share must be >= 0 and the fail limit >= 1");
      }
      this.probeShare = share;
      this.probeFailLimit = failLimit;
      return this;
    }

    /**
     * For satisfaction, finds all solutions instead of the first one. Restarts are not used then.
     *
     * @param all true to find all solutions.
     * @return this builder.
     */
    public Builder allSolutions(boolean all) {
      this.allSolutions = all;
      return this;
    }

    /**
     * With {@link #allSolutions(boolean)}, reports solutions that differ in the given variables
     * only, once each: after a solution the search does not try other values of the other
     * variables. The branching must fix the given variables before the others, for example with a
     * {@link org.jacop.search.SequenceSelect} whose first selection is on them.
     *
     * @param vars the variables that tell solutions apart.
     * @return this builder.
     */
    public Builder distinctOn(Var... vars) {
      this.projection = vars.clone();
      return this;
    }

    /**
     * Stops after the given number of solutions; 0 (the default) means no limit.
     *
     * @param limit the number of solutions.
     * @return this builder.
     */
    public Builder solutionLimit(long limit) {
      this.solutionLimit = limit;
      return this;
    }

    /**
     * Stops after the given number of failures; 0 (the default) means no limit.
     *
     * @param limit the number of failures.
     * @return this builder.
     */
    public Builder failLimit(long limit) {
      this.failLimit = limit;
      return this;
    }

    /**
     * Stops after the given wall-clock time.
     *
     * @param limit the time limit.
     * @return this builder.
     */
    public Builder timeLimit(Duration limit) {
      this.timeLimitMillis = limit.toMillis();
      return this;
    }

    /**
     * Records the values of these variables at each solution, for {@link FreeSearch#getSolution()}
     * and {@link FreeSearch#assignSolution()}.
     *
     * @param vars the variables.
     * @return this builder.
     */
    public Builder record(Var... vars) {
      this.recorded = vars.clone();
      return this;
    }

    /**
     * Adds a monitor that receives the events of the search.
     *
     * @param monitor the monitor.
     * @return this builder.
     */
    public Builder monitor(SearchMonitor monitor) {
      monitors.add(monitor);
      return this;
    }

    /**
     * Calls the handler at each solution, with the store in the solution state.
     *
     * @param handler the handler.
     * @return this builder.
     */
    public Builder onSolution(Consumer<FreeSearch> handler) {
      this.solutionHandler = handler;
      return this;
    }

    /**
     * For optimisation, reads at every node the objective value of the best solution found outside
     * this search, for example by another search of the same model in a parallel portfolio, and
     * looks only for better solutions. The supplier gives {@link Integer#MAX_VALUE} when minimising
     * ({@link Integer#MIN_VALUE} when maximising) as long as there is none, and is called from the
     * thread of the search. When the search then explores its whole space, the best solution found
     * outside or by this search is optimal.
     *
     * @param bound the objective value of the best solution found elsewhere.
     * @return this builder.
     */
    public Builder sharedBound(IntSupplier bound) {
      this.sharedBound = bound;
      return this;
    }

    /**
     * For optimisation with restarts, replays a solution found outside this search when it is
     * better than the best one of this search: a run of its own fixes the variables to their values
     * in it and searches for at most {@value FreeSearch#IMPORT_FAIL_LIMIT} failures. The replayed
     * solution then becomes the best of this search, from which its large neighbourhoods and the
     * values of the last solution start. Usually given with {@link #sharedBound(IntSupplier)} for
     * the same source.
     *
     * @param solution the best solution found elsewhere.
     * @return this builder.
     */
    public Builder sharedSolution(SharedSolution solution) {
      this.sharedSolution = solution;
      return this;
    }

    /**
     * Builds the search.
     *
     * @return the search.
     */
    public FreeSearch build() {
      if (store == null || select == null) {
        throw new IllegalArgumentException("A store and a branching are required");
      }
      if (hook != null && (restarts == null || allSolutions && cost == null)) {
        throw new IllegalArgumentException("A restart hook needs restarts");
      }
      return new FreeSearch(this);
    }
  }
}
