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
import org.jacop.search.restart.Calculator;
import org.jacop.search.restart.GeometricCalculator;

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

  private final Store store;
  private final SelectChoicePoint<? extends Var> mainSelect;
  private final SelectChoicePoint<? extends Var> alternative;
  private final Alternation alternation;
  private SelectChoicePoint<? extends Var> select;
  private final IntVar cost;
  private final boolean maximize;
  private final Calculator restarts;
  private final boolean restartOnSolution;
  private final boolean allSolutions;
  private final long solutionLimit;
  private final long failLimit;
  private final long timeLimitMillis;
  private final Var[] recorded;
  private final Set<Var> projection;
  private final List<SearchMonitor> monitors;
  private final Consumer<FreeSearch> solutionHandler;

  private final List<Frame> stack = new ArrayList<>();
  private int stackSize;
  private int rootLevel;
  private long deadline;
  private boolean stopRequested;
  private boolean limitReached;

  private boolean hasBound;
  private int bound;
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
    select = mainSelect;
    cost = builder.cost;
    maximize = builder.maximize;
    allSolutions = builder.allSolutions && cost == null;
    // restarts would find the same solutions again
    restarts = allSolutions ? null : builder.restarts;
    restartOnSolution = builder.restartOnSolution && restarts != null;
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
   * restarts counted in failures, and a restart after each solution for optimisation. For
   * optimisation, leave the objective out of the variables when it is defined by them.
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
        .restartOnSolution(true);
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
      select = branchingOfRun();
      RunEnd end = run();
      if (end == RunEnd.EXHAUSTED) {
        return true;
      }
      if (end == RunEnd.STOP) {
        return false;
      }
      restartCount++;
      unwind();
      for (SearchMonitor m : monitors) {
        m.onRestart(this);
      }
      if (restarts != null) {
        restarts.newLimit();
      }
    }
  }

  private SelectChoicePoint<? extends Var> branchingOfRun() {
    if (alternative == null) {
      return mainSelect;
    }
    boolean useAlternative =
        alternation == Alternation.EVERY_RESTART ? restartCount % 2 == 0 : solutions == 0;
    return useAlternative ? alternative : mainSelect;
  }

  private RunEnd run() {
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
      Var decision = failedFrame == null ? null : failedFrame.var;
      // failures under the alternative branching would teach the heuristics of the main one
      // about a search they do not make
      if (select == mainSelect) {
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
      if (restarts != null && runFailures >= restarts.getFailLimit()) {
        return RunEnd.RESTART;
      }
      failedFrame = top();
      consistent = rightBranch();
      nextIndex = failedFrame.firstIndex;
    }
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
    if (hasBound) {
      try {
        if (maximize) {
          if (cost.min() < bound) {
            cost.domain.inMin(store.level, cost, bound);
          }
        } else if (cost.max() > bound) {
          cost.domain.inMax(store.level, cost, bound);
        }
      } catch (FailException e) {
        store.recentlyFailedConstraint = null;
        return false;
      }
    }
    return store.consistency();
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
      return RunEnd.RESTART;
    }
    return null;
  }

  private boolean outOfLimits() {
    if (stopRequested) {
      return true;
    }
    if ((failLimit > 0 && failures >= failLimit)
        || ((nodes & 0xff) == 0 && System.currentTimeMillis() > deadline)) {
      limitReached = true;
      return true;
    }
    return false;
  }

  /** Asks the search to stop at the next node; it can be called from a solution handler. */
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
    private Alternation alternation;
    private IntVar cost;
    private boolean maximize;
    private Calculator restarts;
    private boolean restartOnSolution;
    private boolean allSolutions;
    private long solutionLimit;
    private long failLimit;
    private long timeLimitMillis;
    private Var[] recorded;
    private Var[] projection;
    private final List<SearchMonitor> monitors = new ArrayList<>();
    private Consumer<FreeSearch> solutionHandler;

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
     * Builds the search.
     *
     * @return the search.
     */
    public FreeSearch build() {
      if (store == null || select == null) {
        throw new IllegalArgumentException("A store and a branching are required");
      }
      return new FreeSearch(this);
    }
  }
}
