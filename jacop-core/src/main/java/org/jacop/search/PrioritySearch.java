/*
 * PrioritySearch.java
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

package org.jacop.search;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.List;
import java.util.Map;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.XltC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.restart.Calculator;

/**
 * PrioritySearch selects first a row in the matrix based on metric of the variable at the pririty
 * vector. As soon as a row is choosen, variables are selected for indomain method. The row
 * selection is done with the help of pririty variable comparatos. Two comparators can be employed
 * main and tiebreaking one. If two are not sufficient to differentiate two rows than the
 * lexigraphical ordering is used.
 *
 * <p>Based on paper "Priority Search with MiniZinc" by Thibaut Feydy, Adrian Goldwaser, Andreas
 * Schutt, Peter J. Stuckey,and Kenneth D. Young, in ModRef'2017: The Sixtenth International
 * Workshop on Constraint Modelling and Reformulation at CP 2017.
 *
 * @param <T> type of variable being used in the Search.
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
@SuppressWarnings("serial")
public class PrioritySearch<T extends Var> extends DepthFirstSearch<T> {

  static final boolean DEBUG_ALL = false;

  int n; // length of priority variables and sub-vectors
  T[] priority;
  ComparatorVariable<T> comparator;
  ComparatorVariable<T> tieBreak;

  List<DepthFirstSearch<T>> search;

  BitSet visited;

  List<T> allVars;

  int noSolutions;

  int solutionsLimit = -1; // Integer.MAX_VALUE;
  boolean solutionsReached;

  private static final String SOLUTION_COST_IS = "Solution cost is {}";

  /**
   * It constructs a PrioritySearch.
   *
   * @param priority prority variables used to select a sub-vector of vars (row)
   * @param dfs vector of depth first searches to be selected from; they must have SelectChoicePoint
   *     set.
   * @param comparator the variable comparator to choose the proper sub.search. // * @param indomain
   *     variable ordering value to be used to determine value for a given variable.
   */
  public PrioritySearch(T[] priority, ComparatorVariable<T> comparator, DepthFirstSearch<T>[] dfs) {
    int pLength = priority.length;
    int vLength = dfs.length;
    if (pLength != vLength) {
      throw new RuntimeException(
          "length of priority variables and depth first searches must be the same");
    }

    n = priority.length;
    this.priority = priority;
    this.comparator = comparator;
    this.visited = new BitSet(n);

    search = new ArrayList<>(2 * dfs.length);
    for (int i = 0; i < 2 * dfs.length; i++) {
      search.add(null);
    }
    for (int i = 0; i < n; i++) {

      dfs[i].setMasterSearch(this);
      search.set(2 * i, dfs[i]);
      if (!(dfs[i] instanceof PrioritySearch) && dfs[i].heuristic == null) {
        throw new RuntimeException("heuristic in depth first search must be set");
      }

      LinkingSearch<T> linkingSearch = new LinkingSearch<>(this);
      search.set(2 * i + 1, linkingSearch);
      DepthFirstSearch<T> last = lastSearch(dfs[i]);
      last.addChildSearch(linkingSearch);
      linkingSearch.setMasterSearch(last);
    }
    this.allVars = getVariables(this);
  }

  /**
   * It constructs a PrioritySearch.
   *
   * @param priority prority variables used to select a sub-vector of vars (row)
   * @param dfs vector of depth first searches to be selected from; they must have SelectChoicePoint
   *     set.
   * @param comparator the variable comparator to choose the proper sub.search.
   * @param tieBreak the variable tie breaking comparator to choose the proper sub.search.
   */
  public PrioritySearch(
      T[] priority,
      ComparatorVariable<T> comparator,
      ComparatorVariable<T> tieBreak,
      DepthFirstSearch<T>[] dfs) {
    this(priority, comparator, dfs);

    this.tieBreak = tieBreak;
  }

  @SuppressWarnings("unchecked")
  private DepthFirstSearch<T> asDfs(Search<? extends Var> s) {
    return (DepthFirstSearch<T>) s;
  }

  DepthFirstSearch<T> lastSearch(DepthFirstSearch<T> dfs) {
    DepthFirstSearch<T> ns = dfs;
    DepthFirstSearch<T> lastNotNullSearch;

    do {
      lastNotNullSearch = ns;
      // find next search
      if (ns.childSearches == null) {
        ns = null;
      } else {
        ns = asDfs(ns.childSearches[0]);
      }
    } while (ns != null);

    return lastNotNullSearch;
  }

  /**
   * Initializes the search before labeling: sets store, solution listener variables, and handles
   * level raising.
   *
   * @param store the constraint store
   * @return true if level was raised, false otherwise
   */
  private boolean initializeSearch(Store store) {
    this.store = store;
    ((SimpleSolutionListener<T>) solutionListener).setVariables(allVars);

    for (DepthFirstSearch<T> dfs : search) {
      dfs.setStore(store);
    }

    boolean raisedLevel = false;
    if (store.raiseLevelBeforeConsistency) {
      store.raiseLevelBeforeConsistency = false;
      store.setLevel(store.level + 1);
      raisedLevel = true;
    }

    depth = store.level;
    return raisedLevel;
  }

  /**
   * Executes consistency check and sub-search selection, handling solution limit exceptions.
   *
   * @param collectStatistics whether to collect statistics after solution limit exception
   * @return true if consistency check passed, false otherwise
   */
  private boolean executeSubSearch(boolean collectStatistics) {
    if (initializeListener != null) {
      initializeListener.executedAtInitialize(store);
    }

    final boolean result = store.consistency();
    store.setLevel(store.level + 1);
    depth = store.level;

    visited.clear();
    int subSearch = getSubSearch();
    visited.set(subSearch);

    if (result) {
      try {
        search.get(2 * subSearch).labeling();
      } catch (SolutionsLimitReached _) {
        if (collectStatistics) {
          getStatistics();
        }
        solutionsReached = true;
        if (printInfo) {
          log.info("Solution limit {} reached", solutionsLimit);
        }
      }

      visited.set(subSearch, false);
    }

    store.removeLevel(store.level);
    store.setLevel(store.level - 1);
    depth--;

    return result;
  }

  /**
   * Executes consistency check and sub-search selection, returning the sub-search result.
   *
   * @param collectStatistics whether to collect statistics after solution limit exception
   * @return the result from sub-search labeling, or false if consistency check failed
   */
  private boolean executeSubSearchWithResult(boolean collectStatistics) {
    if (initializeListener != null) {
      initializeListener.executedAtInitialize(store);
    }

    boolean result = store.consistency();
    store.setLevel(store.level + 1);
    depth = store.level;

    visited.clear();
    int subSearch = getSubSearch();
    visited.set(subSearch);

    if (result) {
      try {
        result = search.get(2 * subSearch).labeling();
      } catch (SolutionsLimitReached _) {
        if (collectStatistics) {
          getStatistics();
        }
        solutionsReached = true;
        if (printInfo) {
          log.info("Solution limit {} reached", solutionsLimit);
        }
      }

      visited.set(subSearch, false);
    }

    store.removeLevel(store.level);
    store.setLevel(store.level - 1);
    depth--;

    return result;
  }

  /**
   * Finalizes search execution: collects statistics, checks timeout, and prints results.
   *
   * @param raisedLevel whether level was raised during initialization
   * @param exitSolutionCount the solution count to pass to exit listener
   * @return true if solutions were found, false otherwise
   */
  private boolean finalizeSearch(boolean raisedLevel, int exitSolutionCount) {
    getStatistics();
    notifyExitListener(exitSolutionCount);
    aggregateTimeoutFromSubSearches();
    logTimeoutIfOccurred();
    if (noSolutions > 0) {
      return finalizeWithSolutionsFound(raisedLevel);
    }
    return finalizeWithNoSolutions(raisedLevel);
  }

  private void notifyExitListener(int exitSolutionCount) {
    if (exitListener != null) {
      exitListener.executedAtExit(store, exitSolutionCount);
    }
  }

  private void aggregateTimeoutFromSubSearches() {
    for (int i = 0; i < n; i++) {
      timeOutOccured |= search.get(2 * i).timeOutOccured;
    }
  }

  private void logTimeoutIfOccurred() {
    if (timeOutOccured && printInfo) {
      log.info("Time-out {}s", tOut);
    }
  }

  private boolean finalizeWithSolutionsFound(boolean raisedLevel) {
    if (assignSolution) {
      assignSolution();
    }
    logSolutionCostIfNeeded();
    if (printInfo) {
      log.info("{}", statistics());
    }
    restoreStoreLevelIfRaised(raisedLevel);
    return true;
  }

  private void logSolutionCostIfNeeded() {
    if (printInfo && costVariable != null) {
      CostVariableHandler costHandler =
          SearchHandlerRegistry.getInstance().findCostHandler(costVariable);
      if (costHandler != null) {
        double costValue = costHandler.getCostValue(costVariable);
        log.info(SOLUTION_COST_IS, costValue);
      } else if (costVariable instanceof IntVar) {
        log.info(SOLUTION_COST_IS, search.getFirst().costValue);
      }
    }
  }

  private void restoreStoreLevelIfRaised(boolean raisedLevel) {
    if (raisedLevel) {
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
    }
  }

  private boolean finalizeWithNoSolutions(boolean raisedLevel) {
    if (printInfo) {
      log.info("No solution found.");
      log.info("{}", statistics());
    }
    restoreStoreLevelIfRaised(raisedLevel);
    return false;
  }

  /** {@inheritDoc} */
  public boolean labeling(Store store, SelectChoicePoint<T> select) {

    heuristic = select;
    return labeling(store);
  }

  /**
   * Starts the labeling process using this search's configured sub-searches.
   *
   * @param store the constraint store.
   * @return {@code true} if at least one solution was found, {@code false} otherwise.
   */
  public boolean labeling(Store store) {

    boolean raisedLevel = initializeSearch(store);

    if (costVariable == null) {
      optimize = false;
    }

    executeSubSearch(false);

    return finalizeSearch(raisedLevel, noSolutions);
  }

  /**
   * Starts the labeling process with optimization of the given cost variable.
   *
   * @param store the constraint store.
   * @param select the choice point selector (ignored, sub-searches have their own selectors).
   * @param costVar the cost variable to optimize.
   * @return true if at least one solution was found, false otherwise.
   */
  public boolean labeling(Store store, SelectChoicePoint<T> select, Var costVar) {

    return labeling(store, costVar);
  }

  /**
   * Starts the labeling process with optimization of the given cost variable.
   *
   * @param store the constraint store.
   * @param costVar the cost variable to optimize.
   * @return true if at least one solution was found, false otherwise.
   */
  public boolean labeling(Store store, Var costVar) {

    boolean raisedLevel = initializeSearch(store);

    if (solutionsLimit == -1) {
      solutionsLimit = Integer.MAX_VALUE;
    }

    for (DepthFirstSearch<T> dfs : search) {
      DepthFirstSearch<T> ns = dfs;
      do {
        ns.setCostVar(costVar);
        ns.respectSolutionListenerAdvice = true;
        // find next search
        ns = ns.childSearches == null ? null : asDfs(ns.childSearches[0]);
      } while (ns != null);
    }

    depth = store.level;
    costVariable = costVar;
    for (int i = 0; i < n; i++) {
      search.get(2 * i).costVariable = costVar;
    }
    optimize = true;
    cost = null;

    executeSubSearch(true);

    return finalizeSearch(raisedLevel, noSolutions);
  }

  /** {@inheritDoc} */
  public boolean labeling() {

    boolean raisedLevel = initializeSearch(allVars.getFirst().getStore());
    configureCostVariableForLabeling();
    depth = store.level;
    cost = null;

    boolean result = executeSubSearchWithResult(true);
    return labelingPostExecution(raisedLevel, result);
  }

  private void configureCostVariableForLabeling() {
    if (costVariable != null) {
      for (DepthFirstSearch<T> dfs : search) {
        dfs.setCostVar(costVariable);
        dfs.respectSolutionListenerAdvice = true;
        dfs.costVariable = costVariable;
      }
      optimize = true;
      cost = null;
      if (solutionsLimit == -1) {
        solutionsLimit = Integer.MAX_VALUE;
      }
    }
    if (costVariable == null) {
      optimize = false;
    }
  }

  private boolean labelingPostExecution(boolean raisedLevel, boolean result) {
    getStatistics();
    notifyExitListener(solutionListener.solutionsNo());
    aggregateTimeoutFromSubSearches();
    logTimeoutIfOccurred();
    if (noSolutions > 0) {
      return labelingWithSolutionsFound(raisedLevel, result);
    }
    return labelingWithNoSolutions(raisedLevel);
  }

  private boolean labelingWithSolutionsFound(boolean raisedLevel, boolean result) {
    ((SimpleSolutionListener<?>) solutionListener).setSolutionsNo(noSolutions);
    if (assignSolution) {
      assignSolution();
    }
    if (printInfo && costVariable != null && costVariable instanceof IntVar) {
      log.info(SOLUTION_COST_IS, costValue);
    }
    if (printInfo) {
      log.info("{}", statistics());
    }
    restoreStoreLevelIfRaised(raisedLevel);
    return masterSearch == null ? true : result;
  }

  private boolean labelingWithNoSolutions(boolean raisedLevel) {
    if (printInfo) {
      log.info("No solution found.");
      log.info("{}", statistics());
    }
    restoreStoreLevelIfRaised(raisedLevel);
    return false;
  }

  @Override
  public boolean label(int n) {
    throw new RuntimeException("Method label is not defined for PrioritySearch.");
  }

  private int getStatistic(java.util.function.ToIntFunction<Search<?>> getter) {
    int result = 0;
    for (DepthFirstSearch<T> l : search) {
      result += getter.applyAsInt(l);
      if (l.childSearches != null) {
        result += getter.applyAsInt(l.childSearches[0]);
      }
    }
    return result;
  }

  @Override
  public int getNodes() {
    return nodes = getStatistic(Search::getNodes);
  }

  @Override
  public int getDecisions() {
    return decisions = getStatistic(Search::getDecisions);
  }

  @Override
  public int getWrongDecisions() {
    return wrongDecisions = getStatistic(Search::getWrongDecisions);
  }

  @Override
  public int getBacktracks() {
    return numberBacktracks = getStatistic(Search::getBacktracks);
  }

  @Override
  public int getMaximumDepth() {
    return maxDepthExcludePaths = getStatistic(Search::getMaximumDepth);
  }

  /** Collects and aggregates search statistics from all sub-searches. */
  public void getStatistics() {

    nodes = getNodes();
    decisions = getDecisions();
    wrongDecisions = getWrongDecisions();
    numberBacktracks = getBacktracks();
    maxDepthExcludePaths = getMaximumDepth();
  }

  String statistics() {

    return "No solutions : "
        + noSolutions
        + "\n"
        + "Nodes : "
        + nodes
        + "\n"
        + "Decisions : "
        + decisions
        + "\n"
        + "Wrong Decisions : "
        + wrongDecisions
        + "\n"
        + "Backtracks : "
        + numberBacktracks
        + "\n"
        + "Max Depth : "
        + maxDepthExcludePaths
        + "\n";
  }

  /**
   * Sets the cost variable for optimization.
   *
   * @param cost the cost variable.
   */
  public void setCostVariable(Var cost) {
    costVariable = cost;
  }

  int getSubSearch() {

    int current = 0;
    while (current < n && visited.get(current)) {
      current++;
    }
    if (current == n) {
      return n;
    }

    if (comparator != null) {
      double currentMeasure = comparator.metric(priority[current]);
      for (int i = current + 1; i < n; i++) {
        if (!visited.get(i)) {
          if (comparator.compare(currentMeasure, priority[i]) < 0) {
            current = i;
            currentMeasure = comparator.metric(priority[current]);
          } else if (tieBreak != null
              && comparator.compare(currentMeasure, priority[i]) == 0
              && tieBreak.compare(currentMeasure, priority[i]) < 0) {
            current = i;
          }
        }
      }
    }

    return current;
  }

  /**
   * Collects all variables from all sub-searches of the given PrioritySearch.
   *
   * @param ps the PrioritySearch to collect variables from.
   * @return list of all variables across all sub-searches.
   */
  public List<T> getVariables(PrioritySearch<T> ps) {

    List<T> vars = new ArrayList<>();

    for (int i = 0; i < ps.search.size() / 2; i++) {
      SelectChoicePoint<T> heuristic = ps.search.get(2 * i).heuristic;

      if (heuristic == null) {
        // PrioritySearch
        List<T> vs = null;
        for (int j = 0; j < ps.search.size() / 2; j++) {
          vs = getVariables((PrioritySearch<T>) ps.search.get(2 * j));
        }

        vars.addAll(vs);

      } else {
        Map<T, Integer> position = heuristic.getVariablesMapping();

        vars.addAll(position.keySet());
      }
    }

    return vars;
  }

  /**
   * Adds a restart calculator as a consistency listener to all sub-searches.
   *
   * @param s the search to add the restart calculator to.
   * @param calc the restart calculator to add.
   */
  public void addRestartCalculator(DepthFirstSearch<T> s, Calculator calc) {

    List<DepthFirstSearch<T>> searchList;
    if (s instanceof PrioritySearch<T> prioritySearch) {
      searchList = prioritySearch.getSearchSeq();
    } else {
      searchList = List.of(s);
    }

    for (DepthFirstSearch<T> dfs : searchList) {
      if (dfs instanceof PrioritySearch<T> prioritySearch) {
        for (int i = 0; i < prioritySearch.search.size() / 2; i++) {
          addRestartCalculator(prioritySearch.search.get(2 * i), calc);
        }
      } else {
        ConsistencyListener consist = dfs.getConsistencyListener();
        dfs.setConsistencyListener(calc);
        dfs.consistencyListener.setChildrenListeners(consist);
      }
    }
  }

  /**
   * Sets the maximum number of solutions to find.
   *
   * @param no the solution limit.
   */
  public void setSolutionLimit(int no) {
    solutionsLimit = no;
  }

  /**
   * Returns the list of sub-searches used by this priority search.
   *
   * @return the list of depth first searches.
   */
  public List<DepthFirstSearch<T>> getSearchSeq() {
    return search;
  }

  /** {@inheritDoc} */
  public String toString() {
    StringBuilder b = new StringBuilder();

    b.append("PrioritySearch(")
        .append(Arrays.asList(priority))
        .append(", ")
        .append(comparator.getClass().getName());

    if (tieBreak == null) {
      b.append(", null");
    } else {
      b.append(", ").append(tieBreak.getClass().getName());
    }

    b.append(", [");
    for (int i = 0; i < search.size() / 2; i++) {
      b.append(search.get(2 * i)).append(", ");
    }
    b.append("])");

    return b.toString();
  }

  /**
   * Returns the number of solutions found during the search.
   *
   * @return the number of solutions found.
   */
  public int noSolutions() {
    return noSolutions;
  }

  static final class SolutionsLimitReached extends RuntimeException {

    SolutionsLimitReached() {}
  }

  class LinkingSearch<T extends Var> extends DepthFirstSearch<T> {

    final DepthFirstSearch<T> master;

    /** Last child search run in the child loop (used when no early return). */
    DepthFirstSearch<T> lastChildSearchRun;

    LinkingSearch(DepthFirstSearch<T> m) {
      master = m;
    }

    @SuppressWarnings("unchecked")
    private void updateIntVarCost(int newCost, int costValueForSearch) {
      if (newCost < costValue) {
        costValue = newCost;
        master.costValue = newCost;

        for (int i = 0; i < n; i++) {
          DepthFirstSearch<T> ls = (DepthFirstSearch<T>) lastSearch(search.get(2 * i));
          ls.costValue = costValueForSearch;
          ls.cost = new XltC((IntVar) search.get(2 * i).costVariable, newCost);
        }
      }
    }

    @SuppressWarnings("unchecked")
    private void updateIntVarCost(int newCost) {
      updateIntVarCost(newCost, newCost);
    }

    @SuppressWarnings("unchecked")
    private void updateFloatCost(double newCost, CostVariableHandler costHandler) {
      if (costHandler.isBetterCost(costValueFloat, newCost, true)) {
        costValueFloat = newCost;
        master.costValueFloat = newCost;

        for (int i = 0; i < n; i++) {
          DepthFirstSearch<T> ls = (DepthFirstSearch<T>) lastSearch(search.get(2 * i));
          ls.costValueFloat = costHandler.getCostValue(search.get(2 * i).costVariable);
          ls.cost = costHandler.createCostConstraint(search.get(2 * i).costVariable, newCost);
        }
      }
    }

    @SuppressWarnings("unchecked")
    void constraineCost() {
      if (costVariable instanceof IntVar v) {
        int newCost = v.dom().max();
        updateIntVarCost(newCost, v.dom().max());
      } else {
        CostVariableHandler costHandler =
            SearchHandlerRegistry.getInstance().findCostHandler(costVariable);
        if (costHandler != null) {
          double newCost = costHandler.getCostValue(costVariable);
          updateFloatCost(newCost, costHandler);
        }
      }
    }

    @SuppressWarnings("unchecked")
    void constraineCostFromChild(DepthFirstSearch<T> child) {
      if (costVariable instanceof IntVar) {
        int newCost = child.costValue;
        updateIntVarCost(newCost);
      } else {
        CostVariableHandler costHandler =
            SearchHandlerRegistry.getInstance().findCostHandler(costVariable);
        if (costHandler != null) {
          double newCost = child.costValueFloat;
          updateFloatCost(newCost, costHandler);
        }
      }
    }

    @SuppressWarnings("unchecked")
    public boolean labeling() {
      int index = getSubSearch();
      if (index < n) {
        return runSubSearchLabeling(index);
      }
      return labelingAtPriorityLevel(index);
    }

    private boolean runSubSearchLabeling(int index) {
      visited.set(index);
      boolean result = search.get(2 * index).labeling();
      visited.set(index, false);
      return result;
    }

    @SuppressWarnings("unchecked")
    private boolean labelingAtPriorityLevel(int index) {
      if (costVariable != null) {
        return labelingWithCost(index);
      }
      if (master.childSearches != null) {
        return labelingNoCostWithChildSearches(index);
      }
      return labelingNoCostNoChildSearches(index);
    }

    @SuppressWarnings("unchecked")
    private boolean labelingWithCost(int index) {
      if (master.childSearches != null) {
        Boolean earlyReturn = runChildSearchesWithCost(index);
        if (earlyReturn != null) {
          return earlyReturn;
        }
        noSolutions += lastChildSearchRun.getSolutionListener().solutionsNo();
        constraineCostFromChild(lastChildSearchRun);
      } else {
        constraineCost();
        noSolutions++;
      }
      return finishLabelingAfterSolution(index);
    }

    @SuppressWarnings("unchecked")
    private Boolean runChildSearchesWithCost(int index) {
      lastChildSearchRun = null;
      for (Search<? extends Var> childObj : master.childSearches) {
        DepthFirstSearch<T> child = (DepthFirstSearch<T>) asDfs(childObj);
        lastChildSearchRun = child;
        child.setStore(store);
        child.getSolutionListener().setParentSolutionListener(solutionListener);
        child.setCostVar(costVariable);
        int currentChildSolutionNo = child.getSolutionListener().solutionsNo();
        boolean result = child.labeling();
        if (result) {
          break;
        }
        if (child.getSolutionListener().solutionsNo() > currentChildSolutionNo) {
          noSolutions = child.getSolutionListener().solutionsNo();
          constraineCostFromChild(child);
          if (noSolutions >= solutionsLimit) {
            throw new SolutionsLimitReached();
          }
          master.solutionListener.executeAfterSolution(this, null);
          visited.set(index, false);
          return false;
        }
      }
      return null;
    }

    @SuppressWarnings("unchecked")
    private Boolean runChildSearchesNoCost(int index) {
      lastChildSearchRun = null;
      for (Search<? extends Var> childObj : master.childSearches) {
        DepthFirstSearch<T> child = (DepthFirstSearch<T>) asDfs(childObj);
        lastChildSearchRun = child;
        child.setStore(store);
        child.getSolutionListener().setParentSolutionListener(solutionListener);
        int currentChildSolutionNo = child.getSolutionListener().solutionsNo();
        boolean result = child.labeling();
        if (result) {
          break;
        }
        if (child.getSolutionListener().solutionsNo() > currentChildSolutionNo) {
          noSolutions = child.getSolutionListener().solutionsNo();
          if (noSolutions >= solutionsLimit) {
            throw new SolutionsLimitReached();
          }
          master.solutionListener.executeAfterSolution(this, null);
          visited.set(index, false);
          return false;
        }
      }
      return null;
    }

    private boolean finishLabelingAfterSolution(int index) {
      if (noSolutions >= solutionsLimit) {
        throw new SolutionsLimitReached();
      }
      master.solutionListener.executeAfterSolution(this, null);
      visited.set(index, false);
      return false;
    }

    @SuppressWarnings("unchecked")
    private boolean labelingNoCostWithChildSearches(int index) {
      Boolean earlyReturn = runChildSearchesNoCost(index);
      if (earlyReturn != null) {
        return earlyReturn;
      }
      noSolutions += lastChildSearchRun.getSolutionListener().solutionsNo();
      if (noSolutions >= solutionsLimit) {
        throw new SolutionsLimitReached();
      }
      master.solutionListener.executeAfterSolution(this, null);
      visited.set(index, false);
      return false;
    }

    private boolean labelingNoCostNoChildSearches(int index) {
      noSolutions++;
      master.solutionListener.executeAfterSolution(this, null);
      if (noSolutions >= solutionsLimit) {
        throw new SolutionsLimitReached();
      }
      visited.set(index, false);
      return false;
    }
  }
}
