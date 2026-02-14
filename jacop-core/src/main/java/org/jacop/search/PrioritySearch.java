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

  static final boolean debugAll = false;

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
      if (!"org.jacop.search.PrioritySearch".equals(dfs[i].getClass().getName())
          && dfs[i].heuristic == null) {
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

    this.store = store;
    ((SimpleSolutionListener<T>) solutionListener).setVariables(allVars);

    for (DepthFirstSearch<T> dfs : search) {
      dfs.setStore(store);
    }

    if (store.raiseLevelBeforeConsistency) {
      store.raiseLevelBeforeConsistency = false;
      store.setLevel(store.level + 1);
    }

    depth = store.level;

    if (costVariable == null) {
      optimize = false;
    }

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

    if (exitListener != null) {
      exitListener.executedAtExit(store, noSolutions);
    }

    for (int i = 0; i < n; i++) {
      timeOutOccured |= search.get(2 * i).timeOutOccured;
    }

    if (timeOutOccured && printInfo) {
      log.info("Time-out {}s", tOut);
    }

    if (noSolutions > 0) {

      if (assignSolution) {
        assignSolution();
      }

      if (printInfo) {
        log.info("{}", statistics());
      }

      return true;
    } else {

      if (printInfo) {

        log.info("No solution found.");

        log.info(
            "Depth First Search {}\n\nNodes : {}\nDecisions : {}\nWrong Decisions : {}\nBacktracks : {}\nMax Depth : {}",
            searchId,
            nodes,
            decisions,
            wrongDecisions,
            numberBacktracks,
            maxDepthExcludePaths);
      }

      return false;
    }
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

    this.store = store;
    ((SimpleSolutionListener<T>) solutionListener).setVariables(allVars);

    if (solutionsLimit == -1) {
      solutionsLimit = Integer.MAX_VALUE;
    }

    for (DepthFirstSearch<T> dfs : search) {
      DepthFirstSearch<T> ns = dfs;
      do {
        ns.setStore(store);
        ns.setCostVar(costVar);
        ns.respectSolutionListenerAdvice = true;
        // find next search
        ns = ns.childSearches == null ? null : asDfs(ns.childSearches[0]);
      } while (ns != null);
    }

    if (store.raiseLevelBeforeConsistency) {
      store.raiseLevelBeforeConsistency = false;
      store.setLevel(store.level + 1);
    }

    // heuristic = select;  // has selection already
    depth = store.level;
    costVariable = costVar;
    for (int i = 0; i < n; i++) {
      search.get(2 * i).costVariable = costVar;
    }
    optimize = true;
    cost = null;

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
        getStatistics();

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

    getStatistics();

    if (exitListener != null) {
      exitListener.executedAtExit(store, noSolutions);
    }

    for (int i = 0; i < n; i++) {
      timeOutOccured |= search.get(2 * i).timeOutOccured;
    }

    if (timeOutOccured && printInfo) {
      log.info("Time-out {}s", tOut);
    }

    if (noSolutions > 0) {

      if (assignSolution) {
        assignSolution();
      }

      if (printInfo) {
        CostVariableHandler costHandler =
            SearchHandlerRegistry.getInstance().findCostHandler(costVariable);
        if (costHandler != null) {
          double costValue = costHandler.getCostValue(costVariable);
          log.info("Solution cost is {}", costValue);
        } else if (costVariable instanceof IntVar) {
          log.info("Solution cost is {}", search.getFirst().costValue);
        }
      }

      if (printInfo) {
        log.info("{}", statistics());
      }

      return true;

    } else {

      if (printInfo) {

        log.info("No solution found.");

        log.info("{}", statistics());
      }

      return false;
    }
  }

  /** {@inheritDoc} */
  public boolean labeling() {

    this.store = allVars.getFirst().getStore();
    ((SimpleSolutionListener<T>) solutionListener).setVariables(allVars);

    for (DepthFirstSearch<T> dfs : search) {
      dfs.setStore(store);
    }

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

    boolean raisedLevel = false;

    if (store.raiseLevelBeforeConsistency) {
      store.raiseLevelBeforeConsistency = false;
      store.setLevel(store.level + 1);
      raisedLevel = true;
    }

    depth = store.level;
    cost = null;

    if (costVariable == null) {
      optimize = false;
    }

    if (initializeListener != null) {
      initializeListener.executedAtInitialize(store);
    }

    // Iterative Solution listener sets it to zero so it can find the next batch, so it has to be
    // executed
    // after initialize listener.

    // If constraints employ only one time execution of the part of
    // the consistency technique then the results of that part must be
    // stored in one level above the level search starts from as this
    // can be removed.
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
        getStatistics();

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

    getStatistics();

    if (exitListener != null) {
      exitListener.executedAtExit(store, solutionListener.solutionsNo());
    }

    for (int i = 0; i < n; i++) {
      timeOutOccured |= search.get(2 * i).timeOutOccured;
    }

    if (timeOutOccured && printInfo) {
      log.info("Time-out {}s", tOut);
    }

    if (noSolutions > 0) {
      // update number solutions in solution listener; otherwise it will be zero :(
      ((SimpleSolutionListener<?>) solutionListener).setSolutionsNo(noSolutions);

      if (printInfo && costVariable != null && costVariable instanceof IntVar) {
        log.info("Solution cost is {}", costValue);
      }

      if (printInfo) {
        log.info("{}", statistics());
      }

      if (raisedLevel) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }

      if (masterSearch == null) {
        return true;
      } else {
        return result;
      }

    } else {

      if (printInfo) {

        log.info("No solution found.");

        log.info("{}", statistics());
      }

      if (raisedLevel) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }

      return false;
    }
  }

  @Override
  public boolean label(int n) {
    throw new RuntimeException("Method label is not defined for PrioritySearch.");
  }

  @Override
  public int getNodes() {
    nodes = 0;
    for (DepthFirstSearch<T> l : search) {
      nodes += l.getNodes();

      if (l.childSearches != null) {
        nodes += l.childSearches[0].getNodes();
      }
    }
    return nodes;
  }

  @Override
  public int getDecisions() {
    decisions = 0;
    for (DepthFirstSearch<T> l : search) {
      decisions += l.getDecisions();

      if (l.childSearches != null) {
        decisions += l.childSearches[0].getDecisions();
      }
    }
    return decisions;
  }

  @Override
  public int getWrongDecisions() {
    wrongDecisions = 0;
    for (DepthFirstSearch<T> l : search) {
      wrongDecisions += l.getWrongDecisions();

      if (l.childSearches != null) {
        wrongDecisions += l.childSearches[0].getWrongDecisions();
      }
    }
    return wrongDecisions;
  }

  @Override
  public int getBacktracks() {
    numberBacktracks = 0;
    for (DepthFirstSearch<T> l : search) {
      numberBacktracks += l.getBacktracks();

      if (l.childSearches != null) {
        numberBacktracks += l.childSearches[0].getBacktracks();
      }
    }
    return numberBacktracks;
  }

  @Override
  public int getMaximumDepth() {
    maxDepthExcludePaths = 0;
    for (DepthFirstSearch<T> l : search) {
      maxDepthExcludePaths += l.getMaximumDepth();

      if (l.childSearches != null) {
        maxDepthExcludePaths += l.childSearches[0].getMaximumDepth();
      }
    }
    return maxDepthExcludePaths;
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

    LinkingSearch(DepthFirstSearch<T> m) {
      master = m;
    }

    @SuppressWarnings("unchecked")
    void constraineCost() {
      if (costVariable instanceof IntVar var) {
        int newCost = var.dom().max();

        if (newCost < costValue) {
          costValue = newCost;
          master.costValue = newCost;

          for (int i = 0; i < n; i++) {
            DepthFirstSearch<T> ls = (DepthFirstSearch<T>) lastSearch(search.get(2 * i));
            ls.costValue = var.dom().max();
            ls.cost = new XltC((IntVar) search.get(2 * i).costVariable, newCost);
          }
        }

      } else {
        CostVariableHandler costHandler =
            SearchHandlerRegistry.getInstance().findCostHandler(costVariable);
        if (costHandler != null) {
          double newCost = costHandler.getCostValue(costVariable);

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
      }
    }

    @SuppressWarnings("unchecked")
    void constraineCostFromChild(DepthFirstSearch<T> child) {
      if (costVariable instanceof IntVar) {
        int newCost = child.costValue;

        if (newCost < costValue) {
          costValue = newCost;
          master.costValue = newCost;

          for (int i = 0; i < n; i++) {
            DepthFirstSearch<T> ls = (DepthFirstSearch<T>) lastSearch(search.get(2 * i));
            ls.costValue = newCost;
            ls.cost = new XltC((IntVar) search.get(2 * i).costVariable, newCost);
          }
        }

      } else {
        CostVariableHandler costHandler =
            SearchHandlerRegistry.getInstance().findCostHandler(costVariable);
        if (costHandler != null) {
          double newCost = child.costValueFloat;

          if (costHandler.isBetterCost(costValueFloat, newCost, true)) {
            costValueFloat = newCost;
            master.costValueFloat = newCost;

            for (int i = 0; i < n; i++) {
              DepthFirstSearch<T> ls = (DepthFirstSearch<T>) lastSearch(search.get(2 * i));
              ls.costValueFloat = newCost;
              ls.cost = costHandler.createCostConstraint(search.get(2 * i).costVariable, newCost);
            }
          }
        }
      }
    }

    @SuppressWarnings("unchecked")
    public boolean labeling() {

      int index = getSubSearch();
      if (index < n) {
        visited.set(index);

        boolean result = search.get(2 * index).labeling();

        visited.set(index, false);
        return result;

      } else { // index == n
        if (costVariable != null) {

          if (master.childSearches != null) {

            DepthFirstSearch<T> childSearch = null;

            for (Search<? extends Var> childObj : master.childSearches) {
              DepthFirstSearch<T> child = (DepthFirstSearch<T>) asDfs(childObj);
              childSearch = child;
              child.setStore(store);
              child.getSolutionListener().setParentSolutionListener(solutionListener);
              child.setCostVar(costVariable);
              int currentChildSolutionNo = child.getSolutionListener().solutionsNo();

              boolean result = child.labeling();

              if (result) {
                // gets here when the limit of solutions was reached
                break;
              } else {
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
            }

            noSolutions += childSearch.getSolutionListener().solutionsNo();
            constraineCostFromChild(childSearch);

          } else { // no child search

            constraineCost();
            noSolutions++;
          }
          if (noSolutions >= solutionsLimit) {
            throw new SolutionsLimitReached();
          }
          master.solutionListener.executeAfterSolution(this, null);
          visited.set(index, false);
          return false;
        } else if (master.childSearches != null) { // no optimization and child search
          DepthFirstSearch<T> childSearch = null;

          for (Search<? extends Var> childObj2 : master.childSearches) {
            DepthFirstSearch<T> child = (DepthFirstSearch<T>) asDfs(childObj2);
            childSearch = child;
            child.setStore(store);
            child.getSolutionListener().setParentSolutionListener(solutionListener);
            int currentChildSolutionNo = child.getSolutionListener().solutionsNo();

            boolean result = child.labeling();

            if (result) {
              // gets here when the limit of solutions was reached
              break;
            } else {
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
          }

          noSolutions += childSearch.getSolutionListener().solutionsNo();
          if (noSolutions >= solutionsLimit) {
            throw new SolutionsLimitReached();
          }

          master.solutionListener.executeAfterSolution(this, null);

          visited.set(index, false);
          return false;
        } else { // not optimization and no child search
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
  }
}
