/*
 * RestartSearch.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.search.restart;

import java.util.Random;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XltC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.ConsistencyListener;
import org.jacop.search.CostVariableHandler;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrioritySearch;
import org.jacop.search.Search;
import org.jacop.search.SearchHandlerRegistry;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.SolutionListener;

/**
 * Implements restart search. Only cost as IntVar is possible.
 *
 * @param <T> type of variables used in this search.
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */
@Slf4j
public class RestartSearch<T extends Var> {

  final Store store;
  final DepthFirstSearch<T> search;
  final SelectChoicePoint<T> select;
  final Calculator calculator;
  final Var cost;
  // relax and reconstruct
  private final Random generator;
  SolutionListener<T> lastSolutionListener;
  CustomReport reportSolution;
  Search<T> lastNotNullSearch;
  int intCostValue = Integer.MAX_VALUE;
  double floatCostValue = Double.MAX_VALUE;
  int numberRestarts;
  boolean atLeastOneSolution;
  boolean timeOutCheck;
  long timeOut;
  IntVar[] rarVars;
  int probability;
  int[] values;
  int restartsLimit; // no limit

  @SuppressWarnings("unchecked")
  public RestartSearch(
      Store store, DepthFirstSearch<T> s, SelectChoicePoint<T> sel, Calculator calculator, T cost) {
    this.search = s;
    this.calculator = calculator;
    this.cost = cost;
    this.select = sel;
    this.store = store;

    DepthFirstSearch<T> ns = search;
    lastNotNullSearch = ns;

    do {
      // ns.setCostVar(null); // cost is handled internally by restart search

      if (ns instanceof PrioritySearch<T> prioritySearch) {
        prioritySearch.addRestartCalculator(prioritySearch, calculator);
      }

      // add calculator & do not assign solutions
      ConsistencyListener cs = ns.getConsistencyListener();
      ns.setConsistencyListener(calculator);
      ns.consistencyListener.setChildrenListeners(cs);
      ns.setAssignSolution(false);
      ns.setPrintInfo(false);
      lastNotNullSearch = ns;

      // find next search
      if (ns.childSearches == null) {
        ns = null;
      } else {
        ns = (DepthFirstSearch<T>) ns.childSearches[0];
      }
    } while (ns != null);

    if (cost != null) {
      lastSolutionListener = lastNotNullSearch.getSolutionListener();
      lastSolutionListener.setChildrenListeners(new CostListener<>());
    }

    generator = Store.seedPresent() ? new Random(Store.getSeed()) : new Random();
  }

  public RestartSearch(
      Store store, DepthFirstSearch<T> s, SelectChoicePoint<T> sel, Calculator calculator) {
    this(store, s, sel, calculator, null);
  }

  public boolean labeling() {

    store.setLevel(store.level + 1);
    boolean result = true;
    while (result) {

      if (rarVars != null) {

        store.setLevel(store.level + 1);

        if (values != null) {
          assignRelaxedVariables();
        }
      }

      if (cost == null) {
        result = search.labeling(store, select);
      } else {
        result = search.labeling(store, select, cost);
      }

      if (rarVars != null) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }

      if (restartsLimit > 0 && numberRestarts > restartsLimit) {
        break;
      }

      atLeastOneSolution |= result;

      int sl = ((SimpleSolutionListener<?>) lastNotNullSearch.getSolutionListener()).solutionLimit;
      if (sl > 0 && search.getSolutionListener().solutionsNo() >= sl) {
        return false;
      }

      if (timeOutCheck && System.currentTimeMillis() > timeOut) {
        search.timeOutOccured = true;
        log.info("%% =====TIME-OUT=====");
        return false;
      }

      if (result) {
        if (cost != null) {
          if (!calculator.pointsExhausted()) {
            // optimization solution found and no better exists
            result = false;
          } else {
            boundCost();
          }
        } else {
          break;
        } // single solution for satisfy search found
      } else { // no result
        result = true;
        if (calculator.pointsExhausted()) {
          if (cost != null) {
            boundCost();
          } else {
            result = !atLeastOneSolution;
          }
        } else // fail before points are exhausted
        if (rarVars == null) {
          // restart search fails
          result = false;
        } else if (cost != null) {
          boundCost();
        }
      }

      calculator.newLimit();

      if (result) {
        numberRestarts++;
      }
    }

    store.removeLevel(store.level);
    store.setLevel(store.level - 1);

    return true;
  }

  void boundCost() {

    if (cost instanceof IntVar var) {
      store.impose(new XltC(var, intCostValue));
    } else {
      CostVariableHandler costHandler = SearchHandlerRegistry.getInstance().findCostHandler(cost);
      if (costHandler != null) {
        Constraint costConstraint = costHandler.createCostConstraint(cost, floatCostValue);
        store.impose(costConstraint);
      }
    }
  }

  public int getIntCost() {
    return intCostValue;
  }

  public double getFloatCost() {
    return floatCostValue;
  }

  public void addReporter(CustomReport r) {
    reportSolution = r;
  }

  public int restarts() {
    return numberRestarts;
  }

  public void setTimeOut(long timeout) {
    timeOutCheck = true;
    timeOut = System.currentTimeMillis() + timeout * 1000;
  }

  public void setTimeOutMilliseconds(long timeout) {
    timeOutCheck = true;
    timeOut = System.currentTimeMillis() + timeout;
  }

  @SuppressWarnings("unchecked")
  void searchSingleSolution(DepthFirstSearch<T> label) {

    DepthFirstSearch<T> s = label;
    DepthFirstSearch<T> parentSearch = null;
    do {
      s.getSolutionListener().recordSolutions(false);
      s.getSolutionListener().searchAll(false);

      if (parentSearch != null) {
        s.getSolutionListener().setParentSolutionListener(parentSearch.getSolutionListener());
      }

      parentSearch = s;
      // find next search
      if (s.childSearches == null) {
        s = null;
      } else {
        s = (DepthFirstSearch<T>) s.childSearches[0];
      }
    } while (s != null);
  }

  public void setRelaxAndReconstruct(IntVar[] vs, int p) {

    rarVars = new IntVar[vs.length];
    System.arraycopy(vs, 0, rarVars, 0, vs.length);
    probability = p;
  }

  public void assignRelaxedVariables() {

    for (int i = 0; i < rarVars.length; i++) {
      IntVar var = rarVars[i];
      int rn = generator.nextInt(101);
      if (rn <= probability) {
        var.domain.inValue(store.level, var, values[i]);
      }
    }
  }

  public int[] getLastSolution() {
    return values;
  }

  public IntVar[] getRelaxedVariables() {
    return rarVars;
  }

  public int getProbability() {
    return probability;
  }

  public void setRestartsLimit(int l) {
    restartsLimit = l;
  }

  public boolean atLeastOneSolution() {
    return atLeastOneSolution;
  }

  public class CostListener<T extends Var> extends SimpleSolutionListener<T> {

    public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

      boolean returnCode = super.executeAfterSolution(search, select);

      if (reportSolution != null) {
        reportSolution.report();
      }

      if (cost instanceof IntVar var) {
        intCostValue = var.value();
      } else {
        CostVariableHandler costHandler = SearchHandlerRegistry.getInstance().findCostHandler(cost);
        if (costHandler != null) {
          floatCostValue = costHandler.getCostValue(cost);
        }
      }

      if (rarVars != null) {
        values = new int[rarVars.length];
        for (int i = 0; i < rarVars.length; i++) {
          values[i] = rarVars[i].value();
        }
      }

      return returnCode;
    }
  }
}
