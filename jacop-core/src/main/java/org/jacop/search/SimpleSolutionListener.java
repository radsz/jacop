/*
 * SimpleSolutionListener.java
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

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.lang.reflect.Array;
import java.util.List;
import java.util.Map;
import lombok.Getter;
import lombok.Setter;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XeqC;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * It defines a simple solution listener which should be used if some basic functionality of search
 * when a solution is encountered are required.
 *
 * @param <T> type of variable being used in search.
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class SimpleSolutionListener<T extends Var> implements SolutionListener<T> {

  /** It specifies if the debugging information should be printed. */
  private static final boolean DEBUG = false;

  /**
   * It is executed right after consistency of the current search node. The return code specifies if
   * the search should continue or exit.
   */
  public T[] vars;

  /** It specifies the number of solutions we want to find. */
  @Setter public int solutionLimit = -1;

  @Getter public Domain[][] solutions;

  /**
   * If this search is a slave search than each solution within this search must be connected to a
   * solution of the master search. The parentSolutionListener is a solution listener of the master
   * search.
   */
  @Setter public SolutionListener<? extends Var> parentSolutionListener;

  /**
   * If this search is a slave search than each solution within this search must be connected to a
   * solution of the master search. This array stores for each solution recorded by this solution
   * listener the solution number of the master slave.
   */
  public int[] parentSolutionNo;

  /** It contains children of the solution listener. */
  public SolutionListener<T>[] childrenSolutionListeners;

  protected int noSolutions;
  boolean alwaysUpdateToMostRecentSolution = true;
  boolean recordSolutions;

  /**
   * It returns null if no solution was recorded, or the variables for which the solution(s) was
   * recorded.
   */
  public T[] getVariables() {
    return vars;
  }

  /**
   * Sets the variables for which solutions will be recorded.
   *
   * @param vs the array of variables to track.
   */
  public void setVariables(T[] vs) {
    vars = vs;
    solutions = new Domain[1][vars.length];
    parentSolutionNo = new int[1];
  }

  /**
   * Sets the variables for which solutions will be recorded.
   *
   * @param vs the list of variables to track.
   */
  @SuppressWarnings("unchecked")
  public void setVariables(List<T> vs) {
    vars = (T[]) vs.toArray(new Var[0]);
    solutions = new Domain[1][vars.length];
    parentSolutionNo = new int[1];
  }

  /**
   * Checks whether the solution limit has been reached.
   *
   * @return true if the number of solutions found equals the solution limit, false otherwise.
   */
  public boolean solutionLimitReached() {

    return solutionLimit == noSolutions;
  }

  /** It returns the solution number no. The first solution has an index 1. */
  public Domain[] getSolution(int no) {

    if (ASSERTS_ENABLED && no > noSolutions) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !recordSolutions) {
      throw new IllegalStateException("Assertion failed");
    }

    return solutions[no - 1];
  }

  /** It returns number of solutions found while using this choice point selector. */
  public int solutionsNo() {
    return noSolutions;
  }

  public void setSolutionsNo(int no) {
    noSolutions = no;
  }

  /** It records all solutions so they can be later retrieved and used. */
  public void recordSolutions(boolean status) {

    recordSolutions = status;
  }

  /**
   * It searches for all solutions, but they do not have to be recorded as this is decided by
   * another parameter.
   */
  public void searchAll(boolean status) {

    if (status) {
      solutionLimit = Integer.MAX_VALUE;
    } else {
      solutionLimit = 1;
    }
  }

  /**
   * It records a solution. It uses the current value of the search variables (they must be all
   * grounded) as well as the current number of the solution in master search (if there is one).
   */
  public void recordSolution() {

    if (recordSolutions) {
      ensureSolutionCapacity();
      Domain[] currentSolution = new Domain[vars.length];
      copyVarsToSolution(currentSolution);
      solutions[noSolutions] = currentSolution;
      noSolutions++;
      updateParentAfterRecordSolution();
    } else {
      copyVarsToSolution(solutions[0]);
      noSolutions++;
      updateParentAfterOverwriteSolution();
    }
  }

  private void ensureSolutionCapacity() {
    if (noSolutions >= solutions.length) {
      Domain[][] oldSolutions = solutions;
      solutions = new Domain[noSolutions * 2][];
      System.arraycopy(oldSolutions, 0, solutions, 0, noSolutions);
      int[] oldParentSolutionNo = parentSolutionNo;
      parentSolutionNo = new int[noSolutions * 2];
      System.arraycopy(oldParentSolutionNo, 0, parentSolutionNo, 0, noSolutions);
    }
  }

  private void copyVarsToSolution(Domain[] dest) {
    for (int i = 0; i < vars.length; i++) {
      if (!vars[i].singleton()) {
        throw new RuntimeException("Variable is not grounded in the solution");
      }
      dest[i] = vars[i].dom();
    }
  }

  private void updateParentAfterRecordSolution() {
    if (parentSolutionListener != null) {
      parentSolutionNo[noSolutions] = parentSolutionListener.solutionsNo() - 1;
    }
  }

  private void updateParentAfterOverwriteSolution() {
    if (parentSolutionListener != null) {
      parentSolutionNo[0] = parentSolutionListener.solutionsNo();
      ((SimpleSolutionListener<?>) parentSolutionListener).noSolutions = noSolutions;
    }
  }

  /**
   * Executed after a solution is found. Records the solution and determines whether the search
   * should continue.
   *
   * @param search the search that found the solution.
   * @param select the choice point selector used in the search.
   * @return true if the solution limit has been reached and search should stop, false otherwise.
   */
  @SuppressWarnings("unchecked")
  public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

    if (vars == null) {
      initializeVarsFromSelect(select);
    }

    if (vars != null) {
      recordSolution();
    }

    if (childrenSolutionListeners != null) {
      return executeChildrenAndCheckLimit(search, select);
    }

    return solutionLimit <= noSolutions;
  }

  @SuppressWarnings("unchecked")
  private void initializeVarsFromSelect(SelectChoicePoint<T> select) {
    Map<T, Integer> position = select.getVariablesMapping();
    if (position.isEmpty()) {
      vars = null;
    } else {
      T[] array = (T[]) Array.newInstance(Var.class, position.size());
      vars = array;
      for (Map.Entry<T, Integer> entry : position.entrySet()) {
        vars[entry.getValue()] = entry.getKey();
      }
    }
    if (vars != null) {
      solutions = new Domain[1][vars.length];
      parentSolutionNo = new int[1];
    }
  }

  private boolean executeChildrenAndCheckLimit(Search<T> search, SelectChoicePoint<T> select) {
    boolean code = false;
    for (SolutionListener<T> childrenSolutionListener : childrenSolutionListeners) {
      code |= childrenSolutionListener.executeAfterSolution(search, select);
    }
    return code && (solutionLimit <= noSolutions);
  }

  /**
   * It assigns the last found solution to the store. If the function returns false that means that
   * for some reason the solution which was supposed to be a solution is not. It can be caused by a
   * number of issues, starting with wrongly implemented plugins, wrongly implemented consistency or
   * satisfied function of the constraint.
   *
   * @param store the store in the context of which the search took place.
   * @return true if the store is consistent after assigning a solution, false otherwise.
   */
  public boolean assignSolution(Store store) {
    if (recordSolutions) {
      return assignSolution(store, noSolutions - 1);
    } else {
      return assignSolution(store, 0);
    }
  }

  /**
   * Assigns the solution with the given number to the store.
   *
   * @param store the store in the context of which the search took place.
   * @param number the solution number to assign (0-based index).
   * @return true if the store is consistent after assigning the solution, false otherwise.
   */
  public boolean assignSolution(Store store, int number) {

    if (number == noSolutions - 1 && !recordSolutions) {
      number = 0;
    }

    if (ASSERTS_ENABLED && number >= noSolutions) {
      throw new IllegalStateException(String.valueOf("Smaller number of solutions were found."));
    }
    if (ASSERTS_ENABLED && !recordSolutions && number != 0) {
      throw new IllegalStateException(String.valueOf("The solutions were not stored."));
    }
    if (ASSERTS_ENABLED && solutions.length <= number) {
      throw new IllegalStateException(
          String.valueOf("The solution of the given number was not stored."));
    }

    if (vars != null) {

      if (ASSERTS_ENABLED && store.currentConstraint != null) {
        throw new IllegalStateException("Assertion failed");
      }

      for (int i = 0; i < vars.length; i++) {
        vars[i].dom().in(store.level, vars[i], solutions[number][i]);
      }

      return store.consistency();
    } else {
      return false;
    }
  }

  @Override
  public String toString() {

    StringBuilder buf = new StringBuilder();

    if (noSolutions > 1) {
      buf.append("\nNo of solutions : ").append(noSolutions);
      buf.append("\nLast Solution : [");
    } else {
      buf.append("\nSolution : [");
    }

    int solutionIndex = 0;

    if (recordSolutions) {
      solutionIndex = noSolutions - 1;
    }

    if (vars != null) {
      for (int i = 0; i < vars.length; i++) {
        buf.append(vars[i].id()).append("=").append(solutions[solutionIndex][i]);
        if (i < vars.length - 1) {
          buf.append(", ");
        }
      }
    }

    buf.append("]\n");

    return buf.toString();
  }

  /**
   * Returns the most recent solution as an array of primitive constraints.
   *
   * @return array of primitive constraints enforcing the last solution, or null if no variables.
   */
  public PrimitiveConstraint[] returnSolution() {

    return returnSolution(noSolutions - 1);
  }

  /**
   * It returns the solution with the given number (value 0 denotes the first solution) as a set of
   * primitive constraints.
   *
   * @param number the solution number (0 denotes the first solution).
   * @return array of primitive constraint which if imposed will enforce given solution.
   */
  public PrimitiveConstraint[] returnSolution(int number) {

    if (vars == null) {
      return null;
    }

    PrimitiveConstraint[] result = new PrimitiveConstraint[vars.length];
    int no = 0;
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] instanceof IntVar v) {
        result[no] = new XeqC(v, ((IntDomain) solutions[i][number]).min());
      }
      no++;
    }
    return result;
  }

  public boolean isRecordingSolutions() {
    return recordSolutions;
  }

  /**
   * Finds the index of a child solution that corresponds to the given parent solution number.
   *
   * @param parentNo the parent solution number to match.
   * @return the index of the matching solution, or -1 if no match is found.
   */
  public int findSolutionMatchingParent(int parentNo) {

    if (!isRecordingSolutions()) {

      return 0;
    }

    int left = 0;
    int right = noSolutions - 1;

    int middle = left;

    while (left + 1 < right) {

      if (DEBUG) {
        log.debug("left {} right {} middle {}", left, right, middle);
      }

      middle = (left + right) >> 1;

      if (parentSolutionNo[middle] < parentNo) {
        left = middle;
      } else if (parentSolutionNo[middle] > parentNo) {
        right = middle;
      } else {
        break;
      }
    }

    if (parentSolutionNo[middle] == parentNo) {
      return middle;
    } else if (parentSolutionNo[right] == parentNo) {
      return right;
    } else if (parentSolutionNo[left] == parentNo) {
      return left;
    } else {
      return -1;
    }
  }

  /**
   * Sets the children solution listeners.
   *
   * @param children the array of child solution listeners.
   */
  public void setChildrenListeners(SolutionListener<T>[] children) {

    childrenSolutionListeners = children;
  }

  /**
   * Sets a single child solution listener.
   *
   * @param child the child solution listener.
   */
  @SuppressWarnings("unchecked")
  public void setChildrenListeners(SolutionListener<T> child) {
    childrenSolutionListeners = new SolutionListener[1];
    childrenSolutionListeners[0] = child;
  }

  /** Prints all recorded solutions, or the last solution if solutions were not recorded. */
  public void printAllSolutions() {

    if (recordSolutions) {
      printRecordedSolutionsContent();
    } else {
      printLastOrNoSolutionContent();
    }
  }

  private void printRecordedSolutionsContent() {
    log.info("\nAll solutions: \n");
    log.info("Number of Solutions: {}", noSolutions);
    log.info("{}", appendVarIds(new StringBuilder()));
    for (int s = 0; s < noSolutions; s++) {
      StringBuilder solutionLine = new StringBuilder();
      for (int i = 0; i < solutions[0].length; i++) {
        solutionLine.append(solutions[s][i]).append(" ");
      }
      log.info("{}", solutionLine);
    }
  }

  private void printLastOrNoSolutionContent() {
    if (noSolutions > 0) {
      log.info("\nLast recorded solution: \n");
      log.info("Number of Solutions: {}", noSolutions);
      log.info("{}", appendVarIds(new StringBuilder()));
      StringBuilder solutionLine = new StringBuilder();
      for (int i = 0; i < solutions[0].length; i++) {
        solutionLine.append(solutions[0][i]).append(" ");
      }
      log.info("{}", solutionLine);
    } else {
      log.info("\nNo solution found. \n");
    }
  }

  private StringBuilder appendVarIds(StringBuilder sb) {
    for (int i = 0; i < solutions[0].length; i++) {
      sb.append(vars[i].id()).append(" ");
    }
    return sb;
  }

  /**
   * Returns the parent solution number corresponding to the given child solution number.
   *
   * @param childSolutionNo the child solution number (1-based).
   * @return the parent solution number, or -1 if not available.
   */
  public int getParentSolution(int childSolutionNo) {

    if (parentSolutionNo == null || parentSolutionNo.length < childSolutionNo) {
      return -1;
    }

    return parentSolutionNo[childSolutionNo - 1];
  }
}
