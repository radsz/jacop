/*
 * Lds.java
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

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Var;

/**
 * Defines functionality of limited discrepancy search. Plugin in this object to search to change
 * your depth first search into limited discrepancy search.
 *
 * @param <T> type of variable being used in the search.
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class Lds<T extends Var> implements ExitChildListener<T> {

  boolean timeOut;

  int noDiscrepancies;

  int maxNoDiscrepancies;

  boolean recentExitingLeftChildGoingForDiscrepancy;

  boolean recentExitingRightChild;

  ExitChildListener<T>[] exitChildListeners;

  /**
   * The search will not be allowed to deviate more than maxDiscrepancies times from the heuristic
   * (e.g. variable and value ordering) in the search.
   *
   * @param maxDiscrepancies maximal number of discrepancies allowed.
   */
  public Lds(int maxDiscrepancies) {

    assert maxDiscrepancies >= 0;

    this.maxNoDiscrepancies = maxDiscrepancies;
  }

  /**
   * It is executed after exiting the left child. The parameters specify the variable and value used
   * in the choice point. The parameter status specifies the return code from the child. The return
   * parameter of this function specifies if the search should continue undisturbed or exit the
   * current search node with value false.
   */
  public boolean leftChild(T v, int value, boolean status) {

    if (!status) {
      return handleLeftChildFailureVar(v, value);
    }
    return true;
  }

  private boolean handleLeftChildFailureVar(T v, int value) {
    noDiscrepancies++;
    if (noDiscrepancies >= maxNoDiscrepancies) {
      notifyExitChildListenersVar(v, value);
      noDiscrepancies--;
      return false;
    }
    if (exitChildListeners != null) {
      boolean code = false;
      for (ExitChildListener<T> exitChildListener : exitChildListeners) {
        code |= exitChildListener.leftChild(v, value, false);
      }
      if (!code) {
        noDiscrepancies--;
      }
      return code;
    }
    return true;
  }

  private void notifyExitChildListenersVar(T v, int value) {
    if (exitChildListeners != null) {
      for (ExitChildListener<T> exitChildListener : exitChildListeners) {
        exitChildListener.leftChild(v, value, false);
      }
    }
  }

  /**
   * It is executed after exiting the left child. The parameters specify the choice point. The
   * parameter status specifies the return code from the child. The return parameter of this
   * function specifies if the search should continue undisturbed or exit the current search node
   * with false. If the continuing to the right child will exceed the number of allowed
   * discrepancies then this function will return false so the right child will not be explored.
   */
  public boolean leftChild(PrimitiveConstraint choice, boolean status) {

    if (!status) {
      return handleLeftChildFailureChoice(choice);
    }
    return true;
  }

  private boolean handleLeftChildFailureChoice(PrimitiveConstraint choice) {
    noDiscrepancies++;
    if (noDiscrepancies >= maxNoDiscrepancies) {
      notifyExitChildListenersChoice(choice);
      noDiscrepancies--;
      return false;
    }
    if (exitChildListeners != null) {
      boolean code = false;
      for (ExitChildListener<T> exitChildListener : exitChildListeners) {
        code |= exitChildListener.leftChild(choice, false);
      }
      if (!code) {
        noDiscrepancies--;
      }
      return code;
    }
    return true;
  }

  private void notifyExitChildListenersChoice(PrimitiveConstraint choice) {
    if (exitChildListeners != null) {
      for (ExitChildListener<T> exitChildListener : exitChildListeners) {
        exitChildListener.leftChild(choice, false);
      }
    }
  }

  /**
   * Exiting the right children requires reduction of the current number of discrepancies being
   * used.
   */
  public void rightChild(T v, int value, boolean status) {

    noDiscrepancies--;
  }

  /**
   * It is executed after the right child has been explored.
   *
   * @param choice the constraint representing the choice.
   * @param status the status of the child exploration.
   */
  public void rightChild(PrimitiveConstraint choice, boolean status) {

    noDiscrepancies--;
  }

  /**
   * Sets an array of children exit child listeners.
   *
   * @param children the array of exit child listeners to be set as children.
   */
  public void setChildrenListeners(ExitChildListener<T>[] children) {

    exitChildListeners = children;
  }

  /**
   * Sets a single child exit child listener.
   *
   * @param child the exit child listener to be set as a child.
   */
  @SuppressWarnings("unchecked")
  public void setChildrenListeners(ExitChildListener<T> child) {
    exitChildListeners = new ExitChildListener[1];
    exitChildListeners[0] = child;
  }
}
