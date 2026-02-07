/*
 * SimpleTimeOut.java
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

package org.jacop.search;

/**
 * It defines a simple time out listener. It only records the fact that timeout listener occurred as
 * well as number of solutions found before the timeout.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.10
 */
public class SimpleTimeOut implements TimeOutListener {

  /** It specifies if the timeout has already occurred. */
  public boolean timeOutOccurred;

  /** It records number of found solutions. */
  public int solutionsNo;

  /** It contains child(ren) of this timeout listener. */
  public TimeOutListener[] timeOutListeners;

  /**
   * It is executed when the timeout occurs.
   *
   * @param solutionsNo the number of solutions found before the timeout.
   */
  public void executedAtTimeOut(int solutionsNo) {
    this.solutionsNo = solutionsNo;
    this.timeOutOccurred = true;

    if (timeOutListeners != null) {
      for (TimeOutListener timeOutListener : timeOutListeners) {
        timeOutListener.executedAtTimeOut(solutionsNo);
      }
    }
  }

  /**
   * Sets an array of children timeout listeners.
   *
   * @param children the array of timeout listeners to be set as children.
   */
  public void setChildrenListeners(TimeOutListener[] children) {
    timeOutListeners = children;
  }

  /**
   * Sets a single child timeout listener.
   *
   * @param child the timeout listener to be set as a child.
   */
  public void setChildrenListeners(TimeOutListener child) {
    timeOutListeners = new TimeOutListener[1];
    timeOutListeners[0] = child;
  }
}
