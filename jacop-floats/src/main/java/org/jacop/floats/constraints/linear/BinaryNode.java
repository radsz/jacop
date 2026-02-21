/*
 * BinaryNode.java
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

package org.jacop.floats.constraints.linear;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * Binary Node of the tree representing linear constraint.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public abstract class BinaryNode {

  static final AtomicInteger n = new AtomicInteger(0);
  int id;

  // tree structure
  BinaryNode parent;
  BinaryNode left;
  BinaryNode right;

  abstract void propagateAndPrune();

  abstract void prune();

  abstract void propagate();

  abstract double min();

  abstract double max();

  abstract double lb();

  abstract double ub();

  abstract void updateBounds(double min, double max, double lb, double ub);

  /**
   * Updates bounds if they have changed and propagates to parent. This helper method extracts the
   * common pattern of checking if new bounds differ from current bounds, updating them, and
   * propagating to the parent node.
   *
   * @param newMin the new minimum bound
   * @param newMax the new maximum bound
   * @param newLb the new lower lookahead bound
   * @param newUb the new upper lookahead bound
   * @param andPrune if true, calls propagateAndPrune on parent; otherwise calls propagate
   * @return true if bounds were updated and propagation occurred
   */
  protected boolean updateBoundsAndPropagate(
      double newMin, double newMax, double newLb, double newUb, boolean andPrune) {
    double nodeMin = min();
    double nodeMax = max();

    if (newMin > nodeMin) {
      return applyNewMinAndPropagate(nodeMax, newMin, newMax, newLb, newUb, andPrune);
    }
    if (newMax < nodeMax) {
      return applyNewMaxAndPropagate(nodeMin, newMax, newLb, newUb, andPrune);
    }
    return false;
  }

  private boolean applyNewMinAndPropagate(
      double nodeMax, double newMin, double newMax, double newLb, double newUb, boolean andPrune) {
    if (newMax < nodeMax) {
      if (newMin > newMax) {
        throw org.jacop.core.Store.failException;
      }
      updateBounds(newMin, newMax, newLb, newUb);
    } else {
      if (newMin > nodeMax) {
        throw org.jacop.core.Store.failException;
      }
      updateBounds(newMin, nodeMax, newLb, newUb);
    }
    propagateToParent(andPrune);
    return true;
  }

  private boolean applyNewMaxAndPropagate(
      double nodeMin, double newMax, double newLb, double newUb, boolean andPrune) {
    if (nodeMin > newMax) {
      throw org.jacop.core.Store.failException;
    }
    updateBounds(nodeMin, newMax, newLb, newUb);
    propagateToParent(andPrune);
    return true;
  }

  private void propagateToParent(boolean andPrune) {
    if (andPrune) {
      parent.propagateAndPrune();
    } else {
      parent.propagate();
    }
  }

  /**
   * Returns a string representation of this binary node.
   *
   * @return the node's id as a string
   */
  public String toString() {
    return "" + id;
  }
}
