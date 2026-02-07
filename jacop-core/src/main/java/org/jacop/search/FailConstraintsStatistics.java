/*
 * FailConstraintsStatistics.java
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

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import org.jacop.constraints.Constraint;
import org.jacop.core.Store;

/**
 * Defines functionality for FailConstraintsStatistics plug-in, that collects statistics on the
 * failed constraints; both for each individual constraint as well as a class of constraints.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.10
 */
public class FailConstraintsStatistics implements ConsistencyListener {

  // data structures to collect fail constraint statistics
  public final Map<String, Integer> failConstraintsStatistics = new HashMap<>();
  public final Map<String, Integer> failConstraintsIdStatistics = new HashMap<>();
  final Store store;
  public long otherFails;

  /**
   * Creates a new fail constraints statistics listener for the given store.
   *
   * @param s the constraint store to monitor.
   */
  public FailConstraintsStatistics(Store s) {
    store = s;
  }

  private static List<Entry<String, Integer>> sortByValues(Map<String, Integer> map) {
    List<Entry<String, Integer>> list = new LinkedList<>(map.entrySet());

    // Sorting
    list.sort((o1, o2) -> o2.getValue().compareTo(o1.getValue()));

    return list;
  }

  /**
   * Records statistics about failed constraints after a consistency check.
   *
   * @param consistent whether the consistency check succeeded.
   * @return the value of {@code consistent}.
   */
  public boolean executeAfterConsistency(boolean consistent) {

    if (consistent) {
      return true;
    } else { // consistency failed
      if (store.recentlyFailedConstraint != null) {
        collectFailStatistics(store.recentlyFailedConstraint);
      } else {
        otherFails++;
      }
      return false;
    }
  }

  /** {@inheritDoc} */
  public void setChildrenListeners(ConsistencyListener[] children) {}

  /** {@inheritDoc} */
  public void setChildrenListeners(ConsistencyListener child) {}

  void collectFailStatistics(Constraint currentConstraint) {

    // ======== add fail constraints classes to list of fails
    String cName = currentConstraint.getClass().getSimpleName();
    if (cName.isEmpty()) {
      cName = currentConstraint.getClass().getTypeName();
    }
    Integer n = failConstraintsStatistics.get(cName);
    if (n != null) {
      failConstraintsStatistics.put(cName, ++n);
    } else {
      failConstraintsStatistics.put(cName, 1);
    }

    // ======== add fail constraints id's to list of fails
    Integer k = failConstraintsIdStatistics.get(currentConstraint.id());
    if (k != null) {
      failConstraintsIdStatistics.put(currentConstraint.id(), ++k);
    } else {
      failConstraintsIdStatistics.put(currentConstraint.id(), 1);
    }
    // ========
  }

  /** {@inheritDoc} */
  public String toString() {

    StringBuilder c = new StringBuilder();

    c.append("*** Failed classes of constraints ***\n");
    for (Entry<String, Integer> cls : sortByValues(failConstraintsStatistics)) {
      c.append(cls.getKey()).append("\t").append(cls.getValue()).append("\n");
    }
    c.append("*** Failed constraints ***\n");
    for (Entry<String, Integer> constraint : sortByValues(failConstraintsIdStatistics)) {
      c.append(constraint.getKey()).append("\t").append(constraint.getValue()).append("\n");
    }
    c.append("*** Fails not caused by constraints ").append(otherFails).append("\n");

    return c.toString();
  }
}
