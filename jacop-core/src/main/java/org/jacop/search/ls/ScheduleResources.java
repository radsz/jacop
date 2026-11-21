/*
 * ScheduleResources.java
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

package org.jacop.search.ls;

import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * It tells whether a model has a unary resource that the scheduling search of {@link LocalSearch}
 * can read as a machine. It is a class of its own so that the check does not load {@link
 * LocalSearch} for models that have none.
 */
public final class ScheduleResources {

  private ScheduleResources() {}

  /**
   * Tells whether the store has a resource that the scheduling search can read as a machine (a
   * {@code CumulativeBasic} that is not optional, with a fixed limit and fixed tasks of which no
   * two fit together), without building the model of the search.
   *
   * @param store the store.
   * @return true when such a constraint is attached to a variable of the store.
   */
  public static boolean hasResource(Store store) {
    return hasResource(Arrays.copyOf(store.vars, store.size()));
  }

  /**
   * Tells whether a resource that the scheduling search can read as a machine (see {@link
   * #hasResource(Store)}) is attached to one of the variables.
   *
   * @param vars the variables, such as the decision variables that include the task starts.
   * @return true when such a constraint is attached to one of them.
   */
  public static boolean hasResource(Var[] vars) {
    // a cumulative is attached to each of its starts: each is checked once
    Set<Constraint> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Var v : vars) {
      Constraint[][] lists = v == null ? null : v.dom().modelConstraints;
      if (lists == null) {
        continue;
      }
      for (int e = 0; e < lists.length; e++) {
        for (int j = v.dom().modelConstraintsToEvaluate[e] - 1; j >= 0; j--) {
          Constraint c = lists[e][j];
          if (c instanceof CumulativeBasic cb
              && seen.add(c)
              && !c.getClass().getSimpleName().contains("Optional")
              && unary(cb)) {
            return true;
          }
        }
      }
    }
    return false;
  }

  /**
   * Tells whether the store may hold a permutation flow shop for the iterated greedy search of
   * {@link LocalSearch}: an all different whose variables are columns of tables.
   *
   * @param store the store.
   * @return true when such a constraint is attached to a variable of the store.
   */
  public static boolean hasPermutation(Store store) {
    return hasPermutation(Arrays.copyOf(store.vars, store.size()));
  }

  /**
   * Tells whether one of the variables is in an all different and a column of a table with two
   * other columns, as the positions of a permutation flow shop are (see {@link
   * #hasPermutation(Store)}).
   *
   * @param vars the variables, such as the decision variables.
   * @return true when one of them is.
   */
  public static boolean hasPermutation(Var[] vars) {
    for (Var v : vars) {
      Constraint[][] lists = v == null ? null : v.dom().modelConstraints;
      if (lists == null) {
        continue;
      }
      boolean alldiff = false;
      boolean key = false;
      for (int e = 0; e < lists.length; e++) {
        for (int j = v.dom().modelConstraintsToEvaluate[e] - 1; j >= 0; j--) {
          Constraint c = lists[e][j];
          alldiff |= c instanceof Alldistinct || c instanceof Alldifferent;
          key |= c instanceof HybridTable t && t.columnCount() >= 3;
        }
      }
      if (alldiff && key) {
        return true;
      }
    }
    return false;
  }

  // a fixed limit, fixed tasks and no two tasks that fit together: a machine for machineOf
  private static boolean unary(CumulativeBasic cb) {
    IntVar[][] t = cb.tasks();
    IntVar limit = cb.limit();
    if (!limit.singleton()) {
      return false;
    }
    int smallest = Integer.MAX_VALUE;
    int second = Integer.MAX_VALUE;
    for (int k = 0; k < t[0].length; k++) {
      if (!t[1][k].singleton() || !t[2][k].singleton()) {
        return false;
      }
      int r = t[2][k].value();
      if (t[1][k].value() <= 0 || r <= 0) {
        continue;
      }
      if (r < smallest) {
        second = smallest;
        smallest = r;
      } else if (r < second) {
        second = r;
      }
    }
    return second != Integer.MAX_VALUE && (long) smallest + second > limit.value();
  }
}
