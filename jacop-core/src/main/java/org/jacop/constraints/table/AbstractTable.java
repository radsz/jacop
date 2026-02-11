/*
 * AbstractTable.java
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

package org.jacop.constraints.table;

import java.util.Arrays;
import java.util.Map;
import java.util.Set;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Abstract base for Table and SimpleTable constraints. Provides shared fields (x, tuple, varMap,
 * store, noNoGround, variableQueue), constructor with tuple filtering, validTuple, consistency loop
 * structure, queueVariable, removeLevel, pruning event, and partial toString.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public abstract class AbstractTable extends Constraint implements UsesQueueVariable, Stateful {

  static final boolean debug = false;

  /** Variables within the scope of table constraint. */
  public final IntVar[] x;

  /** Tuples specifying the allowed values. */
  public final int[][] tuple;

  /** Maps variables to their indices. */
  final Map<IntVar, Integer> varMap;

  Store store;
  Set<IntVar> variableQueue;
  int noNoGround;

  /**
   * Constructs an AbstractTable, filtering infeasible tuples.
   *
   * @param list the variables in the scope of the constraint.
   * @param tuples the tuples which define allowed values.
   * @param reuseTuplesArgument specifies if the table of tuples should be used directly without
   *     copying.
   */
  protected AbstractTable(IntVar[] list, int[][] tuples, boolean reuseTuplesArgument) {

    checkInputForNullness(new String[] {"list", "tuples"}, list, tuples);
    checkInput(
        tuples, i -> i.length == list.length, "tuple need to have the same size as list argument.");

    this.x = Arrays.copyOf(list, list.length);
    this.varMap = Var.positionMapping(list, false, this.getClass());

    if (reuseTuplesArgument) {
      this.tuple = tuples;
    } else {
      // create tuples for the constraint; remove non feasible tuples
      int size = list.length;
      boolean[] tuplesToRemove = new boolean[tuples.length];
      int n = 0;
      for (int i = 0; i < tuples.length; i++) {
        for (int j = 0; j < size; j++) {
          if (!list[j].domain.contains(tuples[i][j])) {
            tuplesToRemove[i] = true;
          }
        }
        if (tuplesToRemove[i]) {
          n++;
        }
      }
      int k = tuples.length - n;
      this.tuple = new int[k][size];
      int m = 0;
      for (int i = 0; i < tuples.length; i++) {
        if (!tuplesToRemove[i]) {
          this.tuple[m] = Arrays.copyOf(tuples[i], size);
          m++;
        }
      }
    }

    this.queueIndex = 1;
    setScope(list);
  }

  /**
   * Checks if the tuple at the given index is valid with respect to current variable domains.
   *
   * @param index the index of the tuple to check
   * @return true if the tuple is valid, false otherwise
   */
  boolean validTuple(int index) {

    int[] t = tuple[index];
    int n = t.length;
    int i = 0;
    while (i < n) {
      if (!x[i].dom().contains(t[i])) {
        return false;
      }
      i++;
    }
    return true;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void consistency(Store store) {

    do {

      store.propagationHasOccurred = false;

      Set<IntVar> fdvs = variableQueue;
      variableQueue = createVariableQueue();

      updateTable(fdvs);
      filterDomains();

    } while (store.propagationHasOccurred);

    if (noNoGround == 1) {
      removeConstraint();
    }
  }

  /**
   * Updates the table bit-set by removing tuples that are no longer supported.
   *
   * @param fdvs the set of recently changed variables.
   */
  abstract void updateTable(Set<IntVar> fdvs);

  /** Filters variable domains based on the current table state. */
  abstract void filterDomains();

  /** Creates a new empty variable queue of the appropriate type for the subclass. */
  abstract Set<IntVar> createVariableQueue();

  @Override
  public void queueVariable(int level, Var v) {
    variableQueue.add((IntVar) v);
  }

  /**
   * It removes the specified level from the constraint.
   *
   * @param level the level to be removed.
   */
  public void removeLevel(int level) {
    variableQueue.clear();
  }

  /**
   * Appends the shared part of toString (constraint name, variables, tuples).
   *
   * @param constraintName the name of the concrete constraint.
   * @return a StringBuilder with the shared portion.
   */
  protected StringBuilder toStringBase(String constraintName) {
    StringBuilder s = new StringBuilder(id());

    s.append(" : ").append(constraintName).append("(");
    s.append(Arrays.asList(x));

    s.append(", [");
    for (int i = 0; i < tuple.length; i++) {
      s.append("[");
      for (int j = 0; j < tuple[i].length; j++) {
        s.append(tuple[i][j]);
        if (j < tuple[i].length - 1) {
          s.append(", ");
        }
      }
      s.append("]");
      if (i < tuple.length - 1) {
        s.append(", ");
      }
    }
    s.append("])");
    return s;
  }
}
