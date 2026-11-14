/*
 * TableReified.java
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

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * TableReified links a 0/1 variable b to a table constraint: b = 1 if and only if the variables
 * form one of the tuples (reified table), or, as a half-reification, b = 1 implies that they do.
 * Once b is fixed the constraint filters as Compact-Table (b = 1) or as CT-neg (b = 0); before, b
 * is set to 0 when no valid tuple is left and, for the full reification, to 1 when the valid tuples
 * cover every combination of values. This is generalized arc consistency on the variables and b.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class TableReified extends CompactGroundTable
    implements SatisfiedPresent, Copyable<TableReified> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The 0/1 control variable. */
  final IntVar b;

  /** True for the half-reification, b = 1 implies the table. */
  final boolean implication;

  /**
   * It constructs a reified table constraint, b = 1 if and only if list is one of the tuples.
   *
   * @param list the variables in the scope of the constraint.
   * @param tuples the allowed tuples.
   * @param b the 0/1 control variable.
   */
  public TableReified(IntVar[] list, int[][] tuples, IntVar b) {
    this(list, tuples, b, false);
  }

  /**
   * It constructs a reified or half-reified table constraint.
   *
   * @param list the variables in the scope of the constraint.
   * @param tuples the allowed tuples.
   * @param b the 0/1 control variable.
   * @param implication true for b = 1 implies the table, false for b = 1 if and only if the table.
   */
  public TableReified(IntVar[] list, int[][] tuples, IntVar b, boolean implication) {
    super(list, tuples, new IntVar[] {checkControl(list, b)});
    this.b = b;
    this.implication = implication;
    numberId = idNumber.incrementAndGet();
  }

  private TableReified(TableReified original, VarMap map) {
    super(original, map, new IntVar[] {map.get(original.b)});
    this.b = map.get(original.b);
    this.implication = original.implication;
    numberId = idNumber.incrementAndGet();
  }

  private static IntVar checkControl(IntVar[] list, IntVar b) {
    if (b == null || b.min() < 0 || b.max() > 1) {
      throw new IllegalArgumentException("TableReified: the control variable must be 0/1");
    }
    for (IntVar v : list) {
      if (v == b) {
        throw new IllegalArgumentException("TableReified: the control variable is in the list");
      }
    }
    return b;
  }

  @Override
  public void queueVariable(int level, Var v) {
    if (v != b) {
      super.queueVariable(level, v);
    }
  }

  @Override
  public void consistency(Store store) {
    newEpochIfNeeded();
    pruning = false;
    updateQueued();
    pruning = true;
    try {
      if (!b.singleton()) {
        if (isEmpty()) {
          b.domain.in(store.level, b, 0, 0);
        } else if (!implication && count() == combinations()) {
          b.domain.in(store.level, b, 1, 1);
        } else {
          return;
        }
      }
      if (b.value() == 1) {
        if (isEmpty()) {
          throw Store.failException;
        }
        int notGround = 0;
        for (int i = 0; i < arity; i++) {
          filterPositive(i);
          if (!x[i].singleton()) {
            notGround++;
          }
        }
        if (notGround <= 1) {
          removeConstraint();
        }
      } else if (implication) {
        removeConstraint();
      } else {
        filterNegativeToFixpoint();
        if (isEmpty()) {
          removeConstraint();
        }
      }
    } finally {
      pruning = false;
    }
  }

  /** The number of combinations of values of the variables, capped above the number of tuples. */
  private long combinations() {
    long product = 1;
    for (int i = 0; i < arity && product <= tupleCount; i++) {
      product *= x[i].getSize();
    }
    return product;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {
    if (!b.singleton() || !grounded()) {
      return false;
    }
    boolean in = !isEmpty() && assignmentInTable();
    return b.value() == 1 ? in : implication || !in;
  }

  @Override
  public String toString() {
    StringBuilder s =
        new StringBuilder(id()).append(implication ? " : tableImplied(" : " : tableReified(");
    return appendTuples(s).append(", ").append(b).append(")").toString();
  }

  @Override
  public TableReified copy(VarMap map) {
    return new TableReified(this, map);
  }
}
