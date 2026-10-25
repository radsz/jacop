/*
 * NegativeTable.java
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

/**
 * NegativeTable forbids the given tuples (a conflict table). It implements CT-neg, "Extending
 * Compact-Table to Negative and Short Tables", Hélène Verhaeghe, Christophe Lecoutre and Pierre
 * Schaus, AAAI 2017: the tuples that are still valid are kept in a reversible sparse bit-set, and a
 * value loses its support when the valid tuples containing it cover every combination of values of
 * the other variables, which is checked by counting bits. It achieves generalized arc consistency.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class NegativeTable extends CompactGroundTable
    implements SatisfiedPresent, Copyable<NegativeTable> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs a negative table constraint.
   *
   * @param list the variables in the scope of the constraint.
   * @param tuples the forbidden tuples.
   */
  public NegativeTable(IntVar[] list, int[][] tuples) {
    super(list, tuples, null);
    numberId = idNumber.incrementAndGet();
  }

  private NegativeTable(NegativeTable original, VarMap map) {
    super(original, map, null);
    numberId = idNumber.incrementAndGet();
  }

  @Override
  public void consistency(Store store) {
    newEpochIfNeeded();
    pruning = false;
    updateQueued();
    if (isEmpty()) {
      removeConstraint();
      return;
    }
    pruning = true;
    filterNegativeToFixpoint();
    pruning = false;
    if (isEmpty()) {
      removeConstraint();
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {
    if (isEmpty()) {
      return true;
    }
    return grounded() && !assignmentInTable();
  }

  @Override
  public String toString() {
    return appendTuples(new StringBuilder(id()).append(" : negativeTable(")).append(")").toString();
  }

  @Override
  public NegativeTable copy(VarMap map) {
    return new NegativeTable(this, map);
  }
}
