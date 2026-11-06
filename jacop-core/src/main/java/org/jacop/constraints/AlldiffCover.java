/*
 * AlldiffCover.java
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

package org.jacop.constraints;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.ClauseModel;

/**
 * The value cover clauses of an all different constraint whose variables have exactly as many
 * values as there are variables (a permutation): each value is taken, x1 = v or x2 = v or ... A
 * propagator of all different removes a value once another variable takes it but does not assign
 * the last variable that can take a value. Chuffed adds the same clauses for its all different over
 * n variables and n values; on XCSP3 Pentominoes-05-18 (90 cells, 18 pieces placed by tables) they
 * turn no answer in 60 s into a solution in seconds.
 *
 * <p>The system property {@code org.jacop.lcg.alldiffCover} set to false turns them off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class AlldiffCover {

  /**
   * The most (variable, value) pairs whose literals the clauses may use, from the system property
   * {@code org.jacop.lcg.alldiffCoverLimit}. Each pair is an equality literal linked to two bound
   * literals; on XCSP3 NumberPartitioning-200 and -260 (40,000 and 67,600 pairs) the literals cost
   * more than the clauses gain, while Pentominoes needs at most 14,400.
   */
  static final int LITERAL_LIMIT = Integer.getInteger("org.jacop.lcg.alldiffCoverLimit", 1 << 14);

  private AlldiffCover() {}

  /**
   * Adds the cover clauses when the variables have as many values as there are variables.
   *
   * @param list the variables
   * @param model where the clauses go
   * @return the number of clauses added
   */
  static int clauses(IntVar[] list, ClauseModel model) {
    if ("false".equalsIgnoreCase(System.getProperty("org.jacop.lcg.alldiffCover"))
        || list.length < 3) {
      return 0;
    }
    Set<IntVar> distinct = Collections.newSetFromMap(new IdentityHashMap<>());
    IntDomain values = new IntervalDomain();
    long pairs = 0;
    for (IntVar x : list) {
      if (!distinct.add(x)) {
        return 0;
      }
      values = values.union(x.dom());
      pairs += x.getSize();
    }
    if (values.getSize() != list.length || pairs > LITERAL_LIMIT) {
      return 0;
    }
    int[] literals = new int[list.length];
    int added = 0;
    for (ValueEnumeration en = values.valueEnumeration(); en.hasMoreElements(); ) {
      int v = en.nextElement();
      int size = 0;
      boolean taken = false;
      for (IntVar x : list) {
        if (x.singleton(v)) {
          taken = true;
          break;
        }
        if (!x.singleton() && x.domain.contains(v)) {
          literals[size++] = model.valueLiteral(x, v);
        }
      }
      if (!taken) {
        model.clause(literals, size);
        added++;
      }
    }
    return added;
  }
}
