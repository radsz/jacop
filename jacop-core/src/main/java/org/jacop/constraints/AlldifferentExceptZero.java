/*
 * AlldifferentExceptZero.java
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

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * AlldifferentExceptZero constraint assures that all FDVs except those with zero value have
 * differnet values.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */
public class AlldifferentExceptZero extends Alldifferent
    implements UsesQueueVariable, SatisfiedPresent {

  protected AlldifferentExceptZero() {}

  /**
   * It constructs the alldifferent constraint for the supplied variable.
   *
   * @param list variables which are constrained to take different values.
   */
  public AlldifferentExceptZero(IntVar[] list) {

    super(list);
  }

  /**
   * It constructs the alldifferent constraint for the supplied variable.
   *
   * @param variables variables which are constrained to take different values.
   */
  public AlldifferentExceptZero(List<? extends IntVar> variables) {
    this(variables.toArray(new IntVar[0]));
  }

  @Override
  public void consistency(Store store) {

    int groundPos = grounded.value();
    do {

      store.propagationHasOccurred = false;

      LinkedHashSet<IntVar> fdvs = variableQueue;
      variableQueue = new LinkedHashSet<>();

      for (IntVar Q : fdvs) {
        if (Q.singleton()) {
          int qPos = positionMapping.get(Q);
          if (qPos > groundPos) {
            list[qPos] = list[groundPos];
            list[groundPos] = Q;
            positionMapping.put(Q, groundPos);
            positionMapping.put(list[qPos], qPos);
            groundPos++;
            if (Q.value() != 0) {
              for (int i = groundPos; i < list.length; i++) {
                list[i].domain.inComplement(store.level, list[i], Q.min());
              }
            }
          } else if (qPos == groundPos) {
            groundPos++;
            if (Q.value() != 0) {
              for (int i = groundPos; i < list.length; i++) {
                list[i].domain.inComplement(store.level, list[i], Q.min());
              }
            }
          }
        }
      }

    } while (store.propagationHasOccurred);
    grounded.update(groundPos);

    ArrayList<IntVar> vars = new ArrayList<>();
    int j = 0;
    for (int i = groundPos; i < list.length; i++) {
      if (!list[i].domain.contains(0)) {
        vars.add(list[i]);
      }
    }

    // we only check for more than two variables since two
    // variables with domains of size at least two (they are not
    // ground) are always satisfied.
    if (vars.size() > 2 && notSatisfied(vars.toArray(new IntVar[0]))) {
      throw Store.failException;
    }
  }

  public boolean notSatisfied(IntVar[] vs) {
    return notSatisfiedByMatching(vs);
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : AlldifferentExceptZero([");
    appendArrayToString(result, list);
    result.append("])");

    return result.toString();
  }
}
