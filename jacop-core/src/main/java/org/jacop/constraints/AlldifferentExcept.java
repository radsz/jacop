/*
 * AlldifferentExcept.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.util.BipartiteGraphMatching;

/**
 * AlldifferentExcept constraint assures that all FDVs except those given as a set of values
 * (parameter s) have differnet values.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */
public class AlldifferentExcept extends Alldifferent
    implements UsesQueueVariable, SatisfiedPresent {

  IntDomain s;

  protected AlldifferentExcept() {}

  /**
   * It constructs the alldifferent constraint for the supplied variable.
   *
   * @param list variables which are constrained to take different values.
   */
  public AlldifferentExcept(IntVar[] list, IntDomain s) {

    super(list);

    this.s = s;
  }

  /**
   * It constructs the alldifferent constraint for the supplied variable.
   *
   * @param variables variables which are constrained to take different values.
   */
  public AlldifferentExcept(List<? extends IntVar> variables, IntDomain s) {
    this(variables.toArray(new IntVar[0]), s);
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
            if (!s.contains(Q.value())) {
              for (int i = groundPos; i < list.length; i++) {
                list[i].domain.inComplement(store.level, list[i], Q.min());
              }
            }
          } else if (qPos == groundPos) {
            groundPos++;
            if (!s.contains(Q.value())) {
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
      if (!s.isIntersecting(list[i].dom())) {
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

  /**
   * Check whether the constraint is not satisfied based on bipartite graph matching.
   *
   * @return true if constraint is not satisfied
   */
  public boolean notSatisfied(IntVar[] vs) {

    Map<Integer, Integer> valueMap = new HashMap<>();
    int valueIndex = 0;

    int[][] adj = new int[vs.length + 1][];
    adj[0] = new int[0];

    for (int i = 0; i < vs.length; i++) {
      IntVar v = vs[i];

      adj[i + 1] = new int[v.dom().getSize()];
      int j = 0;
      for (ValueEnumeration e = v.dom().valueEnumeration(); e.hasMoreElements(); ) {
        int el = e.nextElement();
        Integer elIndex = valueMap.get(el);
        if (elIndex == null) {
          valueMap.put(el, valueIndex);
          adj[i + 1][j] = valueIndex + 1;
          valueIndex++;
        } else {
          adj[i + 1][j] = elIndex + 1;
        }
        j++;
      }
    }

    // compute maximal value for count
    BipartiteGraphMatching matcher = new BipartiteGraphMatching(adj, vs.length, valueMap.size());
    int maxNumberDifferent = matcher.hopcroftKarp();

    return maxNumberDifferent < vs.length; // not satisfied
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : AlldifferentExcept([");

    for (int i = 0; i < list.length; i++) {
      result.append(list[i]);
      if (i < list.length - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(s).append(")");

    return result.toString();
  }
}
