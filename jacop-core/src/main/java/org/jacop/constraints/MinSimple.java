/*
 * MinSimple.java
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

import java.util.List;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Simplifiable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.MaxExplanation;

/**
 * MinSimple constraint implements the minimum/2 constraint. It provides the minimum variable from
 * all variables on the list.
 *
 * <p>min(x1, x2) = min.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class MinSimple extends Constraint
    implements Simplifiable, SatisfiedPresent, Copyable<MinSimple>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies a variables between which a minimum value is being searched for. */
  private final IntVar x1;

  private final IntVar x2;

  /** It specifies variable min which stores the minimum value present in the list. */
  private final IntVar min;

  /**
   * It constructs min constraint.
   *
   * @param min variable denoting the minimum value
   * @param x1 first variable for which a minimum value is imposed.
   * @param x2 second variable for which a minimum value is imposed.
   */
  public MinSimple(IntVar x1, IntVar x2, IntVar min) {

    checkInputForNullness(new String[] {"x1", "x2", "min"}, new Object[] {x1, x2, min});

    this.numberId = idNumber.incrementAndGet();
    this.min = min;
    this.x1 = x1;
    this.x2 = x2;

    this.queueIndex = 1;

    setScope(x1, x2, min);
  }

  @Override
  public void consistency(final Store store) {

    do {

      store.propagationHasOccurred = false;

      int minMin = min.min();

      x1.domain.inMin(store.level, x1, minMin);
      x2.domain.inMin(store.level, x2, minMin);

      int minValue = Math.min(x1.min(), x2.min());
      int maxValue = Math.min(x1.max(), x2.max());

      min.domain.in(store.level, min, minValue, maxValue);

      if (x1.min() > min.max()) {
        x2.domain.in(store.level, x2, min.dom());
      }
      if (x2.min() > min.max()) {
        x1.domain.in(store.level, x1, min.dom());
      }

    } while (store.propagationHasOccurred);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    // once one of x1 and x2 is above min, the other takes the domain of min, so a value
    // removed inside the domain of min must wake the constraint as well
    if (v == min
        && (consistencyPruningEvents == null || !consistencyPruningEvents.containsKey(v))) {
      return IntDomain.ANY;
    }
    return super.getConsistencyPruningEvent(v);
  }

  /**
   * Checks if the constraint is satisfied.
   *
   * @return true if the constraint is satisfied, false otherwise.
   */
  public boolean satisfied() {

    if (!min.singleton()) {
      return false;
    }
    int minVal = min.value();
    return x1.min() >= minVal
        && x2.min() >= minVal
        && (x1.singleton(minVal) || x2.singleton(minVal));
  }

  @Override
  public String toString() {

    return id() + " : minSimple(" + x1 + ", " + x2 + ", " + min + ")";
  }

  @Override
  public Optional<List<Constraint>> simplify() {
    if (getClass() != MinSimple.class) {
      return Optional.empty();
    }
    return GlobalSimplification.extremum(new IntVar[] {x1, x2}, min, false, null);
  }

  @Override
  public MinSimple copy(VarMap map) {
    return new MinSimple(map.get(x1), map.get(x2), map.get(min));
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return getClass() == MinSimple.class
        && MaxExplanation.explain(trail, entry, new IntVar[] {x1, x2}, min, false, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == MinSimple.class
        && MaxExplanation.explainFailure(trail, new IntVar[] {x1, x2}, min, false, out);
  }
}
