/*
 * AllEqual.java
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

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/**
 * Constraints forall i != j: x[i] #= x[j].
 *
 * <p>Domain consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class AllEqual extends PrimitiveConstraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies a left hand variable in equality constraint. */
  private final IntVar[] x;

  private final int n;

  private TimeStamp<Integer> position;

  /**
   * It constructs constraint x[i] = x[j].
   *
   * @param x variables x.
   */
  public AllEqual(IntVar[] x) {

    checkInputForNullness(new String[] {"x"}, new Object[] {x});

    numberId = idNumber.incrementAndGet();

    this.x = x;
    this.n = x.length;

    setScope(x);
  }

  @Override
  public void consistency(final Store store) {

    // bottom up
    for (int i = 1; i < n; i++) {

      // domain consistency
      x[i - 1].domain.in(store.level, x[i - 1], x[i].domain);

      x[i].domain.in(store.level, x[i], x[i - 1].domain);
    }

    // top down
    for (int i = n - 2; i >= 0; i--) {

      // domain consistency
      x[i + 1].domain.in(store.level, x[i], x[i].domain);

      x[i].domain.in(store.level, x[i], x[i + 1].domain);
    }
  }

  @Override
  public void include(Store store) {
    position = new TimeStamp<>(store, 0);
  }

  @Override
  public void notConsistency(final Store store) {

    int start = position.value();

    for (int i = start; i < n; i++) {
      if (x[i].singleton()) {
        if (start == 0) {
          swap(start++, i);
        } else if (x[0].value() == x[i].value()) {
          swap(start++, i);
        } else {
          removeConstraint();
          return;
        }
      }
    }

    if (start == n - 1) {
      x[start].domain.inComplement(store.level, x[start], x[0].value());
    } else if (start == n) {
      throw Store.failException;
    }

    position.update(start);
  }

  private void swap(int i, int j) {
    if (i != j) {
      IntVar tmp = x[i];
      x[i] = x[j];
      x[j] = tmp;
    }
  }

  @Override
  public boolean satisfied() {

    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (!(x[i].singleton() && x[j].singleton() && x[i].value() == x[j].value())) {
          return false;
        }
      }
    }
    return true;
  }

  @Override
  public boolean notSatisfied() {

    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (i != j && !x[i].domain.isIntersecting(x[j].domain)) {
          return true;
        }
      }
    }
    return false;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public String toString() {
    return id() + " : AllEqual(" + Arrays.asList(x) + " )";
  }
}
