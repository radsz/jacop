/*
 * Increasing.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Increasing constraint assures that all variables are in increasing order.
 *
 * <p>After the first call, the constraint propagates only from the positions whose variables have
 * changed since the last call, forward for the lower bounds and backward for the upper bounds, and
 * stops as soon as a bound does not change (as Gecode's NaryLqLe and Choco's PropIncreasing).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Increasing extends Constraint implements UsesQueueVariable {

  static final AtomicInteger idNumber = new AtomicInteger(0);
  final IntVar[] x;
  final int n;
  // List of decomposed constraints
  protected List<Constraint> constraints;
  byte strict = 0;
  // true when a variable occurs more than once in x
  private final boolean hasDuplicates;

  // position of each variable of x; built at impose for distinct variables only
  private Map<Var, Integer> position;

  // position of each variable of x by its index in the store, when these indexes are close
  private int[] positionByStoreIndex;
  private int firstStoreIndex;

  // positions changed since the last call, without repetitions
  private int[] changed;
  private boolean[] isChanged;
  private int changedSize;

  // true until the first call, which propagates over all positions
  private boolean propagateAll = true;

  /**
   * It constructs an increasing constraint.
   *
   * @param x variables which must be in increasing order.
   */
  public Increasing(IntVar[] x) {

    checkInputForNullness("x", x);

    this.numberId = idNumber.incrementAndGet();
    this.x = Arrays.copyOf(x, x.length);
    this.n = x.length;
    this.hasDuplicates = Arrays.stream(x).distinct().count() < n;

    this.queueIndex = 1;

    setScope(x);
  }

  /**
   * It constructs an increasing constraint.
   *
   * @param x variables which must be in increasing order.
   * @param strict true if strict increasing order is required, false otherwise.
   */
  public Increasing(IntVar[] x, boolean strict) {
    this(x);

    if (strict) {
      this.strict = 1;
    }
  }

  /**
   * It constructs an increasing constraint.
   *
   * @param x variables which must be in increasing order.
   */
  public Increasing(List<? extends IntVar> x) {
    this(x.toArray(new IntVar[0]));
  }

  /**
   * It constructs an increasing constraint.
   *
   * @param x variables which must be in increasing order.
   * @param strict true if strict increasing order is required, false otherwise.
   */
  public Increasing(List<? extends IntVar> x, boolean strict) {
    this(x.toArray(new IntVar[0]), strict);
  }

  @Override
  public void impose(Store store) {
    super.impose(store);
    if (!hasDuplicates) {
      int minIndex = Integer.MAX_VALUE;
      int maxIndex = Integer.MIN_VALUE;
      for (IntVar v : x) {
        minIndex = Math.min(minIndex, v.index());
        maxIndex = Math.max(maxIndex, v.index());
      }
      if (minIndex >= 0 && (long) maxIndex - minIndex < 4L * n + 64) {
        firstStoreIndex = minIndex;
        positionByStoreIndex = new int[maxIndex - minIndex + 1];
        for (int i = 0; i < n; i++) {
          positionByStoreIndex[x[i].index() - minIndex] = i;
        }
      } else {
        position = new HashMap<>();
        for (int i = 0; i < n; i++) {
          position.put(x[i], i);
        }
      }
      changed = new int[n];
      isChanged = new boolean[n];
    }
    propagateAll = true;
  }

  @Override
  public void queueVariable(int level, Var var) {
    int i;
    if (positionByStoreIndex != null) {
      i = positionByStoreIndex[var.index() - firstStoreIndex];
    } else if (position != null) {
      i = position.get(var);
    } else {
      return;
    }
    if (!isChanged[i]) {
      isChanged[i] = true;
      changed[changedSize++] = i;
    }
  }

  @Override
  public void consistency(Store store) {

    if (hasDuplicates || propagateAll) {
      propagateAllPositions(store);
      propagateAll = false;
      clearChanged();
      return;
    }

    // inMin never changes a maximum and inMax never changes a minimum, so the forward and the
    // backward propagation from each changed position are independent. A pass stops when the
    // next bound already holds, because from there on the bounds held at the last fixpoint.
    // Positions changed by these passes are queued too; they need no further propagation.
    int size = changedSize;
    for (int k = 0; k < size; k++) {
      int p = changed[k];
      for (int i = p + 1; i < n; i++) {
        int lb = x[i - 1].min() + strict;
        if (x[i].min() >= lb) {
          break;
        }
        x[i].domain.inMin(store.level, x[i], lb);
      }
      for (int i = p; i > 0; i--) {
        int ub = x[i].max() - strict;
        if (x[i - 1].max() <= ub) {
          break;
        }
        x[i - 1].domain.inMax(store.level, x[i - 1], ub);
      }
    }
    clearChanged();
  }

  private void clearChanged() {
    for (int k = 0; k < changedSize; k++) {
      isChanged[changed[k]] = false;
    }
    changedSize = 0;
  }

  private void propagateAllPositions(Store store) {

    // lower bounds forward, then upper bounds backward; inMax never changes a minimum, so for
    // distinct variables the two passes reach the fixpoint. A repeated variable can be changed
    // behind a pass, so then the passes are repeated.
    do {
      store.propagationHasOccurred = false;
      for (int i = 1; i < n; i++) {
        int lb = x[i - 1].min() + strict;
        if (x[i].min() < lb) {
          x[i].domain.inMin(store.level, x[i], lb);
        }
      }
      for (int i = n - 1; i > 0; i--) {
        int ub = x[i].max() - strict;
        if (x[i - 1].max() > ub) {
          x[i - 1].domain.inMax(store.level, x[i - 1], ub);
        }
      }
    } while (hasDuplicates && store.propagationHasOccurred);
  }

  @Override
  public List<Constraint> decompose(Store store) {
    List<Constraint> cs = new ArrayList<>();

    for (int i = 1; i < n; i++) {
      if (strict == 1) {
        cs.add(new XltY(x[i - 1], x[i]));
      } else {
        cs.add(new XlteqY(x[i - 1], x[i]));
      }
    }

    return cs;
  }

  @Override
  public void imposeDecomposition(Store store) {

    if (constraints == null) {
      constraints = decompose(store);
    }

    for (Constraint c : constraints) {
      store.impose(c);
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : Increasing([");

    for (int i = 0; i < n; i++) {
      result.append(x[i]);
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(strict == 1 ? "strict" : "non-strict").append(")");

    return result.toString();
  }
}
