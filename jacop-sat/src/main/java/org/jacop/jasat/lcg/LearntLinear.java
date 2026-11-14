/*
 * LearntLinear.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.lcg;

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;

/**
 * A linear inequality {@code sum a[i] * x[i] <= c} learnt by cut-based conflict analysis ({@link
 * LinearConflict}), propagated on bounds and explained by its linear form. The caller makes sure
 * the sum of the largest magnitudes of the terms fits in a long.
 */
final class LearntLinear extends Constraint implements LinearExplainable {

  private static final AtomicInteger idNumber = new AtomicInteger(0);

  private final IntVar[] x;
  private final long[] a;
  private final long c;
  private final LinearForm form;

  LearntLinear(LinearForm f) {
    super(f.vars());
    numberId = idNumber.incrementAndGet();
    x = f.vars();
    a = f.weights();
    c = f.c();
    form = f;
  }

  @Override
  public LinearForm linearForm() {
    return form;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void consistency(Store store) {
    long min = 0;
    for (int i = 0; i < x.length; i++) {
      min += a[i] * (a[i] > 0 ? x[i].min() : x[i].max());
    }
    long slack = c - min;
    if (slack < 0) {
      throw Store.failException;
    }
    // one pass is a fixpoint: a pruned bound is not one the smallest sum reads
    for (int i = 0; i < x.length; i++) {
      long w = a[i];
      if (w > 0) {
        long room = slack / w;
        if (x[i].max() - (long) x[i].min() > room) {
          x[i].domain.inMax(store.level, x[i], (int) (x[i].min() + room));
        }
      } else {
        long room = slack / -w;
        if (x[i].max() - (long) x[i].min() > room) {
          x[i].domain.inMin(store.level, x[i], (int) (x[i].max() - room));
        }
      }
    }
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder(id()).append(" : LearntLinear(");
    for (int i = 0; i < x.length; i++) {
      s.append(i == 0 ? "" : " + ").append(a[i]).append('*').append(x[i].id());
    }
    return s.append(" <= ").append(c).append(')').toString();
  }
}
