/*
 * AbstractArgMinMax.java
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
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.InitOnce;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Abstract base for ArgMax and ArgMin constraints. Provides shared fields, constructor logic,
 * default pruning events, and custom per-variable pruning event logic.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractArgMinMax extends Constraint implements SatisfiedPresent {

  /** It specifies a list of variables among which the extremum is being searched for. */
  protected final IntVar[] list;

  /** It specifies variable which stores the index of the extremum. */
  protected final IntVar extremeIndex;

  /** It specifies indexOffset within an element constraint list[index-indexOffset] = value. */
  protected int indexOffset;

  final InitOnce init = new InitOnce();

  /** Scratch array: prefixWorst[i] is the best of the worst values of list[0..i-1]. */
  private final int[] prefixWorst;

  /** Scratch array: suffixWorst[i] is the best of the worst values of list[i..n-1]. */
  private final int[] suffixWorst;

  /**
   * Constructs an arg-min/max constraint.
   *
   * @param idNum the id counter for the concrete subclass.
   * @param list the array of variables.
   * @param extremeIndex variable denoting the index of the extremum.
   */
  protected AbstractArgMinMax(AtomicInteger idNum, IntVar[] list, IntVar extremeIndex) {

    checkInputForNullness(new String[] {"list", "extremeIndex"}, list, new Object[] {extremeIndex});
    if (list.length == 0) {
      throw new IllegalArgumentException(
          "Constraint " + getClass().getSimpleName() + " needs a non-empty list");
    }

    this.queueIndex = 1;
    this.numberId = idNum.incrementAndGet();
    this.indexOffset = 0;
    this.extremeIndex = extremeIndex;
    this.list = Arrays.copyOf(list, list.length);
    this.prefixWorst = new int[list.length + 1];
    this.suffixWorst = new int[list.length + 1];

    setScope(Stream.concat(Arrays.stream(list), Stream.of(extremeIndex)));
  }

  /**
   * Checks entailment: the index is fixed to a position that holds the first extremum, so every
   * earlier element is strictly worse and every later one is worse or equal, whatever their values.
   *
   * @param max true for the maximum (ArgMax), false for the minimum (ArgMin).
   * @return true if the constraint is entailed.
   */
  protected boolean firstExtremumEntailed(boolean max) {
    if (!extremeIndex.singleton()) {
      return false;
    }
    int idx = extremeIndex.value() - 1 - indexOffset;
    if (idx < 0 || idx >= list.length || !list[idx].singleton()) {
      return false;
    }
    int extreme = list[idx].value();
    int strict = max ? -1 : 1;
    for (int i = 0; i < list.length; i++) {
      int bound = i < idx ? extreme + strict : extreme;
      if (max ? list[i].max() > bound : list[i].min() < bound) {
        return false;
      }
    }
    return true;
  }

  /**
   * Restricts the index to the positions that can still hold the first extremum. Position i can
   * hold the first maximum only if max(x[i]) exceeds min(x[j]) of every earlier element j and
   * reaches min(x[j]) of every later element j; the minimum is the mirror. When the list has no
   * repeated variables, x[i] at its best bound and every other element at its worst bound is a
   * support, so every index kept has a support (Gange and Stuckey, CP 2020). It runs in O(n).
   *
   * @param store the constraint store.
   * @param max true for the maximum (ArgMax), false for the minimum (ArgMin).
   */
  protected void pruneIndexToFirstExtremum(Store store, boolean max) {
    int n = list.length;
    prefixWorst[0] = IntDomain.MIN_INT;
    for (int i = 0; i < n; i++) {
      prefixWorst[i + 1] = Math.max(prefixWorst[i], worst(i, max));
    }
    suffixWorst[n] = IntDomain.MIN_INT;
    for (int i = n - 1; i >= 0; i--) {
      suffixWorst[i] = Math.max(suffixWorst[i + 1], worst(i, max));
    }
    int kept = 0;
    int removed = 0;
    for (ValueEnumeration e = extremeIndex.dom().valueEnumeration(); e.hasMoreElements(); ) {
      if (canBeFirst(e.nextElement() - 1 - indexOffset, max)) {
        kept++;
      } else {
        removed++;
      }
    }
    if (kept == 0) {
      throw Store.failException;
    }
    if (removed == 0) {
      return;
    }
    IntervalDomain idxDomain = new IntervalDomain();
    for (ValueEnumeration e = extremeIndex.dom().valueEnumeration(); e.hasMoreElements(); ) {
      int cp = e.nextElement();
      if (canBeFirst(cp - 1 - indexOffset, max)) {
        if (idxDomain.getSize() == 0) {
          idxDomain.unionAdapt(cp, cp);
        } else {
          idxDomain.addLastElement(cp);
        }
      }
    }
    extremeIndex.domain.in(store.level, extremeIndex, idxDomain);
  }

  private boolean canBeFirst(int i, boolean max) {
    int best = best(i, max);
    return best > prefixWorst[i] && best >= suffixWorst[i + 1];
  }

  // Values are negated for the minimum, so that larger is always better.
  private int best(int i, boolean max) {
    return max ? list[i].max() : -list[i].min();
  }

  private int worst(int i, boolean max) {
    return max ? list[i].min() : -list[i].max();
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {

    // If consistency function mode
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }

    if (v == extremeIndex) {
      return IntDomain.ANY;
    } else {
      return IntDomain.BOUND;
    }
  }
}
