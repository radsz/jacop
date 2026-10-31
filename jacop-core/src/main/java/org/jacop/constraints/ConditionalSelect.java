/*
 * ConditionalSelect.java
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
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.ShiftExplanation;

/**
 * ConditionalSelect constraint enforces y = x[k], where k is the first index with b[k] = 1 (the
 * semantics of MiniZinc's if_then_else for integers). Unlike {@link Conditional} over equality
 * constraints, it reasons about the branches that are still possible before the selected one is
 * known: y is kept within the bounds of the branches whose x[i] can still equal y, a branch whose
 * x[i] cannot equal y is ruled out, and when only one branch remains it is selected.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ConditionalSelect extends Constraint
    implements SatisfiedPresent, Copyable<ConditionalSelect>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The 0/1 conditions; the first one equal to 1 selects the branch. */
  private final IntVar[] b;

  /** The branch values. */
  private final IntVar[] x;

  /** The selected value. */
  private final IntVar y;

  /**
   * It constructs a ConditionalSelect constraint.
   *
   * @param b 0/1 conditions
   * @param x branch values, one per condition
   * @param y the value of the first branch whose condition is 1
   */
  public ConditionalSelect(IntVar[] b, IntVar[] x, IntVar y) {

    checkInputForNullness(new String[] {"b", "x", "y"}, new Object[] {b, x, y});
    if (b.length != x.length) {
      throw new IllegalArgumentException(
          "ConditionalSelect: the lists of conditions and values must have the same length");
    }
    if (b.length == 0) {
      throw new IllegalArgumentException(
          "ConditionalSelect: the lists of conditions and values must not be empty");
    }
    for (IntVar be : b) {
      if (be.min() < 0 || be.max() > 1) {
        throw new IllegalArgumentException(
            "ConditionalSelect: the conditions must be 0/1 variables, not " + be);
      }
    }

    this.queueIndex = 0;
    this.numberId = idNumber.incrementAndGet();

    this.b = Arrays.copyOf(b, b.length);
    this.x = Arrays.copyOf(x, x.length);
    this.y = y;

    setScope(Stream.concat(Stream.concat(Arrays.stream(b), Arrays.stream(x)), Stream.of(y)));
  }

  @Override
  public void consistency(final Store store) {

    do {
      store.propagationHasOccurred = false;

      // the branches that can still be selected: up to the first condition fixed to 1,
      // skipping conditions fixed to 0; "feasible" ones can still give y its value
      boolean allBeforeFalse = true;
      int feasible = 0;
      int last = -1;
      int lo = Integer.MAX_VALUE;
      int hi = Integer.MIN_VALUE;
      for (int i = 0; i < b.length; i++) {
        if (b[i].max() == 0) {
          continue;
        }
        boolean forced = b[i].min() == 1;
        if (x[i].domain.isIntersecting(y.domain)) {
          feasible++;
          last = i;
          lo = Math.min(lo, x[i].min());
          hi = Math.max(hi, x[i].max());
        } else if (allBeforeFalse) {
          // the first reachable branch cannot give y its value, so it is not selected
          b[i].domain.inValue(store.level, b[i], 0);
          continue;
        }
        if (forced) {
          break;
        }
        allBeforeFalse = false;
      }

      if (feasible == 0) {
        throw Store.failException;
      }

      if (feasible == 1) {
        // the only branch left is the selected one: the reachable conditions before it are 0
        for (int i = 0; i < last; i++) {
          if (b[i].max() == 1) {
            b[i].domain.inValue(store.level, b[i], 0);
          }
        }
        b[last].domain.inValue(store.level, b[last], 1);
        y.domain.in(store.level, y, x[last].dom());
        x[last].domain.in(store.level, x[last], y.dom());
        if (y.singleton() && x[last].singleton()) {
          removeConstraint();
          return;
        }
      } else {
        y.domain.in(store.level, y, lo, hi);
      }

    } while (store.propagationHasOccurred);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {

    int i = 0;
    while (i < b.length && b[i].max() == 0) {
      i++;
    }
    return i < b.length && b[i].min() == 1 && y.singleton() && x[i].singleton(y.value());
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : ConditionalSelect(").append(Arrays.asList(b)).append(", ");
    result.append(Arrays.asList(x)).append(", ").append(y).append(" )");
    return result.toString();
  }

  @Override
  public ConditionalSelect copy(VarMap map) {
    return new ConditionalSelect(map.get(b), map.get(x), map.get(y));
  }

  // explanations for lazy clause generation; the semantics need some condition to be 1

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (getClass() != ConditionalSelect.class) {
      return false;
    }
    IntVar v = trail.variable(entry);
    int kind = trail.kind(entry);
    int mark = out.size();
    if (v == y && kind != AtomicTrail.NE && bound(trail, entry, kind == AtomicTrail.GE, out)) {
      return true;
    }
    out.truncate(mark);
    for (int i = 0; i < b.length; i++) {
      if (v == b[i] && kind != AtomicTrail.NE) {
        if (trail.value(entry) <= 0 && kind == AtomicTrail.LE) {
          // b[i] = 0: x[i] cannot give y its value and neither can any branch before it
          if (outBefore(trail, entry, i + 1, out)) {
            return true;
          }
          out.truncate(mark);
        } else if (kind == AtomicTrail.GE && trail.value(entry) >= 1) {
          // b[i] = 1: the branches before it are not selected, those after it cannot be
          if (falseBefore(trail, entry, i, out) && outAfter(trail, entry, i, out)) {
            return true;
          }
          out.truncate(mark);
        }
      }
    }
    // y and the selected branch are equal
    int k = selected(trail, entry, out);
    if (k >= 0) {
      if (v == y && ShiftExplanation.explain(trail, entry, y, x[k], 0, out)) {
        return true;
      }
      if (v == x[k] && x[k] != y && ShiftExplanation.explain(trail, entry, x[k], y, 0, out)) {
        return true;
      }
    }
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return getClass() == ConditionalSelect.class && outBefore(trail, trail.size(), b.length, out);
  }

  // y >= a (lower) or y <= a: every branch that can be selected is within the bound
  private boolean bound(AtomicTrail trail, int entry, boolean lower, EntryList out) {
    long a = trail.value(entry);
    for (int i = 0; i < b.length; i++) {
      if (isFalse(trail, entry, b[i], out)) {
        continue;
      }
      if (x[i] == y) {
        return false;
      }
      int e =
          lower
              ? trail.earliestLowerBound(x[i], a, entry)
              : trail.earliestUpperBound(x[i], a, entry);
      if (e == Integer.MAX_VALUE) {
        // a branch that cannot give y its value is left out of the bound
        if (!ShiftExplanation.disjointBefore(trail, entry, x[i], y, 0, out)) {
          return false;
        }
      } else if (e >= 0) {
        out.add(e);
      }
      if (isTrue(trail, entry, b[i], out)) {
        return true;
      }
    }
    return true;
  }

  // the branches from 0 to end - 1 are each not selected (condition 0) or cannot give y its value
  private boolean outBefore(AtomicTrail trail, int position, int end, EntryList out) {
    for (int i = 0; i < end; i++) {
      if (isFalse(trail, position, b[i], out)) {
        continue;
      }
      if (x[i] == y || !ShiftExplanation.disjointBefore(trail, position, x[i], y, 0, out)) {
        return false;
      }
      if (end == b.length && isTrue(trail, position, b[i], out)) {
        return true; // the branches after a condition of 1 are never selected
      }
    }
    return true;
  }

  // the branches after k, up to a condition of 1, cannot give y its value
  private boolean outAfter(AtomicTrail trail, int position, int k, EntryList out) {
    for (int i = k + 1; i < b.length; i++) {
      if (isFalse(trail, position, b[i], out)) {
        continue;
      }
      if (x[i] == y || !ShiftExplanation.disjointBefore(trail, position, x[i], y, 0, out)) {
        return false;
      }
      if (isTrue(trail, position, b[i], out)) {
        return true;
      }
    }
    return true;
  }

  private boolean falseBefore(AtomicTrail trail, int position, int k, EntryList out) {
    for (int i = 0; i < k; i++) {
      if (!isFalse(trail, position, b[i], out)) {
        return false;
      }
    }
    return true;
  }

  // the branch selected just before a position, with its reason, or -1
  private int selected(AtomicTrail trail, int position, EntryList out) {
    int mark = out.size();
    for (int i = 0; i < b.length; i++) {
      if (isFalse(trail, position, b[i], out)) {
        continue;
      }
      if (isTrue(trail, position, b[i], out)) {
        return i;
      }
      break;
    }
    out.truncate(mark);
    return -1;
  }

  // whether c was 0 just before a position, adding the atom that says so
  private static boolean isFalse(AtomicTrail trail, int position, IntVar c, EntryList out) {
    int e = trail.earliestUpperBound(c, 0, position);
    if (e == Integer.MAX_VALUE) {
      return false;
    }
    if (e >= 0) {
      out.add(e);
    }
    return true;
  }

  // whether c was 1 just before a position, adding the atom that says so
  private static boolean isTrue(AtomicTrail trail, int position, IntVar c, EntryList out) {
    int e = trail.earliestLowerBound(c, 1, position);
    if (e == Integer.MAX_VALUE) {
      return false;
    }
    if (e >= 0) {
      out.add(e);
    }
    return true;
  }
}
