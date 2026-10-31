/*
 * LinearForm.java
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

package org.jacop.lcg;

import java.util.Arrays;
import org.jacop.core.IntVar;

/**
 * A constraint written as {@code sum weights[i] * vars[i] rel c}, with rel one of {@code <=},
 * {@code >=}, {@code =} and {@code !=}, from which {@link LinearExplainable} explains it.
 *
 * @param vars the variables; one may occur more than once
 * @param weights their weights
 * @param c the right-hand side
 * @param relation {@link #LE}, {@link #GE}, {@link #EQ} or {@link #NE}
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public record LinearForm(IntVar[] vars, long[] weights, long c, int relation) {

  /** The relation {@code <=}. */
  public static final int LE = 0;

  /** The relation {@code >=}. */
  public static final int GE = 1;

  /** The relation {@code =}. */
  public static final int EQ = 2;

  /** The relation {@code !=}. */
  public static final int NE = 3;

  /**
   * Returns the negation of this constraint.
   *
   * @return the same sum with the opposite relation
   */
  public LinearForm negated() {
    return switch (relation) {
      case LE -> new LinearForm(vars, weights, c + 1, GE);
      case GE -> new LinearForm(vars, weights, c - 1, LE);
      case EQ -> new LinearForm(vars, weights, c, NE);
      default -> new LinearForm(vars, weights, c, EQ);
    };
  }

  /**
   * Adds to {@code out} the reason of an entry this constraint propagated, for an inequality or
   * equality only when the bounds of the other variables imply it (a propagator on domains may
   * prune further).
   *
   * @param trail the trail
   * @param entry the entry
   * @param out where the reason entries are added
   * @return false when there is no such reason
   */
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return relation == NE
        ? LinearExplanation.explainNotEqual(trail, entry, vars, weights, c, out)
        : LinearExplanation.explainChecked(
            trail, entry, vars, weights, c, relation != GE, relation != LE, out);
  }

  /**
   * Adds to {@code out} the reason of a failure of this constraint now.
   *
   * @param trail the trail
   * @param out where the reason entries are added
   * @return false when there is no such reason
   */
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return relation == NE
        ? LinearExplanation.explainNotEqualFailure(trail, vars, weights, c, out)
        : LinearExplanation.explainFailure(
            trail, vars, weights, c, relation != GE, relation != LE, out);
  }

  /**
   * Adds to {@code out} the reason why this constraint holds for every assignment of the domains
   * just before a trail position.
   *
   * @param trail the trail
   * @param position the trail position (an entry index, or {@link AtomicTrail#size()} for now)
   * @param out where the reason entries are added
   * @return false when it is not entailed by the bounds (and, for one free variable of {@code !=},
   *     its holes), or a sum overflows a {@code long}
   */
  public boolean explainEntailed(AtomicTrail trail, int position, EntryList out) {
    long smallest = 0;
    long largest = 0;
    try {
      for (int i = 0; i < vars.length; i++) {
        long lo = Math.multiplyExact(weights[i], trail.minBefore(vars[i], position));
        long hi = Math.multiplyExact(weights[i], trail.maxBefore(vars[i], position));
        smallest = Math.addExact(smallest, Math.min(lo, hi));
        largest = Math.addExact(largest, Math.max(lo, hi));
      }
    } catch (ArithmeticException overflow) {
      return false;
    }
    // the bounds cited are lifted: on the side that holds, the sum's bound may move by the slack
    switch (relation) {
      case LE -> {
        if (largest > c) {
          return false;
        }
        addLifted(trail, position, false, c - largest, out);
      }
      case GE -> {
        if (smallest < c) {
          return false;
        }
        addLifted(trail, position, true, smallest - c, out);
      }
      case EQ -> {
        if (smallest != c || largest != c) {
          return false;
        }
        addLifted(trail, position, false, 0, out);
        addLifted(trail, position, true, 0, out);
      }
      default -> {
        if (smallest > c) {
          addLifted(trail, position, true, smallest - c - 1, out);
        } else if (largest < c) {
          addLifted(trail, position, false, c - 1 - largest, out);
        } else {
          return notEqualByHole(trail, position, out);
        }
      }
    }
    return true;
  }

  // the bounds that make the sum smallest (lowerSum) or largest, weakened within the slack
  private void addLifted(
      AtomicTrail trail, int position, boolean lowerSum, long slack, EntryList out) {
    LinearExplanation.addLiftedBounds(
        trail, position, vars, weights, -1, null, lowerSum, slack, out);
  }

  // != with every variable but one fixed, whose value that would make the sum c is a hole
  private boolean notEqualByHole(AtomicTrail trail, int position, EntryList out) {
    int free = -1;
    long rest = c;
    for (int i = 0; i < vars.length; i++) {
      int lo = trail.minBefore(vars[i], position);
      if (lo == trail.maxBefore(vars[i], position)) {
        try {
          rest = Math.subtractExact(rest, Math.multiplyExact(weights[i], lo));
        } catch (ArithmeticException overflow) {
          return false;
        }
      } else if (free < 0 || vars[free] == vars[i]) {
        // a repeated free variable would need its weights summed; only one occurrence is handled
        if (free >= 0) {
          return false;
        }
        free = i;
      } else {
        return false;
      }
    }
    if (free < 0 || weights[free] == 0) {
      return false;
    }
    if (rest % weights[free] != 0) {
      addFixed(trail, position, free, out);
      return true;
    }
    long v = rest / weights[free];
    if (v < Integer.MIN_VALUE
        || v > Integer.MAX_VALUE
        || !trail.excludedBefore(vars[free], (int) v, position, out)) {
      return false;
    }
    addFixed(trail, position, free, out);
    return true;
  }

  private void addFixed(AtomicTrail trail, int position, int free, EntryList out) {
    for (int i = 0; i < vars.length; i++) {
      if (i != free) {
        trail.addLowerBound(vars[i], position, out);
        trail.addUpperBound(vars[i], position, out);
      }
    }
  }

  @Override
  public boolean equals(Object o) {
    return o instanceof LinearForm f
        && c == f.c
        && relation == f.relation
        && Arrays.equals(vars, f.vars)
        && Arrays.equals(weights, f.weights);
  }

  @Override
  public int hashCode() {
    return 31 * (31 * (31 * Arrays.hashCode(vars) + Arrays.hashCode(weights)) + Long.hashCode(c))
        + relation;
  }

  @Override
  public String toString() {
    return "LinearForm[vars="
        + Arrays.toString(vars)
        + ", weights="
        + Arrays.toString(weights)
        + ", c="
        + c
        + ", relation="
        + relation
        + "]";
  }
}
