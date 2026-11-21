/*
 * FlowReason.java
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

import java.util.IdentityHashMap;
import java.util.Map;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Reasons for lazy clause generation of the constraints propagated with a {@link BoundedFlow}
 * ({@link SymmetricGCC}, {@link CardinalityMatrix}, {@link Same}, {@link UsedBy}), by the cuts of
 * their networks (G. Downing, T. Feydy and P. J. Stuckey, "Explaining flow-based propagation",
 * CPAIOR 2012). An atom is explained by the network of the domains just before it, with the
 * negation of the atom in place of the domain of its variable; when that network has no feasible
 * circulation, a set X of nodes has arcs entering it whose lower bounds exceed the upper bounds of
 * the arcs leaving it (Hoffman's theorem), and the reason is the atoms that give those bounds: the
 * removals of the values whose arcs leave X missing, and the bounds of the counters on the arcs
 * across X. A failure is explained the same way by the network now.
 *
 * <p>This class reads the domains before a trail position, with the negated atom applied, and
 * gathers the atoms an explanation cites. Bounds are collected first and cited once per variable,
 * by the weakest atom that gives them. The constraint builds the network from what this class reads
 * and checks that its cut does violate Hoffman's condition before it gives the reason, so a reason
 * is never wrong, only absent.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class FlowReason {

  private final AtomicTrail trail;
  private final int position;
  private final EntryList out;
  private final int mark;
  private final EntryList scratch = new EntryList();

  // the negated atom: its variable (null for a failure), kind and value
  private IntVar negated;
  private int negatedKind;
  private int negatedValue;

  // per variable the lower bound and the upper bound the reason must give
  private final Map<IntVar, long[]> needs = new IdentityHashMap<>();
  private boolean broken;

  /**
   * Starts a reason.
   *
   * @param trail the trail
   * @param position the trail position (the explained entry, or the size of the trail for a
   *     failure)
   * @param out where the reason entries are added
   */
  FlowReason(AtomicTrail trail, int position, EntryList out) {
    this.trail = trail;
    this.position = position;
    this.out = out;
    this.mark = out.size();
  }

  /**
   * A reason of the atom of an entry: the network is read with the negation of that atom.
   *
   * @param trail the trail
   * @param entry the entry
   * @param out where the reason entries are added
   * @return the reason
   */
  static FlowReason ofEntry(AtomicTrail trail, int entry, EntryList out) {
    FlowReason reason = new FlowReason(trail, entry, out);
    reason.negated = trail.variable(entry);
    reason.negatedKind = trail.kind(entry);
    reason.negatedValue = trail.value(entry);
    return reason;
  }

  /**
   * The variable of the negated atom.
   *
   * @return the variable, null for a failure
   */
  IntVar negated() {
    return negated;
  }

  /** Drops what was gathered, for another try with another network. */
  void clear() {
    needs.clear();
    broken = false;
    out.truncate(mark);
  }

  /**
   * The domain a variable's atoms are relative to.
   *
   * @param z the variable
   * @return its initial domain, which must not be changed
   */
  IntDomain root(IntVar z) {
    return trail.rootDomain(z);
  }

  /**
   * The minimum of a variable before the position, with the negated atom.
   *
   * @param z the variable
   * @return its minimum
   */
  int min(IntVar z) {
    int min = trail.minBefore(z, position);
    if (z == negated) {
      if (negatedKind == AtomicTrail.LE) {
        min = (int) Math.max(min, (long) negatedValue + 1);
      } else if (negatedKind == AtomicTrail.NE) {
        min = Math.max(min, negatedValue);
      }
    }
    return min;
  }

  /**
   * The maximum of a variable before the position, with the negated atom.
   *
   * @param z the variable
   * @return its maximum
   */
  int max(IntVar z) {
    int max = trail.maxBefore(z, position);
    if (z == negated) {
      if (negatedKind == AtomicTrail.GE) {
        max = (int) Math.min(max, (long) negatedValue - 1);
      } else if (negatedKind == AtomicTrail.NE) {
        max = Math.min(max, negatedValue);
      }
    }
    return max;
  }

  /**
   * Whether a variable may take a value before the position, with the negated atom.
   *
   * @param z the variable
   * @param v the value
   * @return true when v is in its domain
   */
  boolean contains(IntVar z, int v) {
    if (v < min(z) || v > max(z) || !trail.rootDomain(z).contains(v)) {
      return false;
    }
    if (z == negated && negatedKind == AtomicTrail.NE) {
      return true;
    }
    scratch.clear();
    return !trail.excludedBefore(z, v, position, scratch);
  }

  /**
   * Cites that a variable cannot take a value, which {@link #contains} said.
   *
   * @param z the variable
   * @param v the value
   */
  void exclude(IntVar z, int v) {
    if (!trail.rootDomain(z).contains(v) || negationExcludes(z, v)) {
      return;
    }
    int min = trail.minBefore(z, position);
    int max = trail.maxBefore(z, position);
    if (v < min) {
      needLower(z, (long) v + 1);
    } else if (v > max) {
      needUpper(z, (long) v - 1);
    } else if (!trail.excludedBefore(z, v, position, out)) {
      broken = true;
    }
  }

  private boolean negationExcludes(IntVar z, int v) {
    if (z != negated) {
      return false;
    }
    return switch (negatedKind) {
      case AtomicTrail.GE -> v >= negatedValue;
      case AtomicTrail.LE -> v <= negatedValue;
      default -> v != negatedValue;
    };
  }

  /**
   * Cites that a variable is at least a bound.
   *
   * @param z the variable
   * @param bound the bound
   */
  void needLower(IntVar z, long bound) {
    long[] need = needs.computeIfAbsent(z, k -> new long[] {Long.MIN_VALUE, Long.MAX_VALUE});
    need[0] = Math.max(need[0], bound);
  }

  /**
   * Cites that a variable is at most a bound.
   *
   * @param z the variable
   * @param bound the bound
   */
  void needUpper(IntVar z, long bound) {
    long[] need = needs.computeIfAbsent(z, k -> new long[] {Long.MIN_VALUE, Long.MAX_VALUE});
    need[1] = Math.min(need[1], bound);
  }

  /**
   * Cites the bounds gathered and sorts the reason.
   *
   * @return false when some cited fact did not hold before the position, so there is no reason
   */
  boolean finish() {
    if (broken) {
      return false;
    }
    for (Map.Entry<IntVar, long[]> e : needs.entrySet()) {
      IntVar z = e.getKey();
      long[] need = e.getValue();
      if (need[0] != Long.MIN_VALUE
          && !(z == negated && min(z) >= need[0] && negationGives(true))) {
        if (!cite(trail.earliestLowerBound(z, need[0], position))) {
          return false;
        }
      }
      if (need[1] != Long.MAX_VALUE
          && !(z == negated && max(z) <= need[1] && negationGives(false))) {
        if (!cite(trail.earliestUpperBound(z, need[1], position))) {
          return false;
        }
      }
    }
    out.sortUnique(mark);
    return true;
  }

  // whether the negated atom gives the variable's lower (or upper) bound beyond the domain before
  private boolean negationGives(boolean lower) {
    return negatedKind == AtomicTrail.NE
        || negatedKind == (lower ? AtomicTrail.LE : AtomicTrail.GE);
  }

  private boolean cite(int e) {
    if (e == Integer.MAX_VALUE) {
      return false;
    }
    if (e >= 0) {
      out.add(e);
    }
    return true;
  }

  /**
   * Whether the cut of a network that has no feasible circulation violates Hoffman's condition: the
   * lower bounds of the arcs entering it add up to more than the upper bounds of the arcs leaving
   * it.
   *
   * @param flow the network, after a {@link BoundedFlow#solve} that returned false
   * @return true when the cut proves infeasibility
   */
  static boolean violated(BoundedFlow flow) {
    if (!flow.hasCut()) {
      return false;
    }
    long entering = 0;
    long leaving = 0;
    for (int a = 0; a < flow.arcCount(); a++) {
      boolean tail = flow.inCut(flow.tail(a));
      boolean head = flow.inCut(flow.head(a));
      if (tail && !head) {
        leaving += flow.upper(a);
      } else if (!tail && head) {
        entering += flow.lower(a);
      }
    }
    return entering > leaving;
  }
}
