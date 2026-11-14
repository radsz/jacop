/*
 * SetExplanation.java
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

package org.jacop.set.constraints;

import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.set.core.SetVar;

/**
 * Explanations for lazy clause generation of set constraints that hold element by element, such as
 * c = a ∩ b, which holds when c_e = a_e ∧ b_e for every element e. The membership of an element in
 * a set is the atom of its membership variable in the set's {@link SetMirror}, or a fact when the
 * element was in the greatest lower bound or outside the least upper bound when the mirror was
 * made.
 *
 * <p>A membership is explained by the memberships of the same element in the other sets, when the
 * relation on that element forces it; a failure, by the memberships of an element the relation
 * cannot hold on. Each reason is checked against the relation, and the reason falls back to the
 * generic one when it does not imply the atom (a membership that cardinality reasoning gave, for
 * example), so the explanations are sound for any propagator of a constraint that implies the
 * relation.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class SetExplanation {

  /** A relation on the memberships of one element in the sets of a constraint. */
  @FunctionalInterface
  interface Relation {

    /**
     * Tells whether memberships of an element satisfy the relation.
     *
     * @param element the element
     * @param in the membership of the element in each set, by argument position
     * @return true when they do
     */
    boolean holds(int element, boolean[] in);
  }

  private static final int OUT = 0;
  private static final int IN = 1;
  private static final int OPEN = 2;

  private SetExplanation() {}

  /**
   * Adds to {@code out} the reason of a membership atom: the memberships of its element in the
   * other sets that force it under the relation.
   *
   * @param trail the trail
   * @param entry the entry of the atom
   * @param sets the sets of the constraint, by argument position
   * @param relation the relation the constraint implies on every element
   * @param out where the reason entries are added
   * @return false when the entry is not a membership of these sets or the relation does not force
   *     it, so the generic reason is used
   */
  static boolean explain(
      AtomicTrail trail, int entry, SetVar[] sets, Relation relation, EntryList out) {
    IntVar x = trail.variable(entry);
    for (SetVar s : sets) {
      SetMirror m = mirrorOf(s);
      if (m == null) {
        continue;
      }
      int[] elements = m.elements();
      for (int e : elements) {
        if (m.member(e) == x) {
          return explainElement(trail, entry, sets, relation, e, out);
        }
      }
    }
    return false;
  }

  /**
   * Adds to {@code out} the reason of a failure now: the memberships of an element that the
   * relation cannot hold on.
   *
   * @param trail the trail
   * @param sets the sets of the constraint, by argument position
   * @param relation the relation the constraint implies on every element
   * @param out where the reason entries are added
   * @return false when the relation holds on every element, so the generic reason is used
   */
  static boolean explainFailure(
      AtomicTrail trail, SetVar[] sets, Relation relation, EntryList out) {
    int position = trail.size();
    for (SetVar s : sets) {
      SetMirror m = mirrorOf(s);
      if (m == null) {
        continue;
      }
      for (int e : m.elements()) {
        int[] state = states(trail, sets, e, position);
        if (!satisfiable(sets, state, relation, e, null, false)) {
          minimize(sets, state, relation, e, null, false);
          addAtoms(trail, sets, state, e, position, out);
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Adds to {@code out} the reason of a bound of a set's cardinality, or of a membership, that the
   * elements the relation forces into the set (or out of it) give with the other bound, when the
   * mirror alone does not: the constraint changed the set and its domain derived the atom.
   *
   * @param trail the trail
   * @param entry the entry of the atom
   * @param sets the sets of the constraint, by argument position
   * @param relation the relation the constraint implies on every element
   * @param out where the reason entries are added
   * @return false when the forced memberships do not give the atom
   */
  static boolean explainCardinality(
      AtomicTrail trail, int entry, SetVar[] sets, Relation relation, EntryList out) {
    IntVar y = trail.variable(entry);
    int kind = trail.kind(entry);
    for (SetVar s : sets) {
      SetMirror m = mirrorOf(s);
      if (m == null || !m.covers(y)) {
        continue;
      }
      IntVar[] vars = m.mirrorVariables();
      IntVar card = vars[vars.length - 1];
      int mark = out.size();
      if (y == card && kind != AtomicTrail.NE) {
        boolean in = kind == AtomicTrail.GE;
        int count = forced(trail, entry, sets, relation, m, in, null, null);
        if (in ? count >= trail.value(entry) : count <= trail.value(entry)) {
          forced(trail, entry, sets, relation, m, in, null, out);
          return true;
        }
      } else if (y != card) {
        boolean in = kind == AtomicTrail.GE || (kind == AtomicTrail.NE && trail.value(entry) == 0);
        // in: the others that may be in only reach the minimum; out: those in reach the maximum
        int count = forced(trail, entry, sets, relation, m, !in, y, null);
        if (in
            ? count <= trail.minBefore(card, entry) - 1
            : count >= trail.maxBefore(card, entry)) {
          if (in) {
            trail.addLowerBound(card, entry, out);
          } else {
            trail.addUpperBound(card, entry, out);
          }
          forced(trail, entry, sets, relation, m, !in, y, out);
          return true;
        }
      }
      out.truncate(mark);
    }
    return false;
  }

  /*
   * The elements of m's set just before the position that the relation forces in (in) and those
   * fixed in when the mirror was made, or, for in false, the elements not forced out; skip's element
   * is left out. With out, the atoms forcing the counted (in) or excluded (not in) elements are
   * added.
   */
  private static int forced(
      AtomicTrail trail,
      int position,
      SetVar[] sets,
      Relation relation,
      SetMirror m,
      boolean in,
      IntVar skip,
      EntryList out) {
    int[] elements = m.elements();
    int count = m.rootGlbSize() + (in ? 0 : elements.length - (skip == null ? 0 : 1));
    for (int e : elements) {
      IntVar x = m.member(e);
      if (x == skip) {
        continue;
      }
      int[] state = states(trail, sets, e, position);
      if (!satisfiable(sets, state, relation, e, x, !in)) {
        count += in ? 1 : -1;
        if (out != null) {
          minimize(sets, state, relation, e, x, !in);
          addAtoms(trail, sets, state, e, position, out);
        }
      }
    }
    return count;
  }

  /**
   * Adds to {@code out} the reason of a failure on a set's cardinality: the elements the relation
   * forces into the set (or out of it), with those already in (or out), exceed its maximum
   * cardinality (or leave fewer than its minimum). The failing change itself is not on the trail,
   * so the memberships the relation forces count as well.
   *
   * @param trail the trail
   * @param sets the sets of the constraint, by argument position
   * @param relation the relation the constraint implies on every element
   * @param out where the reason entries are added
   * @return false when no set's cardinality fails this way
   */
  static boolean explainCardinalityFailure(
      AtomicTrail trail, SetVar[] sets, Relation relation, EntryList out) {
    int position = trail.size();
    for (SetVar s : sets) {
      SetMirror m = mirrorOf(s);
      if (m == null) {
        continue;
      }
      IntVar[] vars = m.mirrorVariables();
      IntVar card = vars[vars.length - 1];
      int[] elements = m.elements();
      for (boolean in : new boolean[] {true, false}) {
        // in: elements in, against the maximum; out: elements that may be in, against the minimum
        int count = m.rootGlbSize() + (in ? 0 : elements.length);
        int[][] forced = new int[elements.length][];
        for (int k = 0; k < elements.length; k++) {
          int e = elements[k];
          IntVar x = m.member(e);
          int[] state = states(trail, sets, e, position);
          if (!satisfiable(sets, state, relation, e, x, !in)) {
            forced[k] = state;
            count += in ? 1 : -1;
          }
        }
        boolean fails =
            in ? count > trail.maxBefore(card, position) : count < trail.minBefore(card, position);
        if (!fails) {
          continue;
        }
        if (in) {
          trail.addUpperBound(card, position, out);
        } else {
          trail.addLowerBound(card, position, out);
        }
        for (int k = 0; k < elements.length; k++) {
          if (forced[k] != null) {
            IntVar x = m.member(elements[k]);
            minimize(sets, forced[k], relation, elements[k], x, !in);
            addAtoms(trail, sets, forced[k], elements[k], position, out);
          }
        }
        return true;
      }
    }
    return false;
  }

  private static boolean explainElement(
      AtomicTrail trail, int entry, SetVar[] sets, Relation relation, int e, EntryList out) {
    IntVar x = trail.variable(entry);
    boolean value = membership(trail, entry);
    int[] state = states(trail, sets, e, entry);
    // the atom is forced when the relation cannot hold with the opposite membership
    if (satisfiable(sets, state, relation, e, x, !value)) {
      return false;
    }
    minimize(sets, state, relation, e, x, !value);
    addAtoms(trail, sets, state, e, entry, out);
    return true;
  }

  // the membership a 0/1 variable's atom gives
  private static boolean membership(AtomicTrail trail, int entry) {
    int kind = trail.kind(entry);
    return kind == AtomicTrail.GE || (kind == AtomicTrail.NE && trail.value(entry) == 0);
  }

  private static SetMirror mirrorOf(SetVar s) {
    return s.lcgMirror();
  }

  private static int fact(boolean inGlb, boolean inLub) {
    if (inGlb) {
      return IN;
    }
    return inLub ? OPEN : OUT;
  }

  // the membership of e in each set just before a trail position
  private static int[] states(AtomicTrail trail, SetVar[] sets, int e, int position) {
    int[] state = new int[sets.length];
    for (int k = 0; k < sets.length; k++) {
      SetVar s = sets[k];
      SetMirror m = mirrorOf(s);
      IntVar member = m == null ? null : m.member(e);
      if (member != null) {
        if (trail.minBefore(member, position) >= 1) {
          state[k] = IN;
        } else if (trail.maxBefore(member, position) <= 0) {
          state[k] = OUT;
        } else {
          state[k] = OPEN;
        }
      } else if (m != null) {
        state[k] = fact(m.inRootGlb(e), m.inRootLub(e));
      } else {
        // a set without a mirror does not change
        state[k] = fact(s.domain.glb().contains(e), s.domain.lub().contains(e));
      }
    }
    return state;
  }

  // whether some memberships allowed by the states satisfy the relation, with x's membership set
  // to the given value when x is not null
  private static boolean satisfiable(
      SetVar[] sets, int[] state, Relation relation, int e, IntVar x, boolean xValue) {
    int n = sets.length;
    boolean[] in = new boolean[n];
    for (int bits = 0; bits < 1 << n; bits++) {
      if (allowed(sets, state, bits, x, xValue, in) && relation.holds(e, in)) {
        return true;
      }
    }
    return false;
  }

  private static boolean allowed(
      SetVar[] sets, int[] state, int bits, IntVar x, boolean xValue, boolean[] in) {
    for (int k = 0; k < sets.length; k++) {
      in[k] = (bits >> k & 1) == 1;
      if (state[k] != OPEN && in[k] != (state[k] == IN)) {
        return false;
      }
      // a set given twice has one membership
      for (int j = 0; j < k; j++) {
        if (sets[j] == sets[k] && in[j] != in[k]) {
          return false;
        }
      }
    }
    if (x != null) {
      for (int k = 0; k < sets.length; k++) {
        SetMirror m = mirrorOf(sets[k]);
        if (m != null && isMemberVariable(m, x) && in[k] != xValue) {
          return false;
        }
      }
    }
    return true;
  }

  private static boolean isMemberVariable(SetMirror m, IntVar x) {
    for (IntVar v : m.mirrorVariables()) {
      if (v == x) {
        return true;
      }
    }
    return false;
  }

  // opens the fixed memberships the conclusion does not need, one at a time
  private static void minimize(
      SetVar[] sets, int[] state, Relation relation, int e, IntVar x, boolean xValue) {
    for (int k = 0; k < sets.length; k++) {
      if (state[k] == OPEN) {
        continue;
      }
      int kept = state[k];
      state[k] = OPEN;
      if (satisfiable(sets, state, relation, e, x, xValue)) {
        state[k] = kept;
      }
    }
  }

  // adds the atoms of the fixed memberships that are not facts
  private static void addAtoms(
      AtomicTrail trail, SetVar[] sets, int[] state, int e, int position, EntryList out) {
    for (int k = 0; k < sets.length; k++) {
      SetMirror m = mirrorOf(sets[k]);
      IntVar member = m == null ? null : m.member(e);
      if (member == null || state[k] == OPEN) {
        continue;
      }
      if (state[k] == IN) {
        trail.addLowerBound(member, position, out);
      } else {
        trail.addUpperBound(member, position, out);
      }
    }
  }

  /**
   * Adds to {@code out} the atom that an element was in a set (or out of it) just before a trail
   * position, when it was.
   *
   * @param trail the trail
   * @param s the set
   * @param e the element
   * @param position the trail position
   * @param in true for the element in the set, false for out of it
   * @param out where the entry is added
   * @return false when the membership was not known then
   */
  static boolean membership(
      AtomicTrail trail, SetVar s, int e, int position, boolean in, EntryList out) {
    SetVar[] sets = {s};
    int[] state = states(trail, sets, e, position);
    if (state[0] != (in ? IN : OUT)) {
      return false;
    }
    addAtoms(trail, sets, state, e, position, out);
    return true;
  }
}
