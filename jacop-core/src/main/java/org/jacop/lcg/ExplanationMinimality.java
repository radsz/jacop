/*
 * ExplanationChecker.java
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

import java.util.IdentityHashMap;
import java.util.Map;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Measures how far explanations are from minimal, as a tool to find weak ones: in a scratch store
 * with a copy of the constraint over the trail's initial domains, atoms of a reason are dropped
 * while propagation still derives the explained atom, and the atoms left are weakened to earlier
 * atoms of the same bound. Only atoms on the trail are tried, since only those have literals the
 * solver knows. It costs a store and a propagation per atom, so the solver samples explanations
 * ({@code -Djacop.lcg.minimality}).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class ExplanationMinimality {

  private final AtomicTrail trail;

  /**
   * Creates the measure for the explanations of a trail.
   *
   * @param trail the trail
   */
  public ExplanationMinimality(AtomicTrail trail) {
    this.trail = trail;
  }

  /** Reasons with more atoms than this are not minimised by {@link #minimise}. */
  private static final int MINIMISE_LIMIT = 400;

  /** Weaker atoms of one bound that {@link #minimise} tries, from the weakest. */
  private static final int LIFT_LIMIT = 16;

  /**
   * Measures how much of a reason the constraint's propagation needs, in a scratch store: atoms are
   * dropped one by one while the rest still lets propagation derive the atom (or the failure, for
   * {@code entry} -1), and each bound atom left is then replaced by the weakest earlier atom of the
   * same bound that still does. Propagation may be weaker than the explanation (energy reasoning,
   * for example), so a reason it cannot use as a whole is only counted.
   *
   * @param c the constraint that propagated the entry, or failed
   * @param entry the entry, or -1 for a failure
   * @param reason the entries of its reason
   * @return {atoms, atoms kept, atoms lifted to an earlier trail atom, atoms that a weaker bound no
   *     trail atom gives could replace}, with -1 kept when propagation does not derive the atom
   *     from the whole reason, or null when the reason cannot be checked
   */
  public int[] minimise(Constraint c, int entry, EntryList reason) {
    int n = reason.size();
    if (n > MINIMISE_LIMIT || !Copyable.canCopy(c)) {
      return null;
    }
    Store scratch = new Store();
    Map<Var, Var> copies = new IdentityHashMap<>();
    for (Var v : c.arguments()) {
      if (!copy(scratch, v, copies)) {
        return null;
      }
    }
    for (int k = 0; k < n; k++) {
      if (copies.get(trail.variable(reason.get(k))) == null) {
        return null;
      }
    }
    if (entry >= 0 && copies.get(trail.variable(entry)) == null) {
      return null;
    }
    VarMap map =
        new VarMap() {
          @Override
          public Store target() {
            return scratch;
          }

          @Override
          @SuppressWarnings("unchecked")
          public <V extends Var> V get(V v) {
            return (V) copies.get(v);
          }
        };
    try {
      scratch.impose(((Copyable<?>) c).copy(map));
      if (!scratch.consistency()) {
        return new int[] {n, 0, 0};
      }
    } catch (FailException _) {
      return new int[] {n, 0, 0};
    }
    int[] atoms = new int[n];
    for (int k = 0; k < n; k++) {
      atoms[k] = reason.get(k);
    }
    if (!derives(scratch, copies, atoms, n, entry)) {
      return new int[] {n, -1, 0};
    }
    int kept = n;
    for (int k = kept - 1; k >= 0; k--) {
      int dropped = atoms[k];
      atoms[k] = atoms[kept - 1];
      if (derives(scratch, copies, atoms, kept - 1, entry)) {
        kept--;
      } else {
        atoms[kept - 1] = atoms[k];
        atoms[k] = dropped;
      }
    }
    int lifted = 0;
    int liftedOff = 0;
    for (int k = 0; k < kept; k++) {
      int f = atoms[k];
      if (trail.kind(f) == AtomicTrail.NE) {
        continue;
      }
      int[] weaker = new int[LIFT_LIMIT];
      int numWeaker = 0;
      for (int e = trail.previousEntry(f);
          e >= 0 && numWeaker < LIFT_LIMIT;
          e = trail.previousEntry(e)) {
        if (trail.kind(e) == trail.kind(f) && trail.value(e) != trail.value(f)) {
          weaker[numWeaker++] = e;
        }
      }
      for (int w = numWeaker - 1; w >= 0; w--) {
        atoms[k] = weaker[w];
        if (derives(scratch, copies, atoms, kept, entry)) {
          lifted++;
          break;
        }
        atoms[k] = f;
      }
      if (weakerValue(scratch, copies, atoms, kept, entry, k)) {
        liftedOff++;
      }
    }
    return new int[] {n, kept, lifted, liftedOff};
  }

  // whether propagation in the scratch store derives the entry (or a failure) from the atoms
  // whether a bound weaker than atoms[k]'s, which no trail atom gives, still derives the entry: the
  // weakest such bound is found by bisection between the root bound and the atom's
  private boolean weakerValue(
      Store scratch, Map<Var, Var> copies, int[] atoms, int n, int entry, int k) {
    int f = atoms[k];
    boolean ge = trail.kind(f) == AtomicTrail.GE;
    IntDomain root = trail.rootDomain(trail.variable(f));
    // ge: [x >= v] for v in (root min, value]; le: [x <= v] for v in [value, root max)
    long weak = ge ? root.min() : root.max();
    long strong = trail.value(f);
    if (Math.abs(strong - weak) <= 1) {
      return false;
    }
    overrideAt = k;
    try {
      // invariant: strong derives, weak does not (dropping the atom was tried)
      while (Math.abs(strong - weak) > 1) {
        long mid = (strong + weak) / 2;
        overrideValue = (int) mid;
        if (derives(scratch, copies, atoms, n, entry)) {
          strong = mid;
        } else {
          weak = mid;
        }
      }
    } finally {
      overrideAt = -1;
    }
    return strong != trail.value(f);
  }

  private int overrideAt = -1;
  private int overrideValue;

  private boolean derives(Store scratch, Map<Var, Var> copies, int[] atoms, int n, int entry) {
    int base = scratch.level;
    scratch.setLevel(base + 1);
    try {
      for (int k = 0; k < n; k++) {
        int f = atoms[k];
        impose(
            scratch,
            (IntVar) copies.get(trail.variable(f)),
            trail.kind(f),
            k == overrideAt ? overrideValue : trail.value(f));
      }
      if (entry >= 0) {
        IntVar y = (IntVar) copies.get(trail.variable(entry));
        int v = trail.value(entry);
        switch (trail.kind(entry)) {
          case AtomicTrail.GE -> y.domain.inMax(scratch.level, y, v - 1);
          case AtomicTrail.LE -> y.domain.inMin(scratch.level, y, v + 1);
          default -> y.domain.in(scratch.level, y, v, v);
        }
      }
      return !scratch.consistency();
    } catch (FailException _) {
      return true;
    } finally {
      scratch.removeLevel(base + 1);
      scratch.setLevel(base);
    }
  }

  // copies a variable of the constraint, as the explanation checker does
  private boolean copy(Store scratch, Var v, Map<Var, Var> copies) {
    if (copies.containsKey(v)) {
      return true;
    }
    if (v instanceof IntVar x) {
      IntVar copy = copy(scratch, x);
      copies.put(v, copy);
      return copy != null;
    }
    if (!(v instanceof Mirrored m) || m.mirror() == null) {
      return false;
    }
    IntVar[] mirror = m.mirror();
    IntVar[] mirrorCopies = new IntVar[mirror.length];
    for (int i = 0; i < mirror.length; i++) {
      if (!copy(scratch, mirror[i], copies)) {
        return false;
      }
      mirrorCopies[i] = (IntVar) copies.get(mirror[i]);
    }
    copies.put(v, m.copyMirrored(scratch, mirrorCopies));
    return true;
  }

  private IntVar copy(Store scratch, IntVar x) {
    IntDomain root = trail.rootDomain(x);
    if (x.getClass() == IntVar.class) {
      return new IntVar(scratch, x.id(), root.cloneLight());
    }
    if (x.getClass() == BooleanVar.class) {
      return new BooleanVar(scratch, x.id(), root.min(), root.max());
    }
    return null;
  }

  private static void impose(Store scratch, IntVar y, int kind, int v) {
    switch (kind) {
      case AtomicTrail.GE -> y.domain.inMin(scratch.level, y, v);
      case AtomicTrail.LE -> y.domain.inMax(scratch.level, y, v);
      default -> {
        if (y.domain.contains(v)) {
          y.domain.inComplement(scratch.level, y, v);
        }
      }
    }
  }
}
