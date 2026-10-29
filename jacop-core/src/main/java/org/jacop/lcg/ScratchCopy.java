/*
 * ScratchCopy.java
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
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * A copy of a constraint in a scratch store, over fresh variables with a trail's initial domains,
 * in which atoms of the trail can be imposed. The explanation checker and the replayed explanations
 * use it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class ScratchCopy {

  final Store store = new Store();

  /** The copy of each variable of the constraint (and of the variables mirroring them). */
  final Map<Var, Var> copies = new IdentityHashMap<>();

  private final AtomicTrail trail;

  private ScratchCopy(AtomicTrail trail) {
    this.trail = trail;
  }

  /**
   * Copies the variables of a constraint, but not the constraint.
   *
   * @return the scratch copy, or null when the constraint cannot be copied or has variables other
   *     than {@link IntVar}, {@link BooleanVar} and {@link Mirrored} ones
   */
  static ScratchCopy of(AtomicTrail trail, Constraint c) {
    if (!Copyable.canCopy(c)) {
      return null;
    }
    ScratchCopy s = new ScratchCopy(trail);
    for (Var v : c.arguments()) {
      if (!s.copy(v)) {
        return null;
      }
    }
    return s;
  }

  /** Imposes a copy of the constraint in the scratch store. */
  void imposeCopy(Constraint c) {
    store.impose(((Copyable<?>) c).copy(varMap()));
  }

  /** Returns the copy of an integer variable, or null when it is not one of the constraint. */
  IntVar get(IntVar x) {
    return (IntVar) copies.get(x);
  }

  /**
   * Imposes the atom of an entry on the copy of its variable.
   *
   * @return false when the variable is not one of the constraint
   */
  boolean impose(int entry) {
    IntVar y = get(trail.variable(entry));
    if (y == null) {
      return false;
    }
    impose(y, trail.kind(entry), trail.value(entry));
    return true;
  }

  /**
   * Imposes the negation of the atom of an entry on the copy of its variable.
   *
   * @return false when the variable is not one of the constraint
   */
  boolean imposeNegation(int entry) {
    IntVar y = get(trail.variable(entry));
    if (y == null) {
      return false;
    }
    int v = trail.value(entry);
    switch (trail.kind(entry)) {
      case AtomicTrail.GE -> y.domain.inMax(store.level, y, v - 1);
      case AtomicTrail.LE -> y.domain.inMin(store.level, y, v + 1);
      default -> y.domain.in(store.level, y, v, v);
    }
    return true;
  }

  private void impose(IntVar y, int kind, int v) {
    switch (kind) {
      case AtomicTrail.GE -> y.domain.inMin(store.level, y, v);
      case AtomicTrail.LE -> y.domain.inMax(store.level, y, v);
      default -> {
        if (y.domain.contains(v)) {
          y.domain.inComplement(store.level, y, v);
        }
      }
    }
  }

  private VarMap varMap() {
    return new VarMap() {
      @Override
      public Store target() {
        return store;
      }

      @Override
      @SuppressWarnings("unchecked")
      public <V extends Var> V get(V v) {
        Var copy = copies.get(v);
        if (copy == null) {
          throw new IllegalArgumentException(v + " is not a variable of the constraint");
        }
        return (V) copy;
      }
    };
  }

  /**
   * Copies a variable of the constraint: an integer variable with its initial domain, or a {@link
   * Mirrored} one tied to copies of its mirror, which then hold its atoms.
   *
   * @return false when the variable cannot be copied
   */
  private boolean copy(Var v) {
    if (copies.containsKey(v)) {
      return true;
    }
    if (v instanceof IntVar x) {
      IntVar copy = copyInt(x);
      copies.put(v, copy);
      return copy != null;
    }
    if (!(v instanceof Mirrored m) || m.mirror() == null) {
      return false;
    }
    IntVar[] mirror = m.mirror();
    IntVar[] mirrorCopies = new IntVar[mirror.length];
    for (int i = 0; i < mirror.length; i++) {
      if (!copy(mirror[i])) {
        return false;
      }
      mirrorCopies[i] = (IntVar) copies.get(mirror[i]);
    }
    copies.put(v, m.copyMirrored(store, mirrorCopies));
    return true;
  }

  private IntVar copyInt(IntVar x) {
    IntDomain root = trail.rootDomain(x);
    if (x.getClass() == IntVar.class) {
      return new IntVar(store, x.id(), root.cloneLight());
    }
    if (x.getClass() == BooleanVar.class) {
      return new BooleanVar(store, x.id(), root.min(), root.max());
    }
    return null;
  }
}
