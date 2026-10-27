/*
 * Reconstruction.java
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

package org.jacop.presolve;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Postsolve of eliminated variables. The definitions of the eliminated variables are copied into a
 * store of their own, over copies of their variables taken at the level of the derivation. For a
 * solution of the child, the other variables take their values in the parent; the variables still
 * open (those presolve left free) and then the eliminated ones, in the reverse order of
 * elimination, get the first value that propagation accepts. Each definition was chosen because
 * every assignment of its other variables leaves a value for its eliminated variable, so this
 * succeeds without backtracking.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class Reconstruction implements VarMap {

  private final Store store = new Store();
  // parent variable to its copy here, in the order the definitions name them
  private final Map<Var, IntVar> copies = new LinkedHashMap<>();
  private final Set<Var> eliminatedVars = Collections.newSetFromMap(new IdentityHashMap<>());
  private final List<IntVar> labelling = new ArrayList<>();

  Reconstruction(List<IntVar> eliminated, List<Constraint> definitions) {
    eliminatedVars.addAll(eliminated);
    Map<Var, IntVar> byIdentity = new IdentityHashMap<>();
    for (Constraint c : definitions) {
      for (Var v : c.arguments()) {
        byIdentity.computeIfAbsent(
            v,
            x -> {
              IntVar copy = ((IntVar) x).copyTo(store);
              copies.put(x, copy);
              return copy;
            });
      }
    }
    for (Constraint c : definitions) {
      store.impose(((Copyable<?>) c).copy(this));
    }
    for (Map.Entry<Var, IntVar> e : copies.entrySet()) {
      if (!eliminatedVars.contains(e.getKey())) {
        labelling.add(e.getValue());
      }
    }
    for (int i = eliminated.size() - 1; i >= 0; i--) {
      labelling.add(copies.get(eliminated.get(i)));
    }
  }

  @Override
  public Store target() {
    return store;
  }

  @Override
  @SuppressWarnings("unchecked")
  public <V extends Var> V get(V v) {
    return (V) copies.get(v);
  }

  /**
   * Gives values to the eliminated variables of the parent, and to the variables of their
   * definitions that the parent has not fixed, from the values of the others.
   *
   * @param parent the parent store, at the level where the child's solution was written.
   * @return false if a definition cannot be satisfied, which means the child's solution is not
   *     complete or the derivation is wrong.
   */
  boolean apply(Store parent) {
    int base = store.level;
    try {
      store.setLevel(base + 1);
      for (Map.Entry<Var, IntVar> e : copies.entrySet()) {
        if (!eliminatedVars.contains(e.getKey())) {
          IntVar v = (IntVar) e.getKey();
          IntVar copy = e.getValue();
          copy.domain.in(store.level, copy, v.dom());
        }
      }
      if (!store.consistency()) {
        return false;
      }
      for (IntVar x : labelling) {
        if (!x.singleton() && !assign(x)) {
          return false;
        }
      }
      for (Map.Entry<Var, IntVar> e : copies.entrySet()) {
        IntVar v = (IntVar) e.getKey();
        if (!v.singleton()) {
          int value = e.getValue().value();
          v.domain.in(parent.level, v, value, value);
        }
      }
      return true;
    } catch (FailException f) {
      return false;
    } finally {
      while (store.level > base) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }
    }
  }

  /** Assigns the first value propagation accepts, one level up. */
  private boolean assign(IntVar x) {
    for (ValueEnumeration e = x.dom().valueEnumeration(); e.hasMoreElements(); ) {
      int value = e.nextElement();
      store.setLevel(store.level + 1);
      try {
        x.domain.in(store.level, x, value, value);
        if (store.consistency()) {
          return true;
        }
      } catch (FailException f) {
        // try the next value
      }
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
    }
    return false;
  }
}
