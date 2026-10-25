/*
 * VarMap.java
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

package org.jacop.api;

import java.util.ArrayList;
import java.util.List;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * A mapping from variables to variables of a target store, used by {@link Copyable#copy(VarMap)}.
 * The mapped variable has the same static type as the original one, so a copied constraint never
 * casts it.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public interface VarMap {

  /**
   * Returns the store the mapped variables belong to; constraints that create auxiliary variables
   * create them there.
   *
   * @return the target store.
   */
  Store target();

  /**
   * Returns the variable that stands for a given variable.
   *
   * @param <V> the type of the variable.
   * @param v the variable.
   * @return the mapped variable.
   * @throws IllegalArgumentException if the variable has no mapping.
   */
  <V extends Var> V get(V v);

  /**
   * Maps every variable of an array.
   *
   * @param <V> the type of the variables.
   * @param vars the variables.
   * @return a new array, of the same runtime type, holding the mapped variables.
   */
  default <V extends Var> V[] get(V[] vars) {
    V[] result = vars.clone();
    for (int i = 0; i < vars.length; i++) {
      result[i] = get(vars[i]);
    }
    return result;
  }

  /**
   * Maps every variable of a two-dimensional array.
   *
   * @param <V> the type of the variables.
   * @param vars the variables.
   * @return a new array, of the same runtime type, holding the mapped variables.
   */
  default <V extends Var> V[][] get(V[][] vars) {
    V[][] result = vars.clone();
    for (int i = 0; i < vars.length; i++) {
      result[i] = get(vars[i]);
    }
    return result;
  }

  /**
   * Maps every variable of a list.
   *
   * @param <V> the type of the variables.
   * @param vars the variables.
   * @return a new list holding the mapped variables.
   */
  default <V extends Var> List<V> get(List<V> vars) {
    List<V> result = new ArrayList<>(vars.size());
    for (V v : vars) {
      result.add(get(v));
    }
    return result;
  }
}
