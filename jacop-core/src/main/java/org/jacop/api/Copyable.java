/*
 * Copyable.java
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

import java.util.Arrays;
import org.jacop.constraints.Constraint;

/**
 * A constraint that can be rebuilt over other variables, usually the variables of another store.
 * Deriving a store from another one (presolve, sub-problems) copies every constraint this way.
 *
 * <p>The copy contract: {@link #copy(VarMap)} returns a new constraint of the same class, not
 * imposed, over {@code map.get(v)} for every variable {@code v} of this constraint and with the
 * same parameters. It does not impose, does not change this constraint or its store, and carries no
 * search state (weights, time stamps, first-consistency work). Fixed data such as coefficients or
 * tuples may be shared with the copy, so neither constraint may modify it. A subclass of a copyable
 * class is copyable only if it declares {@code copy} itself.
 *
 * @param <T> the class of the copy, normally the implementing class.
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public interface Copyable<T extends Constraint> {

  /**
   * Creates a new, not imposed constraint of the same class over the mapped variables.
   *
   * @param map the mapping from this constraint's variables to the variables of the copy.
   * @return the copy.
   */
  T copy(VarMap map);

  /**
   * Checks whether this instance can be copied. Constraints that wrap other constraints, for
   * example reifications, can be copied only if the wrapped constraints can.
   *
   * @return true if {@link #copy(VarMap)} succeeds for this instance.
   */
  default boolean canCopy() {
    return true;
  }

  /**
   * Checks whether a constraint can be copied.
   *
   * @param c the constraint.
   * @return true if the constraint is {@link Copyable} and this instance can be copied.
   */
  static boolean canCopy(Object c) {
    return c instanceof Copyable<?> copyable
        && DECLARES_COPY.get(c.getClass())
        && copyable.canCopy();
  }

  /**
   * Checks whether all constraints can be copied.
   *
   * @param cs the constraints.
   * @return true if every constraint is {@link Copyable} and can be copied.
   */
  static boolean canCopyAll(Object... cs) {
    for (Object c : cs) {
      if (!canCopy(c)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Copies constraints that are known to be copyable into an array of the same runtime type.
   *
   * @param <C> the static type of the constraints.
   * @param cs the constraints.
   * @param map the variable mapping.
   * @return the copies, in order.
   */
  static <C extends Constraint> C[] copyOf(C[] cs, VarMap map) {
    C[] copies = Arrays.copyOf(cs, cs.length);
    for (int i = 0; i < cs.length; i++) {
      copies[i] = copyOf(cs[i], map);
    }
    return copies;
  }

  /**
   * Whether a class declares {@link #copy(VarMap)} itself. A subclass that inherits the method
   * would be copied as an instance of its superclass, so it is not copyable.
   */
  ClassValue<Boolean> DECLARES_COPY =
      new ClassValue<>() {
        @Override
        protected Boolean computeValue(Class<?> type) {
          try {
            return type.getMethod("copy", VarMap.class).getDeclaringClass() == type;
          } catch (NoSuchMethodException e) {
            return false;
          }
        }
      };

  /**
   * Copies a constraint that is known to be copyable, keeping its static type; used by constraints
   * that wrap other constraints.
   *
   * @param <C> the static type of the constraint.
   * @param c the constraint, which must be {@link Copyable}.
   * @param map the variable mapping.
   * @return the copy.
   * @throws UnsupportedOperationException if the constraint is not copyable.
   */
  @SuppressWarnings("unchecked")
  static <C extends Constraint> C copyOf(C c, VarMap map) {
    if (!canCopy(c)) {
      throw new UnsupportedOperationException(
          "Constraint " + c.getClass().getName() + " cannot be copied");
    }
    return (C) ((Copyable<?>) c).copy(map);
  }
}
