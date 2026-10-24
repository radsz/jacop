/*
 * Var.java
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

package org.jacop.core;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;
import lombok.Getter;
import org.jacop.constraints.Constraint;

/**
 * Defines a variable and related operations on it.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public abstract class Var implements Backtrackable {

  /** It is a counter to indicate number of created variables. */
  public static final AtomicInteger idNumber = new AtomicInteger(0);

  /** Id string of the variable. */
  public String id;

  /** It specifies the index at which it is stored in Store. */
  public int storeIndex = -1;

  /** It specifies the current weight of the variable. */
  public int weight = 1;

  /**
   * Each variable is created in a store. This attribute represents the store in which this variable
   * was created.
   */
  @Getter public Store store;

  /** Pruning activity of this variable. */
  double pruningActivity = 1.0d;

  /**
   * Creates an empty position mapping.
   *
   * @param <T> type of the variable.
   * @param <R> type of the mapped value.
   * @return a new empty map.
   */
  public static <T extends Var, R> Map<T, R> createEmptyPositioning() {
    return new LinkedHashMap<>();
  }

  /**
   * Creates a position mapping from variables to their indices in the given array.
   *
   * @param <T> type of the variable.
   * @param list array of variables to map.
   * @param skipSingletons if true, duplicate singleton variables are ignored.
   * @param clazz the constraint class used for error reporting.
   * @return a map from each variable to its index in the array.
   */
  public static <T extends Var> Map<T, Integer> positionMapping(
      T[] list, boolean skipSingletons, Class<?> clazz) {

    Map<T, Integer> position = new LinkedHashMap<>();
    addPositionMapping(position, list, skipSingletons, clazz);
    return position;
  }

  /**
   * Creates a position mapping from variables to values computed by the given function.
   *
   * @param <T> type of the variable.
   * @param <R> type of the mapped value.
   * @param list array of variables to map.
   * @param function the function applied to each variable to compute the mapped value.
   * @param skipSingletons if true, duplicate singleton variables are ignored.
   * @param clazz the constraint class used for error reporting.
   * @return a map from each variable to its computed value.
   */
  public static <T extends Var, R> Map<T, R> positionMapping(
      T[] list, Function<T, R> function, boolean skipSingletons, Class<?> clazz) {

    Map<T, R> position = new LinkedHashMap<>();
    addPositionMapping(position, list, function, skipSingletons, clazz);
    return position;
  }

  /**
   * Adds index-based position mappings for the given variables into an existing map.
   *
   * @param <T> type of the variable.
   * @param position the map to add entries to.
   * @param list array of variables to map.
   * @param skipSingletons if true, duplicate singleton variables are ignored.
   * @param clazz the constraint class used for error reporting.
   */
  public static <T extends Var> void addPositionMapping(
      Map<T, Integer> position, T[] list, boolean skipSingletons, Class<?> clazz) {

    for (int i = 0; i < list.length; i++) {
      if (position.get(list[i]) != null) {
        if (skipSingletons && list[i].singleton()) {
          continue;
        }
        throw new IllegalArgumentException(
            "Constraint "
                + clazz.getSimpleName()
                + " can not create a position mapping for list as duplicates in the list exists.");
      }
      position.put(list[i], i);
    }
  }

  /**
   * Adds function-based position mappings for the given variables into an existing map.
   *
   * @param <T> type of the variable.
   * @param <R> type of the mapped value.
   * @param position the map to add entries to.
   * @param list array of variables to map.
   * @param function the function applied to each variable to compute the mapped value.
   * @param skipSingletons if true, duplicate singleton variables are ignored.
   * @param clazz the constraint class used for error reporting.
   */
  public static <T extends Var, R> void addPositionMapping(
      Map<T, R> position,
      T[] list,
      Function<T, R> function,
      boolean skipSingletons,
      Class<?> clazz) {

    for (T aList : list) {
      if (position.get(aList) != null) {
        if (skipSingletons && aList.singleton()) {
          continue;
        }
        throw new IllegalArgumentException(
            "Constraint "
                + clazz.getSimpleName()
                + " can not create a position mapping for list as duplicates in the list exists.");
      }
      position.put(aList, function.apply(aList));
    }
  }

  /**
   * This function returns current domain of the variable.
   *
   * @return the domain of the variable.
   */
  public abstract Domain dom();

  /**
   * It returns the size of the current domain.
   *
   * @return the size of the variables domain.
   */
  public abstract int getSize();

  /**
   * It returns the size of the current domain.
   *
   * @return the size of the variables domain.
   */
  public abstract double getSizeFloat();

  /**
   * It checks if the domain is empty.
   *
   * @return true if variable domain is empty.
   */
  public abstract boolean isEmpty();

  /**
   * It registers constraint with current variable, so anytime this variable is changed the
   * constraint is reevaluated. Pruning events constants from 0 to n, where n is the strongest
   * pruning event.
   *
   * @param c the constraint which is being attached to the variable.
   * @param pruningEvent type of the event which must occur to trigger the execution of the
   *     consistency function.
   */
  public void putModelConstraint(Constraint c, int pruningEvent) {
    if (singleton()) {
      return;
    }
    if (pruningEvent == Domain.NONE) {
      return;
    }
    dom().putModelConstraint(store.level, this, c, pruningEvent);
    store.recordChange(this);
  }

  /**
   * It registers constraint with current variable, so always when this variable is changed the
   * constraint is reevaluated.
   *
   * @param c the constraint which is added as a search constraint.
   */
  public void putSearchConstraint(Constraint c) {
    if (singleton()) {
      return;
    }
    dom().putSearchConstraint(store.level, this, c);
    store.recordChange(this);
  }

  /**
   * It detaches constraint from the current variable, so change in variable will not cause
   * constraint reevaluation. It is only removed from the current level onwards. Removing current
   * level at later stage will automatically re-attached the constraint to the variable.
   *
   * @param c the constraint being detached from the variable.
   */
  public void removeConstraint(Constraint c) {
    if (singleton()) {
      return;
    }
    Domain d = dom();
    int i = d.searchConstraintsToEvaluate - 1;
    for (; i >= 0; i--) {
      if (d.searchConstraints.get(i) == c) {
        d.removeSearchConstraint(store.level, this, i, c);
      }
    }
    if (i == -1) {
      d.removeModelConstraint(store.level, this, c);
    }
    store.recordChange(this);
  }

  /**
   * It checks if the domain contains only one value.
   *
   * @return true if the variable domain is a singleton, false otherwise.
   */
  public abstract boolean singleton();

  /**
   * It returns current number of constraints which are associated with variable and are not yet
   * satisfied.
   *
   * @return number of constraints attached to the variable.
   */
  public int sizeConstraints() {
    return dom().sizeConstraints();
  }

  /**
   * It returns all constraints which are associated with variable, even the ones which are already
   * satisfied.
   *
   * @return number of constraints attached at the earliest level of the variable.
   */
  public int sizeConstraintsOriginal() {
    return dom().sizeConstraintsOriginal();
  }

  /**
   * It returns current number of constraints which are associated with variable and are not yet
   * satisfied.
   *
   * @return number of attached search constraints.
   */
  public int sizeSearchConstraints() {
    return dom().searchConstraintsToEvaluate;
  }

  /**
   * This function returns stamp of the current domain of variable. It is equal or smaller to the
   * stamp of store. Larger difference indicates that variable has not been changed for a longer
   * time.
   *
   * @return level for which the most recent changes have been applied to.
   */
  public abstract int level();

  /**
   * It returns the string representation of the variable using the full representation of the
   * domain.
   *
   * @return string representation.
   */
  public String toStringFull() {
    return id + dom().toStringFull();
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id);
    if (singleton()) {
      result.append(" = ");
    } else {
      result.append("::");
    }
    result.append(dom());
    return result.toString();
  }

  /**
   * It informs the variable that its variable has changed according to the specified event.
   *
   * @param event the type of the change (GROUND, BOUND, ANY).
   */
  public abstract void domainHasChanged(int event);

  /**
   * It registers constraint with current variable, so anytime this variable is changed the
   * constraint is reevaluated.
   *
   * @param c the constraint being attached to this variable.
   */
  public abstract void putConstraint(Constraint c);

  /**
   * This function returns variable id.
   *
   * @return the id of the variable.
   */
  public String id() {
    return id;
  }

  /**
   * This function returns the index of variable in store array.
   *
   * @return the index of the variable.
   */
  public int index() {
    return storeIndex;
  }

  /**
   * Computes the accumulated failure count (AFC) value for this variable.
   *
   * @return the sum of AFC values of all constraints attached to this variable.
   */
  public float afcValue() {
    float value = 0.0f;
    for (Constraint c : dom().constraints()) {
      value += c.afc();
    }
    return value;
  }

  /** Increments the pruning activity counter for this variable. */
  public void updateActivity() {
    pruningActivity += 1.0;
  }

  /**
   * Returns the current pruning activity value for this variable.
   *
   * @return the pruning activity.
   */
  public double activity() {
    return pruningActivity;
  }

  /** Applies the decay factor from the store to this variable's pruning activity. */
  public void applyDecay() {
    pruningActivity = pruningActivity * store.decay;
  }
}
