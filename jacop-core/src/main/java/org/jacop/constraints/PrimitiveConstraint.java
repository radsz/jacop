/*
 * PrimitiveConstraint.java
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

import java.util.HashMap;
import java.util.Map;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.StoreAware;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Standard unified interface for all primitive constraints. In addition to functions defined by
 * interface Constraint it also defines function notConsistency and notSatisfied. Only
 * PrimitiveConstraints can be used as arguments to constraints Not, And, Or, etc.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public abstract class PrimitiveConstraint extends Constraint
    implements StoreAware, SatisfiedPresent {

  /** It specifies the events which must occur for notConsistency() method being executed. */
  protected Map<Var, Integer> notConsistencyPruningEvents;

  /**
   * It retrieves the pruning event which causes reevaluation of the constraint notConsistency()
   * function.
   *
   * @param v for which pruning event is retrieved
   * @return the int denoting the pruning event associated with given variable.
   */
  public int getNotConsistencyPruningEvent(Var v) {

    // If notConsistency function mode
    if (notConsistencyPruningEvents != null) {
      Integer possibleEvent = notConsistencyPruningEvents.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }

    if (!constraintScope.isEmpty()) {

      int eventAcross =
          constraintScope.stream()
              .filter(i -> i.arguments().contains(v))
              .mapToInt(i -> i.getNestedPruningEvent(v, false))
              .max()
              .orElseGet(this::getDefaultNotConsistencyPruningEvent);

      if (eventAcross < getDefaultNotConsistencyPruningEvent()) {
        eventAcross = getDefaultNotConsistencyPruningEvent();
      }

      return eventAcross;
    }
    return getDefaultNotConsistencyPruningEvent();
  }

  @Override
  public void impose(Store store) {

    super.impose(store);
    include(store);
  }

  /**
   * It retrieves the pruning event for which any composed constraint which uses this constraint
   * should be evaluated. This events are the ones which can change satisfied status?
   *
   * @param v for which pruning event is retrieved
   * @param mode decides if pruning event for consistency or nonconsistency is required.
   * @return pruning event associated with the given variable for a given consistency mode.
   */
  public int getNestedPruningEvent(Var v, boolean mode) {

    // If consistency function mode
    if (mode) {
      if (consistencyPruningEvents != null) {
        Integer possibleEvent = consistencyPruningEvents.get(v);
        if (possibleEvent != null) {
          return possibleEvent;
        }
      }

      if (constraintScope != null && !constraintScope.isEmpty()) {

        int eventAcross =
            constraintScope.stream()
                .filter(i -> i.arguments().contains(v))
                .mapToInt(i -> i.getNestedPruningEvent(v, true))
                .max()
                .orElse(Integer.MIN_VALUE);

        if (eventAcross != Integer.MIN_VALUE) {
          return eventAcross;
        }
      }

      return getDefaultNestedConsistencyPruningEvent();
    } else { // If notConsistency function mode
      if (notConsistencyPruningEvents != null) {
        Integer possibleEvent = notConsistencyPruningEvents.get(v);
        if (possibleEvent != null) {
          return possibleEvent;
        }
      }
      if (constraintScope != null && !constraintScope.isEmpty()) {

        int eventAcross =
            constraintScope.stream()
                .filter(i -> i.arguments().contains(v))
                .mapToInt(i -> i.getNestedPruningEvent(v, false))
                .max()
                .orElse(Integer.MIN_VALUE);

        if (eventAcross != Integer.MIN_VALUE) {
          return eventAcross;
        }
      }
      return getDefaultNestedNotConsistencyPruningEvent();
    }
  }

  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return getDefaultNotConsistencyPruningEvent();
  }

  protected int getDefaultNestedConsistencyPruningEvent() {
    return getDefaultConsistencyPruningEvent();
  }

  /**
   * Returns the default pruning event used for the notConsistency method.
   *
   * @return the default pruning event for notConsistency evaluation.
   */
  protected int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  /**
   * It makes pruning in such a way that constraint is notConsistent. It removes values which always
   * belong to a solution.
   *
   * @param store the constraint store in which context the notConsistency technique is evaluated.
   */
  public abstract void notConsistency(Store store);

  /**
   * It checks if constraint would be always not satisfied.
   *
   * @return true if constraint must be notSatisfied, false otherwise.
   */
  public abstract boolean notSatisfied();

  /**
   * It allows to specify customized events required to trigger execution of notConsitency() method.
   *
   * @param v variable for which customized event is setup.
   * @param pruningEvent the type of the event being setup.
   */
  public void setNotConsistencyPruningEvent(Var v, int pruningEvent) {

    if (notConsistencyPruningEvents == null) {
      notConsistencyPruningEvents = new HashMap<>();
    }

    notConsistencyPruningEvents.put(v, pruningEvent);
  }

  /**
   * Includes this constraint and all nested constraints in the given store.
   *
   * @param store the constraint store in which to include this constraint.
   */
  public void include(Store store) {
    if (constraintScope != null) {
      constraintScope.forEach(i -> i.include(store));
    }
  }

  /**
   * Computes the maximum pruning event for a variable across a set of nested constraints. For each
   * constraint that contains the variable in its arguments, both consistency and notConsistency
   * nested pruning events are checked and the maximum is returned.
   *
   * <p>This helper eliminates duplicated pruning-event computation in reified constraints such as
   * IfThen, Eq, Reified, Xor, Implies, etc.
   *
   * @param v the variable for which to compute the pruning event.
   * @param constraints the nested constraints to query.
   * @return the maximum pruning event, or {@link Domain#NONE} if the variable is not found.
   */
  protected static int computeMaxPruningEvent(Var v, PrimitiveConstraint... constraints) {
    int eventAcross = -1;
    for (PrimitiveConstraint constraint : constraints) {
      if (constraint.arguments().contains(v)) {
        int event = constraint.getNestedPruningEvent(v, true);
        if (event > eventAcross) {
          eventAcross = event;
        }
        event = constraint.getNestedPruningEvent(v, false);
        if (event > eventAcross) {
          eventAcross = event;
        }
      }
    }
    return eventAcross == -1 ? Domain.NONE : eventAcross;
  }

  /**
   * Checks whether the given variable has a boolean domain (0..1).
   *
   * @param v the variable to check.
   * @return an error message if the domain is not boolean, or null if valid.
   */
  protected static String checkBooleanDomain(IntVar v) {
    if (v.min() < 0 || v.max() > 1) {
      return "Variable " + v + " does not have boolean domain";
    }
    return null;
  }

  /**
   * Checks whether all given variables have boolean domains (0..1).
   *
   * @param vars the variables to check.
   * @return an error message for the first non-boolean variable found, or null if all are valid.
   */
  protected static String checkBooleanDomains(IntVar... vars) {
    for (IntVar v : vars) {
      String error = checkBooleanDomain(v);
      if (error != null) {
        return error;
      }
    }
    return null;
  }

  /**
   * Computes the pruning event for a variable in a reified constraint context. This method checks
   * the events map first, then checks if the variable is the boolean variable (returning GROUND),
   * and finally computes the maximum pruning event across nested constraints.
   *
   * <p>This helper eliminates duplicated pruning-event computation in reified constraints such as
   * Reified and Implies.
   *
   * @param v the variable for which to compute the pruning event.
   * @param eventsMap the map of custom pruning events, or null if none.
   * @param b the boolean variable of the reified constraint.
   * @param c the nested constraint.
   * @return the pruning event for the variable.
   */
  protected static int getPruningEventFor(
      Var v, Map<Var, Integer> eventsMap, IntVar b, PrimitiveConstraint c) {
    if (eventsMap != null) {
      Integer possibleEvent = eventsMap.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }
    if (v == b) {
      return IntDomain.GROUND;
    }
    return computeMaxPruningEvent(v, c);
  }

  /**
   * Throws an IllegalStateException indicating that a more precise method exists and should be used
   * instead. This helper method eliminates duplication in subclasses that override default pruning
   * event methods to throw this exception.
   *
   * @throws IllegalStateException always, with a message indicating a more precise method exists.
   */
  protected static int throwMorePreciseMethodExists() {
    throw new IllegalStateException("Not implemented as more precise method exists.");
  }
}
