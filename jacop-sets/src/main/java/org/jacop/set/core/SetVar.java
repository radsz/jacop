/*
 * SetVar.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.set.core;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.ArrayList;
import org.jacop.constraints.Constraint;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Defines a Finite Domain Variable (FDV) and related operations on it.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class SetVar extends Var {

  // Ensure search handlers are registered when SetVar is first used
  static {
    try {
      Class.forName("org.jacop.set.search.SetSearchSupport");
    } catch (ClassNotFoundException _) {
      // SetSearchSupport not available - handlers won't be registered
      // This is OK if jacop-sets search package is not on classpath
    }
  }

  /** It specifies the current domain associated with this set variable. */
  public SetDomain domain;

  /**
   * It creates a variable in a given store, with a given name and a given domain.
   *
   * @param store store in which the variable is created.
   * @param name the name for the variable being created.
   * @param dom the domain of the variable being created.
   */
  public SetVar(Store store, String name, SetDomain dom) {
    dom.searchConstraints = new ArrayList<>();
    dom.modelConstraints = new Constraint[SetDomain.eventsInclusion.length][];
    dom.modelConstraintsToEvaluate = new int[SetDomain.eventsInclusion.length];

    if (ASSERTS_ENABLED && name.lastIndexOf(" ") != -1) {
      throw new IllegalStateException(String.valueOf("Name can not contain space character"));
    }

    id = name;
    domain = dom;
    domain.stamp = 0;
    storeIndex = store.putVariable(this);
    this.store = store;
  }

  /**
   * It creates a variable in a given store, with a given name and a given domain.
   *
   * @param store store in which the variable is created.
   * @param dom the domain of the variable being created.
   */
  public SetVar(Store store, SetDomain dom) {
    this(store, store.getVariableIdPrefix() + idNumber.incrementAndGet(), dom);
  }

  /** No parameter, explicit, empty constructor for subclasses. */
  public SetVar() {}

  /**
   * This constructor creates a variable with empty domain (standard IntervalDomain domain),
   * automatically generated name, and empty attached constraint list.
   *
   * @param store store in which the variable is created.
   */
  public SetVar(Store store) {
    this(store, store.getVariableIdPrefix() + idNumber.incrementAndGet(), new BoundSetDomain());
  }

  /**
   * This constructor creates a set variable with domain a set min..max automatically generated
   * name, and empty attached constraint list.
   *
   * @param store store in which the variable is created.
   * @param min the minimum value of the domain.
   * @param max the maximum value of the domain.
   */
  public SetVar(Store store, int min, int max) {
    this(
        store,
        store.getVariableIdPrefix() + idNumber.incrementAndGet(),
        new BoundSetDomain(min, max));
  }

  /**
   * This constructor creates a variable with an empty domain (standard IntervalDomain domain), the
   * specified name, and an empty attached constraint list.
   *
   * @param store store in which the variable is created.
   * @param name the name for the variable being created.
   */
  public SetVar(Store store, String name) {
    this(store, name, new BoundSetDomain());
  }

  /**
   * This constructor creates a variable in a given store, with the domain specified by min..max and
   * with the given name.
   *
   * @param store the store in which the variable is created.
   * @param name the name of the variable being created.
   * @param min the minimum value of the variables domain.
   * @param max the maximum value of the variables domain.
   */
  public SetVar(Store store, String name, int min, int max) {
    this(store, name, new BoundSetDomain(min, max));
  }

  /**
   * It is possible to add the domain of variable. It should be used with care, only right after
   * variable was created and before it is used in constraints or search. Current implementation
   * requires domains being added in the increasing order (e.g. 1..5 before 9..10).
   *
   * @param min the left bound of the interval being added.
   * @param max the right bound of the interval being added.
   */
  public void addDom(int min, int max) {
    domain.addDom(min, max);
  }

  /**
   * It is possible to add the domain of variable. It should be used with care, only right after
   * variable was created and before it is used in constraints or search.
   *
   * @param dom the added domain.
   */
  public void addDom(SetDomain dom) {
    domain.addDom(dom);
  }

  /**
   * It is possible to set the domain of variable. It should be used with care, only right after
   * variable was created and before it is used in constraints or search.
   *
   * @param min the left bound of the interval used to set this variable domain to.
   * @param max the right bound of the interval used to set this variable domain to.
   */
  public void setDomain(int min, int max) {
    domain.setDomain(min, max);
  }

  /**
   * It is possible to set the domain of variable. It should be used with care, only right after
   * variable was created and before it is used in constraints or search.
   *
   * @param dom domain to which the current variable domain is set to.
   */
  public void setDomain(SetDomain dom) {
    domain.setDomain(dom);
  }

  /**
   * This function returns current domain of the variable.
   *
   * @return the domain of the variable.
   */
  public SetDomain dom() {
    return domain;
  }

  /**
   * It checks if the domains of variables are equal.
   *
   * @param v the variable to which current variable is compared to.
   * @return true if both variables have the same domain.
   */
  public boolean eq(SetVar v) {
    return domain.eq(v.dom());
  }

  /**
   * It returns the size of the current domain.
   *
   * @return the size of the variables domain.
   */
  public int getSize() {
    return domain.getSize();
  }

  /**
   * It returns the size of the current domain.
   *
   * @return the size of the variables domain.
   */
  public double getSizeFloat() {
    return getSize();
  }

  /**
   * It checks if the domain is empty.
   *
   * @return true if variable domain is empty.
   */
  public boolean isEmpty() {
    return domain.isEmpty();
  }

  /**
   * It returns the values which have been removed at current store level. It does _not_ return the
   * recent pruning in between the calls to that function.
   *
   * @return difference between the current level and the one before it.
   */
  public SetDomain recentDomainPruning() {

    return domain.recentDomainPruning(store.level);
  }

  /**
   * It checks if the domain contains only one value.
   *
   * @return true if the variable domain is a singleton, false otherwise.
   */
  public boolean singleton() {
    return domain.singleton();
  }

  /**
   * This function returns stamp of the current domain of variable. It is equal or smaller to the
   * stamp of store. Larger difference indicates that variable has been changed for a longer time.
   *
   * @return level for which the most recent changes have been applied to.
   */
  public int level() {
    return domain.stamp;
  }

  /**
   * Removes the domain information stored at the specified level.
   *
   * @param removedLevel the level to be removed from the domain history.
   */
  public void remove(int removedLevel) {
    domain.removeLevel(removedLevel, this);
  }

  /**
   * It informs the variable that its variable has changed according to the specified event.
   *
   * @param event the type of the change (GROUND, BOUND, ANY).
   */
  public void domainHasChanged(int event) {

    boolean singleton = singleton();
    if (ASSERTS_ENABLED
        && ((event == SetDomain.LUB_EVENT && singleton)
            || (event == SetDomain.GLB_EVENT && singleton)
            || (event == SetDomain.ANY && singleton)
            || (event == SetDomain.BOUND && singleton)
            || (event == SetDomain.CARDINALITY_EVENT && singleton)
            || (event == SetDomain.GROUND && !singleton)
            || (event != SetDomain.LUB_EVENT
                && event != SetDomain.GLB_EVENT
                && event != SetDomain.ANY
                && event != SetDomain.BOUND
                && event != SetDomain.CARDINALITY_EVENT
                && event != SetDomain.GROUND))) {
      throw new IllegalStateException(
          String.valueOf("Wrong event generated " + event + "? " + singleton()));
    }

    store.addChanged(this, event, Integer.MIN_VALUE);
  }

  /**
   * Registers a constraint with the default pruning event (ANY).
   *
   * @param c the constraint to be attached to this variable.
   */
  public void putConstraint(Constraint c) {
    putModelConstraint(c, SetDomain.ANY);
  }
}
