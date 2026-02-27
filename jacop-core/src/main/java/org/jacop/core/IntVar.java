/*
 * IntVar.java
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

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.ArrayList;
import org.jacop.constraints.Constraint;

/**
 * Defines a Finite Domain Variable (FDV) and related operations on it.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class IntVar extends Var {

  /** It stores pointer to a current domain, which has stamp equal to store stamp. */
  public IntDomain domain;

  /*
  public SatCpBridge satBridge;
  */

  /**
   * It creates a variable in a given store, with a given name and a given domain.
   *
   * @param store store in which the variable is created.
   * @param name the name for the variable being created.
   * @param dom the domain of the variable being created.
   */
  public IntVar(Store store, String name, IntDomain dom) {

    commonInitialization(store, name, dom);
  }

  /**
   * It creates a variable in a given store, with a given name and a given domain.
   *
   * @param store store in which the variable is created.
   * @param dom the domain of the variable being created.
   */
  public IntVar(Store store, IntDomain dom) {
    this(store, store.getVariableIdPrefix() + idNumber.incrementAndGet(), dom);
  }

  /** No parameter, explicit, empty constructor for subclasses. */
  public IntVar() {}

  /**
   * This constructor creates a variable with empty domain (standard IntervalDomain domain),
   * automatically generated name, and empty attached constraint list.
   *
   * @param store store in which the variable is created.
   */
  public IntVar(Store store) {
    this(store, store.getVariableIdPrefix() + idNumber.incrementAndGet(), new IntervalDomain(5));
  }

  /**
   * This constructor creates a variable with a domain between min..max, automatically generated
   * name, and empty attached constraint list.
   *
   * @param store store in which the variable is created.
   * @param min the minimum value of the domain.
   * @param max the maximum value of the domain.
   */
  public IntVar(Store store, int min, int max) {
    this(store, store.getVariableIdPrefix() + idNumber.incrementAndGet(), min, max);
  }

  /**
   * This constructor creates a variable with an empty domain (standard IntervalDomain domain), the
   * specified name, and an empty attached constraint list.
   *
   * @param store store in which the variable is created.
   * @param name the name for the variable being created.
   */
  public IntVar(Store store, String name) {
    this(store, name, new IntervalDomain(5));
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
  public IntVar(Store store, String name, int min, int max) {

    if ((long) max - min > 63L) {
      commonInitialization(store, name, new IntervalDomain(min, max));
    } else {
      commonInitialization(store, name, new SmallDenseDomain(min, max));
    }
  }

  private void commonInitialization(Store store, String name, IntDomain dom) {

    dom.searchConstraints = new ArrayList<>();
    dom.modelConstraints = new Constraint[IntDomain.eventsInclusion.length][];
    dom.modelConstraintsToEvaluate = new int[IntDomain.eventsInclusion.length];

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
   * It is possible to add the domain of variable. It should be used with care, only right after
   * variable was created and before it is used in constraints or search. Current implementation
   * requires domains being added in the increasing order (e.g. 1..5 before 9..10).
   *
   * @param min the left bound of the interval being added.
   * @param max the right bound of the interval being added.
   */
  public void addDom(int min, int max) {
    domain.unionAdapt(min, max);
  }

  /**
   * It is possible to add the domain of variable. It should be used with care, only right after
   * variable was created and before it is used in constraints or search.
   *
   * @param dom the added domain.
   */
  public void addDom(IntDomain dom) {
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
  public void setDomain(IntDomain dom) {
    domain.setDomain(dom);
  }

  /**
   * This function returns current value in the domain of the variable. If current domain of
   * variable is not singleton then warning is printed and minimal value is returned.
   *
   * @return the value to which the variable has been grounded to.
   */
  public int value() {

    if (ASSERTS_ENABLED && !singleton()) {
      throw new IllegalStateException(
          String.valueOf("Request for a value of not grounded variable " + this));
    }

    return domain.min();
  }

  /**
   * It checks if the domain contains only one value equal to c.
   *
   * @param val value to which we compare the singleton of the variable.
   * @return true if a variable domain is singleton and it is equal to the specified value.
   */
  public boolean singleton(int val) {
    return domain.singleton(val);
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
   * This function returns current maximal value in the domain of the variable.
   *
   * @return the maximum value belonging to the domain.
   */
  public int max() {
    return domain.max();
  }

  /**
   * This function returns current minimal value in the domain of the variable.
   *
   * @return the minimum value beloning to the domain.
   */
  public int min() {
    return domain.min();
  }

  /**
   * This function returns current domain of the variable.
   *
   * @return the domain of the variable.
   */
  public IntDomain dom() {
    return domain;
  }

  /**
   * It checks if the domains of variables are equal.
   *
   * @param v the variable to which current variable is compared to.
   * @return true if both variables have the same domain.
   */
  public boolean eq(IntVar v) {
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
   * It registers constraint with current variable, so anytime this variable is changed the
   * constraint is reevaluated. Pruning events constants from 0 to n, where n is the strongest
   * pruning event.
   *
   * @param c the constraint which is being attached to the variable.
   * @param pruningEvent type of the event which must occur to trigger the execution of the
   *     consistency function.
   */

  /**
   * It returns the values which have been removed at current store level. It does _not_ return the
   * recent pruning in between the calls to that function.
   *
   * @return difference between the current level and the one before it.
   */
  public IntDomain recentDomainPruning() {

    return domain.recentDomainPruning(store.level);
  }

  @Override
  public int level() {
    return domain.stamp;
  }

  /**
   * Removes the specified level from the variable's domain, effectively backtracking to that level.
   *
   * @param removedLevel the level to be removed.
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

    if (ASSERTS_ENABLED
        && !((event == IntDomain.ANY && !singleton())
            || (event == IntDomain.BOUND && !singleton())
            || (event == IntDomain.GROUND && singleton()))) {
      throw new IllegalStateException(String.valueOf("Wrong event generated"));
    }

    store.addChanged(this, event, Integer.MIN_VALUE);
  }

  /**
   * Registers a constraint with this variable using the ANY pruning event.
   *
   * @param c the constraint to be attached to the variable.
   */
  public void putConstraint(Constraint c) {
    putModelConstraint(c, IntDomain.ANY);
  }
}
