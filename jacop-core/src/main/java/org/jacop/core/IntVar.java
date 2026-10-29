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

  // the bounds of domain, refreshed on every change of it, so that min() and max() read a field of
  // the variable instead of the domain (Gecode's IntVarImp keeps them the same way); an empty
  // domain has lb > ub
  private int lb = Integer.MAX_VALUE;
  private int ub = Integer.MIN_VALUE;

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
      commonInitialization(store, name, new LazyBitSetDomain(min, max));
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
    refreshBounds();
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
    widenDomainFor(min, max);
    domain.unionAdapt(min, max);
    refreshBounds();
  }

  /**
   * It is possible to add the domain of variable. It should be used with care, only right after
   * variable was created and before it is used in constraints or search.
   *
   * @param dom the added domain.
   */
  public void addDom(IntDomain dom) {
    if (!dom.isEmpty()) {
      widenDomainFor(dom.min(), dom.max());
    }
    domain.addDom(dom);
    refreshBounds();
  }

  /**
   * Replaces a domain that cannot hold the values min..max as well by the representation that
   * IntVar(store, name, min, max) chooses for the joined span: a SmallDenseDomain holds at most 64
   * values and a LazyBitSetDomain keeps its holes as bits below LazyBitSetDomain.MAX_SPAN values.
   */
  private void widenDomainFor(int min, int max) {
    if (domain.isEmpty()) {
      return;
    }
    long span = (long) Math.max(domain.max(), max) - Math.min(domain.min(), min);
    boolean tooSmall =
        domain.domainId() == IntDomain.SMALL_DENSE_DOMAIN_ID && span > 63L
            || domain instanceof LazyBitSetDomain lazy
                && !lazy.rangeHoles
                && span >= LazyBitSetDomain.MAX_SPAN;
    if (!tooSmall) {
      return;
    }
    IntDomain wider =
        new LazyBitSetDomain(domain.min(), domain.max(), span >= LazyBitSetDomain.MAX_SPAN);
    wider.setDomain(domain);
    wider.searchConstraints = domain.searchConstraints;
    wider.modelConstraints = domain.modelConstraints;
    wider.modelConstraintsToEvaluate = domain.modelConstraintsToEvaluate;
    wider.searchConstraintsToEvaluate = domain.searchConstraintsToEvaluate;
    wider.searchConstraintsCloned = domain.searchConstraintsCloned;
    wider.previousDomain = domain.previousDomain;
    wider.stamp = domain.stamp;
    domain = wider;
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
    refreshBounds();
  }

  /**
   * It is possible to set the domain of variable. It should be used with care, only right after
   * variable was created and before it is used in constraints or search.
   *
   * @param dom domain to which the current variable domain is set to.
   */
  public void setDomain(IntDomain dom) {
    domain.setDomain(dom);
    refreshBounds();
  }

  /**
   * Reads the bounds of the domain again. The domain classes and IntVar call it after every change
   * of the domain; code that changes the domain of a variable in another way, after the variable
   * was created, calls it too.
   */
  public final void refreshBounds() {
    IntDomain d = domain;
    if (d.isEmpty()) {
      lb = Integer.MAX_VALUE;
      ub = Integer.MIN_VALUE;
    } else {
      lb = d.min();
      ub = d.max();
    }
  }

  // sets the bounds kept for a domain restored in place on backtracking, which does not visit the
  // variable
  void setBounds(int min, int max) {
    lb = min;
    ub = max;
  }

  // reads the bounds of a domain that is not empty (after a change, or restored on backtracking);
  // a test per domain class keeps each call monomorphic, so the JIT can inline it
  private void readBounds() {
    IntDomain d = domain;
    if (d instanceof IntervalDomain interval) {
      lb = interval.min();
      ub = interval.max();
    } else if (d instanceof SmallDenseDomain smallDense) {
      lb = smallDense.min();
      ub = smallDense.max();
    } else if (d instanceof LazyBitSetDomain lazy) {
      lb = lazy.min();
      ub = lazy.max();
    } else if (d instanceof BoundDomain bound) {
      lb = bound.min();
      ub = bound.max();
    } else {
      lb = d.min();
      ub = d.max();
    }
  }

  // with asserts enabled, checks that the bounds are those of the domain
  private void checkBounds() {
    IntDomain d = domain;
    if (d.isEmpty() ? lb <= ub : lb != d.min() || ub != d.max()) {
      throw new IllegalStateException(
          "Cached bounds " + lb + ".." + ub + " of " + id + " differ from its domain " + d);
    }
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

    return min();
  }

  /**
   * It checks if the domain contains only one value equal to c.
   *
   * @param val value to which we compare the singleton of the variable.
   * @return true if a variable domain is singleton and it is equal to the specified value.
   */
  public boolean singleton(int val) {
    if (ASSERTS_ENABLED) {
      checkBounds();
    }
    return lb == val && ub == val;
  }

  /**
   * It checks if the domain contains only one value.
   *
   * @return true if the variable domain is a singleton, false otherwise.
   */
  public boolean singleton() {
    if (ASSERTS_ENABLED) {
      checkBounds();
    }
    return lb == ub;
  }

  /**
   * This function returns current maximal value in the domain of the variable.
   *
   * @return the maximum value belonging to the domain.
   */
  public int max() {
    if (ASSERTS_ENABLED) {
      checkBounds();
    }
    return ub;
  }

  /**
   * This function returns current minimal value in the domain of the variable.
   *
   * @return the minimum value beloning to the domain.
   */
  public int min() {
    if (ASSERTS_ENABLED) {
      checkBounds();
    }
    return lb;
  }

  /**
   * This function returns current domain of the variable.
   *
   * @return the domain of the variable.
   */
  public IntDomain dom() {
    return domain;
  }

  @Override
  public IntVar copyTo(Store target) {
    if (getClass() != IntVar.class) {
      return (IntVar) super.copyTo(target);
    }
    return new IntVar(target, id(), domain.cloneLight());
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
    readBounds();
  }

  /**
   * Tells the store's domain change recorder, if any, that a value is about to be removed on its
   * own; see {@link DomainChangeRecorder#removingValue}.
   *
   * @param value the value
   */
  public void removingValue(int value) {
    if (store.domainChangeRecorder != null) {
      store.domainChangeRecorder.removingValue(this, value);
    }
  }

  /**
   * It informs the variable that its variable has changed according to the specified event.
   *
   * @param event the type of the change (GROUND, BOUND, ANY).
   */
  public void domainHasChanged(int event) {

    // an ANY event leaves the bounds as they were
    if (event != IntDomain.ANY) {
      readBounds();
    }

    if (ASSERTS_ENABLED
        && !((event == IntDomain.ANY && !singleton())
            || ((event == IntDomain.BOUND
                    || event == IntDomain.MIN_EVENT
                    || event == IntDomain.MAX_EVENT)
                && !singleton())
            || (event == IntDomain.GROUND && singleton()))) {
      throw new IllegalStateException(String.valueOf("Wrong event generated"));
    }

    if (store.domainChangeRecorder != null) {
      store.domainChangeRecorder.domainChanged(this, event);
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
