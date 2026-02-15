/*
 * BoundSetDomain.java
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

import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.SmallDenseDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * Defines a set interval determined by a least upper bound(lub) and a greatest lower bound(glb).
 * The domain consist of zero, one or several sets.
 *
 * @author Radoslaw Szymanek, Krzysztof Kuchcinski and Robert Åkemalm
 * @version 5.0
 */
public class BoundSetDomain extends SetDomain {

  /** An empty domain, so no constant creation of empty domains is required. */
  public static final BoundSetDomain emptyDomain = new BoundSetDomain();

  /** It specifies an empty set domain. */
  public static final SetDomain EMPTY = emptyDomain;

  // FIXME do not use emptySet to assign to lub, glb.
  /** The greatest lower bound of the domain. */
  public IntDomain glbDomain;

  /** The least upper bound of the domain. */
  public IntDomain lubDomain;

  /** The cardinality of the set. */
  public IntDomain cardDomain;

  /** Initializes common fields for all constructors. */
  private void initCommonFields() {
    searchConstraints = null;
    searchConstraintsToEvaluate = 0;
    previousDomain = null;
    searchConstraintsCloned = false;
  }

  /**
   * Copies common domain fields (constraints, stamp, etc.) from this domain to a result domain.
   * This helper method reduces duplication when creating new domain instances during backtracking.
   *
   * @param result the domain to copy fields to
   * @param level the store level for the new domain
   */
  private void copyCommonFieldsToResult(BoundSetDomain result, int level) {
    result.modelConstraints = modelConstraints;
    result.searchConstraints = searchConstraints;
    result.stamp = level;
    result.previousDomain = this;
    result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
    result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
  }

  /**
   * Fires GROUND event if the domain is a singleton, otherwise fires the specified event.
   *
   * @param v the set variable to notify
   * @param dom the domain to check for singleton
   * @param event the event to fire if the domain is not a singleton
   */
  private static void notifySingletonOrEvent(SetVar v, SetDomain dom, int event) {
    if (dom.singleton()) {
      v.domainHasChanged(SetDomain.GROUND);
    } else {
      v.domainHasChanged(event);
    }
  }

  /**
   * Updates cardinality after a glb growth (same-level) and fires the appropriate event.
   *
   * @param v the set variable to notify
   */
  private void adaptCardAfterGlbGrowth(SetVar v) {
    cardDomain.intersectAdapt(glbDomain.getSize(), lubDomain.getSize());
    if (cardDomain.isEmpty()) {
      throw Store.failException;
    }
    if (cardDomain.max() == glbDomain.getSize()) {
      lubDomain = glbDomain;
      cardDomain.intersectAdapt(glbDomain.getSize(), glbDomain.getSize());
    }
    notifySingletonOrEvent(v, this, SetDomain.GLB_EVENT);
  }

  /**
   * Updates cardinality after a lub shrink (same-level) and fires the appropriate event.
   *
   * @param v the set variable to notify
   */
  private void adaptCardAfterLubShrink(SetVar v) {
    cardDomain.intersectAdapt(glbDomain.getSize(), lubDomain.getSize());
    if (cardDomain.isEmpty()) {
      throw Store.failException;
    }
    if (cardDomain.min() == lubDomain.getSize()) {
      glbDomain = lubDomain;
      cardDomain.intersectAdapt(lubDomain.getSize(), lubDomain.getSize());
    }
    notifySingletonOrEvent(v, this, SetDomain.LUB_EVENT);
  }

  /**
   * Applies a new-level glb change: creates a new domain with the given resultGlb, computes
   * cardinality, installs it on the variable, and fires the appropriate event.
   *
   * @param level the store level
   * @param v the set variable
   * @param resultGlb the new greatest lower bound
   */
  private void applyNewLevelGlbChange(int level, SetVar v, IntDomain resultGlb) {
    IntDomain resultCardinality = cardDomain.intersect(resultGlb.getSize(), lubDomain.getSize());
    if (resultCardinality.isEmpty()) {
      throw Store.failException;
    }

    BoundSetDomain result = new BoundSetDomain();
    result.glbDomain = resultGlb;
    if (resultCardinality.max() == resultGlb.getSize()) {
      result.lubDomain = resultGlb;
      resultCardinality.intersectAdapt(resultGlb.getSize(), resultGlb.getSize());
    } else {
      result.lubDomain = lubDomain.cloneLight();
    }
    result.cardDomain = resultCardinality;

    copyCommonFieldsToResult(result, level);
    v.domain = result;

    notifySingletonOrEvent(v, result, SetDomain.GLB_EVENT);
  }

  /**
   * Applies a new-level lub change: creates a new domain with the given resultLub, computes
   * cardinality, installs it on the variable, and fires the appropriate event.
   *
   * @param level the store level
   * @param v the set variable
   * @param resultLub the new least upper bound
   */
  private void applyNewLevelLubChange(int level, SetVar v, IntDomain resultLub) {
    IntDomain resultCardinality = cardDomain.intersect(glbDomain.getSize(), resultLub.getSize());
    if (resultCardinality.isEmpty()) {
      throw Store.failException;
    }

    BoundSetDomain result = new BoundSetDomain();
    if (resultCardinality.min() == resultLub.getSize()) {
      result.glbDomain = resultLub;
      resultCardinality.intersectAdapt(resultLub.getSize(), resultLub.getSize());
    } else {
      result.glbDomain = glbDomain.cloneLight();
    }
    result.lubDomain = resultLub;
    result.cardDomain = resultCardinality;

    copyCommonFieldsToResult(result, level);
    v.domain = result;

    notifySingletonOrEvent(v, result, SetDomain.LUB_EVENT);
  }

  /**
   * Creates BoundSetDomain object. It requires glb to be a subset of lubDomain.
   *
   * @param glb it specifies the left bound of the SetDomain (inclusive).
   * @param lub it specifies the right bound of the setDomain (inclusive).
   * @param cardinality it specifies the allowed cardinality of the assigned set.
   */
  public BoundSetDomain(IntDomain glb, IntDomain lub, IntDomain cardinality) {

    if (!lub.contains(glb)) {
      throw new IllegalArgumentException();
    }

    this.glbDomain = glb.cloneLight();
    this.lubDomain = lub.cloneLight();
    this.cardDomain = cardinality.cloneLight();

    initCommonFields();
  }

  /**
   * Creates a new instance of SetDomain. It requires glb to be a subset of lubDomain.
   *
   * @param glb it specifies the left bound of the SetDomain (inclusive).
   * @param lub it specifies the right bound of the setDomain (inclusive).
   */
  public BoundSetDomain(IntDomain glb, IntDomain lub) {

    if (!lub.contains(glb)) {
      throw new IllegalArgumentException();
    }

    this.glbDomain = glb.cloneLight();
    this.lubDomain = lub.cloneLight();
    this.cardDomain = new IntervalDomain(glb.getSize(), lub.getSize());

    // TODO: test the replacement of intervaldomain when possible by SmallDenseDomain.
    // this.cardDomain = new SmallDenseDomain(glb.getSize(), lub.getSize());

    initCommonFields();
  }

  /**
   * It is a constructor which will create an empty SetDomain. An empty SetDomain has a glb and a
   * lub that is empty.
   */
  public BoundSetDomain() {

    this.glbDomain = new IntervalDomain(0);
    this.lubDomain = new IntervalDomain(0);
    this.cardDomain = new IntervalDomain(0, 0);

    initCommonFields();
  }

  /**
   * It creates a new instance of SetDomain with glb empty and lub={e1..e2}
   *
   * @param e1 the minimum element of lubDomain.
   * @param e2 the maximum element of lubDomain.
   */
  public BoundSetDomain(int e1, int e2) {

    if (e2 - e1 > 63) {
      this.glbDomain = new IntervalDomain(0);
      this.lubDomain = new IntervalDomain(e1, e2);
    } else {
      this.glbDomain = new SmallDenseDomain();
      this.lubDomain = new SmallDenseDomain(e1, e2);
    }

    this.cardDomain = new IntervalDomain(0, e2 - e1 + 1);

    initCommonFields();
  }

  /**
   * Adds a set of value to the possible values used within this set domain. It changes the
   * cardinality too to avoid cardinality constraining the domain.
   */
  public void addDom(IntDomain set) {

    assert set.checkInvariants() == null : set.checkInvariants();

    this.lubDomain = this.lubDomain.union(set);
    this.cardDomain = new IntervalDomain(glbDomain.getSize(), lubDomain.getSize());
  }

  /** Adds a set to the domain. */
  public void addDom(SetDomain domain) {

    assert domain.lub().checkInvariants() == null : domain.lub().checkInvariants();
    assert domain.glb().checkInvariants() == null : domain.glb().checkInvariants();

    lubDomain = lubDomain.union(domain.lub());
    glbDomain = glbDomain.intersect(domain.glb());
    this.cardDomain = new IntervalDomain(glbDomain.getSize(), lubDomain.getSize());
  }

  /**
   * Adds an interval [min..max] to the domain.
   *
   * @param min min value in the set
   * @param max max value in the set
   */
  public void addDom(int min, int max) {
    this.addDom(new IntervalDomain(min, max));
  }

  @Override
  public void addDom(Interval i) {

    this.lubDomain = this.lubDomain.union(i.min(), i.max());
    this.cardDomain = new IntervalDomain(glbDomain.getSize(), lubDomain.getSize());
  }

  /**
   * Returns the cardinality of the setDomain as [glb.card(), lubDomain.card()]
   *
   * @return The cardinality of the setDomain given as a boundDomain.
   */
  public IntDomain card() {
    return cardDomain;
  }

  /** Sets the domain to an empty SetDomain. */
  @Override
  public void clear() {
    glbDomain = new IntervalDomain();
    lubDomain = new IntervalDomain();
    this.cardDomain = new IntervalDomain(0, 0);
  }

  @Override
  public BoundSetDomain copy() {

    BoundSetDomain cloned =
        new BoundSetDomain(glbDomain.cloneLight(), lubDomain.cloneLight(), cardDomain);
    cloned.stamp = stamp;
    cloned.previousDomain = previousDomain;

    cloned.searchConstraints = searchConstraints;
    cloned.searchConstraintsToEvaluate = searchConstraintsToEvaluate;

    cloned.modelConstraints = modelConstraints;
    cloned.modelConstraintsToEvaluate = modelConstraintsToEvaluate;

    cloned.searchConstraintsCloned = searchConstraintsCloned;

    return cloned;
  }

  /**
   * It clones the domain object, only data responsible for encoding domain values is cloned. All
   * other fields must be set separately.
   *
   * @return return a clone of the domain. It aims at getting domain of the proper class type.
   */
  public SetDomain cloneLight() {
    // FIXME, why no glb and lub cloning is safe?
    return new BoundSetDomain(glbDomain, lubDomain, cardDomain);
  }

  /**
   * It creates a complement of a domain.
   *
   * @return it returns the complement of this domain.
   */
  public SetDomain complement() {
    // FIXME, is it right?
    // FIXME, it is not possible to express the complement of the set interval using just one set,
    // right?
    return new BoundSetDomain(this.lubDomain.complement(), this.glbDomain.complement());
  }

  /** It checks if the supplied set or setDomain is a subset of this domain. */
  public boolean contains(IntDomain set) {

    assert set.checkInvariants() == null : set.checkInvariants();

    return this.lubDomain.contains(set);
  }

  /**
   * Checks if this domain contains the specified domain.
   *
   * @param domain the domain to check for containment
   * @return true if this domain contains the specified domain, false otherwise
   */
  public boolean contains(SetDomain domain) {

    assert domain.checkInvariants() == null : domain.checkInvariants();

    return this.lubDomain.contains(domain.lub());
  }

  /** It checks if value belongs to the domain. */
  public boolean contains(int value) {
    return lubDomain.contains(value);
  }

  /**
   * It returns an unique identifier of the domain.
   *
   * @return it returns an integer id of the domain.
   */
  @Override
  public int domainId() {
    return SET_DOMAIN_ID;
  }

  /**
   * It checks if the domain is equal to the supplied domain.
   *
   * @param domain against which the equivalence test is performed.
   * @return true if suppled domain has the same elements as this domain.
   */
  public boolean eq(SetDomain domain) {
    return domain.glb().eq(this.glbDomain) && domain.lub().eq(this.lubDomain);
  }

  /** Returns the number of elements in the domain. */
  @Override
  public int getSize() {
    return (int) Math.pow(2, (double) lubDomain.getSize() - glbDomain.getSize());
  }

  /**
   * It returns the greatest lower bound of the domain.
   *
   * @return the greatest lower bound of the domain.
   */
  public IntDomain glb() {
    return glbDomain;
  }

  /**
   * This function is equivalent to in(int storeLevel, Variable var, int min, int max).
   *
   * @param storeLevel the level of the store at which the change occurrs.
   * @param v the set variable for which the domain may change.
   * @param inGlb the greatest lower bound of the domain.
   * @param inLub the least upper bound of the domain.
   */
  public void in(int storeLevel, SetVar v, IntDomain inGlb, IntDomain inLub) {

    if (!inLub.contains(inGlb)) {
      throw Store.failException;
    }

    if (glbDomain.contains(inGlb) && inLub.contains(lubDomain)) {
      return;
    }

    if (stamp == storeLevel) {
      applyInAtSameLevel(storeLevel, v, inGlb, inLub);
    } else {
      applyInAtNewLevel(storeLevel, v, inGlb, inLub);
    }
  }

  private void applyInAtSameLevel(int storeLevel, SetVar v, IntDomain inGlb, IntDomain inLub) {
    int eventGlb = glbDomain.unionAdapt(inGlb);
    int eventLub = lubDomain.intersectAdapt(inLub);

    if (lubDomain.eq(glbDomain)) {
      cardDomain.intersectAdapt(glbDomain.getSize(), lubDomain.getSize());
      if (cardDomain.isEmpty()) {
        throw Store.failException;
      }
      v.domainHasChanged(IntDomain.GROUND);
      return;
    }

    int min = glbDomain.getSize();
    int max = lubDomain.getSize();
    if (min > max) {
      throw Store.failException;
    }

    int eventCardinality = cardDomain.intersectAdapt(min, max);
    if (cardDomain.isEmpty()) {
      throw Store.failException;
    }

    if (eventCardinality != Domain.NONE) {
      if (cardDomain.min() == lubDomain.getSize()) {
        glbDomain = lubDomain;
        cardDomain.intersectAdapt(lubDomain.getSize(), lubDomain.getSize());
        v.domainHasChanged(IntDomain.GROUND);
        return;
      }
      if (cardDomain.max() == glbDomain.getSize()) {
        lubDomain = glbDomain;
        cardDomain.intersectAdapt(glbDomain.getSize(), glbDomain.getSize());
        v.domainHasChanged(IntDomain.GROUND);
        return;
      }
    }

    if (eventGlb != Domain.NONE && eventLub != Domain.NONE) {
      v.domainHasChanged(SetDomain.ANY);
    } else if (eventGlb != Domain.NONE) {
      v.domainHasChanged(SetDomain.GLB_EVENT);
    } else if (eventLub != Domain.NONE) {
      v.domainHasChanged(SetDomain.LUB_EVENT);
    }
  }

  private void applyInAtNewLevel(int storeLevel, SetVar v, IntDomain inGlb, IntDomain inLub) {
    assert stamp < storeLevel;

    IntDomain resultGlb = glbDomain.cloneLight();
    int eventGlb = resultGlb.unionAdapt(inGlb);

    IntDomain resultLub = lubDomain.cloneLight();
    int eventLub = resultLub.intersectAdapt(inLub);

    IntDomain resultCardinality = cardDomain.intersect(glbDomain.getSize(), lubDomain.getSize());
    if (resultCardinality.isEmpty()) {
      throw Store.failException;
    }

    if (!resultCardinality.eq(cardDomain)) {
      if (cardDomain.min() == lubDomain.getSize()) {
        resultGlb = lubDomain;
        eventGlb = SetDomain.GLB_EVENT;
        resultCardinality.intersectAdapt(lubDomain.getSize(), lubDomain.getSize());
      }
      if (cardDomain.max() == glbDomain.getSize()) {
        resultLub = glbDomain;
        eventLub = SetDomain.LUB_EVENT;
        resultCardinality.intersectAdapt(glbDomain.getSize(), glbDomain.getSize());
      }
    }

    BoundSetDomain result = new BoundSetDomain();
    result.glbDomain = resultGlb;
    result.lubDomain = resultLub;
    result.cardDomain = resultCardinality;

    copyCommonFieldsToResult(result, storeLevel);
    v.domain = result;

    if (result.singleton()) {
      v.domainHasChanged(SetDomain.GROUND);
    } else {
      if (eventGlb == SetDomain.GLB_EVENT && eventLub == SetDomain.LUB_EVENT) {
        v.domainHasChanged(SetDomain.BOUND);
      } else if (eventGlb != Domain.NONE) {
        v.domainHasChanged(SetDomain.GLB_EVENT);
      } else if (eventLub != Domain.NONE) {
        v.domainHasChanged(SetDomain.LUB_EVENT);
      }
    }
  }

  /**
   * It updates the domain to have values only within the domain. The type of update is decided by
   * the value of stamp. It informs the variable of a change if it occurred.
   *
   * @param storeLevel level of the store at which the update occurs.
   * @param v variable for which this domain is used.
   * @param setDom the domain according to which the domain is updated.
   */
  public void in(int storeLevel, SetVar v, SetDomain setDom) {
    in(storeLevel, v, setDom.glb(), setDom.lub());
  }

  /**
   * It intersects current domain with the one given as a parameter.
   *
   * @param domain domain with which the intersection needs to be computed.
   * @return the intersection between supplied domain and this domain.
   */
  public SetDomain intersect(SetDomain domain) {

    assert domain.checkInvariants() == null : domain.checkInvariants();

    IntDomain lub_i = lubDomain.intersect(domain.lub());

    if (lub_i.isEmpty()) {
      return emptyDomain;
    }

    IntDomain glb_i = glbDomain.intersect(domain.glb());

    return new BoundSetDomain(glb_i, lub_i);
  }

  /**
   * It intersects current domain with the one given as a parameter.
   *
   * @param domain domain with which the intersection needs to be computed.
   * @return the intersection between supplied domain and this domain.
   */
  public SetDomain intersect(IntDomain domain) {

    assert domain.checkInvariants() == null : domain.checkInvariants();

    IntDomain lubResult = lubDomain.intersect(domain);

    if (lubResult.isEmpty()) {
      return emptyDomain;
    }

    IntDomain glbResult = glbDomain.intersect(domain);

    return new BoundSetDomain(glbResult, lubResult);
  }

  /**
   * It returns true if given domain is empty.
   *
   * @return true if the given domain is empty.
   */
  @Override
  public boolean isEmpty() {
    return glbDomain.isEmpty() && lubDomain.isEmpty();
  }

  /**
   * It returns true if given domain intersects this domain.
   *
   * @return true if the given domain intersects this domain.
   */
  // FIXME, improve the implementation.
  public boolean isIntersecting(SetDomain domain) {
    return !this.intersect(domain).isEmpty();
  }

  /**
   * In intersects current domain with the interval min..max.
   *
   * @param min the left bound of the interval (inclusive)
   * @param max the right bound of the interval (inclusive)
   * @return the intersection between the specified interval and this domain.
   */
  // FIXME, improve the implementation.
  public boolean isIntersecting(int min, int max) {
    return lubDomain.isIntersecting(new IntervalDomain(min, max));
  }

  /**
   * A set is never numeric.
   *
   * @return false
   */
  @Override
  public boolean isNumeric() {
    return false;
  }

  /**
   * A set is not sparse.
   *
   * @return false
   */
  @Override
  public boolean isSparseRepresentation() {
    return false;
  }

  /**
   * It returns the least upper bound of the domain.
   *
   * @return the least upper bound of the domain.
   */
  public IntDomain lub() {
    return lubDomain;
  }

  /**
   * It sets the domain to the specified domain.
   *
   * @param domain the domain from which this domain takes all elements.
   */
  public void setDomain(SetDomain domain) {

    assert domain.checkInvariants() == null : domain.checkInvariants();

    this.glbDomain = domain.glb();
    this.lubDomain = domain.lub();
  }

  /** It sets the domain to the the set {min..max}. It grounds it. FIXME should it be grounded? */
  public void setDomain(int min, int max) {

    assert (min <= max);
    // FIXME, BUG?
    this.lubDomain = new IntervalDomain(min, max);
    this.glbDomain = new IntervalDomain();

    // FIXME, remove after checking.
    throw new RuntimeException("check that the caller of this function is using it as intended.");
  }

  /**
   * It returns true if given domain has only one set-element.
   *
   * @return true if the domain contains only one set-element.
   */
  @Override
  public boolean singleton() {
    return lubDomain.eq(glbDomain);
  }

  /**
   * It returns true if given domain has only one set-element and this set-element only contains c.
   *
   * @return true if the domain contains only one set-element and this set-element only contains c.
   */
  public boolean singleton(IntDomain set) {

    return lubDomain.eq(set) && glbDomain.eq(set);
  }

  @Override
  public boolean singleton(Domain value) {

    if (!singleton()) {
      return false;
    }

    if (value instanceof IntDomain domain) {
      return glbDomain.eq(domain);
    }

    if (value instanceof BoundSetDomain input) {
      if (!input.singleton()) {
        throw new IllegalArgumentException("The input parameter value is not a singleton domain.");
      }

      return glbDomain.eq(input.glbDomain);
    }

    throw new IllegalArgumentException("Not recognized domain type for the input parameter value.");
  }

  /**
   * It subtracts domain from current domain and returns the result.
   *
   * @param domain the domain which is subtracted from this domain.
   * @return the result of the subtraction.
   */
  public SetDomain subtract(SetDomain domain) {

    assert domain.checkInvariants() == null : domain.checkInvariants();

    IntDomain glbResult = glbDomain.subtract(domain.lub());
    IntDomain lubResult = lubDomain.subtract(domain.glb());

    return new BoundSetDomain(glbResult, lubResult);
  }

  /**
   * It subtracts the elements of the set {min..max}.
   *
   * @param min the left bound of the set.
   * @param max the right bound of the set.
   * @return the domain after removing the int elements specified by the set.
   */
  public SetDomain subtract(int min, int max) {

    IntDomain lubResult = lubDomain.subtract(min, max);
    IntDomain glbResult = glbDomain.subtract(min, max);

    return new BoundSetDomain(glbResult, lubResult);
  }

  /**
   * It subtracts the set {value}. FIXME, it does not subtract set {value}, it subtracts value from
   * the set domain.
   *
   * @return the result of the subtraction.
   */
  public SetDomain subtract(int value) {

    SetDomain domain = this.cloneLight();

    domain.lub().subtract(value);
    domain.glb().subtract(value);

    return domain;
  }

  /** It returns string description of the domain. */
  @Override
  public String toString() {

    assert checkInvariants() == null : checkInvariants();

    if (this.glbDomain.eq(this.lubDomain)) {
      if (glbDomain.singleton()) {
        return "{" + glbDomain.toString() + "}";
      } else {
        return glbDomain.toString();
      }
    } else {

      StringBuilder result = new StringBuilder("{");

      if (glbDomain.singleton()) {
        result.append("{").append(glbDomain.toString()).append("}");
      } else {
        result.append(glbDomain.toString());
      }

      result.append("..");

      if (lubDomain.singleton()) {
        result.append("{").append(lubDomain.toString()).append("}");
      } else {
        result.append(lubDomain.toString());
      }

      result.append("}[card=").append(cardDomain).append("]");

      return result.toString();
    }
  }

  /**
   * It computes union of the supplied domain with this domain.
   *
   * @param domain the domain for which the union is computed.
   * @return the union of this domain with the supplied one.
   */
  public SetDomain union(SetDomain domain) {

    assert domain.checkInvariants() == null : domain.checkInvariants();

    IntDomain glbResult = glbDomain.intersect(domain.glb());
    IntDomain lubResult = lubDomain.union(domain.lub());

    return new BoundSetDomain(glbResult, lubResult);
  }

  /**
   * It computes union of this domain and the interval.
   *
   * @param min the left bound of the interval (inclusive).
   * @param max the right bound of the interval (inclusive).
   * @return the union of this domain and the interval.
   */
  public SetDomain union(int min, int max) {

    // FIXME, why not max >= min?
    assert max > min : "min value is larger than max value";

    IntDomain glbResult = glbDomain.union(min, max);
    IntDomain lubResult = lubDomain.union(min, max);

    return new BoundSetDomain(glbResult, lubResult);
  }

  /**
   * It computes union of this domain and value.
   *
   * @param value it specifies the value which is being added.
   * @return domain which is a union of this one and the value.
   */
  public SetDomain union(int value) {

    IntDomain glbResult = glbDomain.union(value);
    IntDomain lubResult = lubDomain.union(value);

    return new BoundSetDomain(glbResult, lubResult);
  }

  /**
   * It returns value enumeration of the domain values.
   *
   * @return valueEnumeration which can be used to enumerate the sets of this domain one by one.
   */
  @Override
  public ValueEnumeration valueEnumeration() {

    return new SetDomainValueEnumeration(this);
  }

  /**
   * Checks whether all domain invariants hold.
   *
   * @return It returns the information about the first invariant which does not hold or null
   *     otherwise.
   */
  public String checkInvariants() {

    if (!lubDomain.contains(glbDomain)) {
      return "Greatest lower bound is larger than least upper bound ";
    }

    // Fine, all invariants hold.
    return null;
  }

  /**
   * It adds if necessary an element to glbDomain.
   *
   * @param level level at which the change is recorded.
   * @param v set variable to which the change applies to.
   * @param element the element which must be in glbDomain.
   */
  public void inGlb(int level, SetVar v, int element) {

    if (glbDomain.contains(element)) {
      return;
    }

    if (!lubDomain.contains(element)) {
      throw Store.failException;
    }

    if (stamp == level) {

      glbDomain.unionAdapt(element);
      adaptCardAfterGlbGrowth(v);

    } else {

      assert stamp < level;
      applyNewLevelGlbChange(level, v, glbDomain.union(element));
    }
  }

  @Override
  public void inGlb(int level, SetVar v, IntDomain intersect) {

    if (glbDomain.contains(intersect)) {
      return;
    }

    if (!lubDomain.contains(intersect)) {
      throw Store.failException;
    }

    if (stamp == level) {

      int event = glbDomain.unionAdapt(intersect);

      if (event != Domain.NONE) {
        adaptCardAfterGlbGrowth(v);
      }

    } else {

      assert stamp < level;
      applyNewLevelGlbChange(level, v, glbDomain.union(intersect));
    }
  }

  /**
   * It removes if necessary an element from lubDomain.
   *
   * @param level level at which the change is recorded.
   * @param v set variable to which the change applies to.
   * @param element the element which can not be in lubDomain.
   */
  @Override
  public void inLubComplement(int level, SetVar v, int element) {

    if (!lubDomain.contains(element)) {
      return;
    }

    if (glbDomain.contains(element)) {
      throw Store.failException;
    }

    if (stamp == level) {

      lubDomain.subtractAdapt(element);
      adaptCardAfterLubShrink(v);

    } else {

      assert stamp < level;
      applyNewLevelLubChange(level, v, lubDomain.subtract(element));
    }
  }

  @Override
  public void inValue(int level, SetVar v, IntDomain set) {

    if (!set.contains(glbDomain)) {
      throw Store.failException;
    }

    if (!lubDomain.contains(set)) {
      throw Store.failException;
    }

    if (!cardDomain.contains(set.getSize())) {
      throw Store.failException;
    }

    if (lubDomain.eq(glbDomain)) {
      return;
    }

    if (stamp == level) {

      glbDomain.unionAdapt(set);
      lubDomain = glbDomain;
      cardDomain.intersectAdapt(glbDomain.getSize(), glbDomain.getSize());

    } else {

      assert stamp < level;

      // FIXME, allow specification of the sets in parts, so no unnecessary copying occur.
      BoundSetDomain result = new BoundSetDomain(set, set);
      result.cardDomain = new IntervalDomain(set.getSize(), set.getSize());

      copyCommonFieldsToResult(result, level);
      v.domain = result;
    }

    v.domainHasChanged(SetDomain.GROUND);
  }

  @Override
  public void inLub(int level, SetVar v, IntDomain intersect) {

    if (intersect.contains(lubDomain)) {
      return;
    }

    if (!intersect.contains(glbDomain)) {
      throw Store.failException;
    }

    if (stamp == level) {

      // IntDomain.INTERVAL_DOMAIN_ID) {
      //       event = replacement.intersectAdapt(lub);
      //       lubDomain = replacement;
      int event = lubDomain.intersectAdapt(intersect);

      if (event != Domain.NONE) {
        adaptCardAfterLubShrink(v);
      }

    } else {

      assert stamp < level;
      applyNewLevelLubChange(level, v, lubDomain.intersect(intersect));
    }
  }

  /**
   * It assigns a set variable to the least upper bound of its current domain.
   *
   * @param level the level of the store at which the change takes place.
   * @param v the variable for which the domain is changing.
   */
  public void inValueLub(int level, SetVar v) {
    groundTo(level, v, lubDomain);
  }

  /**
   * It assigns a set variable to glb of its current domain.
   *
   * @param level level of the store at which the change takes place.
   * @param v variable for which the domain is changing.
   */
  public void inValueGlb(int level, SetVar v) {
    groundTo(level, v, glbDomain);
  }

  /**
   * Grounds the set variable to the given target domain (either glb or lub).
   *
   * @param level the store level
   * @param v the set variable
   * @param target the domain to ground to (either glbDomain or lubDomain)
   */
  private void groundTo(int level, SetVar v, IntDomain target) {

    if (lubDomain.eq(glbDomain)) {
      return;
    }

    if (!cardDomain.contains(target.getSize())) {
      throw Store.failException;
    }

    if (stamp == level) {

      glbDomain = target;
      lubDomain = target;
      cardDomain.intersectAdapt(target.getSize(), target.getSize());

    } else {

      assert stamp < level;

      BoundSetDomain result = new BoundSetDomain();
      IntDomain cloned = target.cloneLight();
      result.glbDomain = cloned;
      result.lubDomain = cloned;
      result.cardDomain = new IntervalDomain(target.getSize(), target.getSize());

      copyCommonFieldsToResult(result, level);
      v.domain = result;
    }

    v.domainHasChanged(SetDomain.GROUND);
  }

  @Override
  public void inCardinality(int level, SetVar v, int min, int max) {

    if (min <= cardDomain.min() && cardDomain.max() <= max) {
      return;
    }

    boolean earlyReturn =
        stamp == level
            ? applyInCardinalityAtSameLevel(level, v, min, max)
            : applyInCardinalityAtNewLevel(level, v, min, max);

    if (!earlyReturn) {
      v.domainHasChanged(SetDomain.CARDINALITY_EVENT);
    }
  }

  /** Returns true if inValue was called (caller should skip CARDINALITY_EVENT). */
  private boolean applyInCardinalityAtSameLevel(int level, SetVar v, int min, int max) {
    IntDomain cardDom = v.domain.card();

    cardDom.intersectAdapt(min, max);

    if (v.domain.card().isEmpty()) {
      throw Store.failException;
    }

    if (cardDom.max() == glbDomain.getSize()) {
      this.inValue(level, v, glbDomain);
      return true;
    }

    if (cardDom.min() == lubDomain.getSize()) {
      this.inValue(level, v, lubDomain);
      return true;
    }

    return false;
  }

  /** Returns true if inValue was called (caller should skip CARDINALITY_EVENT). */
  private boolean applyInCardinalityAtNewLevel(int level, SetVar v, int min, int max) {
    assert stamp < level;

    IntDomain resultCardinality = cardDomain.intersect(min, max);

    if (resultCardinality.isEmpty()) {
      throw Store.failException;
    }

    if (resultCardinality.max() == glbDomain.getSize()) {
      this.inValue(level, v, glbDomain);
      return true;
    }
    if (resultCardinality.min() == lubDomain.getSize()) {
      this.inValue(level, v, lubDomain);
      return true;
    }

    BoundSetDomain result = new BoundSetDomain(glbDomain, lubDomain);
    result.cardDomain = resultCardinality;

    copyCommonFieldsToResult(result, level);
    v.domain = result;
    return false;
  }
}
