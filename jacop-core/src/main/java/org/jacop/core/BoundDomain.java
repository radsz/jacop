/*
 * BoundDomain.java
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

import java.util.Iterator;
import java.util.Random;
import org.jacop.constraints.Constraint;

/**
 * Defines interval of numbers which is part of FDV definition which consist of one or several
 * intervals.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
class BoundDomain extends IntDomain {

  /** It predefines empty domain so there is no need to constantly create it when needed. */
  public static final BoundDomain emptyDomain = new BoundDomain();

  private static final Random generator =
      Store.seedPresent() ? new Random(Store.getSeed()) : new Random();

  /** The minimal value of the domain. */
  public int minBound;

  /** The maximal value of the domain. */
  public int maxBound;

  /**
   * It is a constructor which will create an empty Bound domain. An empty domain has minimum larger
   * than maximum.
   */
  public BoundDomain() {
    minBound = 1;
    maxBound = 0;
  }

  /**
   * Creates a new instance of BoundDomain. It requires min to be smaller or equal to max.
   *
   * @param min it specifies the left bound of the BoundDomain (inclusive).
   * @param max it specifies the right bound of the BoundDomain (inclusive).
   */
  public BoundDomain(int min, int max) {

    assert min <= max;

    this.minBound = min;
    this.maxBound = max;

    searchConstraints = null;
    searchConstraintsToEvaluate = 0;
    previousDomain = null;
    searchConstraintsCloned = false;
  }

  @Override
  public void unionAdapt(Interval i) {

    if (minBound < maxBound) {
      if (i.min() < minBound) {
        minBound = i.min();
      }

      if (i.max() > maxBound) {
        maxBound = i.max();
      }
    } else {

      minBound = i.min();
      maxBound = i.max();
    }
  }

  @Override
  public void unionAdapt(int min, int max) {

    if (this.minBound < this.maxBound) {
      if (this.minBound < min) {
        this.minBound = min;
      }

      if (this.maxBound > max) {
        this.maxBound = max;
      }
    } else {
      this.minBound = min;
      this.maxBound = max;
    }
  }

  @Override
  public void unionAdapt(int value) {
    unionAdapt(value, value);
  }

  @Override
  public void addDom(IntDomain domain) {

    if (minBound < maxBound) {
      if (domain.min() < minBound) {
        minBound = domain.min();
      }

      if (domain.max() > maxBound) {
        maxBound = domain.max();
      }
    } else {

      minBound = domain.min();
      maxBound = domain.max();
    }
  }

  @Override
  public void clear() {
    minBound = 1;
    maxBound = 0;
  }

  public IntDomain getPreviousDomain() {
    return previousDomain;
  }

  @Override
  public BoundDomain copy() {

    BoundDomain cloned;

    if (!isEmpty()) {
      cloned = new BoundDomain(minBound, maxBound);
    } else {
      cloned = new BoundDomain();
    }

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
   * It clones this domain.
   *
   * @return clone of this domain.
   */
  public BoundDomain cloneLight() {
    if (!isEmpty()) {
      return new BoundDomain(minBound, maxBound);
    } else {
      return new BoundDomain();
    }
  }

  @Override
  public IntDomain complement() {

    if (minBound == MIN_INT) {

      if (maxBound == MAX_INT) {
        return new BoundDomain();
      }

      return new BoundDomain(maxBound + 1, MAX_INT);
    }

    if (maxBound == MAX_INT) {
      return new BoundDomain(MIN_INT, minBound - 1);
    }

    IntervalDomain complement = new IntervalDomain();
    complement.unionAdapt(MIN_INT, minBound - 1);
    complement.unionAdapt(maxBound + 1, MAX_INT);

    return complement;
  }

  @Override
  public boolean contains(IntDomain domain) {

    if (isEmpty()) {
      return domain.isEmpty();
    }

    return minBound <= domain.min() && maxBound >= domain.max();
  }

  @Override
  public boolean contains(int value) {

    return minBound <= value && maxBound >= value;
  }

  @Override
  public boolean contains(int min, int max) {

    return min <= min() && max >= max();
  }

  /**
   * It divides the domain by a given constant.
   *
   * @param div the constant by which the domain should be divided.
   * @return the domain obtained by dividing this domain by a given constant.
   */
  public IntDomain divide(int div) {
    return new BoundDomain(div(minBound, div), maxBound / div);
  }

  private int div(int a, int b) {
    int div;
    int rem;

    div = a / b;
    rem = a % b;
    return rem > 0 ? div + 1 : div;
  }

  @Override
  public int domainId() {
    return BOUND_DOMAIN_ID;
  }

  public boolean eq(IntDomain domain) {

    if (domain.isEmpty() && isEmpty()) {
      return true;
    }

    return minBound == domain.min()
        && maxBound == domain.max()
        && (maxBound - minBound + 1) == domain.getSize();
  }

  @Override
  public Interval getInterval(int position) {
    if (position == 0) {
      return new Interval(minBound, maxBound);
    }

    return null;
  }

  @Override
  public int getSize() {
    return maxBound - minBound + 1;
  }

  @Override
  public void in(int storeLevel, Var v, int min, int max) {

    assert min <= max;

    if (this.maxBound < min || this.minBound > max) {
      throw failException;
    }

    if (min <= this.minBound && max >= this.maxBound) {
      return;
    }

    if (stamp == storeLevel) {

      if (this.minBound < min) {
        this.minBound = min;
      }

      if (this.maxBound > max) {
        this.maxBound = max;
      }

      if (this.minBound == this.maxBound) {
        v.domainHasChanged(GROUND);
      } else {
        v.domainHasChanged(BOUND);
      }

    } else {

      assert stamp < storeLevel;

      BoundDomain result;

      if (this.minBound < min) {
        if (this.maxBound > max) {
          result = new BoundDomain(min, max);
        } else {
          result = new BoundDomain(min, this.maxBound);
        }
      } else {
        // case this.minBound, this.maxBound means no change which is handled above.
        result = new BoundDomain(this.minBound, max);
      }

      result.modelConstraints = modelConstraints;
      result.searchConstraints = searchConstraints;
      result.stamp = storeLevel;
      result.previousDomain = this;
      result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
      result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
      ((IntVar) v).domain = result;

      if (result.singleton()) {
        v.domainHasChanged(GROUND);
      } else {
        v.domainHasChanged(BOUND);
      }
    }
  }

  @Override
  public void in(int storeLevel, Var v, IntDomain domain) {

    in(storeLevel, v, domain.min(), domain.max());
  }

  @Override
  public void inValue(int storeLevel, IntVar v, int value) {

    if (!(value >= minBound && value <= maxBound)) {
      throw failException;
    }

    if (minBound == value && maxBound == value) { // ground and equal value already
      return;
    }

    if (stamp == storeLevel) {

      this.minBound = value;
      this.maxBound = value;
    } else {

      assert stamp < storeLevel;

      BoundDomain result = new BoundDomain(value, value);

      result.modelConstraints = modelConstraints;
      result.searchConstraints = searchConstraints;
      result.stamp = storeLevel;
      result.previousDomain = this;
      result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
      result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
      v.domain = result;
    }

    v.domainHasChanged(GROUND);
  }

  @Override
  public void inComplement(int storeLevel, Var v, int complement) {

    if (this.maxBound == this.minBound && this.maxBound == complement) {
      throw failException;
    }

    // Can not be removed without changing the code below.
    if (complement != this.minBound && complement != this.maxBound) {
      return;
    }

    if (stamp == storeLevel) {

      if (this.minBound == complement) {
        this.minBound++;
      } else {
        // Assumes that check that complement must be equal to one of the bounds is
        // done above.
        this.maxBound--;
      }

      if (this.minBound == this.maxBound) {
        v.domainHasChanged(GROUND);
      } else {
        v.domainHasChanged(BOUND);
      }

    } else {

      assert stamp < storeLevel;

      BoundDomain result;

      if (this.minBound == complement) {
        result = new BoundDomain(this.minBound + 1, this.maxBound);
      } else {
        result = new BoundDomain(this.minBound, this.maxBound - 1);
      }

      result.modelConstraints = modelConstraints;
      result.searchConstraints = searchConstraints;
      result.stamp = storeLevel;
      result.previousDomain = this;
      result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
      result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
      ((IntVar) v).domain = result;

      if (result.singleton()) {
        v.domainHasChanged(GROUND);
      } else {
        v.domainHasChanged(BOUND);
      }
    }
  }

  @Override
  public void inComplement(int storeLevel, Var v, int min, int max) {

    assert min <= max;

    // all elements are removed so fail.
    if (this.minBound >= min && this.maxBound <= max) {
      throw failException;
    }

    // Can not be removed without changing the code below.
    // none of the elements are removed can ignore the call.
    if (max < this.minBound || this.maxBound < min) {
      return;
    }

    // For bound domain, creating holes in the domain not possible.
    if (min > this.minBound && max < this.maxBound) {
      return;
    }

    if (stamp == storeLevel) {

      if (max < this.maxBound) {
        this.minBound = max + 1;
      } else {
        this.maxBound = min - 1;
      }

      if (this.minBound == this.maxBound) {
        v.domainHasChanged(GROUND);
      } else {
        v.domainHasChanged(BOUND);
      }

    } else {

      assert stamp < storeLevel;

      BoundDomain result;

      if (max < this.maxBound) {
        result = new BoundDomain(max + 1, this.maxBound);
      } else {
        result = new BoundDomain(this.minBound, min - 1);
      }

      result.modelConstraints = modelConstraints;
      result.searchConstraints = searchConstraints;
      result.stamp = storeLevel;
      result.previousDomain = this;
      result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
      result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
      ((IntVar) v).domain = result;

      if (result.singleton()) {
        v.domainHasChanged(GROUND);
      } else {
        v.domainHasChanged(BOUND);
      }
    }
  }

  @Override
  public void inMax(int storeLevel, Var v, int max) {

    if (this.minBound > max) {
      throw failException;
    }

    // If removed the code below has to change.
    if (max >= this.maxBound) {
      return;
    }

    if (stamp == storeLevel) {

      this.maxBound = max;

      if (this.minBound == this.maxBound) {
        v.domainHasChanged(GROUND);
      } else {
        v.domainHasChanged(BOUND);
      }

    } else {

      assert stamp < storeLevel;

      BoundDomain result = new BoundDomain(minBound, max);

      result.modelConstraints = modelConstraints;
      result.searchConstraints = searchConstraints;
      result.stamp = storeLevel;
      result.previousDomain = this;
      result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
      result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
      ((IntVar) v).domain = result;

      if (result.singleton()) {
        v.domainHasChanged(GROUND);
      } else {
        v.domainHasChanged(BOUND);
      }
    }
  }

  @Override
  public void inMin(int storeLevel, Var v, int min) {

    if (this.maxBound < min) {
      throw failException;
    }

    if (min <= this.minBound) {
      return;
    }

    if (stamp == storeLevel) {

      this.minBound = min;

      if (this.minBound == this.maxBound) {
        v.domainHasChanged(GROUND);
      } else {
        v.domainHasChanged(BOUND);
      }

    } else {

      assert stamp < storeLevel;

      BoundDomain result = new BoundDomain(min, this.maxBound);

      result.modelConstraints = modelConstraints;
      result.searchConstraints = searchConstraints;
      result.stamp = storeLevel;
      result.previousDomain = this;
      result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
      result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
      ((IntVar) v).domain = result;

      if (result.singleton()) {
        v.domainHasChanged(GROUND);
      } else {
        v.domainHasChanged(BOUND);
      }
    }
  }

  @Override
  public void inShift(int storeLevel, Var v, IntDomain domain, int shift) {
    in(storeLevel, v, domain.min() + shift, domain.max() + shift);
  }

  @Override
  public IntDomain intersect(IntDomain dom) {

    int inputMin = dom.min();
    int inputMax = dom.max();

    if (inputMin > this.maxBound || inputMax < this.minBound) {
      return emptyDomain;
    }

    if (inputMin >= this.minBound) { // inputMin..
      if (inputMax <= this.maxBound) { // inputMin..inputMax
        return new BoundDomain(inputMin, inputMax);
      } else { // inputMin..max
        return new BoundDomain(inputMin, this.maxBound);
      }
    } else // min..
    if (inputMax <= this.maxBound) { // min..inputMax
      return new BoundDomain(this.minBound, inputMax);
    } else { // min..max
      return new BoundDomain(this.minBound, this.maxBound);
    }
  }

  @Override
  public IntDomain intersect(int min, int max) {

    if (min > this.maxBound || max < this.minBound) {
      return emptyDomain;
    }

    if (min >= this.minBound) { // inputMin..
      if (max <= this.maxBound) { // inputMin..inputMax
        return new BoundDomain(min, max);
      } else { // inputMin..max
        return new BoundDomain(min, this.maxBound);
      }
    } else // min..
    if (max <= this.maxBound) { // min..inputMax
      return new BoundDomain(this.minBound, max);
    } else { // min..max
      return new BoundDomain(this.minBound, this.maxBound);
    }
  }

  @Override
  public IntDomain subtract(int value) {

    if (this.maxBound == this.minBound && this.maxBound == value) {
      return emptyDomain;
    }

    // Can not be removed without changing the code below.
    if (value != this.minBound && value != this.maxBound) {
      return new BoundDomain(this.minBound, this.maxBound);
    }

    if (this.minBound == value) {
      return new BoundDomain(this.minBound + 1, this.maxBound);
    } else {
      return new BoundDomain(this.minBound, this.maxBound - 1);
    }
  }

  @Override
  public IntDomain subtract(IntDomain domain) {

    int inputMin = domain.min();
    int inputMax = domain.max();

    if (inputMin <= this.minBound && inputMax >= this.maxBound) {
      return emptyDomain;
    }

    if (this.minBound < inputMin && inputMax < this.maxBound) {
      return new BoundDomain(this.minBound, this.maxBound);
    }

    if (inputMin > this.minBound) {
      return new BoundDomain(this.minBound, inputMin - 1);
    }

    return new BoundDomain(inputMax + 1, this.maxBound);
  }

  @Override
  public BoundDomain subtract(int min, int max) {

    if (min <= this.minBound && max >= this.maxBound) {
      return emptyDomain;
    }

    if (this.minBound < min && max < this.maxBound) {
      return new BoundDomain(this.minBound, this.maxBound);
    }

    if (min > this.minBound) {
      return new BoundDomain(this.minBound, min - 1);
    }

    return new BoundDomain(max + 1, this.maxBound);
  }

  @Override
  public IntervalEnumeration intervalEnumeration() {
    return new BoundDomainIntervalEnumeration(this.minBound, this.maxBound);
  }

  @Override
  public boolean isEmpty() {
    return minBound > maxBound;
  }

  @Override
  public boolean isIntersecting(IntDomain domain) {

    return domain.min() <= this.maxBound && domain.max() >= this.minBound;
  }

  @Override
  public boolean isIntersecting(int min, int max) {

    return min <= this.maxBound && max >= this.minBound;
  }

  @Override
  public boolean isNumeric() {
    return true;
  }

  @Override
  public boolean isSparseRepresentation() {
    return false;
  }

  @Override
  public int leftElement(int intervalNo) {
    assert intervalNo == 0;
    return this.minBound;
  }

  @Override
  public int max() {
    return this.maxBound;
  }

  @Override
  public int min() {
    return this.minBound;
  }

  /**
   * It multiplies the domain by a given constant.
   *
   * @param mul a factor by which the domain is being multiplied.
   * @return Domain created by multiplication of this domain.
   */
  public IntDomain multiply(int mul) {
    return new BoundDomain(this.minBound * mul, this.maxBound * mul);
  }

  @Override
  public int nextValue(int value) {
    if (value < this.minBound) {
      return minBound;
    }
    if (value < this.maxBound) {
      return value + 1;
    }

    return value;
  }

  @Override
  public int noIntervals() {

    if (isEmpty()) {
      return 0;
    } else {
      return 1;
    }
  }

  @Override
  public IntDomain recentDomainPruning(int storeLevel) {
    if (previousDomain == null) {
      return emptyDomain;
    }

    if (stamp < storeLevel) {
      return emptyDomain;
    }

    return previousDomain.subtract(this);
  }

  @Override
  public void removeLevel(int level, Var v) {

    assert this.stamp <= level;

    if (this.stamp == level) {

      ((IntVar) v).domain = this.previousDomain;
    }

    assert v.level() < level;
  }

  @Override
  public int rightElement(int intervalNo) {
    assert intervalNo == 0;
    return maxBound;
  }

  @Override
  public void setDomain(IntDomain domain) {

    if (domain.domainId() == BOUND_DOMAIN_ID) {

      BoundDomain boundDomain = (BoundDomain) domain;

      this.minBound = boundDomain.min();
      this.maxBound = boundDomain.max();

      return;
    }

    setDomain(domain.min(), domain.max());
  }

  @Override
  public void setDomain(int min, int max) {

    assert min <= max;

    this.minBound = min;
    this.maxBound = max;
  }

  @Override
  public boolean singleton() {
    return minBound == maxBound;
  }

  @Override
  public boolean singleton(int c) {
    return minBound == c && maxBound == c;
  }

  @Override
  public int sizeConstraintsOriginal() {

    IntDomain domain = this;

    while (domain.domainId() == BOUND_DOMAIN_ID) {

      BoundDomain dom = (BoundDomain) domain;

      if (dom.previousDomain != null) {
        domain = dom.previousDomain;
      } else {
        break;
      }
    }

    if (domain.domainId() == BOUND_DOMAIN_ID) {
      return domain.modelConstraintsToEvaluate[0]
          + domain.modelConstraintsToEvaluate[1]
          + domain.modelConstraintsToEvaluate[2];
    } else {
      return domain.sizeConstraintsOriginal();
    }
  }

  @Override
  public String toString() {

    if (minBound < maxBound) {
      return "{" + minBound + ".." + maxBound + "}";
    } else if (minBound == maxBound) {
      return String.valueOf(minBound);
    } else {
      return "{}";
    }
  }

  @Override
  public String toStringConstraints() {

    StringBuilder s = new StringBuilder();

    for (Iterator<Constraint> e = searchConstraints.iterator(); e.hasNext(); ) {
      s.append(e.next().id());
      if (e.hasNext()) {
        s.append(", ");
      }
    }

    return s.toString();
  }

  @Override
  public String toStringFull() {

    StringBuilder result = new StringBuilder();

    IntDomain domain = this;

    do {
      if (!domain.singleton()) {
        result.append(this).append("(").append(domain.stamp()).append(") ");
      } else {
        result.append(minBound).append("(").append(domain.stamp()).append(") ");
      }

      result.append("constraints: ");

      for (Constraint searchConstraint : domain.searchConstraints) {
        result.append(searchConstraint);
      }

      if (domain.domainId() == INTERVAL_DOMAIN_ID) {

        IntervalDomain dom = (IntervalDomain) domain;
        domain = dom.previousDomain;

      } else if (domain.domainId() == BOUND_DOMAIN_ID) {

        BoundDomain dom = (BoundDomain) domain;
        domain = dom.previousDomain;
      }

    } while (domain != null);

    return result.toString();
  }

  @Override
  public IntDomain union(IntDomain domain) {

    int min = domain.min();
    int max = domain.max();

    if (min < this.minBound) { // min..
      if (this.maxBound < max) { // min..max
        return new BoundDomain(min, max);
      } else { // min..this.maxBound
        return new BoundDomain(min, this.maxBound);
      }
    } else // this.minBound..
    if (this.maxBound < max) { // this.minBound..max
      return new BoundDomain(this.minBound, max);
    } else { // this.minBound..this.maxBound
      return new BoundDomain(this.minBound, this.maxBound);
    }
  }

  @Override
  public IntDomain union(int min, int max) {

    if (min < this.minBound) { // min..
      if (this.maxBound < max) { // min..max
        return new BoundDomain(min, max);
      } else { // min..this.maxBound
        return new BoundDomain(min, this.maxBound);
      }
    } else // this.minBound..
    if (this.maxBound < max) { // this.minBound..max
      return new BoundDomain(this.minBound, max);
    } else { // this.minBound..this.maxBound
      return new BoundDomain(this.minBound, this.maxBound);
    }
  }

  @Override
  public IntDomain union(int value) {

    if (value < this.minBound) {
      return new BoundDomain(value, this.maxBound);
    }

    if (value > this.maxBound) {
      return new BoundDomain(this.minBound, value);
    }

    return new BoundDomain(this.minBound, this.maxBound);
  }

  @Override
  public ValueEnumeration valueEnumeration() {
    return new BoundDomainValueEnumeration(this);
  }

  @Override
  public int previousValue(int value) {

    if (value > this.minBound) {
      return value - 1;
    }

    return value;
  }

  /**
   * Checks invariants.
   *
   * @return It returns the information about the first invariant which does not hold or null
   *     otherwise.
   */
  public String checkInvariants() {

    if (minBound > maxBound) {
      return "Min value is larger than max value ";
    }

    // Fine, all invariants hold.
    return null;
  }

  @Override
  public void subtractAdapt(int complement) {

    // Can not be removed without changing the code below.
    if (complement != this.minBound && complement != this.maxBound) {
      return;
    }

    if (this.minBound == complement) {
      this.minBound++;
    } else {
      // Assumes that check that complement must be equal to one of the bounds is
      // done above.
      this.maxBound--;
    }
  }

  @Override
  public void subtractAdapt(int min, int max) {

    if (min <= this.minBound) {

      if (max >= this.maxBound) {

        this.clear();

      } else {
        // min <= this.minBound
        // max < this.maxBound
        this.minBound = max + 1;
      }

    } else {
      // min > this.minBound

      if (max >= this.maxBound) {

        this.maxBound = min - 1;
      }
    }
  }

  @Override
  public int intersectAdapt(IntDomain intersect) {

    return intersectAdapt(intersect.min(), intersect.max());
  }

  @Override
  public int intersectAdapt(int minIntersect, int maxIntersect) {

    if (minIntersect <= minBound && maxBound <= maxIntersect) {
      return NONE;
    }

    if (minIntersect > maxBound) {
      // Intersection is empty.
      minBound = 0;
      maxBound = -1;
      return GROUND;
    }

    if (maxBound > maxIntersect) {
      maxBound = maxIntersect;
    }

    if (minBound < minIntersect) {
      minBound = minIntersect;
    }

    return BOUND;
  }

  @Override
  public int getElementAt(int index) {

    if (this.maxBound - this.minBound > index) {
      throw new RuntimeException(
          "The domain does not have as many elements as indicated by index " + index);
    }

    return this.minBound + index;
  }

  // TODO: test it.
  @Override
  public int sizeOfIntersection(IntDomain domain) {

    IntervalEnumeration enumer = domain.intervalEnumeration();

    int result = 0;

    while (enumer.hasMoreElements()) {

      Interval next = enumer.nextElement();

      if (next.max() < this.minBound || this.maxBound < next.min()) {
        continue;
      }

      int min = Math.max(next.min(), this.minBound);
      int max = Math.min(next.max(), this.maxBound);

      result += max - min + 1;
    }

    assert result <= this.getSize() : "Invariant violated. Check the code.";
    return result;
  }

  @Override
  public int getRandomValue() {

    if (generator.nextInt(2) == 0) {
      return min();
    } else {
      return max();
    }
  }
}
