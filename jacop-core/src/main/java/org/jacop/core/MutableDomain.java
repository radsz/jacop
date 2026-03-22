/*
 * MutableDomain.java
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

import lombok.extern.slf4j.Slf4j;

/**
 * Represents a mutable domain that can be modified during search.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class MutableDomain implements MutableVar {

  /** It specifies if debugging info should be printed out. */
  public static final boolean DEBUG = false;

  final int index;

  final Store store;

  MutableDomainValue value;

  /**
   * Constructs an empty mutable domain in the specified store.
   *
   * @param store store in which the mutable domain is created.
   */
  public MutableDomain(Store store) {
    this.value = new MutableDomainValue(IntervalDomain.emptyDomain);
    this.index = store.putMutableVar(this);
    this.store = store;
  }

  /**
   * Constructs a mutable domain with the specified initial domain.
   *
   * @param store store in which the mutable domain is created.
   * @param domain specifies the domain used to create mutable domain.
   */
  public MutableDomain(Store store, IntDomain domain) {
    MutableDomainValue val = new MutableDomainValue();
    val.domain = domain;
    value = val;
    index = store.putMutableVar(this);
    this.store = store;
  }

  int index() {
    return index;
  }

  /**
   * Returns the previous value of this mutable domain variable.
   *
   * @return the previous mutable variable value.
   */
  public MutableVarValue previous() {
    return value.previousMutableDomainVariableValue;
  }

  /**
   * Removes the current level by restoring the previous value if the stamp matches the given level.
   *
   * @param removeLevel the level to be removed.
   */
  public void removeLevel(int removeLevel) {
    if (value.stamp == removeLevel) {
      value = value.previousMutableDomainVariableValue;
    }
  }

  public void setCurrent(MutableVarValue o) {
    value = (MutableDomainValue) o;
  }

  int stamp() {
    return value.stamp;
  }

  @Override
  public String toString() {

    return "MutableVar[" + (index + 1) + "] = " + value;
  }

  /**
   * Updates the mutable domain with a new value, saving the previous state for backtracking.
   *
   * @param val the new value to set for this mutable domain.
   */
  public void update(MutableVarValue val) {

    if (value.stamp == store.level) {

      if (DEBUG) {
        log.debug("1. Level: {}, IN {}, New {}", store.level, value, val);
      }

      value.setValue(((MutableDomainValue) val).domain);

      if (DEBUG) {
        log.debug(", OUT {}", value);
      }

    } else if (value.stamp < store.level) {
      if (DEBUG) {
        log.debug("2. Level: {}, IN {}, New {}", store.level, this, val);
      }

      val.setStamp(store.level);
      val.setPrevious(value);

      value = (MutableDomainValue) val;

      if (DEBUG) {
        log.debug("=> OUT {} OLD {}", this, value().previous());
      }
    }
  }

  /**
   * Returns the current value of this mutable domain.
   *
   * @return the current mutable variable value.
   */
  public MutableVarValue value() {
    return value;
  }
}
