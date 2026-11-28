/*
 * DomainChangeRecorder.java
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

/**
 * Receives every change of an integer variable's domain, after the change. A store calls it only
 * when one is set in {@link Store#domainChangeRecorder}; lazy clause generation uses it to record
 * the changes as atoms with their reasons.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface DomainChangeRecorder {

  /**
   * The domain of a variable has changed.
   *
   * @param x the variable, whose domain is already the new one
   * @param event the pruning event of the change
   */
  void domainChanged(IntVar x, int event);

  /**
   * A value of a variable is about to be removed on its own; a call of {@link #domainChanged}
   * follows unless the removal fails. Domains with many holes report it so that the removed value
   * need not be searched for; the default ignores it.
   *
   * @param x the variable
   * @param value the value
   */
  default void removingValue(IntVar x, int value) {}

  /**
   * The change of a variable's domain reported by the next call of {@link #domainChanged} moves
   * only its bounds: no value between the new bounds is removed. The domains call it right before
   * that report, so that the removed values need not be searched for; the default ignores it.
   *
   * @param x the variable
   */
  default void changingBounds(IntVar x) {}

  /**
   * The values of an interval of a variable are about to be removed; a call of {@link
   * #domainChanged} follows unless no value of the interval is in the domain or the removal fails.
   * The default ignores it.
   *
   * @param x the variable
   * @param min the first value of the interval
   * @param max the last value of the interval
   */
  default void removingInterval(IntVar x, int min, int max) {}
}
