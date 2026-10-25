/*
 * StoreState.java
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
 * The state of a store in a chain of derived stores (presolve, sub-problems). A store that never
 * derives a child stays {@link #ACTIVE}.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public enum StoreState {

  /** The store is worked on: modelling, propagating or searching, at any level. */
  ACTIVE,

  /**
   * A child store was derived at the current level and is alive. The store's domains and trail stay
   * as they are until the child returns: imposing, propagating, changing level and searching are
   * refused.
   */
  SUSPENDED,

  /**
   * The store's constraints were released after a complete derivation, except those needed to
   * recover the values of variables the child does not have. Only postsolve writes values and
   * propagates; imposing and searching are refused.
   */
  SINK,

  /** The derivation ended; the variables keep their last values and everything else is refused. */
  CLOSED
}
