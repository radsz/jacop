/*
 * ValueExclusion.java
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
package org.jacop.lcg;

import org.jacop.core.IntVar;

/**
 * A constraint {@code b -> x != c} (or {@code b <=> x != c}) over a 0/1 variable {@code b}, the
 * half-reified comparison that MiniZinc makes of a disequality in a disjunction. The root
 * refutation of the linear relaxation reads it to state a clause over such Booleans over the values
 * of {@code x} instead.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public interface ValueExclusion {

  /**
   * Returns the 0/1 variable whose value 1 excludes the value from the variable.
   *
   * @return b
   */
  IntVar control();

  /**
   * Returns the variable.
   *
   * @return x
   */
  IntVar variable();

  /**
   * Returns the value excluded.
   *
   * @return c
   */
  int value();
}
