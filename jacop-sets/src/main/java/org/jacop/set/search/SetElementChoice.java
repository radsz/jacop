/*
 * SetElementChoice.java
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

package org.jacop.set.search;

import org.jacop.constraints.Not;
import org.jacop.lcg.Mirrored;
import org.jacop.lcg.MirroredChoice;
import org.jacop.set.constraints.EinA;
import org.jacop.set.core.SetVar;

/**
 * The choice that an element is not in a set variable, the left branch of a set search that leaves
 * elements out first (outdomain_min, outdomain_max); the right branch puts the element in.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class SetElementChoice extends Not implements MirroredChoice {

  private final SetVar set;

  private final int element;

  /**
   * Creates the choice that element is not in set.
   *
   * @param element the element
   * @param set the set variable
   */
  public SetElementChoice(int element, SetVar set) {
    super(new EinA(element, set));
    this.set = set;
    this.element = element;
  }

  @Override
  public Mirrored mirrored() {
    return set;
  }

  @Override
  public int value() {
    return element;
  }

  @Override
  public boolean holds() {
    return false;
  }
}
