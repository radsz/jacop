/*
 * AlldifferentExcept.java
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

package org.jacop.constraints;

import java.util.List;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;

/**
 * AlldifferentExcept constraint assures that all FDVs except those given as a set of values
 * (parameter s) have differnet values.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class AlldifferentExcept extends Alldifferent
    implements UsesQueueVariable, SatisfiedPresent {

  IntDomain s;

  /** Protected constructor for subclassing purposes. */
  protected AlldifferentExcept() {}

  /**
   * It constructs the alldifferent constraint for the supplied variable.
   *
   * @param list variables which are constrained to take different values.
   */
  public AlldifferentExcept(IntVar[] list, IntDomain s) {

    super(list);

    this.s = s;
  }

  /**
   * It constructs the alldifferent constraint for the supplied variable.
   *
   * @param variables variables which are constrained to take different values.
   */
  public AlldifferentExcept(List<? extends IntVar> variables, IntDomain s) {
    this(variables.toArray(new IntVar[0]), s);
  }

  @Override
  protected boolean isExceptionValue(int value) {
    return s.contains(value);
  }

  @Override
  protected boolean hasExceptionValues(IntVar v) {
    return s.isIntersecting(v.dom());
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : AlldifferentExcept([");
    appendArrayToString(result, list);
    result.append("], ").append(s).append(")");

    return result.toString();
  }
}
