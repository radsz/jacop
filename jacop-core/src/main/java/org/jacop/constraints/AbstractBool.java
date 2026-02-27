/*
 * AbstractBool.java
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

import java.util.Collections;
import java.util.List;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Abstract base for boolean logic constraints (OrBool, AndBool). Provides shared decomposition
 * infrastructure and filtering logic.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractBool extends DecomposedConstraint<PrimitiveConstraint> {

  final PrimitiveConstraint c;

  /**
   * It constructs boolean constraint on variables.
   *
   * @param a parameters
   * @param result result variable.
   */
  protected AbstractBool(IntVar[] a, IntVar result) {

    int[] shortCircuit = {-1};
    IntVar[] r = filter(a, shortCircuit);

    if (shortCircuit[0] == getShortCircuitValue()) {
      c = new XeqC(result, getShortCircuitResult());
    } else if (r.length == 0) {
      c = new XeqC(result, getEmptyArrayResult());
    } else if (r.length == 1) {
      c = new XeqY(r[0], result);
    } else if (r.length == 2) {
      c = createSimpleConstraint(r[0], r[1], result);
    } else {
      c = createVectorConstraint(r, result);
    }
  }

  /**
   * Returns the short-circuit value that triggers early termination.
   *
   * @return 1 for OR, 0 for AND
   */
  protected abstract int getShortCircuitValue();

  /**
   * Returns the result value when short-circuit is triggered.
   *
   * @return 1 for OR, 0 for AND
   */
  protected abstract int getShortCircuitResult();

  /**
   * Returns the result value when the filtered array is empty.
   *
   * @return 0 for OR, 1 for AND
   */
  protected abstract int getEmptyArrayResult();

  /**
   * Creates a simple constraint for two variables.
   *
   * @param a first variable
   * @param b second variable
   * @param result result variable
   * @return the constraint instance
   */
  protected abstract PrimitiveConstraint createSimpleConstraint(IntVar a, IntVar b, IntVar result);

  /**
   * Creates a vector constraint for multiple variables.
   *
   * @param vars array of variables
   * @param result result variable
   * @return the constraint instance
   */
  protected abstract PrimitiveConstraint createVectorConstraint(IntVar[] vars, IntVar result);

  /**
   * Filters variables based on boolean logic rules.
   *
   * @param xs array of variables to filter
   * @param shortCircuit output parameter for short-circuit detection
   * @return filtered array of variables
   */
  protected abstract IntVar[] filter(IntVar[] xs, int[] shortCircuit);

  /**
   * It constructs boolean constraint on variables.
   *
   * @param a parameters
   * @param result result variable.
   */
  protected AbstractBool(List<? extends IntVar> a, IntVar result) {
    this(a.toArray(new IntVar[0]), result);
  }

  /**
   * It constructs boolean constraint on variables.
   *
   * @param a a parameter
   * @param b b parameter
   * @param result result variable.
   */
  protected AbstractBool(IntVar a, IntVar b, IntVar result) {
    this(new IntVar[] {a, b}, result);
  }

  @Override
  public void imposeDecomposition(Store store) {
    store.impose(c);
  }

  @Override
  public List<PrimitiveConstraint> decompose(Store store) {
    return Collections.singletonList(c);
  }

  /**
   * Returns a string representation of the constraint.
   *
   * @return string representation of the constraint.
   */
  @Override
  public String toString() {
    return c.toString();
  }
}
