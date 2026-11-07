/*
 * OrBool.java
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

import java.util.ArrayList;
import java.util.List;
import org.jacop.core.IntVar;

/**
 * OrBool constraint implements logic or operation on its arguments and returns result.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class OrBool extends AbstractBool {

  /**
   * It constructs or constraint on variables.
   *
   * @param a parameters
   * @param result result variable.
   */
  public OrBool(IntVar[] a, IntVar result) {
    super(a, result);
  }

  /**
   * It constructs or constraint on variables.
   *
   * @param a parameters
   * @param result result variable.
   */
  public OrBool(List<? extends IntVar> a, IntVar result) {
    super(a, result);
  }

  /**
   * It constructs or constraint on variables.
   *
   * @param a a parameter
   * @param b b parameter
   * @param result result variable.
   */
  public OrBool(IntVar a, IntVar b, IntVar result) {
    super(a, b, result);
  }

  @Override
  protected int getShortCircuitValue() {
    return 1;
  }

  @Override
  protected int getShortCircuitResult() {
    return 1;
  }

  @Override
  protected int getEmptyArrayResult() {
    return 0;
  }

  @Override
  protected PrimitiveConstraint createSimpleConstraint(IntVar a, IntVar b, IntVar result) {
    return new OrBoolSimple(a, b, result);
  }

  @Override
  protected PrimitiveConstraint createVectorConstraint(IntVar[] vars, IntVar result) {
    return new OrBoolVector(vars, result);
  }

  @Override
  protected IntVar[] filter(IntVar[] xs, int[] shortCircuit) {
    List<IntVar> result = new ArrayList<>();
    for (IntVar x : xs) {
      if (x.min() == 1) {
        shortCircuit[0] = 1;
        return new IntVar[0];
      } else if (x.max() != 0) {
        result.add(x);
      }
    }

    return result.toArray(IntVar[]::new);
  }
}
