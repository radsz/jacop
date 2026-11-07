/*
 * ExpectedSum.java
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

package org.jacop.prob.constraints;

import java.util.ArrayList;
import java.util.List;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.prob.dist.Dist;

/**
 * The expectation of a sum with random coefficients: z = D * E[sum(W[i] * x[i])] = sum(m[i] *
 * x[i]), where m[i] = D * E[W[i]] is the mean numerator of the coefficient W[i] over the common
 * denominator D. By linearity of expectation it is a linear constraint over the mean numerators, so
 * it is decomposed into one {@link LinearInt}; z holds the expectation scaled by D, so it is exact
 * and an integer.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ExpectedSum extends DecomposedConstraint<Constraint> {

  final IntVar[] x;
  final int[] meanNumerators;
  final IntVar z;

  /**
   * It constructs z = sum(meanNumerators[i] * x[i]).
   *
   * @param x the variables
   * @param meanNumerators the mean of each coefficient times the common denominator
   * @param z the expectation times the common denominator
   */
  public ExpectedSum(IntVar[] x, int[] meanNumerators, IntVar z) {
    checkInputForNullness(new String[] {"x", "z"}, x, new Object[] {z});
    checkInputForNullness("meanNumerators", meanNumerators);
    if (x.length != meanNumerators.length) {
      throw new IllegalArgumentException(
          "ExpectedSum has x and meanNumerators of different length");
    }
    this.x = x.clone();
    this.meanNumerators = meanNumerators.clone();
    this.z = z;
    queueIndex = 1;
  }

  /**
   * It constructs z = den * E[sum(weights[i] * x[i])] for random coefficients over a common
   * denominator den.
   *
   * @param x the variables
   * @param weights the distribution of each coefficient, all over the same denominator
   * @param z the expectation times the denominator
   * @return the constraint
   * @throws IllegalArgumentException when the denominators differ or a mean numerator is not an int
   */
  public static ExpectedSum of(IntVar[] x, Dist[] weights, IntVar z) {
    if (x.length != weights.length) {
      throw new IllegalArgumentException("ExpectedSum has x and weights of different length");
    }
    int[] m = new int[weights.length];
    for (int i = 0; i < weights.length; i++) {
      if (weights[i].den() != weights[0].den()) {
        throw new IllegalArgumentException(
            "ExpectedSum needs one denominator; use Dist.withDenominator to bring them together");
      }
      long mean = weights[i].meanNumerator();
      if (mean != (int) mean) {
        throw new IllegalArgumentException("ExpectedSum mean numerator " + mean + " is not an int");
      }
      m[i] = (int) mean;
    }
    return new ExpectedSum(x, m, z);
  }

  @Override
  public void imposeDecomposition(Store store) {
    for (Constraint c : decompose(store)) {
      store.impose(c, queueIndex);
    }
  }

  @Override
  public List<Constraint> decompose(Store store) {
    List<Constraint> result = new ArrayList<>();
    result.add(new LinearInt(x, meanNumerators, "==", z));
    return result;
  }

  @Override
  public List<Var> auxiliaryVariables() {
    return new ArrayList<>();
  }
}
