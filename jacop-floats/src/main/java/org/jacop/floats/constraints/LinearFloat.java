/*
 * LinearFloat.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.floats.constraints;

import java.util.List;
import java.util.Set;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.constraints.linear.Linear;
import org.jacop.floats.core.FloatVar;

/**
 * LinearFloat constraint implements the weighted summation over several Variable's . It provides
 * the weighted sum from all Variable's on the list.
 *
 * <p>This version works as argument to Reified and Xor constraints. For other constraints And, Or,
 * Not, Eq, IfThen, IfThenElse it does not work currently.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */
public class LinearFloat extends Linear implements UsesQueueVariable, FloatDerivableConstraint {

  // =================== constructors ========================

  /**
   * Constructs a LinearFloat constraint with a constant sum.
   *
   * @param list variables which are being multiplied by weights.
   * @param weights weight for each variable.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "{@literal !=}"
   * @param sum the sum of weighted variables.
   */
  public LinearFloat(FloatVar[] list, double[] weights, String rel, double sum) {

    super(list[0].getStore(), list, weights, rel, sum);
  }

  /**
   * Constructs a LinearFloat constraint with a variable sum.
   *
   * @param list variables which are being multiplied by weights.
   * @param weights weight for each variable.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "{@literal !=}"
   * @param sum variable containing the sum of weighted variables.
   */
  public LinearFloat(FloatVar[] list, double[] weights, String rel, FloatVar sum) {

    super(sum.getStore(), list, weights, rel, sum);
  }

  /**
   * It constructs the constraint LinearFloat.
   *
   * @param variables variables which are being multiplied by weights.
   * @param weights weight for each variable.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}"
   * @param sum variable containing the sum of weighted variables.
   */
  public LinearFloat(
      List<? extends FloatVar> variables, List<Double> weights, String rel, double sum) {

    super(variables.getFirst().getStore(), variables, weights, rel, sum);
  }

  @Override
  public void queueVariable(int level, Var var) {
    super.queueVariable(level, var);
  }

  /**
   * Computes the derivative of this constraint with respect to a variable.
   *
   * @param store the constraint store
   * @param f the function variable for which to compute the derivative
   * @param vars the set of variables involved in the derivative computation
   * @param x the variable with respect to which the derivative is computed
   * @return the derivative variable, or null if f is not part of this constraint
   */
  public FloatVar derivative(Store store, FloatVar f, Set<FloatVar> vars, FloatVar x) {

    // System.out.println ("FloatLinear of " + f + " on " + x);

    int fIndex = 0;
    while (list[fIndex] != f) {
      fIndex++;
    }

    FloatVar[] df = new FloatVar[list.length];
    double[] ww = new double[list.length];
    FloatVar v = null;

    for (int i = 0; i < list.length; i++) {
      if (i != fIndex) {
        df[i] = Derivative.getDerivative(store, list[i], vars, x);

        // System.out.println ("derivate of " + list[i] + " = " + df[i]);

        ww[i] = weights[i] / (-weights[fIndex]);
      } else {
        v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
        df[i] = v;
        ww[i] = -1.0;
      }
    }

    Constraint c = new LinearFloat(df, ww, "==", 0.0);
    Derivative.poseDerivativeConstraint(c);

    // System.out.println ("Derivative of " + f + " over " + x + " is " + c);

    return v;
  }
}
