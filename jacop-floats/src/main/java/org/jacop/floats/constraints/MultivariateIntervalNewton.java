/*
 * MultivariateIntervalNewton.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.floats.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import org.jacop.constraints.Constraint;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatInterval;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatVar;

/**
 * MultivariateIntervalNewton implements multivariate interval Newton method for solving a system of
 * non linear equations.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class MultivariateIntervalNewton {

  static final boolean DEBUG = false;

  final FloatVar[] f;
  final FloatVar[] x;
  final FloatVar[][] fprime;
  final Stack<Constraint> eval;
  double[] xInit;
  FloatInterval[][] A;
  double[] b;
  Map<FloatVar, Double> map;

  /**
   * Constructs a multivariate interval Newton solver for a system of non-linear equations.
   *
   * @param store the constraint store
   * @param f the array of function variables
   * @param x the array of variable to solve for
   */
  public MultivariateIntervalNewton(Store store, FloatVar[] f, FloatVar[] x) {

    this.f = new FloatVar[f.length];
    System.arraycopy(f, 0, this.f, 0, f.length);
    this.x = new FloatVar[x.length];
    System.arraycopy(x, 0, this.x, 0, x.length);

    eval = new Stack<>();

    Set<FloatVar> vars = new HashSet<>(Arrays.asList(x));

    fprime = new FloatVar[f.length][x.length];
    Derivative.init(store);
    for (int i = 0; i < f.length; i++) {
      for (int j = 0; j < x.length; j++) {

        if (DEBUG) {
          IO.println("Derivative of " + f[i] + " on " + x[j] + " primitive variables = " + vars);
        }

        fprime[i][j] = Derivative.getDerivative(store, f[i], vars, x[j]);

        if (DEBUG) {
          IO.println("\t derivate = " + fprime[i][j]);
        }
      }
    }
  }

  /**
   * Solves the system of non-linear equations using the interval Newton method.
   *
   * @return the solution as an array of FloatIntervals, or null if the system cannot be solved
   */
  public FloatInterval[] solve() {

    A = new FloatInterval[fprime.length][];
    for (int i = 0; i < fprime.length; i++) {
      A[i] = new FloatInterval[fprime[i].length];
      for (int j = 0; j < fprime[i].length; j++) {
        A[i][j] = new FloatInterval(fprime[i][j].min(), fprime[i][j].max());
      }
    }

    xInit = new double[x.length];
    for (int i = 0; i < x.length; i++) {
      xInit[i] = (x[i].max() + x[i].min()) / 2.0;
    }

    b = values();

    if (DEBUG) {
      IO.println("Middle values for x");
      for (double value : xInit) {
        IO.print(value + " ");
      }
      IO.println();

      IO.println("Middle values for f");
      for (double v : b) {
        IO.print(v + ", ");
      }
      IO.println();
    }

    IntervalGaussSeidel igs = new IntervalGaussSeidel(A, b);

    if (DEBUG) {
      IO.println(igs);
    }

    FloatInterval[] v = igs.solve();

    if (v == null) {
      return null;
    }

    FloatInterval[] result = new FloatInterval[v.length];
    for (int i = 0; i < v.length; i++) {
      FloatIntervalDomain r = FloatDomain.addBounds(v[i].min(), v[i].max(), xInit[i], xInit[i]);
      result[i] = new FloatInterval(r.min(), r.max());
    }

    return result;
  }

  // computes -f(xInit), RHS of equation for Gauss-Seidler method a
  // little bit tricky since we need to use constraints and their
  // consistency methods to compute the values; therefore playing
  // with store levels...
  double[] values() {

    map = Var.createEmptyPositioning();

    double[] b = new double[xInit.length];

    // need also -f(xInit)
    for (int i = 0; i < xInit.length; i++) {
      map.put(x[i], xInit[i]);
    }

    for (int i = 0; i < f.length; i++) {
      b[i] = -value(f[i]);
    }

    return b;
  }

  double value(FloatVar f) {

    if (map.get(f) != null) {
      return map.get(f);
    }

    Constraint c = constraint(f);
    if (c != null) {
      eval.push(c);
    } else if (f.singleton()) {
      return f.value();
    }

    double result;

    switch (c) {
      case PdivQeqR qeqR2 -> {
        if (f.equals(qeqR2.r)) {
          result = value(qeqR2.p) / value(qeqR2.q);
        } else {
          throw new RuntimeException(
              "!!! Anable to compute middle value for "
                  + f
                  + "; + Constraint "
                  + c
                  + " does not define a function for variable\n");
        }
      }
      case PmulQeqR qeqR3 -> {
        if (f.equals(qeqR3.r)) {
          result = value(qeqR3.p) * value(qeqR3.q);
        } else {
          throw new RuntimeException(
              "!!! Anable to compute middle value for "
                  + f
                  + "; + Constraint "
                  + c
                  + " does not define a function for variable\n");
        }
      }
      case PmulCeqR ceqR1 -> {
        if (f.equals(ceqR1.r)) {
          result = value(ceqR1.p) * ceqR1.c;
        } else {
          throw new RuntimeException(
              "!!! Anable to compute middle value for "
                  + f
                  + "; + Constraint "
                  + c
                  + " does not define a function for variable\n");
        }
      }
      case PminusQeqR qeqR -> {
        if (f.equals(qeqR.r)) {
          result = value(qeqR.p) - value(qeqR.q);
        } else {
          throw new RuntimeException(
              "!!! Anable to compute middle value for "
                  + f
                  + "; + Constraint "
                  + c
                  + " does not define a function for variable\n");
        }
      }
      case PplusQeqR qeqR1 -> {
        if (f.equals(qeqR1.r)) {
          result = value(qeqR1.p) + value(qeqR1.q);
        } else {
          throw new RuntimeException(
              "!!! Anable to compute middle value for "
                  + f
                  + "; + Constraint "
                  + c
                  + " does not define a function for variable\n");
        }
      }
      case PplusCeqR ceqR -> {
        if (f.equals(ceqR.r)) {
          result = value(ceqR.p) + ceqR.c;
        } else {
          throw new RuntimeException(
              "!!! Anable to compute middle value for "
                  + f
                  + "; + Constraint "
                  + c
                  + " does not define a function for variable\n");
        }
      }
      case LinearFloat float1 -> {
        FloatVar[] v = float1.list;
        double[] w = float1.weights;
        double sum = float1.sum;

        FloatVar vOut = null;
        double wOut = 1000.0;

        for (int i = 0; i < v.length; i++) {
          if (!v[i].equals(f)) {
            sum -= value(v[i]) * w[i];
          } else {
            vOut = v[i];
            wOut = w[i];
          }
        }

        if (vOut != null) {
          result = sum / wOut;
        } else {
          throw new RuntimeException(
              "!!! Anable to compute middle value for "
                  + f
                  + "; + Constraint "
                  + c
                  + " does not define a function for variable\n");
        }
      }
      case null, default ->
          throw new RuntimeException(
              "!!! Constraint " + c + " is not yet supported in Newtoen method\n");
    }

    eval.pop();

    return result;
  }

  Constraint constraint(FloatVar v) {

    List<Constraint> list = new ArrayList<>();

    for (int i = 0; i < v.dom().modelConstraints.length; i++) {
      if (v.dom().modelConstraints[i] != null) {
        for (int j = 0; j < v.dom().modelConstraints[i].length; j++) {
          if (v.dom().modelConstraints[i][j] != null) {

            Constraint c = v.dom().modelConstraints[i][j];

            if (eval.search(c) == -1) {
              if (Derivative.derivateConstraints.contains(c)) {
                continue;
              }

              if (!list.contains(c)) {
                list.add(c);
              }
            }
          }
        }
      }
    }

    Constraint c;
    if (list.size() == 1) {
      c = list.getFirst();
    } else {
      c = Derivative.resolveConstraint(v, list);
    }

    return c;
  }

  boolean contains(FloatVar[] fs, FloatVar r) {

    for (FloatVar f : fs) {
      if (f.equals(r)) {
        return true;
      }
    }

    return false;
  }

  /**
   * Returns a string representation of the Newton solver including functions and derivatives.
   *
   * @return string representation
   */
  public String toString() {
    StringBuilder s = new StringBuilder("MultivariateIntervalNewton:\n");

    s.append(Arrays.asList(f)).append("\n");
    s.append(Arrays.asList(x)).append("\n");
    for (int i = 0; i < fprime.length; i++) {
      for (int j = 0; j < fprime[i].length; j++) {
        s.append("f")
            .append(i)
            .append("/d")
            .append(x[j])
            .append(" = ")
            .append(fprime[i][j])
            .append("\n");
      }
    }
    s.append("\n");

    return s.toString();
  }
}
