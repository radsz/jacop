/*
 * Derivative.java
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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Constraint;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.constraints.linear.Linear;
import org.jacop.floats.core.FloatVar;

/**
 * Derivative for float constraints.
 *
 * <p>The derivative of f with respect to x
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Derivative {

  public static final double MIN_FLOAT = -1e+150;
  public static final double MAX_FLOAT = 1e+150;

  static Stack<Constraint> eval;

  static Set<Constraint> derivateConstraints;

  static Map<FloatVar, Constraint> definitionConstraint;

  static Store store;

  private Derivative() {}

  /**
   * Initializes the derivative computation with a store.
   *
   * @param s the constraint store to use
   */
  public static void init(Store s) {
    store = s;

    derivateConstraints = new HashSet<>();
    eval = new Stack<>();
    definitionConstraint = Var.createEmptyPositioning();
  }

  /**
   * Computes the derivative of a function variable with respect to another variable.
   *
   * @param store the constraint store
   * @param f the function variable to differentiate
   * @param vars the set of primitive variables
   * @param x the variable with respect to which to differentiate
   * @return the derivative as a FloatVar
   */
  public static FloatVar getDerivative(Store store, FloatVar f, Set<FloatVar> vars, FloatVar x) {

    if (f == x) {
      return new FloatVar(store, 1.0, 1.0);
    }
    if (vars.contains(f)) {
      return new FloatVar(store, 0.0, 0.0);
    }

    List<Constraint> constraints = collectConstraintsForDerivative(f);

    if (constraints.size() == 1) {
      return getDerivativeFromSingleConstraint(store, f, vars, x, constraints.getFirst());
    }
    if (constraints.isEmpty() && f.singleton()) {
      return new FloatVar(store, 0.0, 0.0);
    }
    return getDerivativeFromMultipleConstraints(store, f, vars, x, constraints);
  }

  private static List<Constraint> collectConstraintsForDerivative(FloatVar f) {
    List<Constraint> constraints = new ArrayList<>();
    for (int i = 0; i < f.dom().modelConstraints.length; i++) {
      if (f.dom().modelConstraints[i] == null) {
        continue;
      }
      for (int j = 0; j < f.dom().modelConstraints[i].length; j++) {
        if (f.dom().modelConstraints[i][j] == null) {
          continue;
        }
        Constraint currentConstraint = f.dom().modelConstraints[i][j];
        if (eval.search(currentConstraint) != -1) {
          continue;
        }
        if (!derivateConstraints.contains(currentConstraint)) {
          constraints.add(currentConstraint);
        }
      }
    }
    return constraints;
  }

  private static FloatVar getDerivativeFromSingleConstraint(
      Store store, FloatVar f, Set<FloatVar> vars, FloatVar x, Constraint currentConstraint) {
    if (currentConstraint instanceof FloatDerivableConstraint derivableConstraint) {
      eval.push(currentConstraint);
      FloatVar v = derivableConstraint.derivative(store, f, vars, x);
      eval.pop();
      return v;
    }
    throw new UnsupportedOperationException(
        "Constraint " + currentConstraint + " does not support derivatives");
  }

  private static FloatVar getDerivativeFromMultipleConstraints(
      Store store, FloatVar f, Set<FloatVar> vars, FloatVar x, List<Constraint> constraints) {
    Constraint c = resolveConstraint(f, constraints);
    if (c != null) {
      if (c instanceof FloatDerivableConstraint derivableConstraint) {
        eval.push(c);
        FloatVar v = derivableConstraint.derivative(store, f, vars, x);
        eval.pop();
        return v;
      }
      throw new UnsupportedOperationException("Constraint " + c + " does not support derivatives");
    }
    log.info(
        "!!! "
            + constraints.size()
            + " constraints define a function for variable "
            + f
            + "\n"
            + constraints);
    System.exit(0);
    return null;
  }

  static void poseDerivativeConstraint(Constraint c) {

    store.impose(c);

    derivateConstraints.add(c);
  }

  static Constraint resolveConstraint(FloatVar f, List<Constraint> cs) {

    Constraint c = definitionConstraint.get(f);

    List<Constraint> resolved = new ArrayList<>();
    if (c == null) {
      for (Constraint cc : cs) {
        if (constraintDefinesF(f, cc)) {
          resolved.add(cc);
        }
      }
    }

    if (resolved.size() == 1) {
      return resolved.getFirst();
    }

    return c;
  }

  private static boolean constraintDefinesF(FloatVar f, Constraint cc) {
    return constraintDefinesFBinary(f, cc) || constraintDefinesFLinear(f, cc);
  }

  private static boolean constraintDefinesFBinary(FloatVar f, Constraint cc) {
    if (cc instanceof PmulQeqR qeqR && f.equals(qeqR.r)) {
      return true;
    }
    if (cc instanceof PmulCeqR ceqR1 && f.equals(ceqR1.r)) {
      return true;
    }
    if (cc instanceof PplusQeqR qeqR2 && f.equals(qeqR2.r)) {
      return true;
    }
    if (cc instanceof PplusCeqR ceqR && f.equals(ceqR.r)) {
      return true;
    }
    return cc instanceof PdivQeqR qeqR && f.equals(qeqR.p);
  }

  private static boolean constraintDefinesFLinear(FloatVar f, Constraint cc) {
    if (!(cc instanceof LinearFloat float1) || float1.relationType != Linear.EQ) {
      return false;
    }
    double[] ws = float1.weights;
    FloatVar[] ls = float1.list;
    for (int i = 0; i < ls.length; i++) {
      if (f.equals(ls[i]) && ws[i] == -1.0) {
        return true;
      }
    }
    return false;
  }

  /**
   * Defines a constraint that should be used for computing the derivative of a variable.
   *
   * @param f the variable to define the constraint for
   * @param c the constraint that defines the variable
   */
  public static void defineConstraint(FloatVar f, Constraint c) {
    definitionConstraint.put(f, c);
  }

  /**
   * Returns the number of derivative constraints that have been created.
   *
   * @return the number of derivative constraints
   */
  public static int numberDerivativeConstraints() {
    return derivateConstraints.size();
  }

  /**
   * Returns the set of all derivative constraints that have been created.
   *
   * @return the set of derivative constraints
   */
  public static Set<Constraint> derivativeConstraints() {
    return derivateConstraints;
  }
}
