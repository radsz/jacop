/*
 * QueueForward.java
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

package org.jacop.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.Var;

/**
 * Utility class that allows for constraints like Xor, Reified, etc that take other constraints as
 * parameters to forward any changes of variables to the constraints that were provided as
 * arguments.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class QueueForward<T extends Constraint> {

  public final Map<Var, List<T>> forwardMap;

  public final boolean isEmpty;

  /**
   * Constructs a queue forward mapping from variables to constraints that need notification.
   *
   * @param constraints the constraints to consider for forwarding.
   * @param variables the variables whose changes should be forwarded.
   */
  public QueueForward(Collection<T> constraints, Collection<Var> variables) {

    forwardMap = Var.createEmptyPositioning();

    for (Var v : variables) {
      forwardMap.put(v, new ArrayList<>());
      for (T constraint : constraints) {

        if (constraintUsesQueueVariable(constraint, v)) {
          forwardMap.get(v).add(constraint);
        }
      }
    }

    for (Var v : variables) {

      List<T> varConstraints = forwardMap.get(v);

      if (varConstraints == null) {
        continue;
      }

      if (varConstraints.isEmpty()) {
        forwardMap.remove(v);
      }
    }

    isEmpty = forwardMap.isEmpty();
  }

  private boolean constraintUsesQueueVariable(T constraint, Var v) {

    if (constraint instanceof UsesQueueVariable && constraint.arguments().contains(v)) {
      try {
        // We assume that all constraint needing queueVariable declare this method, even for
        // the ones that inherit from other constraints.
        constraint.getClass().getDeclaredMethod("queueVariable", int.class, Var.class);
        return true;
      } catch (NoSuchMethodException _) {
        // constraint may use empty queueVariable provided by abstract class Constraint
        return false;
      }
    }
    return false;
  }

  /**
   * Constructs a queue forward from arrays of constraints and variables.
   *
   * @param constraints the constraints to consider for forwarding.
   * @param vars the variables whose changes should be forwarded.
   */
  public QueueForward(T[] constraints, Var[] vars) {
    this(Arrays.asList(constraints), Arrays.asList(vars));
  }

  /**
   * Constructs a queue forward from an array of constraints and a collection of variables.
   *
   * @param constraints the constraints to consider for forwarding.
   * @param vars the variables whose changes should be forwarded.
   */
  public QueueForward(T[] constraints, Collection<Var> vars) {
    this(Arrays.asList(constraints), vars);
  }

  /**
   * Constructs a queue forward from a single constraint and a collection of variables.
   *
   * @param constraint the constraint to consider for forwarding.
   * @param vars the variables whose changes should be forwarded.
   */
  public QueueForward(T constraint, Collection<Var> vars) {
    this(Collections.singletonList(constraint), vars);
  }

  /**
   * Constructs a queue forward from a collection of constraints and a single variable.
   *
   * @param constraints the constraints to consider for forwarding.
   * @param v the variable whose changes should be forwarded.
   */
  public QueueForward(Collection<T> constraints, Var v) {
    this(constraints, Collections.singletonList(v));
  }

  /**
   * Constructs a queue forward from a single constraint and a single variable.
   *
   * @param constraint the constraint to consider for forwarding.
   * @param v the variable whose changes should be forwarded.
   */
  public QueueForward(T constraint, Var v) {
    this(Collections.singletonList(constraint), Collections.singletonList(v));
  }

  /**
   * Returns whether the forward map is empty (no variables need forwarding).
   *
   * @return true if no variable-to-constraint mappings exist.
   */
  public boolean isEmpty() {
    return isEmpty;
  }

  /**
   * Forwards a variable change event to all constraints that depend on the given variable.
   *
   * @param level the current store level.
   * @param variable the variable that has changed.
   */
  public void queueForward(int level, Var variable) {

    if (isEmpty) {
      return;
    }

    List<T> constraints = forwardMap.get(variable);

    if (constraints == null) {
      return;
    }

    for (Constraint constraint : constraints) {
      constraint.queueVariable(level, variable);
    }
  }
}
