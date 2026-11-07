/*
 * Locks.java
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

package org.jacop.presolve;

import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;
import org.jacop.api.Monotone;
import org.jacop.api.MonotoneDefinition;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;

/**
 * The locks of a constraint on its variables, for dual reductions: in which directions a variable
 * can move without making the constraint false, and beyond which value the constraint holds
 * whatever the other variables take in their current domains.
 *
 * <p>Linear constraints are read through their {@link LinearForm}, other constraints through {@link
 * Monotone}, and {@link Implies} through its condition. Any other constraint locks every variable
 * in both directions.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class Locks {

  /** No value: the constraint is not known to hold beyond any value of the variable. */
  static final long NONE_ABOVE = Long.MAX_VALUE;

  /** No value: the constraint is not known to hold below any value of the variable. */
  static final long NONE_BELOW = Long.MIN_VALUE;

  /** Receives the locks of a constraint, one call per variable and possibly more. */
  interface Sink {

    /**
     * Reports the locks of a constraint on a variable.
     *
     * @param v the variable.
     * @param free the directions in which {@code v} can move, as in {@link Monotone}.
     * @param above the constraint holds whenever {@code v >= above}, or {@link #NONE_ABOVE}.
     * @param below the constraint holds whenever {@code v <= below}, or {@link #NONE_BELOW}.
     */
    void lock(Var v, int free, long above, long below);
  }

  /**
   * A constraint that defines a variable as a monotone function of the others.
   *
   * @param defined the defined variable.
   * @param inputs for each other variable, 1 if the defined value does not decrease when it
   *     increases, -1 if it does not increase, {@link #INDEPENDENT} if it does not depend on it, 0
   *     if neither is known.
   */
  record Definition(Var defined, Map<Var, Integer> inputs) {}

  /** The defined variable does not depend on the input. */
  static final int INDEPENDENT = 2;

  private Locks() {}

  /**
   * Returns a constraint as a definition: {@code b <-> c} defines {@code b}, and a {@link
   * MonotoneDefinition} its defined variable.
   *
   * @param c the constraint.
   * @return the definition, or null if the constraint does not define a variable now.
   */
  static Definition definition(Constraint c) {
    Map<Var, Integer> inputs = new IdentityHashMap<>();
    if (c instanceof Reified r) {
      if (r.b.singleton() || r.c.arguments().contains(r.b)) {
        return null;
      }
      // b = [c], and [c] does not decrease when a variable moves in a direction c allows
      Map<Var, Integer> free = new IdentityHashMap<>();
      collect(r.c, (v, f, above, below) -> free.merge(v, f, (x, y) -> x & y));
      for (Map.Entry<Var, Integer> e : free.entrySet()) {
        int f = e.getValue();
        int m =
            switch (f) {
              case Monotone.INCREASE -> 1;
              case Monotone.DECREASE -> -1;
              case Monotone.INCREASE | Monotone.DECREASE -> INDEPENDENT;
              default -> 0;
            };
        inputs.put(e.getKey(), m);
      }
      return new Definition(r.b, inputs);
    }
    if (c instanceof MonotoneDefinition d && d.defined() instanceof Var defined) {
      for (Var v : c.arguments()) {
        if (v != defined) {
          inputs.put(v, d.monotonicity(v));
        }
      }
      return new Definition(defined, inputs);
    }
    return null;
  }

  /**
   * Reports the locks of a constraint on every one of its variables.
   *
   * @param c the constraint.
   * @param sink the receiver.
   */
  static void collect(Constraint c, Sink sink) {
    LinearForm form = form(c);
    if (form != null) {
      collect(form, c.arguments(), sink);
    } else if (c instanceof Monotone m) {
      for (Var v : c.arguments()) {
        sink.lock(v, m.freeDirections(v), NONE_ABOVE, NONE_BELOW);
      }
    } else if (c instanceof Implies i) {
      // b -> c holds when b is false or c holds, so b can always decrease and every variable of c
      // keeps the locks it has in c
      Constraint condition = i.c;
      boolean shared = condition.arguments().contains(i.b);
      sink.lock(i.b, shared ? 0 : Monotone.DECREASE, NONE_ABOVE, shared ? NONE_BELOW : 0);
      collect(condition, sink);
    } else {
      for (Var v : c.arguments()) {
        sink.lock(v, 0, NONE_ABOVE, NONE_BELOW);
      }
    }
  }

  /**
   * Returns a constraint as a linear relation.
   *
   * @param c the constraint.
   * @return its linear form, or null if it is not linear.
   */
  static LinearForm form(Constraint c) {
    if (c instanceof LinearInt l) {
      return l.linearRelation();
    }
    if (c instanceof LinearExplainable l) {
      return l.linearForm();
    }
    return null;
  }

  /**
   * Reports the locks of a linear relation, and locks in both directions every argument of the
   * constraint the relation does not mention.
   *
   * @param form the relation.
   * @param arguments the variables of the constraint.
   * @param sink the receiver.
   */
  static void collect(LinearForm form, Set<Var> arguments, Sink sink) {
    Map<IntVar, Long> weights = merged(form);
    for (Var v : arguments) {
      if (!(v instanceof IntVar iv) || !weights.containsKey(iv)) {
        sink.lock(v, 0, NONE_ABOVE, NONE_BELOW);
      }
    }
    if (form.relation() == LinearForm.EQ || form.relation() == LinearForm.NE) {
      for (Map.Entry<IntVar, Long> e : weights.entrySet()) {
        sink.lock(
            e.getKey(),
            e.getValue() == 0 ? Monotone.DECREASE | Monotone.INCREASE : 0,
            NONE_ABOVE,
            NONE_BELOW);
      }
      return;
    }
    // as sum w * x <= c
    long sign = form.relation() == LinearForm.LE ? 1 : -1;
    long c = sign * form.c();
    long maxSum = 0;
    for (Map.Entry<IntVar, Long> e : weights.entrySet()) {
      maxSum += maxTerm(sign * e.getValue(), e.getKey());
    }
    for (Map.Entry<IntVar, Long> e : weights.entrySet()) {
      IntVar v = e.getKey();
      long w = sign * e.getValue();
      if (w == 0) {
        sink.lock(v, Monotone.DECREASE | Monotone.INCREASE, NONE_ABOVE, NONE_BELOW);
        continue;
      }
      // the relation holds whenever w * v <= c - (the largest value of the other terms)
      long room = c - (maxSum - maxTerm(w, v));
      if (w > 0) {
        sink.lock(v, Monotone.DECREASE, NONE_ABOVE, Math.floorDiv(room, w));
      } else {
        sink.lock(v, Monotone.INCREASE, Math.ceilDiv(room, w), NONE_BELOW);
      }
    }
  }

  /** The weights of a linear relation with repeated variables merged. */
  static Map<IntVar, Long> merged(LinearForm form) {
    Map<IntVar, Long> weights = new IdentityHashMap<>();
    IntVar[] vars = form.vars();
    for (int i = 0; i < vars.length; i++) {
      weights.merge(vars[i], form.weights()[i], Long::sum);
    }
    return weights;
  }

  private static long maxTerm(long w, IntVar v) {
    return w >= 0 ? w * v.max() : w * v.min();
  }
}
