/*
 * Aliases.java
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

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XeqY;
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * Variable aliasing: the variables of an {@code XeqY} with the same domain become one variable of
 * the child, and the equation is dropped. The child then has fewer variables, and under lazy clause
 * generation fewer atoms and shorter explanations. Two variables are merged only if no other
 * constraint has both of them, so no copied constraint gets a repeated variable, which not every
 * propagator handles; and only variables of the same class are merged, so every copy gets the class
 * it expects.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class Aliases {

  /** Aliasing is on unless the system property jacop.presolve.alias is false. */
  static final boolean ENABLED =
      Boolean.parseBoolean(System.getProperty("jacop.presolve.alias", "true"));

  private final Map<Var, Var> parent = new IdentityHashMap<>();
  private final Map<Var, List<Var>> members = new IdentityHashMap<>();
  private final Map<Var, List<Constraint>> occurrences = new IdentityHashMap<>();
  private final Set<Constraint> dropped = Collections.newSetFromMap(new IdentityHashMap<>());

  private Aliases(List<Constraint> constraints) {
    for (Constraint c : constraints) {
      for (Var v : c.arguments()) {
        occurrences.computeIfAbsent(v, k -> new ArrayList<>()).add(c);
      }
    }
  }

  /**
   * Merges the variables of the equations among the constraints of a store at a fixpoint.
   *
   * @param constraints the constraints carried into the child; the merged equations are removed.
   * @return each merged variable mapped to the variable of its class that stays.
   */
  static Map<Var, Var> merge(List<Constraint> constraints) {
    Aliases a = new Aliases(constraints);
    for (Constraint c : constraints) {
      if (c.getClass() == XeqY.class) {
        a.merge(c);
      }
    }
    // an equation kept before its variables were merged through others is implied now
    for (Constraint c : constraints) {
      if (c.getClass() == XeqY.class) {
        Var[] ends = ends(c);
        if (a.find(ends[0]) == a.find(ends[1])) {
          a.dropped.add(c);
        }
      }
    }
    constraints.removeIf(a.dropped::contains);
    Map<Var, Var> result = new IdentityHashMap<>();
    for (Var v : a.parent.keySet()) {
      Var root = a.find(v);
      if (root != v) {
        result.put(v, root);
      }
    }
    return result;
  }

  private Var find(Var v) {
    Var p = parent.get(v);
    if (p == null) {
      return v;
    }
    Var root = find(p);
    parent.put(v, root);
    return root;
  }

  /** The two variables of an equation, the same one twice for {@code x = x}. */
  private static Var[] ends(Constraint equation) {
    Var[] vars = equation.arguments().toArray(new Var[0]);
    return vars.length == 1 ? new Var[] {vars[0], vars[0]} : vars;
  }

  private void merge(Constraint c) {
    Var[] ends = ends(c);
    Var x = find(ends[0]);
    Var y = find(ends[1]);
    if (x == y) {
      dropped.add(c);
      return;
    }
    if (x.getClass() != y.getClass() || !((IntVar) x).dom().eq(((IntVar) y).dom())) {
      return;
    }
    List<Var> xs = members(x);
    List<Var> ys = members(y);
    if (xs.size() < ys.size() ? shared(xs, y, c) : shared(ys, x, c)) {
      return;
    }
    parent.put(y, x);
    xs.addAll(ys);
    members.remove(y);
    dropped.add(c);
  }

  private List<Var> members(Var root) {
    return members.computeIfAbsent(root, k -> new ArrayList<>(List.of(k)));
  }

  /**
   * Tells whether a constraint other than the equation, and other than another equation, which
   * merging makes implied, has a variable of the class and one of the class of {@code other}.
   */
  private boolean shared(List<Var> vars, Var other, Constraint equation) {
    for (Var v : vars) {
      for (Constraint c : occurrences.getOrDefault(v, List.of())) {
        if (c == equation || c.getClass() == XeqY.class || dropped.contains(c)) {
          continue;
        }
        for (Var w : c.arguments()) {
          if (find(w) == other) {
            return true;
          }
        }
      }
    }
    return false;
  }
}
