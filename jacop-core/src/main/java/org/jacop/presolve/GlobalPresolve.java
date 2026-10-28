/*
 * GlobalPresolve.java
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
import java.util.List;
import java.util.Optional;
import org.jacop.api.Copyable;
import org.jacop.api.Simplifiable;
import org.jacop.constraints.Constraint;

/**
 * Global-specific presolve: a constraint that implements {@link Simplifiable} rewrites itself for
 * the current domains, for example an element constraint whose index can only reach positions that
 * hold {@code index + c} becomes {@code XplusCeqZ}, a table loses the tuples the domains rule out
 * and the columns of fixed variables, and a cumulative loses the tasks that use no resource. Each
 * rewriting keeps every solution, so it is safe under all-solutions search and counting.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class GlobalPresolve {

  /** How many times a rewritten constraint is itself rewritten again. */
  private static final int DEPTH = 3;

  private GlobalPresolve() {}

  /**
   * Rewrites a constraint of a store at a fixpoint for the current domains, and rewrites the result
   * again while it simplifies.
   *
   * @param c the constraint.
   * @return the constraints that replace it, not imposed and {@link Copyable}, an empty list if it
   *     holds for the current domains, or nothing if it has no simpler form.
   */
  public static Optional<List<Constraint>> rewrite(Constraint c) {
    List<Constraint> out = new ArrayList<>();
    return rewrite(c, out, DEPTH) ? Optional.of(out) : Optional.empty();
  }

  private static boolean rewrite(Constraint c, List<Constraint> out, int depth) {
    List<Constraint> rewriting =
        depth > 0 && c instanceof Simplifiable s ? s.simplify().orElse(null) : null;
    if (rewriting == null || !Copyable.canCopyAll(rewriting.toArray())) {
      out.add(c);
      return false;
    }
    for (Constraint r : rewriting) {
      rewrite(r, out, depth - 1);
    }
    return true;
  }
}
