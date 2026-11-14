/*
 * Simplifiable.java
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
package org.jacop.api;

import java.util.List;
import java.util.Optional;
import org.jacop.constraints.Constraint;

/**
 * A constraint that can rewrite itself into simpler constraints for the current domains of its
 * variables (global-specific presolve). A presolve derivation asks every carried constraint that
 * implements it, at a fixpoint of the store, and copies the rewriting into the derived store
 * instead of the constraint.
 *
 * <p>The contract: the returned constraints are new, not imposed, over variables of this
 * constraint's store (a subset of its own variables), and each is {@link Copyable}. Their
 * conjunction has exactly the solutions of this constraint over the current domains, so the
 * rewriting keeps every solution and can be used under all-solutions search and counting. The
 * method changes neither this constraint nor any domain, and may assume that the store is at a
 * fixpoint, so this constraint has propagated. A subclass that does not declare the method itself
 * must not be rewritten as its superclass; implementations check their exact class.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public interface Simplifiable {

  /**
   * Rewrites this constraint for the current domains.
   *
   * @return the constraints that replace this one, an empty list if every assignment of the current
   *     domains satisfies it, or nothing if there is nothing simpler.
   */
  Optional<List<Constraint>> simplify();
}
