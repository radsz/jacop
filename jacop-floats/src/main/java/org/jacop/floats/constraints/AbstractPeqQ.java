/*
 * AbstractPeqQ.java
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

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;

/**
 * Abstract base for float equality/inequality constraints (PeqQ, PneqQ). Provides shared fields,
 * constructor logic, and common consistency methods.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractPeqQ extends PrimitiveConstraint {

  /** It specifies a left hand variable in equality constraint. */
  protected final FloatVar p;

  /** It specifies a right hand variable in equality constraint. */
  protected final FloatVar q;

  /**
   * Constructs an equality/inequality constraint between two float variables.
   *
   * @param idNum the id counter for the concrete subclass.
   * @param p variable p.
   * @param q variable q.
   */
  protected AbstractPeqQ(AtomicInteger idNum, FloatVar p, FloatVar q) {

    checkInputForNullness(new String[] {"p", "q"}, new Object[] {p, q});

    numberId = idNum.incrementAndGet();

    this.queueIndex = 0;

    this.p = p;
    this.q = q;

    setScope(p, q);
  }

  /**
   * Performs domain consistency by intersecting p and q domains in a loop until no further
   * propagation occurs.
   *
   * @param store the constraint store
   */
  protected void domainConsistency(Store store) {
    do {

      // domain consistency
      p.domain.in(store.level, p, q.dom());

      store.propagationHasOccurred = false;

      q.domain.in(store.level, q, p.dom());

    } while (store.propagationHasOccurred);
  }

  /**
   * Performs complement consistency by removing singleton values from the other variable's domain.
   *
   * @param store the constraint store
   */
  protected void complementConsistency(Store store) {

    if (q.singleton()) {
      p.domain.inComplement(store.level, p, q.value());
    }

    if (p.singleton()) {
      q.domain.inComplement(store.level, q, p.value());
    }
  }

  /**
   * Checks if the constraint is satisfied when both variables are grounded and equal.
   *
   * @return true if both variables are grounded and equal within precision
   */
  protected boolean satisfiedWhenEqual() {
    return grounded()
        && java.lang.Math.abs(p.min() - q.max()) <= FloatDomain.precision()
        && java.lang.Math.abs(p.max() - q.min()) <= FloatDomain.precision();
  }

  /**
   * Checks if the constraint is satisfied when domains are disjoint.
   *
   * @return true if the domains do not intersect
   */
  protected boolean satisfiedWhenDisjoint() {
    return !p.domain.isIntersecting(q.domain);
  }
}
