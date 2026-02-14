/*
 * AbstractTrigConstraint.java
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

import org.jacop.api.Stateful;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatInterval;
import org.jacop.floats.core.FloatVar;

/**
 * Abstract base class for trigonometric float constraints (cos, sin, etc.).
 *
 * <p>Provides shared fields and methods for constraints of the form trig(P) = Q.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractTrigConstraint extends Constraint implements Stateful {

  /** It contains variable p. */
  protected final FloatVar p;

  /** It contains variable q. */
  protected final FloatVar q;

  /** Flag indicating if this is the first consistency check. */
  protected boolean firstConsistencyCheck = true;

  /** The backtracking level at which first consistency check occurred. */
  protected int firstConsistencyLevel;

  /**
   * It constructs a trigonometric constraint trig(P) = Q.
   *
   * @param p variable P
   * @param q variable Q
   */
  protected AbstractTrigConstraint(FloatVar p, FloatVar q) {

    checkInputForNullness(new String[] {"p", "q"}, new Object[] {p, q});

    this.queueIndex = 1;
    this.p = p;
    this.q = q;

    setScope(p, q);
  }

  @Override
  public void removeLevel(int level) {
    if (level == firstConsistencyLevel) {
      firstConsistencyCheck = true;
    }
  }

  @Override
  public void consistency(Store store) {

    if (firstConsistencyCheck) {
      q.domain.in(store.level, q, -1.0, 1.0);
      firstConsistencyCheck = false;
      firstConsistencyLevel = store.level;
    }

    boundConsistency(store);
  }

  /**
   * Performs bound consistency propagation specific to the trigonometric function.
   *
   * @param store the constraint store
   */
  protected abstract void boundConsistency(Store store);

  /**
   * Normalizes an angle variable to the range [-2*PI, 2*PI].
   *
   * @param v the variable to normalize
   * @return the normalized interval
   */
  protected FloatInterval normalize(FloatVar v) {
    return org.jacop.floats.core.FloatDomain.normalizeAngle(v.min(), v.max());
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public abstract String toString();
}
