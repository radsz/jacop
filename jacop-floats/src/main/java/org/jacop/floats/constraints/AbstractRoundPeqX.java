/*
 * AbstractRoundPeqX.java
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
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.floats.core.FloatVar;

/**
 * Abstract base class for rounding constraints (floor, ceil, round) that map a float variable P to
 * an integer variable X.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractRoundPeqX extends Constraint implements SatisfiedPresent {

  /** It specifies the integer variable. */
  public IntVar x;

  /** It specifies the float variable. */
  public FloatVar p;

  /**
   * Constructs a rounding constraint with common initialization.
   *
   * @param idNum the atomic id counter for the concrete constraint type
   * @param p the float variable
   * @param x the integer variable
   */
  protected AbstractRoundPeqX(AtomicInteger idNum, FloatVar p, IntVar x) {
    checkInputForNullness(new String[] {"x", "q"}, new Object[] {x, p});

    double q = Double.max(p.min(), p.max());
    if (q > Integer.MAX_VALUE || q < Integer.MIN_VALUE) {
      throw new RuntimeException("Error: JaCoP cannor handle " + p + " in rounding to integer.");
    }
    numberId = idNum.incrementAndGet();

    this.x = x;
    this.p = p;

    setScope(x, p);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }
}
