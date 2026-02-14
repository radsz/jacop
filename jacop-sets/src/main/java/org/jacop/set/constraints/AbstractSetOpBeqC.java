/*
 * AbstractSetOpBeqC.java
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

package org.jacop.set.constraints;

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * Abstract base class for binary set operation constraints of the form A op B = C (intersection,
 * union, difference). Provides shared fields, constructor, queueVariable, pruning event, and the
 * consistency do-while loop structure.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public abstract class AbstractSetOpBeqC extends Constraint
    implements UsesQueueVariable, SatisfiedPresent {

  /** It specifies set variable a. */
  protected final SetVar a;

  /** It specifies set variable b. */
  protected final SetVar b;

  /** It specifies set variable c. */
  protected final SetVar c;

  /**
   * It specifies if the constraint attempts to perform expensive and yet unlikely propagation due
   * to cardinality information.
   */
  protected final boolean performCardinalityReasoning = false;

  /** Change flags for incremental propagation. */
  protected boolean aHasChanged = true;

  protected boolean bHasChanged = true;
  protected boolean cHasChanged = true;

  /**
   * Constructs a set operation constraint A op B = C.
   *
   * @param idNum the atomic id counter for the concrete constraint type
   * @param a set variable a
   * @param b set variable b
   * @param c set variable c (result)
   */
  protected AbstractSetOpBeqC(AtomicInteger idNum, SetVar a, SetVar b, SetVar c) {
    checkInputForNullness(new String[] {"a", "b", "c"}, new Object[] {a, b, c});
    numberId = idNum.incrementAndGet();
    this.a = a;
    this.b = b;
    this.c = c;
    setScope(a, b, c);
  }

  @Override
  public void consistency(Store store) {

    do {
      store.propagationHasOccurred = false;

      boolean aChanged = this.aHasChanged;
      boolean bChanged = this.bHasChanged;
      boolean cChanged = this.cHasChanged;

      this.aHasChanged = false;
      this.bHasChanged = false;
      this.cHasChanged = false;

      propagateOperation(store, aChanged, bChanged, cChanged);

    } while (store.propagationHasOccurred);
  }

  /**
   * Performs the operation-specific propagation within the do-while loop.
   *
   * @param store the constraint store
   * @param aChanged whether variable a has changed
   * @param bChanged whether variable b has changed
   * @param cChanged whether variable c has changed
   */
  protected abstract void propagateOperation(
      Store store, boolean aChanged, boolean bChanged, boolean cChanged);

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return SetDomain.ANY;
  }

  @Override
  public void queueVariable(int level, Var variable) {
    if (variable == a) {
      aHasChanged = true;
    } else if (variable == b) {
      bHasChanged = true;
    } else if (variable == c) {
      cHasChanged = true;
    }
  }
}
