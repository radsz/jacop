/*
 * ProbingRule.java
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

import org.jacop.core.Store;

/**
 * Root probing ({@link Probing}) as a presolve rule. The budget is shared by the rounds of one
 * derivation: each round probes with what is left of it, and the rule adds up what it did.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class ProbingRule implements Rule {

  private final Probing.Mode mode;
  private final long budgetMillis;
  private long spentNanos;
  private Probing.Result result = new Probing.Result(true, 0, 0, 0, 0, 0, false, 0);

  /**
   * It creates the rule.
   *
   * @param mode what probing tries.
   * @param budgetMillis the time probing may take over all rounds, in milliseconds.
   */
  public ProbingRule(Probing.Mode mode, long budgetMillis) {
    this.mode = mode;
    this.budgetMillis = budgetMillis;
  }

  @Override
  public void apply(Context context) {
    if (mode == Probing.Mode.OFF || result.exhausted()) {
      return;
    }
    Store store = context.store();
    if (store.level != context.level()) {
      throw new IllegalStateException(
          "Probing runs at the store's level " + store.level + ", not " + context.level());
    }
    long left = budgetMillis - spentNanos / 1_000_000L;
    Probing.Result r = Probing.of(store).mode(mode).budget(Math.max(left, 0)).probe();
    spentNanos += r.timeNanos();
    result = result.plus(r);
    if (!r.feasible()) {
      throw Store.failException;
    }
  }

  /**
   * Returns what probing did over all rounds.
   *
   * @return the result.
   */
  public Probing.Result result() {
    return result;
  }
}
