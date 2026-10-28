/*
 * AtMostOneRule.java
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

/**
 * The at-most-one rule ({@link AtMostOnes}) as a presolve rule. It is one of the standard rules,
 * switched off by the system property {@code jacop.presolve.atMostOnes=false}, and it adds up what
 * it did over the rounds of one derivation.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class AtMostOneRule implements Rule {

  private final boolean enabled;
  private AtMostOnes.Statistics statistics = new AtMostOnes.Statistics(0, 0, 0, 0, 0);

  /**
   * It creates the rule, on unless the system property {@code jacop.presolve.atMostOnes} is false.
   */
  public AtMostOneRule() {
    this(Boolean.parseBoolean(System.getProperty("jacop.presolve.atMostOnes", "true")));
  }

  /**
   * It creates the rule.
   *
   * @param enabled false for a rule that does nothing.
   */
  public AtMostOneRule(boolean enabled) {
    this.enabled = enabled;
  }

  @Override
  public void apply(Context context) {
    if (enabled) {
      statistics =
          statistics.plus(
              AtMostOnes.apply(
                  context.store(),
                  context.level(),
                  context.constraints(),
                  context::impose,
                  context::remove));
    }
  }

  /**
   * Returns what the rule did over all its rounds.
   *
   * @return the statistics.
   */
  public AtMostOnes.Statistics statistics() {
    return statistics;
  }
}
