/*
 * LpSources.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.constraints.lp;

import java.util.Map;
import java.util.TreeMap;

/**
 * What the rows of a {@link LinearRelaxation} give, by the source they came from: the constraint
 * class of a model row or a linearised row, or the separator of a cut (MIR, Gomory, zero-half,
 * capacity, energy, Hall, tree), with the cuts made in search apart from those of the root. Kept
 * only with {@code -Dorg.jacop.lp.sourceStats=true}, for measurements; a relaxation without it
 * keeps none and behaves as before.
 *
 * <p>For each source: the rows made, the rows in the simplex after the first solve and its cut
 * rounds, the loss of the root bound when the rows of the source alone are left out of that
 * simplex, the rows times the solves they were in the simplex (their cost), the deductions and
 * failures whose integer certificate uses a row of the source (their worth), the share of the
 * multipliers of those certificates on its rows, the rows that aged out of the simplex and came
 * back, and the time of its separation rounds.
 */
final class LpSources {

  /** Whether relaxations keep the statistics. Not final, so that tests can switch it on. */
  static boolean on = Boolean.getBoolean("org.jacop.lp.sourceStats");

  /** The statistics of one source. */
  static final class Stat {
    long rows;
    long rootRows;
    double rootLoss = Double.NaN;
    long rootIntLoss;
    long rowSolves;
    long uses;
    long failUses;
    double share;
    long agedOut;
    long returns;
    long nanos;
  }

  private final Map<String, Stat> stats = new TreeMap<>();

  Stat of(String source) {
    return stats.computeIfAbsent(source, s -> new Stat());
  }

  /**
   * One line per source: {@code source rows rootRows rootLoss rootIntLoss rowSolves uses failUses
   * share agedOut returns seconds}.
   *
   * @return the lines, without a trailing newline
   */
  String report() {
    StringBuilder b = new StringBuilder();
    for (Map.Entry<String, Stat> e : stats.entrySet()) {
      Stat s = e.getValue();
      if (!b.isEmpty()) {
        b.append('\n');
      }
      b.append(e.getKey())
          .append(' ')
          .append(s.rows)
          .append(' ')
          .append(s.rootRows)
          .append(' ')
          .append(s.rootLoss)
          .append(' ')
          .append(s.rootIntLoss)
          .append(' ')
          .append(s.rowSolves)
          .append(' ')
          .append(s.uses)
          .append(' ')
          .append(s.failUses)
          .append(' ')
          .append(String.format(java.util.Locale.ROOT, "%.2f", s.share))
          .append(' ')
          .append(s.agedOut)
          .append(' ')
          .append(s.returns)
          .append(' ')
          .append(String.format(java.util.Locale.ROOT, "%.3f", s.nanos / 1e9));
    }
    return b.toString();
  }
}
