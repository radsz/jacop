/*
 * ObjectiveGap.java
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

package org.jacop.fz;

import java.util.function.Consumer;

/**
 * The best solution and the best proved bound of an optimisation, in values of the minimised cost
 * variable (the negated objective under maximisation), and the relative gap between them: option
 * --gap stops the search once {@code best - bound <= gap * |best|}, as the relative gap of MIP
 * solvers. Each improvement of the bound is printed, when a printer is given, as the statistic
 * {@code objectiveBound} in the model's own objective, so a run's bounds can be read with the time
 * they were proved.
 *
 * <p>A bound is a value that no solution better than the best one goes below. The solver's bounds
 * hold under the bound of branch and bound, which removes the solutions no better than the best:
 * such a bound is below the best value as long as the search has not ended, and the optimum lies
 * between the two.
 */
final class ObjectiveGap {

  private final double gap;
  private final boolean maximise;
  private final Consumer<String> printer;
  private long bound = Long.MIN_VALUE;
  private long best = Long.MAX_VALUE;
  private boolean reached;

  /**
   * Creates the gap of one optimisation.
   *
   * @param gap the relative gap at which to stop, a fraction; negative for none
   * @param maximise whether the cost variable is the negated objective
   * @param printer where the statistic lines of a better bound go, or null for nowhere
   */
  ObjectiveGap(double gap, boolean maximise, Consumer<String> printer) {
    this.gap = gap;
    this.maximise = maximise;
    this.printer = printer;
  }

  /**
   * Takes a proved bound of the cost variable.
   *
   * @param lower a value the cost of any better solution is at least
   * @return true when the gap is reached, now or before
   */
  synchronized boolean bound(long lower) {
    if (lower > bound) {
      bound = lower;
      if (printer != null) {
        printer.accept(
            "%%%mzn-stat: objectiveBound=" + (maximise ? -lower : lower) + "\n%%%mzn-stat-end");
      }
    }
    return check();
  }

  /**
   * Takes the cost of a solution.
   *
   * @param cost the value of the cost variable in the solution
   * @return true when the gap is reached, now or before
   */
  synchronized boolean solution(long cost) {
    best = Math.min(best, cost);
    return check();
  }

  private boolean check() {
    if (!reached && gap >= 0 && best != Long.MAX_VALUE && bound != Long.MIN_VALUE) {
      // in doubles: the values of an int cost variable cannot overflow them
      reached = (double) best - bound <= gap * Math.abs((double) best);
    }
    return reached;
  }

  /**
   * Whether the gap was reached.
   *
   * @return true once the best solution was within the gap of the bound
   */
  synchronized boolean reached() {
    return reached;
  }

  /**
   * Whether the bound proves the best solution optimal: no better solution has a smaller cost.
   *
   * @return true when the bound is at least the best cost
   */
  synchronized boolean proved() {
    return best != Long.MAX_VALUE && bound >= best;
  }

  /**
   * The best proved bound in the model's objective.
   *
   * @return the bound, or null while there is none
   */
  synchronized Long objectiveBound() {
    return bound == Long.MIN_VALUE ? null : maximise ? -bound : bound;
  }
}
