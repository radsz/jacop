/*
 * ProbeCalculator.java
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

package org.jacop.search.restart;

/**
 * A calculator for a restart search of two runs: a first run of at most a given time, and, if that
 * run did not explore the whole tree, a second run without limit. Between the two runs it calls a
 * given action, at the root of the search, for example to turn on a propagator whose first,
 * expensive, call the first run avoided.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class ProbeCalculator extends Calculator {

  private final long probeNanos;
  private final Runnable afterProbe;
  private long deadline = Long.MAX_VALUE;
  private boolean probing = true;

  /**
   * Creates the calculator.
   *
   * @param probeNanos the longest time of the first run, in nanoseconds, counted from {@link
   *     #start()}.
   * @param afterProbe the action run after the first run when a second one follows.
   */
  public ProbeCalculator(long probeNanos, Runnable afterProbe) {
    this.probeNanos = probeNanos;
    this.afterProbe = afterProbe;
    startRun(Long.MAX_VALUE);
  }

  /** Starts the clock of the first run. */
  public void start() {
    deadline = System.nanoTime() + probeNanos;
  }

  @Override
  public boolean executeAfterConsistency(boolean consistent) {
    if (probing && consistent && System.nanoTime() > deadline) {
      // cuts this node and every later one of the first run
      failLimit = -1;
    }
    return super.executeAfterConsistency(consistent);
  }

  @Override
  public void newLimit() {
    if (probing) {
      probing = false;
      afterProbe.run();
    }
    startRun(Long.MAX_VALUE);
  }

  /**
   * Tells whether the first run is still the current one.
   *
   * @return true until the second run starts.
   */
  public boolean probing() {
    return probing;
  }

  @Override
  public String toString() {
    return "probeCalculator(" + probeNanos / 1_000_000 + " ms)";
  }
}
