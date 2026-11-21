/*
 * Trace.java
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

package org.jacop.jalp;

import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.util.Locale;

/**
 * A diagnostic trace of the simplex and the presolve for comparison with other LP codes (osolpro
 * {@code benchmarks/jalp-trace}). The system property {@code org.jacop.jalp.trace} names the file;
 * without it nothing is written and every hook is one test of a static final field.
 *
 * <p>Lines: {@code R kind row column other} per presolve reduction, in the indices of the problem
 * as given (rows and columns of the MPS file); {@code P solve pivot phase entering leaving row
 * primalStep dualStep pivot} per dual simplex pivot; {@code F solve pivot reason} per
 * factorization; {@code A} and {@code B} lines at the start from a postsolved basis (nonbasic
 * columns at artificial bounds, basic columns outside their bounds). {@code solve} numbers the
 * instances of {@link RevisedDualSimplex}, so the reduced problem of the presolve has its own
 * number.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class Trace {

  static final PrintStream OUT = open(System.getProperty("org.jacop.jalp.trace"));

  private static int solves;

  private Trace() {}

  private static PrintStream open(String file) {
    if (file == null) {
      return null;
    }
    try {
      return new PrintStream(file);
    } catch (FileNotFoundException e) {
      throw new IllegalArgumentException("org.jacop.jalp.trace " + file, e);
    }
  }

  static synchronized int nextSolve() {
    return ++solves;
  }

  static void reduction(String kind, int row, int column, int other) {
    OUT.printf(Locale.ROOT, "R %s %d %d %d%n", kind, row, column, other);
  }

  static void pivot(
      int solve,
      long pivot,
      int phase,
      int q,
      int p,
      int r,
      double theta,
      double thetaD,
      double a) {
    OUT.printf(
        Locale.ROOT,
        "P %d %d %d %d %d %d %.6g %.6g %.6g%n",
        solve,
        pivot,
        phase,
        q,
        p,
        r,
        theta,
        thetaD,
        a);
  }

  static void factor(int solve, long pivot, String reason) {
    OUT.printf(Locale.ROOT, "F %d %d %s%n", solve, pivot, reason);
  }
}
