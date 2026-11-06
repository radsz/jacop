/*
 * LpMain.java
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

import java.io.IOException;
import java.nio.file.Path;
import java.util.Locale;

/**
 * Solves linear programs in MPS format and prints one line per file: the name, the status, the
 * objective, the pivots, the factorizations, the times of reading and solving in seconds, and the
 * factorizations made because the solves had grown more costly than a fresh factorization.
 *
 * <p>Usage: {@code java org.jacop.jalp.LpMain [-noscale] [-limit pivots] [-primal] [-reobjective]
 * file.mps[.gz] ...}
 *
 * <p>{@code -primal} solves with the primal simplex from the slack basis. {@code -reobjective}
 * first solves the problem with no objective by the dual simplex, then sets the objective and
 * solves again from that basis (by the primal simplex with {@code -primal}, by the dual one
 * otherwise); the pivots and the time printed are those of the second solve. The system property
 * {@code org.jacop.jalp.main} (a comma-separated list of {@code primal} and {@code reobjective})
 * sets the same options.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LpMain {

  private static final String[] STATUS = {"OPTIMAL", "INFEASIBLE", "LIMIT", "UNBOUNDED"};

  private LpMain() {}

  /**
   * Solves the files given.
   *
   * @param args the options and files
   * @throws IOException when a file cannot be read
   */
  public static void main(String[] args) throws IOException {
    boolean scale = true;
    int limit = Integer.MAX_VALUE;
    String modes = "," + System.getProperty("org.jacop.jalp.main", "") + ",";
    boolean primal = modes.contains(",primal,");
    boolean reobjective = modes.contains(",reobjective,");
    for (int a = 0; a < args.length; a++) {
      String arg = args[a];
      if (arg.equals("-noscale")) {
        scale = false;
      } else if (arg.equals("-limit")) {
        limit = Integer.parseInt(args[++a]);
      } else if (arg.equals("-primal")) {
        primal = true;
      } else if (arg.equals("-reobjective")) {
        reobjective = true;
      } else {
        long t0 = System.nanoTime();
        LpProblem p = MpsReader.read(Path.of(arg));
        long t1 = System.nanoTime();
        RevisedDualSimplex lp = p.simplex(scale);
        lp.setExact(true);
        long pivots = 0;
        int status;
        if (reobjective) {
          double[] cost = new double[p.columns()];
          lp.setCost(cost);
          status = lp.solve(limit);
          pivots = lp.pivots();
          t1 = System.nanoTime();
          if (status == RevisedDualSimplex.OPTIMAL) {
            lp.setCost(p.maximize ? negate(p.cost) : p.cost);
            status = primal ? lp.solvePrimal(limit) : lp.solve(limit);
          }
        } else {
          status = primal ? lp.solvePrimal(limit) : lp.solve(limit);
        }
        long t2 = System.nanoTime();
        double z = (p.maximize ? -lp.objective() : lp.objective()) + p.costConstant;
        System.out.printf(
            Locale.ROOT,
            "%s %s %.12g pivots %d factors %d read %.3f solve %.3f crash %d work %d%n",
            p.name,
            STATUS[status],
            z,
            lp.pivots() - pivots,
            lp.factorizations(),
            (t1 - t0) / 1e9,
            (t2 - t1) / 1e9,
            lp.crashed(),
            lp.refactorsForWork());
      }
    }
  }

  private static double[] negate(double[] c) {
    double[] r = new double[c.length];
    for (int j = 0; j < c.length; j++) {
      r[j] = -c[j];
    }
    return r;
  }
}
