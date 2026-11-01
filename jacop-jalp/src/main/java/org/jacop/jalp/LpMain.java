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
 * objective, the pivots and the time in seconds.
 *
 * <p>Usage: {@code java org.jacop.jalp.LpMain [-noscale] [-limit pivots] file.mps[.gz] ...}
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
    for (int a = 0; a < args.length; a++) {
      String arg = args[a];
      if (arg.equals("-noscale")) {
        scale = false;
      } else if (arg.equals("-limit")) {
        limit = Integer.parseInt(args[++a]);
      } else {
        long t0 = System.nanoTime();
        LpProblem p = MpsReader.read(Path.of(arg));
        long t1 = System.nanoTime();
        RevisedDualSimplex lp = p.simplex(scale);
        lp.setExact(true);
        int status = lp.solve(limit);
        long t2 = System.nanoTime();
        double z = lp.objective() + p.costConstant;
        System.out.printf(
            Locale.ROOT,
            "%s %s %.12g pivots %d factors %d read %.3f solve %.3f%n",
            p.name,
            STATUS[status],
            p.maximize ? z : z,
            lp.pivots(),
            lp.factorizations(),
            (t1 - t0) / 1e9,
            (t2 - t1) / 1e9);
      }
    }
  }
}
