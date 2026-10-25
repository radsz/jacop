/*
 * CdclMain.java
 * <p>
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

package org.jacop.jasat.cdcl;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;

/**
 * Command-line front end of {@link CdclSolver}, following the SAT Competition output format.
 *
 * <pre>
 * CdclMain [-t seconds] [-q] [--drat proof-file] [--chrono limit] [--shrink 0|1] [--elim 0|1]
 *          [--vivify 0|1] [--walk 0|1] file.cnf[.gz]
 * </pre>
 *
 * <p>{@code --chrono} sets {@link CdclSolver#setChronoLimit} (negative turns chronological
 * backtracking off), {@code --shrink 0} turns all-UIP shrinking off, {@code --elim 0} turns
 * variable elimination off, {@code --vivify 0} turns vivification off and {@code --walk 0} turns
 * local search off.
 *
 * <p>Prints {@code s SATISFIABLE} with {@code v} lines, {@code s UNSATISFIABLE} or {@code s
 * UNKNOWN}, and exits with 10, 20 or 0.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class CdclMain {

  private CdclMain() {}

  /**
   * Runs the solver on a DIMACS file.
   *
   * @param args the command line
   * @throws IOException if the input or the proof file fails
   */
  public static void main(String[] args) throws IOException {
    long start = System.nanoTime();
    String file = null;
    String proofFile = null;
    boolean quiet = false;
    double timeout = 0;
    int chrono = 100;
    boolean shrink = true;
    boolean elim = true;
    boolean vivify = true;
    boolean walk = true;
    for (int i = 0; i < args.length; i++) {
      switch (args[i]) {
        case "-t" -> timeout = Double.parseDouble(args[++i]);
        case "-q" -> quiet = true;
        case "--drat" -> proofFile = args[++i];
        case "--chrono" -> chrono = Integer.parseInt(args[++i]);
        case "--shrink" -> shrink = !"0".equals(args[++i]);
        case "--elim" -> elim = !"0".equals(args[++i]);
        case "--vivify" -> vivify = !"0".equals(args[++i]);
        case "--walk" -> walk = !"0".equals(args[++i]);
        default -> file = args[i];
      }
    }
    if (file == null) {
      System.err.println(
          "usage: CdclMain [-t seconds] [-q] [--drat proof-file] [--chrono limit] [--shrink 0|1]"
              + " [--elim 0|1] [--vivify 0|1] [--walk 0|1] file.cnf[.gz]");
      System.exit(1);
    }
    CdclSolver solver = new CdclSolver();
    solver.setChronoLimit(chrono);
    solver.setShrink(shrink);
    solver.setElimination(elim);
    solver.setVivification(vivify);
    solver.setWalk(walk);
    if (timeout > 0) {
      solver.setDeadline(start + (long) (timeout * 1e9));
    }
    long parsed;
    int result;
    try (DratWriter proof =
        proofFile == null ? null : new DratWriter(new FileOutputStream(proofFile))) {
      solver.setProof(proof);
      DimacsReader.read(file, solver);
      parsed = System.nanoTime();
      result = solver.solve();
    }
    PrintStream out = new PrintStream(new java.io.BufferedOutputStream(System.out, 1 << 16), false);
    if (!quiet) {
      out.printf(
          "c vars %d, parse %.2f s, solve %.2f s%n",
          solver.numVars(), (parsed - start) / 1e9, (System.nanoTime() - parsed) / 1e9);
      out.printf(
          "c conflicts %d, decisions %d, propagations %d, restarts %d, reductions %d%n",
          solver.conflicts,
          solver.decisions,
          solver.propagations,
          solver.restarts,
          solver.reductions);
      out.printf(
          "c eliminated variables %d, walk %.2f s%n",
          solver.eliminatedCount(), solver.walkNanos / 1e9);
    }
    if (result == CdclSolver.SAT) {
      out.println("s SATISFIABLE");
      StringBuilder line = new StringBuilder("v");
      for (int v = 1; v <= solver.numVars(); v++) {
        line.append(' ').append(solver.modelValue(v) ? v : -v);
        if (line.length() > 70) {
          out.println(line);
          line.setLength(0);
          line.append('v');
        }
      }
      line.append(" 0");
      out.println(line);
    } else if (result == CdclSolver.UNSAT) {
      out.println("s UNSATISFIABLE");
    } else {
      out.println("s UNKNOWN");
    }
    out.flush();
    System.exit(result);
  }
}
