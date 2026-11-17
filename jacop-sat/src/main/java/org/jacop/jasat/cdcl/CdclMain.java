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
 *          [--factor 0|1] [--factor-effort n] [--vivify 0|1] [--walk 0|1] [--jump share] [--ema 0|1]
 *          [--seed n] [--elim-interval conflicts] [--lucky 0|1] [--sweep 0|1] [--probe 0|1]
 *          [--substitute 0|1] [--congruence 0|1]
 *          file.cnf[.gz]
 * </pre>
 *
 * <p>{@code --chrono} sets {@link CdclSolver#setChronoLimit} (negative turns chronological
 * backtracking off), {@code --shrink 0} turns all-UIP shrinking off, {@code --elim 0} turns
 * variable elimination off, {@code --factor 0} turns bounded variable addition off ({@code
 * --factor-effort} bounds its work), {@code --vivify 0} turns vivification off and {@code --walk 0}
 * turns local search off. {@code --jump} sets the share of the time given to the feasibility-jump
 * local search ({@link CdclSolver#setJumpShare}, 0 turns it off). {@code --ema 0} restarts on
 * Glucose's LBD queue instead of fast and slow LBD averages. {@code --seed} changes the initial
 * decision order and {@code --elim-interval} sets when elimination runs again during search (0 for
 * never). {@code --lucky 0} turns the lucky assignments before the search off ({@link
 * CdclSolver#setLucky}). {@code --sweep 0} turns SAT sweeping off and {@code --probe 0}
 * failed-literal probing off (both on here, off by default in {@link CdclSolver}). {@code
 * --substitute 0} turns equivalent-literal substitution off and {@code --congruence 0} its
 * congruence closure on gates.
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
    boolean factor = true;
    long factorEffort = -1;
    boolean vivify = true;
    boolean ema = true;
    boolean walk = true;
    double jump = CdclSolver.DEFAULT_JUMP_SHARE;
    boolean lucky = true;
    long seed = 0;
    int elimInterval = 5000;
    boolean sweep = true;
    boolean probe = true;
    boolean substitute = true;
    boolean congruence = true;
    for (int i = 0; i < args.length; i++) {
      switch (args[i]) {
        case "-t" -> timeout = Double.parseDouble(args[++i]);
        case "-q" -> quiet = true;
        case "--drat" -> proofFile = args[++i];
        case "--chrono" -> chrono = Integer.parseInt(args[++i]);
        case "--shrink" -> shrink = !"0".equals(args[++i]);
        case "--elim" -> elim = !"0".equals(args[++i]);
        case "--factor" -> factor = !"0".equals(args[++i]);
        case "--factor-effort" -> factorEffort = Long.parseLong(args[++i]);
        case "--vivify" -> vivify = !"0".equals(args[++i]);
        case "--ema" -> ema = !"0".equals(args[++i]);
        case "--walk" -> walk = !"0".equals(args[++i]);
        case "--jump" -> jump = Double.parseDouble(args[++i]);
        case "--lucky" -> lucky = !"0".equals(args[++i]);
        case "--seed" -> seed = Long.parseLong(args[++i]);
        case "--elim-interval" -> elimInterval = Integer.parseInt(args[++i]);
        case "--sweep" -> sweep = !"0".equals(args[++i]);
        case "--probe" -> probe = !"0".equals(args[++i]);
        case "--substitute" -> substitute = !"0".equals(args[++i]);
        case "--congruence" -> congruence = !"0".equals(args[++i]);
        default -> file = args[i];
      }
    }
    if (file == null) {
      System.err.println(
          "usage: CdclMain [-t seconds] [-q] [--drat proof-file] [--chrono limit] [--shrink 0|1]"
              + " [--elim 0|1] [--factor 0|1] [--factor-effort n] [--vivify 0|1] [--walk 0|1]"
              + " [--jump share] [--ema 0|1] [--seed n]"
              + " [--elim-interval conflicts] [--lucky 0|1] [--sweep 0|1] [--probe 0|1]"
              + " [--substitute 0|1] [--congruence 0|1] file.cnf[.gz]");
      System.exit(1);
    }
    CdclSolver solver = new CdclSolver();
    solver.setChronoLimit(chrono);
    solver.setShrink(shrink);
    solver.setElimination(elim);
    solver.setFactoring(factor);
    if (factorEffort >= 0) {
      solver.setFactorEffort(factorEffort);
    }
    solver.setVivification(vivify);
    solver.setEmaRestarts(ema);
    solver.setWalk(walk);
    solver.setJumpShare(jump);
    solver.setLucky(lucky);
    solver.setSeed(seed);
    solver.setEliminationInterval(elimInterval);
    solver.setSweeping(sweep);
    solver.setProbing(probe);
    solver.setSubstitution(substitute);
    solver.setCongruence(congruence);
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
          "c eliminated variables %d, walk %.2f s, jump %.2f s (%d calls, %d models, solved %b)%n",
          solver.eliminatedCount(),
          solver.walkNanos / 1e9,
          solver.jumpNanos / 1e9,
          solver.jumpCalls,
          solver.jumpModels(),
          solver.jumpSolved());
      out.printf(
          "c substituted variables %d, scc equivalences %d, gate equivalences %d, gates %d,"
              + " substitution %.2f s%n",
          solver.substitutedVars,
          solver.sccEquivalences,
          solver.gateEquivalences,
          solver.gatesFound,
          solver.substitutionNanos / 1e9);
      out.printf(
          "c factored variables %d, clauses %d, effort %d, factor %.2f s%n",
          solver.factoredVars, solver.factoredClauses, solver.factorWork, solver.factorNanos / 1e9);
      out.printf(
          "c vivify tried %d (irredundant %d), probes %d, reused %d, strengthened %d (irredundant %d),"
              + " removed %d (irredundant %d), %.2f s%n",
          solver.vivifyTried,
          solver.vivifyTriedIrredundant,
          solver.vivifyProbes,
          solver.vivifyReused,
          solver.vivifyStrengthened,
          solver.vivifyStrengthenedIrredundant,
          solver.vivifyRemoved,
          solver.vivifyRemovedIrredundant,
          solver.vivifyNanos / 1e9);
      out.printf(
          "c lucky %s, %.2f s%n",
          solver.luckyFound == null ? "none" : solver.luckyFound, solver.luckyNanos / 1e9);
      if (sweep) {
        out.printf(
            "c swept variables %d, sweep units %d, sweep equivalences %d, sweep %.2f s%n",
            solver.sweptVariables,
            solver.sweepUnits,
            solver.sweepEquivalences,
            solver.sweepNanos / 1e9);
      }
      if (probe) {
        out.printf(
            "c probed literals %d, failed literals %d, lifted units %d, probe equivalences %d,"
                + " probe %.2f s%n",
            solver.probedLiterals,
            solver.failedLiterals,
            solver.liftedUnits,
            solver.probeEquivalences,
            solver.probeNanos / 1e9);
      }
    }
    if (result == CdclSolver.SAT) {
      out.println("s SATISFIABLE");
      StringBuilder line = new StringBuilder("v");
      for (int v = 1; v <= solver.numInputVars(); v++) {
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
