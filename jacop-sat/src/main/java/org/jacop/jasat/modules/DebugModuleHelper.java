/*
 * DebugModuleHelper.java
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

package org.jacop.jasat.modules;

import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.clauses.MapClause;

/**
 * Helper class for common debug module functionality.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class DebugModuleHelper {

  private DebugModuleHelper() {
    // Utility class
  }

  /**
   * Prints a separator line in debug output.
   *
   * @param core the core instance
   * @param start true for opening line, false for closing line
   */
  public static void printLine(Core core, boolean start) {
    if (start) {
      core.logc(3, "/==================================");
    } else {
      core.logc(3, "\\==================================");
    }
  }

  /** Prints a blank line in debug output. */
  public static void printBlank(Core core) {
    core.logc(3, "");
  }

  /**
   * Prints the trail state for variables in a clause.
   *
   * @param core the core instance
   * @param prefix prefix string for the output
   * @param clause the clause whose variables to print
   */
  public static void printTrail(Core core, String prefix, MapClause clause) {
    StringBuilder sb = new StringBuilder().append("[ ");
    for (int varIdx : clause.literals.keySet()) {
      int value = core.trail.values[varIdx];
      if (value >= 0) {
        sb.append(' ');
      }
      sb.append(value);
      sb.append(' ');
    }
    core.logc(3, prefix + sb.append(']'));
  }

  /**
   * Registers a debug module with the core for all relevant events.
   *
   * @param core the core instance
   * @param module the module to register (must implement all listener interfaces)
   */
  public static void registerModule(
      Core core,
      org.jacop.jasat.modules.interfaces.AssertionListener module1,
      org.jacop.jasat.modules.interfaces.BackjumpListener module2,
      org.jacop.jasat.modules.interfaces.ConflictListener module3,
      org.jacop.jasat.modules.interfaces.ForgetListener module4,
      org.jacop.jasat.modules.interfaces.PropagateListener module5,
      org.jacop.jasat.modules.interfaces.SolutionListener module6,
      org.jacop.jasat.modules.interfaces.ExplanationListener module7,
      org.jacop.jasat.modules.interfaces.ClauseListener module8,
      org.jacop.jasat.modules.interfaces.StartStopListener module9) {
    core.assertionModules[core.numAssertionModules++] = module1;
    core.backjumpModules[core.numBackjumpModules++] = module2;
    core.conflictModules[core.numConflictModules++] = module3;
    core.forgetModules[core.numForgetModules++] = module4;
    core.propagateModules[core.numPropagateModules++] = module5;
    core.solutionModules[core.numSolutionModules++] = module6;
    core.explanationModules[core.numExplanationModules++] = module7;
    core.clauseModules[core.numClauseModules++] = module8;
    core.startStopModules[core.numStartStopModules++] = module9;
  }
}
