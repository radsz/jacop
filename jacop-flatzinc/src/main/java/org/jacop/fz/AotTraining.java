/*
 * AotTraining.java
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

import java.util.ArrayList;
import java.util.List;
import lombok.extern.slf4j.Slf4j;

/**
 * Training run for the JVM's ahead-of-time cache (JDK 25, JEP 483/514/515), used by the {@code
 * fzn-jacop-aot} script. It solves several FlatZinc models in one JVM, so that the cache holds the
 * classes and method profiles of the whole front end and not of one model only:
 *
 * <pre>
 * java -XX:AOTCacheOutput=jacop.aot -cp ... org.jacop.fz.AotTraining -t 3000 a.fzn -- --lcg -f a.fzn
 * </pre>
 *
 * <p>The arguments are Fz2jacop command lines separated by {@code --}. The solver output goes to
 * standard output as usual; the training script discards it.
 */
@Slf4j
public final class AotTraining {

  private AotTraining() {}

  /**
   * Runs each command line in turn.
   *
   * @param args Fz2jacop command lines separated by {@code --}
   */
  public static void main(String[] args) {
    List<String> run = new ArrayList<>();
    for (String arg : args) {
      if (arg.equals("--")) {
        solve(run);
        run.clear();
      } else {
        run.add(arg);
      }
    }
    solve(run);
  }

  private static void solve(List<String> run) {
    if (run.isEmpty()) {
      return;
    }
    try {
      new Fz2jacop().callMain(run.toArray(new String[0]));
    } catch (RuntimeException e) {
      // a model that fails still trained the classes it loaded; go on with the next one
      log.warn("AOT training run {} failed", run, e);
    }
  }
}
