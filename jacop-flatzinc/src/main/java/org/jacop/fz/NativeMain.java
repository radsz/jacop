/*
 * NativeMain.java
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

/**
 * Entry point of {@code fzn-jacop-native}, the GraalVM native image of the FlatZinc front end (made
 * by the {@code fzn-jacop-native-build} script). A native image starts in a few milliseconds and
 * runs compiled code from its first instruction, where the JVM needs about 0.1 s to start and runs
 * JaCoP in its interpreter until the JIT compilers catch up; on easy models the whole run then
 * takes 0.03-0.1 s instead of 0.3-0.6 s (osolpro benchmarks/native-startup).
 *
 * <p>The main thread of a native image has the stack of the operating system (often 8 MB), and
 * {@code -Xss} only sets the stack of new threads. The solver therefore runs in a thread of its
 * own, with the stack the JVM launchers give it ({@code -Xss100M}); {@code
 * -Dorg.jacop.fz.stackMB=...} changes it.
 */
public final class NativeMain {

  /** Stack of the solver thread in MB, as -Xss100M of the fzn-jacop launcher. */
  static final long STACK_MB = Long.getLong("org.jacop.fz.stackMB", 100);

  private NativeMain() {}

  /**
   * Runs {@link Fz2jacop} in a thread with a large stack and waits for it.
   *
   * @param args the arguments of fzn-jacop
   * @throws InterruptedException never in practice; the main thread only waits
   */
  public static void main(String[] args) throws InterruptedException {
    Thread solver = new Thread(null, () -> new Fz2jacop().main(args), "main", STACK_MB << 20);
    // as an exception that leaves main ends the JVM with status 1, after the same report
    solver.setUncaughtExceptionHandler(
        (t, e) -> {
          t.getThreadGroup().uncaughtException(t, e);
          System.exit(1);
        });
    solver.start();
    solver.join();
  }
}
