/*
 * Langford.java
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

package org.jacop.examples.fd;

import java.util.ArrayList;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Assignment;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * It solves Langford problem.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Langford extends ExampleFd {

  public int n = 3;
  public int m = 17;

  private static final String SOLUTION_FOUND = "Solution(s) found";

  /**
   * It executes the program to solve the Langford problem. It is possible to specify two
   * parameters. If no parameter is used then default values for n and m are used.
   *
   * @param args the first parameter denotes n, the second parameter denotes m.
   */
  public static void test(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    Langford example = new Langford();
    if (args.length > 1) {
      example.n = Integer.parseInt(args[0]);
      example.m = Integer.parseInt(args[1]);
    }

    example.model();

    if (example.search()) {
      log.info(SOLUTION_FOUND);
    }

    Langford exampleBound = new Langford();
    if (args.length > 1) {
      exampleBound.n = Integer.parseInt(args[0]);
      exampleBound.m = Integer.parseInt(args[1]);
    }

    Langford exampleDual = new Langford();
    if (args.length > 1) {
      exampleDual.n = Integer.parseInt(args[0]);
      exampleDual.m = Integer.parseInt(args[1]);
    }
    exampleDual.modelDual();

    if (exampleDual.search()) {
      log.info(SOLUTION_FOUND);
    }
  }

  /**
   * It executes the program to solve the Langford problem. It is possible to specify two
   * parameters. If no parameter is used then default values for n and m are used.
   *
   * @param args the first parameter denotes n, the second parameter denotes m.
   */
  static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    Langford exampleDual = new Langford();
    if (args.length > 1) {
      exampleDual.n = Integer.parseInt(args[0]);
      exampleDual.m = Integer.parseInt(args[1]);
    }
    exampleDual.modelDual();

    if (exampleDual.search()) {
      log.info(SOLUTION_FOUND);
    }
  }

  @Override
  public void model() {

    store = new Store();
    vars = new ArrayList<>();

    // Get problem size n from second program argument.
    IntVar[] x = new IntVar[n * m];

    for (int i = 0; i < n * m; i++) {
      x[i] = new IntVar(store, "x" + i, 1, m * n);
      vars.add(x[i]);
    }

    for (int i = 0; i + 1 < n; i++) {
      for (int j = 0; j < m; j++) {

        store.impose(new XplusCeqZ(x[i * m + j], j + 2, x[(i + 1) * m + j]));
      }
    }

    Constraint cx = new Alldistinct(x);
    store.impose(cx);
  }

  /** It uses the dual model. */
  public void modelDual() {

    store = new Store();
    vars = new ArrayList<>();

    IntVar[] x = new IntVar[n * m];

    for (int i = 0; i < n * m; i++) {
      x[i] = new IntVar(store, "x" + i, 0, m * n - 1);
      vars.add(x[i]);
    }

    for (int i = 0; i + 1 < n; i++) {
      for (int j = 0; j < m; j++) {

        store.impose(new XplusCeqZ(x[i * m + j], j + 2, x[(i + 1) * m + j]));
      }
    }

    Constraint cx = new Alldistinct(x);
    store.impose(cx);

    IntVar[] d = new IntVar[n * m];

    for (int i = 0; i < n * m; i++) {
      d[i] = new IntVar(store, "d" + i, 0, m * n - 1);
      vars.add(d[i]);
    }

    store.impose(new Assignment(x, d));
  }
}
