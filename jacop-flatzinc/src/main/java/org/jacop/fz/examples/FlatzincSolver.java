/*
 * FlatzincSolver.java
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

package org.jacop.fz.examples;

import lombok.extern.slf4j.Slf4j;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.fz.FlatzincLoader;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.SelectChoicePoint;

/**
 * The class Run is used to run test programs for JaCoP package. It is used for test purpose only.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class FlatzincSolver {

  FlatzincSolver() {}

  static void main(String[] args) {

    FlatzincSolver run = new FlatzincSolver();

    run.ex(args);
  }

  void ex(String[] args) {

    long t1 = System.currentTimeMillis();

    if (args.length == 0) {
      args = new String[2];
      args[0] = "-s";
      args[1] = "wilkinson.fzn";
    }
    FlatzincLoader fl = new FlatzincLoader(args);
    fl.load();

    Store store = fl.getStore();
    printStoreStats(store);

    DepthFirstSearch<Var> label = fl.getDfs();
    SelectChoicePoint<Var> select = fl.getSelectChoicePoint();
    Var cost = fl.getCost();

    boolean result = runSearch(label, fl.getStore(), select, cost);

    if (!fl.getOptions().getAll() && fl.getSolve().lastSolution != null) {
      IO.print(fl.getSolve().lastSolution);
    }

    fl.getSolve().statistics(result);
    printResult(result);
    printExecutionTime(t1);
  }

  /** Prints store statistics. */
  private void printStoreStats(Store store) {
    log.info(
        "\nIntVar store size: "
            + store.size()
            + "\nNumber of constraints: "
            + store.numberConstraints());
  }

  /** Runs search with optional cost variable. */
  private boolean runSearch(
      DepthFirstSearch<Var> label, Store store, SelectChoicePoint<Var> select, Var cost) {
    if (cost != null) {
      return label.labeling(store, select, cost);
    } else {
      return label.labeling(store, select);
    }
  }

  /** Prints search result. */
  private void printResult(boolean result) {
    if (result) {
      log.info("*** Yes");
    } else {
      log.info("*** No");
    }
  }

  /** Prints execution time. */
  private void printExecutionTime(long startTime) {
    long t2 = System.currentTimeMillis();
    long t = t2 - startTime;
    log.info("\n\t*** Execution time = " + t + " ms");
  }
}
