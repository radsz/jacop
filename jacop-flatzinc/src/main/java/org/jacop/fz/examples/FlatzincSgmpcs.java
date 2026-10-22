/*
 * FlatzincSgmpcs.java
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
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.fz.FlatzincLoader;
import org.jacop.search.sgmpcs.SgmpcsSearch;

/**
 * The class Run is used to run test programs for JaCoP package. It is used for test purpose only.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class FlatzincSgmpcs {

  FlatzincSgmpcs() {}

  static void main(String[] args) {

    FlatzincSgmpcs run = new FlatzincSgmpcs();

    run.ex(args);
  }

  void ex(String[] args) {

    final long t1 = System.currentTimeMillis();

    if (args.length == 0) {
      args = new String[2];
      args[0] = "-s";
      args[1] = "jobshop.fzn";
    }
    FlatzincLoader fl = new FlatzincLoader(args);
    fl.load();

    Store store = fl.getStore();
    printStoreStats(store);

    validateSearchType(fl);
    validateSolveKind(fl);

    int timeOut = fl.getOptions().getTimeOut();
    if (timeOut == 0) {
      timeOut = 900; // default time-out 900s=15min
    }
    IntVar[] vars = (IntVar[]) fl.getSearch().vars();
    IntVar cost = (IntVar) fl.getCost();

    SgmpcsSearch label = new SgmpcsSearch(store, vars, cost);
    label.setFailStrategy(SgmpcsSearch.LUBY); // luby or poly
    label.setProbability(0.25); // limit for probability of selecting search from empty
    label.setEliteSize(4); // size of the set of reference solutions
    label.setTimeOut(timeOut); // time-out in seconds
    label.setInitialSolutionsSize(10); // size of the random initial solutions

    label.setPrintInfo(true);

    boolean result = label.search();
    printSgmpcsResult(result, label);

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

  /** Validates that search type is int_search. */
  private void validateSearchType(FlatzincLoader fl) {
    if (fl.getSearch().type() == null || (!"int_search".equals(fl.getSearch().type()))) {
      throw new RuntimeException(
          "The problem is not of type int_search and cannot be handled by this method");
    }
  }

  /** Validates that solve kind is minimization. */
  private void validateSolveKind(FlatzincLoader fl) {
    if (fl.getSolve().getSolveKind() != 1) {
      throw new RuntimeException(
          "The problem is not minimization problem and cannot be handled by this method");
    }
  }

  /** Prints SGMPCS search result. */
  private void printSgmpcsResult(boolean result, SgmpcsSearch label) {
    if (result) {
      int[] sol = label.lastSolution();
      if (sol != null) {
        log.info("\n%%% Last found solution with cost " + label.lastCost());
        for (int j : sol) {
          IO.print(j + " ");
        }
      } else {
        log.info("\n%%% No solution found with this method");
      }
    }
  }

  /** Prints execution time. */
  private void printExecutionTime(long startTime) {
    long t2 = System.currentTimeMillis();
    long t = t2 - startTime;
    log.info("\n\t*** Execution time = " + t + " ms");
  }
}
