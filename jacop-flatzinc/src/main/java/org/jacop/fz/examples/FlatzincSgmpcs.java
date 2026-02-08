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
public class FlatzincSgmpcs {

  FlatzincSgmpcs() {}

  static void main(String[] args) {

    FlatzincSgmpcs run = new FlatzincSgmpcs();

    run.ex(args);
  }

  void ex(String[] args) {

    long T1;
    T1 = System.currentTimeMillis();

    if (args.length == 0) {
      args = new String[2];
      args[0] = "-s";
      args[1] = "jobshop.fzn";
    }
    FlatzincLoader fl = new FlatzincLoader(args);
    fl.load();

    Store store = fl.getStore();

    IO.println(
        "\nIntVar store size: "
            + store.size()
            + "\nNumber of constraints: "
            + store.numberConstraints());

    if (fl.getSearch().type() == null || (!"int_search".equals(fl.getSearch().type()))) {
      throw new RuntimeException(
          "The problem is not of type int_search and cannot be handled by this method");
    }

    if (fl.getSolve().getSolveKind() != 1) {
      throw new RuntimeException(
          "The problem is not minimization problem and cannot be handled by this method");
    }

    int timeOut = fl.getOptions().getTimeOut();
    if (timeOut == 0) {
      timeOut = 900; // default time-out 900s=15min
    }
    IntVar[] vars = (IntVar[]) fl.getSearch().vars();
    IntVar cost = (IntVar) fl.getCost();

    SgmpcsSearch label = new SgmpcsSearch(store, vars, cost);
    label.setFailStrategy(SgmpcsSearch.luby); // luby or poly
    label.setProbability(0.25); // limit for probability of selecting search from empty
    label.setEliteSize(4); // size of the set of reference solutions
    label.setTimeOut(timeOut); // time-out in seconds
    label.setInitialSolutionsSize(10); // size of the random initial solutions

    label.setPrintInfo(true);

    boolean Result = label.search();

    if (Result) {
      int[] sol = label.lastSolution();
      if (sol != null) {
        IO.println("\n%%% Last found solution with cost " + label.lastCost());
        for (int j : sol) {
          IO.print(j + " ");
        }
      } else {
        IO.println("\n%%% No solution found with this method");
      }
    }

    long T2 = System.currentTimeMillis();
    long T = T2 - T1;
    IO.println("\n\t*** Execution time = " + T + " ms");
  }
}
