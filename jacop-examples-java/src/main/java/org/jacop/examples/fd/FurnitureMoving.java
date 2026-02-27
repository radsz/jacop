/*
 * FurnitureMoving.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Hakan Kjellerstrand and Radoslaw Szymanek
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
import java.util.Arrays;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;

/**
 * It is a simple logic puzzle about furniture moving.
 *
 * <p>Problem from Marriott {@literal &} Stuckey: 'Programming with constraints', page 112f
 *
 * <p>Feature: testing cumulative.
 *
 * <p>Also see <a href="http://www.hakank.org/JaCoP/">...</a>
 *
 * @author Hakan Kjellerstrand (hakank@bonetmail.com) and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class FurnitureMoving extends ExampleFd {

  private static final boolean GENERATE_ALL = true;

  IntVar[] starts;
  IntVar[] endTimes;

  /**
   * It executes the program which solves this logic puzzle.
   *
   * @param args command arguments (none)
   */
  static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    long t1;
    long t2;
    long t;
    t1 = System.currentTimeMillis();

    FurnitureMoving example = new FurnitureMoving();
    example.model();

    example.searchSpecific();

    t2 = System.currentTimeMillis();
    t = t2 - t1;
    log.info("\n\t*** Execution time = " + t + " ms");
  }

  @Override
  public void model() {

    store = new Store();

    final IntVar numPersons = new IntVar(store, "numPersons", 2, 5); // will be minimized
    final IntVar maxTime = new IntVar(store, "maxTime", 60, 60);

    // Start times
    IntVar sp = new IntVar(store, "Sp", 0, 60); // Piano
    IntVar sc = new IntVar(store, "Sc", 0, 60); // Chair
    IntVar sb = new IntVar(store, "Sb", 0, 60); // Bed
    IntVar st = new IntVar(store, "St", 0, 60); // Table
    final IntVar sumStartTimes = new IntVar(store, "SumStartTimes", 0, 1000);

    starts = new IntVar[4];
    starts[0] = sp;
    starts[1] = sc;
    starts[2] = sb;
    starts[3] = st;

    store.impose(new SumInt(starts, "==", sumStartTimes));

    IntVar[] durations = new IntVar[4];
    IntVar[] resources = new IntVar[4];
    endTimes = new IntVar[4];

    int[] durationsInts = {30, 10, 15, 15}; // duration of task
    int[] resourcesInts = {3, 1, 3, 2}; // resources: num persons required for each task
    for (int i = 0; i < durationsInts.length; i++) {
      // converts to FDV
      durations[i] = new IntVar(store, "dur_" + i, durationsInts[i], durationsInts[i]);
      // converts to FDV
      resources[i] = new IntVar(store, "res_" + i, resourcesInts[i], resourcesInts[i]);

      // all tasks must be finished in 60 minutes
      endTimes[i] = new IntVar(store, "end_" + i, 0, 120);
      store.impose(new XplusYeqZ(starts[i], durations[i], endTimes[i]));
      store.impose(new XlteqY(endTimes[i], maxTime));
    }

    store.impose(new Cumulative(starts, durations, resources, numPersons));

    if (GENERATE_ALL) {
      // generate all optimal solutions
      store.impose(new XeqC(numPersons, 3));
    }

    vars = new ArrayList<>();

    vars.addAll(Arrays.asList(starts));

    vars.addAll(Arrays.asList(endTimes));

    vars.add(numPersons);

    cost = numPersons;
  }

  /**
   * It specifies search for that logic puzzle.
   *
   * @return true when solution is found false otherwise
   */
  public boolean searchSpecific() {

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]), new SmallestDomain<>(), new IndomainMin<>());

    searchLabel = new DepthFirstSearch<>();
    searchLabel.getSolutionListener().searchAll(true);
    searchLabel.getSolutionListener().recordSolutions(true);

    boolean result;
    if (GENERATE_ALL) {
      // Generate all optimal solutions.
      // Note: Gives null pointer exception when searchAll(true)
      result = searchLabel.labeling(store, select);
    } else {
      // minimize over numPersons
      result = searchLabel.labeling(store, select, cost);
    }

    Var[] variables = searchLabel.getSolutionListener().getVariables();
    for (int i = 0; i < variables.length; i++) {
      log.info("Variable " + i + " " + variables[i]);
    }

    if (result) {

      searchLabel.printAllSolutions();

      log.info("\nNumber of persons needed: " + cost.value());
      log.info(
          "Piano: "
              + starts[0].value()
              + " .. "
              + endTimes[0].value()
              + "\n"
              + "Chair: "
              + starts[1].value()
              + " .. "
              + endTimes[1].value()
              + "\n"
              + "Bed  : "
              + starts[2].value()
              + " .. "
              + endTimes[2].value()
              + "\n"
              + "Table: "
              + starts[3].value()
              + " .. "
              + endTimes[3].value());
    } // end if result

    return result;
  } // end main
} // end class FurnitureMoving
