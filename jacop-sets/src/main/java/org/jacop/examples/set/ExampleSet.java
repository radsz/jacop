/*
 * Examples.java
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

package org.jacop.examples.set;

import java.util.List;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.MostConstrainedStatic;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.jacop.search.WeightedDegree;
import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMin;

/**
 * It is an abstract class to describe all necessary functions of any store.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public abstract class ExampleSet {

  /** It contains all variables used within a specific example. */
  public List<SetVar> vars;

  /** It specifies the cost function, null if no cost function is used. */
  public IntVar cost;

  /**
   * It specifies the constraint store responsible for holding information about constraints and
   * variables.
   */
  public Store store;

  /** It specifies the search procedure used by a given example. */
  public Search<SetVar> searchLabel;

  /**
   * It prints a matrix of variables. All variables must be grounded.
   *
   * @param matrix matrix containing the grounded variables.
   * @param rows number of elements in the first dimension.
   * @param cols number of elements in the second dimension.
   */
  public static void printMatrix(IntVar[][] matrix, int rows, int cols) {

    for (int i = 0; i < rows; i++) {
      for (int j = 0; j < cols; j++) {
        IO.print(matrix[i][j].value() + " ");
      }
      IO.println();
    }
  }

  /** It specifies a standard way of modeling the problem. */
  public abstract void model();

  /** Prints search statistics (nodes, decisions, wrong decisions, backtracks, max depth). */
  protected void printSearchStats() {
    IO.println();
    IO.print(searchLabel.getNodes() + "\t");
    IO.print(searchLabel.getDecisions() + "\t");
    IO.print(searchLabel.getWrongDecisions() + "\t");
    IO.print(searchLabel.getBacktracks() + "\t");
    IO.print(searchLabel.getMaximumDepth() + "\t");
  }

  /** Prints execution time in ms since the given start time. */
  protected void printExecutionTime(long t1) {
    IO.println("\n\t*** Execution time = " + (System.currentTimeMillis() - t1) + " ms");
  }

  /**
   * It specifies simple search method based on input order and lexigraphical ordering of values.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean search() {

    long T1;
    long T2;
    T1 = System.currentTimeMillis();

    SelectChoicePoint<SetVar> select =
        new SimpleSelect<>(vars.toArray(new SetVar[1]), null, new IndomainSetMin<>());

    searchLabel = new DepthFirstSearch<>();

    boolean result = searchLabel.labeling(store, select);

    if (result) {
      store.print();
    }

    printExecutionTime(T1);
    printSearchStats();
    return result;
  }

  /**
   * It specifies simple search method based on input order and lexigraphical ordering of values. It
   * optimizes the solution by minimizing the cost function.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchOptimal() {

    long T1;
    long T2;
    T1 = System.currentTimeMillis();

    SelectChoicePoint<SetVar> select =
        new SimpleSelect<>(vars.toArray(new SetVar[1]), null, new IndomainSetMin<>());

    searchLabel = new DepthFirstSearch<>();

    boolean result = searchLabel.labeling(store, select, cost);

    if (result) {
      store.print();
    }
    printExecutionTime(T1);
    return result;
  }

  /**
   * It searches for all solutions with the optimal value.
   *
   * @return true if any optimal solution has been found.
   */
  public boolean searchAllOptimal() {

    final long T1 = System.currentTimeMillis();

    SelectChoicePoint<SetVar> select =
        new SimpleSelect<>(vars.toArray(new SetVar[1]), null, new IndomainSetMin<>());

    searchLabel = new DepthFirstSearch<>();
    searchLabel.getSolutionListener().searchAll(true);
    searchLabel.getSolutionListener().recordSolutions(true);

    boolean result = searchLabel.labeling(store, select, cost);
    printExecutionTime(T1);
    return result;
  }

  /**
   * It specifies simple search method based on smallest domain variable order and lexigraphical
   * ordering of values.
   *
   * @param optimal it specifies if the search the optimal solution takes place.
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchSmallestDomain(boolean optimal) {

    final long T1 = System.currentTimeMillis();

    SelectChoicePoint<SetVar> select =
        new SimpleSelect<>(
            vars.toArray(new SetVar[1]), new SmallestDomain<>(), new IndomainSetMin<>());

    searchLabel = new DepthFirstSearch<>();

    if (optimal) {
      searchLabel.labeling(store, select, cost);
    } else {
      searchLabel.labeling(store, select);
    }

    final boolean result = false;
    printSearchStats();
    printExecutionTime(T1);
    return result;
  }

  /**
   * It specifies simple search method based on weighted degree variable order and lexigraphical
   * ordering of values. This search method is rather general any problem good fit. It can be a good
   * first trial to see if the model is correct.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchWeightedDegree() {

    final long T1 = System.currentTimeMillis();

    SelectChoicePoint<SetVar> select =
        new SimpleSelect<>(
            vars.toArray(new SetVar[1]),
            new WeightedDegree<>(store),
            new SmallestDomain<>(),
            new IndomainSetMin<>());

    searchLabel = new DepthFirstSearch<>();

    final boolean result = searchLabel.labeling(store, select);
    printSearchStats();
    if (result) {
      store.print();
    }
    printExecutionTime(T1);
    return result;
  }

  /**
   * It specifies simple search method based variable order which takes into account the number of
   * constraints attached to a variable and lexigraphical ordering of values.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchMostConstrainedStatic() {

    searchLabel = new DepthFirstSearch<>();

    SelectChoicePoint<SetVar> select =
        new SimpleSelect<>(
            vars.toArray(new SetVar[1]), new MostConstrainedStatic<>(), new IndomainSetMin<>());

    final boolean result = searchLabel.labeling(store, select);
    printSearchStats();
    if (!result) {
      IO.println("**** No Solution ****");
    }
    return result;
  }

  /**
   * It specifies simple search method based on most constrained static and lexigraphical ordering
   * of values. It searches for all solutions.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchAllAtOnce() {

    final long T1 = System.currentTimeMillis();

    SelectChoicePoint<SetVar> select =
        new SimpleSelect<>(
            vars.toArray(new SetVar[1]), new MostConstrainedStatic<>(), new IndomainSetMin<>());

    searchLabel = new DepthFirstSearch<>();

    searchLabel.getSolutionListener().searchAll(true);
    searchLabel.getSolutionListener().recordSolutions(true);
    searchLabel.setAssignSolution(true);

    boolean result = searchLabel.labeling(store, select);

    if (result) {
      IO.println("Number of solutions " + searchLabel.getSolutionListener().solutionsNo());
    } else {
      IO.println("Failed to find any solution");
    }
    printExecutionTime(T1);
    return result;
  }

  /**
   * It conducts master-slave search. Both of them use input order variable ordering.
   *
   * @param masterVars it specifies the search variables used in master search.
   * @param slaveVars it specifies the search variables used in slave search.
   * @return true if the solution exists, false otherwise.
   */
  public boolean searchMasterSlave(List<Var> masterVars, List<Var> slaveVars) {

    final long T1 = System.currentTimeMillis();

    Search<SetVar> labelSlave = new DepthFirstSearch<>();
    SelectChoicePoint<SetVar> selectSlave =
        new SimpleSelect<>(slaveVars.toArray(new SetVar[0]), null, new IndomainSetMin<>());
    labelSlave.setSelectChoicePoint(selectSlave);

    Search<SetVar> labelMaster = new DepthFirstSearch<>();
    SelectChoicePoint<SetVar> selectMaster =
        new SimpleSelect<>(masterVars.toArray(new SetVar[0]), null, new IndomainSetMin<>());

    labelMaster.addChildSearch(labelSlave);

    searchLabel = labelMaster;

    boolean result = labelMaster.labeling(store, selectMaster);

    if (result) {
      IO.println("Solution found");
    }

    if (result) {
      store.print();
    }
    printExecutionTime(T1);
    return result;
  }

  /**
   * It returns the search used within an example.
   *
   * @return the search used within an example.
   */
  public Search<SetVar> getSearch() {
    return searchLabel;
  }

  /**
   * It specifies the constraint store used within an example.
   *
   * @return constraint store used within an example.
   */
  public Store getStore() {
    return store;
  }

  /**
   * It returns an array list of variables used to model the example.
   *
   * @return the array list of variables used to model the example.
   */
  public List<SetVar> getSearchVariables() {
    return vars;
  }
}
