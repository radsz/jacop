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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.examples.fd;

import java.util.List;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.CreditCalculator;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMedian;
import org.jacop.search.IndomainMiddle;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainSimpleRandom;
import org.jacop.search.Lds;
import org.jacop.search.MaxRegret;
import org.jacop.search.MostConstrainedStatic;
import org.jacop.search.NoGoodsCollector;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.Shaving;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.jacop.search.SmallestMin;
import org.jacop.search.WeightedDegree;

/**
 * It is an abstract class to describe all necessary functions of any store.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public abstract class ExampleFd {

  /** It contains all variables used within a specific example. */
  public List<IntVar> vars;

  /** It specifies the cost function, null if no cost function is used. */
  public IntVar cost;

  /**
   * It specifies the constraint store responsible for holding information about constraints and
   * variables.
   */
  public Store store;

  private static final String EXECUTION_TIME_PREFIX = "\n\t*** Execution time = ";
  private static final String FAILED_TO_FIND_SOLUTION = "Failed to find any solution";
  private static final String NUMBER_OF_MILLISECONDS = "Number of milliseconds ";

  /** It specifies the search procedure used by a given example. */
  public Search<IntVar> searchLabel;

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
    IO.println(EXECUTION_TIME_PREFIX + (System.currentTimeMillis() - t1) + " ms");
  }

  /**
   * It specifies simple search method based on input order and lexigraphical ordering of values.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean search() {

    long t1;
    long t2;
    t1 = System.currentTimeMillis();

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(vars.toArray(new IntVar[1]), null, new IndomainMin<>());

    searchLabel = new DepthFirstSearch<>();

    boolean result = searchLabel.labeling(store, select);

    if (result) {
      store.print();
    }

    printExecutionTime(t1);
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

    long t1;
    long t2;
    t1 = System.currentTimeMillis();

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(vars.toArray(new IntVar[1]), null, new IndomainMin<>());

    searchLabel = new DepthFirstSearch<>();

    boolean result = searchLabel.labeling(store, select, cost);

    if (result) {
      store.print();
    }

    printExecutionTime(t1);
    return result;
  }

  /**
   * It searches for all solutions with the optimal value.
   *
   * @return true if any optimal solution has been found.
   */
  public boolean searchAllOptimal() {

    final long t1 = System.currentTimeMillis();

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(vars.toArray(new IntVar[1]), null, new IndomainMin<>());

    searchLabel = new DepthFirstSearch<>();
    searchLabel.getSolutionListener().searchAll(true);
    searchLabel.getSolutionListener().recordSolutions(true);

    boolean result = searchLabel.labeling(store, select, cost);

    long t2 = System.currentTimeMillis();
    long t = t2 - t1;
    IO.println(EXECUTION_TIME_PREFIX + t + " ms");

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

    final long t1 = System.currentTimeMillis();

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]), new SmallestDomain<>(), new IndomainMin<>());

    searchLabel = new DepthFirstSearch<>();

    if (optimal) {
      searchLabel.labeling(store, select, cost);
    } else {
      searchLabel.labeling(store, select);
    }

    final boolean result = false;
    printSearchStats();
    printExecutionTime(t1);
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

    final long t1 = System.currentTimeMillis();

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]),
            new WeightedDegree<>(store),
            new SmallestDomain<>(),
            new IndomainMin<>());

    searchLabel = new DepthFirstSearch<>();

    final boolean result = searchLabel.labeling(store, select);
    printSearchStats();
    if (result) {
      store.print();
    }
    printExecutionTime(t1);
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

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]), new MostConstrainedStatic<>(), new IndomainMin<>());

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

    final long t1 = System.currentTimeMillis();

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]), new MostConstrainedStatic<>(), new IndomainMin<>());

    searchLabel = new DepthFirstSearch<>();

    searchLabel.getSolutionListener().searchAll(true);
    searchLabel.getSolutionListener().recordSolutions(true);
    searchLabel.setAssignSolution(true);

    boolean result = searchLabel.labeling(store, select);

    if (result) {
      IO.println("Number of solutions " + searchLabel.getSolutionListener().solutionsNo());
    } else {
      IO.println(FAILED_TO_FIND_SOLUTION);
    }
    printExecutionTime(t1);
    return result;
  }

  /**
   * It searches using an input order search with indomain based on middle value.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchMiddle() {

    long begin = System.currentTimeMillis();

    searchLabel = new DepthFirstSearch<>();

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(vars.toArray(new IntVar[1]), null, new IndomainMiddle<>());

    boolean result = searchLabel.labeling(store, select);

    long end = System.currentTimeMillis();

    IO.println(NUMBER_OF_MILLISECONDS + (end - begin));

    return result;
  }

  /**
   * It searches with shaving which is guided by supplied constraints.
   *
   * @param guidingShaving the array of constraints proposing shaving candidates.
   * @param printInfo it specifies if that function should print any info.
   * @return true if the solution was found, false otherwise.
   */
  public boolean shavingSearch(List<Constraint> guidingShaving, boolean printInfo) {

    Shaving<IntVar> shaving = new Shaving<>();
    shaving.setStore(store);
    shaving.quickShave = true;

    for (Constraint c : guidingShaving) {
      shaving.addShavingConstraint(c);
    }

    long begin = System.currentTimeMillis();

    searchLabel = new DepthFirstSearch<>();
    searchLabel.setPrintInfo(printInfo);

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(vars.toArray(new IntVar[1]), null, new IndomainMiddle<>());

    searchLabel.setConsistencyListener(shaving);
    searchLabel.setExitChildListener(shaving);

    boolean result = searchLabel.labeling(store, select);

    long end = System.currentTimeMillis();

    if (printInfo) {
      IO.println(NUMBER_OF_MILLISECONDS + (end - begin));
      IO.println("Ratio " + (shaving.successes * 100 / (shaving.successes + shaving.failures)));

      if (result) {
        store.print();
      }
    }

    return result;
  }

  /**
   * It conducts the search with restarts from which the no-goods are derived. Every search
   * contributes with new no-goods which are kept so eventually the search is complete (although can
   * be very expensive to maintain explicitly all no-goods found during search).
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchWithRestarts() {

    // Input Order tie breaking
    boolean result = false;
    boolean timeout = true;

    int nodes = 0;
    int decisions = 0;
    int backtracks = 0;
    int wrongDecisions = 0;

    searchLabel = new DepthFirstSearch<>();

    NoGoodsCollector<IntVar> collector = new NoGoodsCollector<>();
    searchLabel.setExitChildListener(collector);
    searchLabel.setTimeOutListener(collector);
    searchLabel.setExitListener(collector);

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]), new SmallestDomain<>(), new IndomainSimpleRandom<>());

    while (timeout) {

      searchLabel.setNodesOut(1000);

      result = searchLabel.labeling(store, select);
      timeout = collector.timeOut;

      nodes += searchLabel.getNodes();
      decisions += searchLabel.getDecisions();
      wrongDecisions += searchLabel.getWrongDecisions();
      backtracks += searchLabel.getBacktracks();

      searchLabel = new DepthFirstSearch<>();
      collector = new NoGoodsCollector<>();
      searchLabel.setExitChildListener(collector);
      searchLabel.setTimeOutListener(collector);
      searchLabel.setExitListener(collector);
    }

    IO.println();
    IO.print(nodes + "\t");
    IO.print(decisions + "\t");
    IO.print(wrongDecisions + "\t");
    IO.print(backtracks + "\t");

    if (result) {
      IO.println(1);
    } else {
      IO.println(0);
    }

    return result;
  }

  /**
   * It uses credit search to solve a problem.
   *
   * @param credits the number of credits available.
   * @param backtracks the maximum number of backtracks used when a path exhausts its credits.
   * @param maxDepth the maximum depth to which the credit distribution takes place.
   * @return true if a solution was found, false otherwise.
   */
  public boolean creditSearch(int credits, int backtracks, int maxDepth) {

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]), new SmallestDomain<>(), new IndomainMin<>());

    CreditCalculator<IntVar> credit = new CreditCalculator<>(credits, backtracks, maxDepth);

    searchLabel = new DepthFirstSearch<>();

    if (searchLabel.getConsistencyListener() == null) {
      searchLabel.setConsistencyListener(credit);
    } else {
      searchLabel.getConsistencyListener().setChildrenListeners(credit);
    }

    searchLabel.setExitChildListener(credit);
    searchLabel.setTimeOutListener(credit);

    final boolean result = searchLabel.labeling(store, select);
    store.print();
    printSearchStats();
    IO.println(result ? 1 : 0);
    return result;
  }

  /**
   * It uses MaxRegret variable ordering heuristic to search for a solution.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchWithMaxRegret() {

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[0]),
            new MaxRegret<>(),
            new SmallestDomain<>(),
            new IndomainMiddle<>());

    searchLabel = new DepthFirstSearch<>();
    searchLabel.getSolutionListener().searchAll(true);
    searchLabel.getSolutionListener().recordSolutions(true);

    return searchLabel.labeling(store, select);
  }

  /**
   * It searches for solution using Limited Discrepancy Search.
   *
   * @param noDiscrepancy maximal number of discrepancies
   * @return true if the solution was found, false otherwise.
   */
  public boolean searchLds(int noDiscrepancy) {

    searchLabel = new DepthFirstSearch<>();

    boolean result;

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]), new SmallestDomain<>(), new IndomainMiddle<>());

    Lds<IntVar> lds = new Lds<>(noDiscrepancy);

    if (searchLabel.getExitChildListener() == null) {
      searchLabel.setExitChildListener(lds);
    } else {
      searchLabel.getExitChildListener().setChildrenListeners(lds);
    }

    // Execution time measurement
    long begin = System.currentTimeMillis();

    result = searchLabel.labeling(store, select);

    // Execution time measurement
    long end = System.currentTimeMillis();

    IO.println(NUMBER_OF_MILLISECONDS + (end - begin));

    return result;
  }

  /**
   * It searches for optimal solution using max regret variable ordering and indomain min for value
   * ordering.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchMaxRegretOptimal() {

    long t1;
    long t2;
    long t;
    t1 = System.currentTimeMillis();

    searchLabel = new DepthFirstSearch<>();

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(vars.toArray(new IntVar[1]), new MaxRegret<>(), new IndomainMin<>());

    boolean result = searchLabel.labeling(store, select, cost);

    t2 = System.currentTimeMillis();
    t = t2 - t1;

    if (result) {
      IO.println("Variables : " + vars);
    } else {
      IO.println(FAILED_TO_FIND_SOLUTION);
    }

    IO.println(EXECUTION_TIME_PREFIX + t + " ms");

    return result;
  }

  /**
   * It searches using smallest domain variable ordering and indomain middle value ordering.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchSmallestMiddle() {

    long begin = System.currentTimeMillis();

    boolean result;

    searchLabel = new DepthFirstSearch<>();

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]), new SmallestDomain<>(), new IndomainMiddle<>());

    result = searchLabel.labeling(store, select);

    long end = System.currentTimeMillis();

    IO.println(NUMBER_OF_MILLISECONDS + (end - begin));

    return result;
  }

  /**
   * It searches using smallest domain variable ordering and indomain middle value ordering.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchSmallestMedian() {

    long begin = System.currentTimeMillis();

    boolean result;

    searchLabel = new DepthFirstSearch<>();

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]), new SmallestDomain<>(), new IndomainMedian<>());

    result = searchLabel.labeling(store, select);

    long end = System.currentTimeMillis();

    IO.println(NUMBER_OF_MILLISECONDS + (end - begin));

    return result;
  }

  /**
   * It searches using Smallest Min variable ordering heuristic and indomainMin value ordering
   * heuristic.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchSmallestMin() {

    long begin = System.currentTimeMillis();

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(vars.toArray(new IntVar[1]), new SmallestMin<>(), new IndomainMin<>());

    searchLabel = new DepthFirstSearch<>();

    boolean solution = searchLabel.labeling(store, select, cost);

    long end = System.currentTimeMillis();

    if (solution) {
      store.print();
    } else {
      IO.println(FAILED_TO_FIND_SOLUTION);
    }

    IO.println(NUMBER_OF_MILLISECONDS + (end - begin));

    return solution;
  }

  /**
   * It conducts master-slave search. Both of them use input order variable ordering.
   *
   * @param masterVars it specifies the search variables used in master search.
   * @param slaveVars it specifies the search variables used in slave search.
   * @return true if the solution exists, false otherwise.
   */
  public boolean searchMasterSlave(List<Var> masterVars, List<Var> slaveVars) {

    final long t1 = System.currentTimeMillis();

    Search<IntVar> labelSlave = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> selectSlave =
        new SimpleSelect<>(slaveVars.toArray(IntVar[]::new), null, new IndomainMin<>());
    labelSlave.setSelectChoicePoint(selectSlave);

    Search<IntVar> labelMaster = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> selectMaster =
        new SimpleSelect<>(masterVars.toArray(IntVar[]::new), null, new IndomainMin<>());

    labelMaster.addChildSearch(labelSlave);

    searchLabel = labelMaster;

    boolean result = labelMaster.labeling(store, selectMaster);

    if (result) {
      IO.println("Solution found");
    }

    if (result) {
      store.print();
    }

    long t2 = System.currentTimeMillis();

    IO.println(EXECUTION_TIME_PREFIX + (t2 - t1) + " ms");

    return result;
  }

  /**
   * It returns the search used within an example.
   *
   * @return the search used within an example.
   */
  public Search<IntVar> getSearch() {
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
  public List<IntVar> getSearchVariables() {
    return vars;
  }
}
