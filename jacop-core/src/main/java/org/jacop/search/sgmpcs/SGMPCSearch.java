/*
 * SGMPCSearch.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.search.sgmpcs;

import java.util.Arrays;
import java.util.Comparator;
import java.util.Random;
import java.util.function.Function;
import lombok.Setter;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.XltC;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;

/**
 * SGMPCSearch - implements Solution-Guided Multi-Point Constructive Search. This search starts with
 * several elite solutions and tries to impove (minimizing cost variable) them by doing either
 * search assuming an elite solution or staring with an empty solution.
 *
 * <p>This implementation is based on paper "Solution-guided Multi-point Constructive Search for Job
 * Shop Scheduling" by J. Christopher Beck, Journal of Artificial Intelligence Research 29 (2007)
 * 49–77.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.10
 */
@Slf4j
public class SGMPCSearch {

  // strategy to get limit l on fails
  public static final int luby = 1;
  public static final int poly = 2;
  static final double precision = 1e-12;
  public final Store store;

  /** Variables for search. */
  public final IntVar[] vars;

  /** Cost variable. */
  public final IntVar cost;

  final boolean trace = false;
  final ImproveSolution<IntVar> search;
  final Function<Integer, Comparator<int[]>> solutionComparator =
      p -> Comparator.comparingInt((int[] o) -> o[p]);
  // e- number of elite solutions
  public int e = 4;
  // eInit- number of solution for selecting the best e elite solutions
  public int eInit = 20;
  // elite solutions
  // at position 0 is cost and values of variables start at positions 1
  public int[][] elite;
  public int costPosition;
  @Setter boolean printInfo = true;
  // Start time of the search to compute termination criteria
  long searchStartTime;
  /*
   * The cost produced by last search
   */ int searchCost;

  /** Parameters. */

  // p- probablity of selecting search starting from reference
  // solution or from empty solution
  double p = 0.25;

  // l- current fail limit
  int l;
  int strategy = poly;
  // number of consequtive fails when searching for a solution
  int numberConsecutiveFails;
  // index fro computing Luby number
  int lubyIndex = 1;
  // last found solution
  int[] solution;
  // time-out value in miliseconds (default 10 second)
  long timeOut = 10000;

  public SGMPCSearch(Store store, IntVar[] vars, IntVar cost) {

    this.store = store;
    this.vars = new IntVar[vars.length];
    System.arraycopy(vars, 0, this.vars, 0, vars.length);
    this.cost = cost;

    search = new SimpleImprovementSearch<>(store, vars, cost);
  }

  public SGMPCSearch(Store store, IntVar[] vars, IntVar cost, ImproveSolution<IntVar> search) {

    this.store = store;
    this.vars = new IntVar[vars.length];
    System.arraycopy(vars, 0, this.vars, 0, vars.length);
    this.cost = cost;

    this.search = search;
  }

  public boolean search() {

    l = strategy == luby ? getLuby(1) : 32;

    findEliteSolutions();

    int bestCostSolution = bestCostSolution();
    if (trace) {
      log.debug(
          "%% Best Cost elite solution is {} with cost {}",
          bestCostSolution, elite[bestCostSolution][costPosition]);
    }

    improveSolution();

    return true;
  }

  /*
   * Finds elite solutions if they do not exist yet.
   */
  public void findEliteSolutions() {

    if (elite == null) {
      elite = new int[e][];
      for (int i = 0; i < e; i++) {
        elite[i] = new int[vars.length + 1];
      }
    } else {
      return;
    }

    costPosition = vars.length;
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] == cost) {
        costPosition = i;
      }
    }

    IntVar[] v;
    if (costPosition == vars.length) {
      v = new IntVar[vars.length + 1];
      System.arraycopy(vars, 0, v, 0, vars.length);
      v[vars.length] = cost;
    } else {
      v = vars;
    }

    DepthFirstSearch<IntVar> label = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> select = new SimpleSelect<>(v, null, new IndomainMin<>());
    label.getSolutionListener().searchAll(true);
    label.getSolutionListener().recordSolutions(true);
    label.getSolutionListener().setSolutionLimit(eInit);
    label.setAssignSolution(false);
    label.setPrintInfo(false);

    label.labeling(store, select);

    int[][] solutionPool = new int[label.getSolutionListener().solutionsNo()][];
    for (int i = 0; i < label.getSolutionListener().solutionsNo(); i++) {
      solutionPool[i] = new int[v.length];
      for (int j = 0; j < label.getSolution(i + 1).length; j++) {
        solutionPool[i][j] = ((IntDomain) label.getSolution(i + 1)[j]).value();
      }
    }

    if (trace) {
      log.debug("%% Initial pool of solutions");

      for (int i = 0; i < solutionPool.length; i++) {
        StringBuilder sb = new StringBuilder("%% Solution ").append(i + 1).append(": ");
        for (int j = 0; j < v.length; j++) {
          sb.append(solutionPool[i][j]).append(" ");
        }
        log.debug("{}", sb);
      }
    }

    Arrays.sort(solutionPool, solutionComparator.apply(costPosition));

    elite = new int[e][];
    for (int i = 0; i < e; i++) {
      elite[i] = new int[solutionPool[i].length];
      System.arraycopy(solutionPool[i], 0, elite[i], 0, elite[i].length);
    }

    if (trace) {
      log.debug("%% Selected best {} solutions", e);

      for (int i = 0; i < e; i++) {
        StringBuilder solution = new StringBuilder("%% Solution ").append(i + 1).append(": ");
        for (int j = 0; j < v.length; j++) {
          solution.append(elite[i][j]).append(" ");
        }
        log.debug("{}", solution);
      }
    }
  }

  /*
   * method tries to improve elite solutions by using
   * solution-guided multi-point constructive search
   */
  boolean improveSolution() {

    Random rand = Store.seedPresent() ? new Random(Store.getSeed()) : new Random();
    Random randomSolution = Store.seedPresent() ? new Random(Store.getSeed()) : new Random();

    searchStartTime = System.currentTimeMillis();

    search.setPrintInfo(printInfo);

    while (!terminationCriteria()) {

      long currentTime = System.currentTimeMillis();
      long restTimeOut = (timeOut - (currentTime - searchStartTime)) / 1000;
      if (restTimeOut <= 0) {
        break;
      }

      search.setTimeOut(restTimeOut);

      int bestCost = elite[bestCostSolution()][costPosition];
      store.impose(new XltC(cost, bestCost));

      if (rand.nextFloat() < p) {

        boolean result = search.searchFromEmptySolution(l);

        if (!result) {
          numberConsecutiveFails++;
          updateFailLimit(true);
        } else {
          if (printInfo) {
            log.info("%% Fails {}({})", search.getNumberFails(), search.getFailLimit());
          }

          solution = search.getSolution();

          if (printInfo) {
            log.info("%% Solution starting from empty ");
            printSolution(solution);
          }

          numberConsecutiveFails = 0;

          int worst = worstCostSolution();
          if (elite[worst][costPosition] > search.getCurrentCost()) {
            replaceEliteSolution(worst, solution, search.getCurrentCost());
          }

          searchCost = search.getCurrentCost();
          updateFailLimit(false);
        }
      } else {

        // select random solution from e elite solutions
        int n = randomSolution.nextInt(e);

        boolean result = search.searchFromEliteSolution(elite[n], l);

        if (!result) {
          numberConsecutiveFails++;
          updateFailLimit(true);
        } else {

          if (printInfo) {
            log.info("%% Fails {}({})", search.getNumberFails(), search.getFailLimit());
          }

          solution = search.getSolution();

          if (printInfo) {
            log.info("%% Solution starting from reference with cost {}", elite[n][costPosition]);
            printSolution(solution);
          }

          numberConsecutiveFails = 0;

          replaceEliteSolution(n, solution, search.getCurrentCost());

          searchCost = search.getCurrentCost();
          updateFailLimit(false);
        }
      }
    }

    return true;
  }

  boolean terminationCriteria() {

    boolean termination;

    long currentTime = System.currentTimeMillis();

    // terminate after time-out or when optimal
    termination =
        (currentTime - searchStartTime > timeOut)
            || (numberConsecutiveFails > 0 && search.getNumberFails() < search.getFailLimit());

    if (printInfo && termination) {
      log.info(
          "%% Termination search fails {}({})", search.getNumberFails(), search.getFailLimit());

      if (solution == null) {

        int bestCostSolution = bestCostSolution();

        solution = new int[vars.length];
        System.arraycopy(elite[bestCostSolution], 0, solution, 0, vars.length);

        searchCost = elite[bestCostSolution][costPosition];
      }
    }

    return termination;
  }

  public void setTimeOut(long t) { // t in seconds
    timeOut = t * 1000;
  }

  void updateFailLimit(boolean fail) {

    if (strategy == poly) {
      if (fail) {
        l += 32;
      } else {
        l = 32;
      }

    } else {
      // Luby
      l = getLuby(lubyIndex);

      lubyIndex++;
    }
  }

  public int getLuby(int i) {

    if (i == 1) {
      return 1;
    }

    double k = Math.log(i + 1) / Math.log(2d);

    if (Math.abs(k - Math.floor(k + 0.5)) < precision) { // k == Math.floor(k + 0.5)
      return (int) Math.pow(2, k - 1);
    } else {
      k = Math.floor(k);
      return getLuby(i - (int) Math.pow(2, k) + 1);
    }
  }

  /*
   * Finds a solution with minimal cost
   */
  int bestCostSolution() {
    int currentCost = IntDomain.MaxInt;
    int solution = -1;

    for (int i = 0; i < elite.length; i++) {
      if (currentCost > elite[i][costPosition]) {
        currentCost = elite[i][costPosition];
        solution = i;
      }
    }

    return solution;
  }

  /*
   * Finds a solution with maximal cost
   */
  int worstCostSolution() {
    int currentCost = IntDomain.MinInt;
    int solution = -1;

    for (int i = 0; i < elite.length; i++) {
      if (currentCost < elite[i][costPosition]) {
        currentCost = elite[i][costPosition];
        solution = i;
      }
    }

    return solution;
  }

  public void setEliteSolutions(int[][] solutions) {
    if (solutions.length != e) {
      log.error(
          "Number of initial solutions not correct; it is {} and should be {}",
          solutions.length,
          e);
      return;
    }

    elite = new int[e][];
    for (int i = 0; i < e; i++) {
      elite[i] = new int[solutions[i].length];
      System.arraycopy(solutions[i], 0, elite[i], 0, elite[i].length);
    }
  }

  void replaceEliteSolution(int n, int[] solution, int searchCost) {

    if (elite[n].length - 1 >= 0) {
      System.arraycopy(solution, 0, elite[n], 0, elite[n].length - 1);
    }
    elite[n][costPosition] = searchCost;
  }

  public void setProbability(double p) {
    this.p = p;
  }

  public void setEliteSize(int e) {
    this.e = e;
  }

  public void setInitialSolutionsSize(int eInit) {
    this.eInit = eInit;
  }

  public void setFailStrategy(int strategy) {
    if (strategy == poly || strategy == luby) {
      this.strategy = strategy;
    } else {
      log.warn("Wrong fail strategy limit; assumed poly");

      this.strategy = poly;
    }
  }

  public void printSolution(int[] solution) {
    StringBuilder sb = new StringBuilder();
    for (int j : solution) {
      sb.append(j).append(" ");
    }
    log.info("{}", sb);
  }

  public int[] lastSolution() {
    return solution;
  }

  public int lastCost() {
    return searchCost;
  }
}
