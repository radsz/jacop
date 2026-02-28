/*
 * FilterBenchmark.java
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

package org.jacop.examples.fd.filters;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Cumulative;
import org.jacop.constraints.Max;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.CreditCalculator;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.MostConstrainedStatic;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleMatrixSelect;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.jacop.search.SmallestMax;
import org.jacop.search.SmallestMin;
import org.jacop.ui.PrintSchedule;

/**
 * This is a set of filter scheduling examples, commonly used in High-Level Synthesis.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class FilterBenchmark {

  static List<IntVar> taskStarts;
  static List<IntVar> taskResources;

  static List<Integer> taskDurations;

  static List<String> taskNames;

  static IntVar cost;

  private static final String TEST_OF_SCHEDULING_FOR = "\n\nTest of scheduling for ";
  private static final String WITH_PREFIX = "with ";
  private static final String ADDERS_AND = " adders and ";
  private static final String MULTIPLIERS = " multipliers";
  private static final String ADD_DURATION = "add duration ";
  private static final String AND_MUL_DURATION = " and mul duration ";
  private static final String EXECUTION_TIME_PREFIX = "\n\t*** Execution time = ";

  /** Default constructor. */
  protected FilterBenchmark() {}

  /** Converts taskVars to IntVar[][] for SimpleMatrixSelect. */
  private static IntVar[][] taskVarsToMatrix(List<List<IntVar>> taskVars) {
    IntVar[][] vars = new IntVar[taskVars.size()][];
    for (int i = 0; i < vars.length; i++) {
      vars[i] = taskVars.get(i).toArray(IntVar[]::new);
    }
    return vars;
  }

  /** Prints standard experiment header. */
  private static void printExperimentHeader(Filter filter, int addNum, int mulNum) {
    log.info(TEST_OF_SCHEDULING_FOR + filter.name() + " example");
    log.info(WITH_PREFIX + addNum + ADDERS_AND + mulNum + MULTIPLIERS);
    log.info(ADD_DURATION + filter.addDel() + AND_MUL_DURATION + filter.mulDel());
  }

  /** Prints experiment header with clock length. */
  private static void printExperimentHeader(Filter filter, int addNum, int mulNum, int clock) {
    log.info(TEST_OF_SCHEDULING_FOR + filter.name() + " example");
    log.info(
        WITH_PREFIX + addNum + ADDERS_AND + mulNum + MULTIPLIERS + ";\nclock length: " + clock);
    log.info(ADD_DURATION + filter.addDel() + AND_MUL_DURATION + filter.mulDel());
  }

  /** Prints store stats and runs consistency; returns consistency result. */
  private static boolean checkConsistency(Store store, String consistentMsg) {
    return checkConsistency(store, consistentMsg, null);
  }

  /** Same as above but runs given action before consistency (e.g. impose extra constraint). */
  private static boolean checkConsistency(
      Store store, String consistentMsg, Runnable beforeConsistency) {
    log.info(
        "\nVariable store size: "
            + store.size()
            + "\nNumber of constraints: "
            + store.numberConstraints());
    if (beforeConsistency != null) {
      beforeConsistency.run();
    }
    boolean result = store.consistency();
    log.info(consistentMsg + " = " + result);
    return result;
  }

  /** Computes pipeline lower bound from filter and resource counts. */
  private static int computePipelineLowerBound(Filter filter, int addNum, int mulNum) {
    int tAdd = (filter.noAdd() * filter.addDel()) / addNum;
    int rAdd = (filter.noAdd() * filter.addDel()) % addNum;
    int addLb = rAdd == 0 ? tAdd : tAdd + 1;
    int tMul = (filter.noMul() * filter.mulDel()) / mulNum;
    int rMul = (filter.noMul() * filter.mulDel()) % mulNum;
    int mulLb = rMul == 0 ? tMul : tMul + 1;
    return Math.max(addLb, mulLb);
  }

  /** Attaches credit calculator to search listeners. */
  private static void attachCreditListeners(
      Search<IntVar> search, CreditCalculator<IntVar> credit) {
    if (search.getConsistencyListener() == null) {
      search.setConsistencyListener(credit);
    } else {
      search.getConsistencyListener().setChildrenListeners(credit);
    }
    if (search.getExitChildListener() == null) {
      search.setExitChildListener(credit);
    } else {
      search.getExitChildListener().setChildrenListeners(credit);
    }
    if (search.getTimeOutListener() == null) {
      search.setTimeOutListener(credit);
    } else {
      search.getTimeOutListener().setChildrenListeners(credit);
    }
  }

  /** Runs labeling with timing, prints time, returns search result. */
  private static boolean runLabelingWithTiming(Store store, SelectChoicePoint<IntVar> select) {
    final long t1 = System.currentTimeMillis();
    Search<IntVar> label = new DepthFirstSearch<>();
    boolean result = label.labeling(store, select, cost);
    log.info(EXECUTION_TIME_PREFIX + (System.currentTimeMillis() - t1) + " ms");
    return result;
  }

  /** Runs two-phase labeling (cost then IO) with timing; returns search result. */
  private static boolean runTwoPhaseLabelingWithTiming(
      Store store, SelectChoicePoint<IntVar> selectMc, SelectChoicePoint<IntVar> selectIo) {
    return runTwoPhaseLabelingWithTiming(store, selectMc, selectIo, null);
  }

  /** Same but uses firstPhaseSearch for first phase when non-null. */
  private static boolean runTwoPhaseLabelingWithTiming(
      Store store,
      SelectChoicePoint<IntVar> selectMc,
      SelectChoicePoint<IntVar> selectIo,
      Search<IntVar> firstPhaseSearch) {
    final long t1 = System.currentTimeMillis();
    Search<IntVar> label = firstPhaseSearch != null ? firstPhaseSearch : new DepthFirstSearch<>();
    boolean result = label.labeling(store, selectMc, cost);
    if (result) {
      label = new DepthFirstSearch<>();
      result = label.labeling(store, selectIo);
    }
    log.info(EXECUTION_TIME_PREFIX + (System.currentTimeMillis() - t1) + " ms");
    return result;
  }

  /** Converts List of IntVar to array. */
  private static IntVar[] listToArray(List<IntVar> list) {
    return list.toArray(IntVar[]::new);
  }

  /** Holds resource range boundaries. */
  private static class ResourceRanges {
    final int addMin;
    final int addMax;
    final int mulMin;
    final int mulMax;

    ResourceRanges(int addNum, int mulNum) {
      this.addMin = 1;
      this.addMax = addMin + addNum - 1;
      this.mulMin = addMax + 1;
      this.mulMax = mulMin + mulNum - 1;
    }
  }

  /**
   * Creates dependency constraints and end operation cost calculation.
   *
   * @param store the constraint store
   * @param dependencies operation dependencies
   * @param delays operation delays
   * @param lastOp indices of last operations
   * @param T start time variables
   * @param D delay values
   * @param costVar variable to store the cost (will be created if null)
   * @param costMax maximum value for cost variable (used only if costVar is null)
   * @return the cost variable
   */
  private static IntVar createDependencyAndCostConstraints(
      Store store,
      int[][] dependencies,
      int[] delays,
      int[] lastOp,
      IntVar[] startTimes,
      int[] durations,
      IntVar costVar,
      int costMax) {
    for (int[] dependency : dependencies) {
      store.impose(
          new XplusClteqZ(
              startTimes[dependency[0]], delays[dependency[0]], startTimes[dependency[1]]));
    }

    List<IntVar> endOp = new ArrayList<>();
    int endMax = costVar == null ? costMax : costVar.max();
    for (int value : lastOp) {
      IntVar end = new IntVar(store, 0, endMax);
      store.impose(new XplusCeqZ(startTimes[value], durations[value], end));
      endOp.add(end);
    }

    if (costVar == null) {
      costVar = new IntVar(store, 0, costMax);
    }
    store.impose(new Max(endOp, costVar));
    return costVar;
  }

  /**
   * Common experiment runner pattern.
   *
   * @param store the constraint store
   * @param headerMsg header message to print
   * @param constraintBuilder function that builds constraints and returns task vars
   * @param selectorBuilder function that creates the selector
   * @param consistencyMsg consistency check message
   * @param extraSuccessLineSupplier function that computes extra line to print on success (called
   *     after constraints built)
   * @return cost value or -1 if no solution found
   */
  private static int runExperiment(
      Store store,
      String headerMsg,
      java.util.function.Function<Store, List<List<IntVar>>> constraintBuilder,
      java.util.function.Function<List<List<IntVar>>, SelectChoicePoint<IntVar>> selectorBuilder,
      String consistencyMsg,
      java.util.function.Supplier<String> extraSuccessLineSupplier) {
    if (headerMsg != null) {
      log.info(headerMsg);
    }
    List<List<IntVar>> taskVars = constraintBuilder.apply(store);
    SelectChoicePoint<IntVar> select = selectorBuilder.apply(taskVars);
    checkConsistency(store, consistencyMsg);
    boolean result = runLabelingWithTiming(store, select);
    String extraLine = extraSuccessLineSupplier != null ? extraSuccessLineSupplier.get() : null;
    return reportResult(result, extraLine);
  }

  /**
   * Common experiment runner for two-phase labeling.
   *
   * @param store the constraint store
   * @param headerMsg header message to print
   * @param constraintBuilder function that builds constraints
   * @param selectMc selector for first phase
   * @param selectIo selector for second phase
   * @param consistencyMsg consistency check message
   * @param extraSuccessLineSupplier function that computes extra line to print on success (called
   *     after constraints built)
   * @param firstPhaseSearch optional search instance for first phase
   * @return cost value or -1 if no solution found
   */
  private static int runTwoPhaseExperiment(
      Store store,
      String headerMsg,
      Runnable constraintBuilder,
      SelectChoicePoint<IntVar> selectMc,
      SelectChoicePoint<IntVar> selectIo,
      String consistencyMsg,
      java.util.function.Supplier<String> extraSuccessLineSupplier,
      Search<IntVar> firstPhaseSearch) {
    if (headerMsg != null) {
      log.info(headerMsg);
    }
    constraintBuilder.run();
    checkConsistency(store, consistencyMsg);
    boolean result =
        firstPhaseSearch != null
            ? runTwoPhaseLabelingWithTiming(store, selectMc, selectIo, firstPhaseSearch)
            : runTwoPhaseLabelingWithTiming(store, selectMc, selectIo);
    String extraLine = extraSuccessLineSupplier != null ? extraSuccessLineSupplier.get() : null;
    return reportResult(result, extraLine);
  }

  /**
   * Populates resource arrays (T, R, D, Tadd, Radd, etc.) based on filter operations.
   *
   * @param store the constraint store
   * @param filter the filter being scheduled
   * @param ranges resource range boundaries
   * @param T start time variables (output)
   * @param R resource assignment variables (output)
   * @param D delay values (output)
   * @param Tadd start times for additions (output)
   * @param Radd resource assignments for additions (output)
   * @param Dadd delays for additions (output)
   * @param ResAdd resource usage for additions (output)
   * @param Tmul start times for multiplications (output)
   * @param Rmul resource assignments for multiplications (output)
   * @param Dmul delays for multiplications (output)
   * @param ResMul resource usage for multiplications (output)
   * @param addDelay delay variable for additions
   * @param mulDelay delay variable for multiplications
   * @param one constant one variable
   * @param tminValue minimum value for T variables
   * @param tmaxValue maximum value for T variables
   */
  private static void populateResourceArrays(
      Store store,
      Filter filter,
      ResourceRanges ranges,
      IntVar[] startTimes,
      IntVar[] resources,
      int[] durations,
      IntVar[] startTimesAdd,
      IntVar[] resourcesAdd,
      IntVar[] durationsAdd,
      IntVar[] resourceUsageAdd,
      IntVar[] startTimesMul,
      IntVar[] resourcesMul,
      IntVar[] durationsMul,
      IntVar[] resourceUsageMul,
      IntVar addDelay,
      IntVar mulDelay,
      IntVar one,
      int tminValue,
      int tmaxValue) {
    int[] delays = filter.delays();
    String nameT = "T";
    String nameR = "R";

    int j = 0;
    int k = 0;
    for (int i = 0; i < delays.length; i++) {
      String t = nameT + i;
      String r = nameR + i;

      startTimes[i] = new IntVar(store, t, tminValue, tmaxValue);

      if (filter.ids()[i] == filter.addId()) {
        resources[i] = new IntVar(store, r, ranges.addMin, ranges.addMax);
        startTimesAdd[j] = startTimes[i];
        resourcesAdd[j] = resources[i];
        durationsAdd[j] = addDelay;
        durations[i] = filter.addDel();
        resourceUsageAdd[j] = one;
        j++;
      } else {
        resources[i] = new IntVar(store, r, ranges.mulMin, ranges.mulMax);
        startTimesMul[k] = startTimes[i];
        resourcesMul[k] = resources[i];
        durationsMul[k] = mulDelay;
        durations[i] = filter.mulDel();
        resourceUsageMul[k] = one;
        k++;
      }
    }
  }

  /**
   * Finalizes static fields Ts, Rs, Ds, Ns from computed arrays.
   *
   * @param T start time variables
   * @param R resource assignment variables
   * @param D delay values
   * @param names operation names
   */
  private static void finalizeStaticFields(
      IntVar[] startTimes, IntVar[] resources, int[] durations, List<String> names) {
    taskStarts = new ArrayList<>();
    taskStarts.addAll(Arrays.asList(startTimes));
    taskResources = new ArrayList<>();
    taskResources.addAll(Arrays.asList(resources));
    taskDurations = new ArrayList<>();
    for (Integer v : durations) {
      taskDurations.add(v);
    }
    taskNames = names;
  }

  /** Prints success/failure and returns cost value or -1. */
  private static int reportResult(boolean result) {
    return reportResult(result, null);
  }

  /** Prints success/failure with optional extra line; returns cost value or -1. */
  private static int reportResult(boolean result, String extraSuccessLine) {
    if (result) {
      log.info("\n*** Yes");
      if (extraSuccessLine != null) {
        log.info(extraSuccessLine);
      }
      PrintSchedule sch = new PrintSchedule(taskNames, taskStarts, taskDurations, taskResources);
      log.info("{}", sch);
      return cost.value();
    } else {
      log.info("*** No");
      return -1;
    }
  }

  /**
   * It executes the program for number of filters, number of resources (adders, multipliers) and
   * number of different synthesis techniques ( algorithmic pipelining, multiplier pipelining,
   * chaining, no special techniques).
   *
   * @param args parameters (none)
   */
  static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    final long t1 = System.currentTimeMillis();

    schedule();

    pipeMulSchedule();

    chainingSchedule();

    pipelineSchedule();

    long t2 = System.currentTimeMillis();
    long t = t2 - t1;
    log.info(EXECUTION_TIME_PREFIX + t + " ms");
  }

  /**
   * It solves available filters for different scenario consisting of different number of resources.
   */
  public static void schedule() {

    int[][] dfqEx = {{1, 1}, {1, 2}, {1, 3}, {2, 2}, {1, 4}, {2, 3}};
    for (int[] config : dfqEx) {
      Store store = new Store();
      experiment1(store, new Dfq(), config[0], config[1]);
    }

    int[][] firEx = {{1, 1}, {1, 2}, {2, 2}, {2, 3}};
    for (int[] config : firEx) {
      Store store = new Store();
      experiment1(store, new Fir(), config[0], config[1]);
    }

    int[][] arEx = {{1, 1}, {1, 2}, {1, 3}, {2, 3}, {2, 4}};
    for (int[] config : arEx) {
      Store store = new Store();
      experiment2(store, new Ar(1, 1), config[0], config[1]);
    }

    int[][] ewfEx = {{1, 1}, {2, 1}, {2, 2}, {3, 3}};
    for (int[] config : ewfEx) {
      Store store = new Store();
      experiment1(store, new Ewf(), config[0], config[1]);
    }

    int[][] ewfEx2 = {{1, 1}, {2, 1}, {2, 2}, {3, 3}};
    for (int[] config : ewfEx2) {
      Store store = new Store();
      experiment1(store, new Ewf(1, 1), config[0], config[1]);
    }

    int[][] dctEx = {{1, 1}, {1, 2}, {2, 2}, {2, 3}, {3, 3}, {3, 4}, {4, 4}};
    for (int[] config : dctEx) {
      Store store = new Store();
      experiment1(store, new Dct(), config[0], config[1]);
    }
  }

  /**
   * It solves available filters for different scenario consisting of different number of resources.
   * It performs pipelining of multiplier operations.
   */
  public static void pipeMulSchedule() {

    int[][] dfqEx = {{1, 1}, {1, 2}};
    for (int[] element : dfqEx) {
      int a = element[0];
      int m = element[1];
      Store store = new Store();
      Dfq dfq = new Dfq();
      experiment1Pm(store, dfq, a, m);
    }

    int[][] firEx = {{1, 1}, {2, 1}, {2, 2}};
    for (int[] item : firEx) {
      int a = item[0];
      int m = item[1];
      Fir fir = new Fir();
      Store store = new Store();
      experiment1Pm(store, fir, a, m);
    }

    int[][] arEx = {{1, 1}, {1, 2}, {2, 2}, {2, 4}};
    for (int[] value : arEx) {
      int a = value[0];
      int m = value[1];
      Ar ar = new Ar();
      Store store = new Store();
      experiment2Pm(store, ar, a, m);
    }

    int[][] ewfEx = {{2, 1}, {3, 1}, {3, 2}};
    for (int[] ints : ewfEx) {
      int a = ints[0];
      int m = ints[1];
      Ewf ewf = new Ewf();
      Store store = new Store();
      experiment1Pm(store, ewf, a, m);
    }

    int[][] dctEx = {{1, 1}, {2, 1}, {2, 2}, {3, 2}, {4, 3}, {5, 4}, {6, 5}};
    for (int[] ex : dctEx) {
      int a = ex[0];
      int m = ex[1];
      Dct dct = new Dct();
      Store store = new Store();
      experiment1Pm(store, dct, a, m);
    }
  }

  /**
   * It solves available filters for different scenario consisting of different number of resources.
   * It performs chaining of operations.
   */
  public static void chainingSchedule() {

    int[][] dfqEx = {{1, 1, 3}, {1, 2, 3}, {2, 2, 3}};
    for (int[] element : dfqEx) {
      int a = element[0];
      int m = element[1];
      int s = element[2];
      Store store = new Store();
      Dfq dfq = new Dfq();
      experiment1C(store, dfq, a, m, s);
    }

    int[][] firEx = {{2, 1, 2}, {2, 2, 2}, {3, 2, 2}, {1, 1, 3}, {2, 1, 3}, {3, 2, 3}};
    for (int[] item : firEx) {
      int a = item[0];
      int m = item[1];
      int s = item[2];
      Fir fir = new Fir();
      Store store = new Store();
      experiment1C(store, fir, a, m, s);
    }

    int[][] arEx = {
      {2, 2, 2}, {2, 3, 2}, {4, 4, 2}, {1, 1, 3}, {1, 2, 3}, {2, 2, 3}, {2, 3, 3}, {2, 4, 3},
      {3, 4, 3}, {2, 2, 4}, {2, 3, 4}, {3, 4, 4}
    };
    for (int[] value : arEx) {
      int a = value[0];
      int m = value[1];
      int s = value[2];
      Ar ar = new Ar();
      Store store = new Store();
      experiment1C(store, ar, a, m, s);
    }

    int[][] ewfEx = {
      {2, 1, 2}, {3, 1, 2}, {1, 1, 3}, {2, 1, 3}, {3, 1, 3}, {1, 1, 4}, {2, 1, 4}, {3, 1, 4}
    };
    for (int[] ints : ewfEx) {
      int a = ints[0];
      int m = ints[1];
      int s = ints[2];
      Ewf ewf = new Ewf();
      Store store = new Store();
      experiment1C(store, ewf, a, m, s);
    }

    int[][] dctEx = {
      {2, 1, 2}, {2, 2, 2}, {3, 2, 2}, {4, 2, 2}, {4, 3, 2}, {5, 4, 2}, {1, 1, 3}, {2, 1, 3},
      {3, 2, 3}, {4, 2, 3}, {5, 3, 3}
    };
    for (int[] ex : dctEx) {
      int a = ex[0];
      int m = ex[1];
      int s = ex[2];
      Dct dct = new Dct();
      Store store = new Store();
      experiment1C(store, dct, a, m, s);
    }
  }

  /**
   * It solves available filters for different scenario consisting of different number of resources.
   * It performs algorithmic pipelining.
   */
  public static void pipelineSchedule() {

    // **************** Pipeline schedules

    int[][] dfqEx = {{1, 3}, {2, 3}};
    for (int[] dfqEx1 : dfqEx) {
      int a = dfqEx1[0];
      int m = dfqEx1[1];
      Store store = new Store();
      Dfq dfqP = new Dfq();
      experiment1P(store, dfqP, a, m);
    }

    int[][] firEx = {{2, 2}, {3, 3}, {3, 4}};
    for (int[] element : firEx) {
      int a = element[0];
      int m = element[1];
      Fir firP = new Fir();
      Store store = new Store();
      experiment1P(store, firP, a, m);
    }

    int[][] arEx = {{2, 4}, {2, 6}, {3, 8}};
    for (int[] item : arEx) {
      int a = item[0];
      int m = item[1];
      Ar arP = new Ar();
      Store store = new Store();
      experiment1P(store, arP, a, m);
    }

    int[][] ewfEx = {{3, 2}, {4, 2}, {4, 3}, {5, 4}};
    for (int[] value : ewfEx) {
      int a = value[0];
      int m = value[1];
      Ewf ewfP = new Ewf();
      Store store = new Store();
      experiment1P(store, ewfP, a, m);
    }

    int[][] dctEx = {{4, 4}, {4, 5}, {5, 6}, {6, 7}, {7, 8}};
    for (int[] ints : dctEx) {
      int a = ints[0];
      int m = ints[1];
      Dct dctP = new Dct();
      Store store = new Store();
      experiment1P(store, dctP, a, m);
    }

    int[][] fftEx = {{1, 1}, {1, 2}, {2, 2}, {3, 4}};
    for (int[] ex : fftEx) {
      int a = ex[0];
      int m = ex[1];
      Fft fftP = new Fft();
      Store store = new Store();
      experiment1P(store, fftP, a, m);
    }
  }

  /**
   * It optimizes scheduling of filter operations.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param addNum number of adders available.
   * @param mulNum number of multipliers available.
   * @return cost of the solution or -1 if no solution found.
   */
  public static int experiment1(Store store, Filter filter, int addNum, int mulNum) {
    printExperimentHeader(filter, addNum, mulNum);
    return runExperiment(
        store,
        null,
        s -> makeConstraints(s, filter, addNum, mulNum),
        taskVars ->
            new SimpleMatrixSelect<>(
                taskVarsToMatrix(taskVars),
                new SmallestMin<>(),
                new MostConstrainedStatic<>(),
                new IndomainMin<>(),
                0),
        "1. Constraints consistent",
        null);
  }

  /**
   * It optimizes scheduling of filter operation in fashion allowing chaining of operations within
   * one clock cycle.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param addNum number of adders available.
   * @param mulNum number of multipliers available.
   * @param clock number of time units within a clock.
   * @return cost of the solution or -1 if no solution found.
   */
  public static int experiment1C(Store store, Filter filter, int addNum, int mulNum, int clock) {
    printExperimentHeader(filter, addNum, mulNum, clock);
    return runExperiment(
        store,
        null,
        s -> makeConstraintsChain(s, filter, addNum, mulNum, clock),
        taskVars ->
            new SimpleMatrixSelect<>(
                taskVarsToMatrix(taskVars),
                new SmallestMin<>(),
                new MostConstrainedStatic<>(),
                new IndomainMin<>(),
                0),
        "2. Constraints consistent",
        () -> "Schedule length: " + div(cost.min(), clock));
  }

  /**
   * Performs integer division with ceiling rounding.
   *
   * @param a the dividend
   * @param b the divisor
   * @return the quotient rounded up to the nearest integer
   */
  private static int div(int a, int b) {
    int div;
    int rem;

    div = a / b;
    rem = a % b;
    return rem > 0 ? div + 1 : div;
  }

  /**
   * It optimizes scheduling of filter operations in a fashion allowing pipelining of multiplication
   * operations.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param addNum number of adders available.
   * @param mulNum number of multipliers available.
   * @return cost of the solution or -1 if no solution found.
   */
  public static int experiment1Pm(Store store, Filter filter, int addNum, int mulNum) {
    String header =
        TEST_OF_SCHEDULING_FOR
            + filter.name()
            + " example with pipeline multiplier\nwith "
            + addNum
            + ADDERS_AND
            + mulNum
            + MULTIPLIERS
            + "\n"
            + ADD_DURATION
            + filter.addDel()
            + AND_MUL_DURATION
            + filter.mulDel();
    return runExperiment(
        store,
        header,
        s -> makeConstraintsPipeMultiplier(s, filter, addNum, mulNum),
        taskVars ->
            new SimpleMatrixSelect<>(
                taskVarsToMatrix(taskVars),
                new SmallestMax<>(),
                new MostConstrainedStatic<>(),
                new IndomainMin<>(),
                0),
        "3. Constraints consistent",
        null);
  }

  /**
   * It optimizes scheduling of filter operation in fashion allowing pipelining of multiplication
   * operations.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param addNum number of adders available.
   * @param mulNum number of multipliers available.
   * @return cost of the solution or -1 if no solution found.
   */
  public static int experiment2Pm(Store store, Filter filter, int addNum, int mulNum) {
    String header =
        TEST_OF_SCHEDULING_FOR
            + filter.name()
            + " example with pipeline multiplier\nwith "
            + addNum
            + ADDERS_AND
            + mulNum
            + MULTIPLIERS
            + "\n"
            + ADD_DURATION
            + filter.addDel()
            + AND_MUL_DURATION
            + filter.mulDel();
    final SelectChoicePoint<IntVar> selectMc =
        new SimpleSelect<>(
            listToArray(taskStarts),
            new MostConstrainedStatic<>(),
            new SmallestDomain<>(),
            new IndomainMin<>());
    final SelectChoicePoint<IntVar> selectIo =
        new SimpleSelect<>(listToArray(taskResources), null, null, new IndomainMin<>());
    return runTwoPhaseExperiment(
        store,
        header,
        () -> makeConstraintsPipeMultiplier(store, filter, addNum, mulNum),
        selectMc,
        selectIo,
        "4. Constraints consistent",
        null,
        null);
  }

  /**
   * It optimizes scheduling of filter operations. It performs algorithmic pipelining.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param addNum number of adders available.
   * @param mulNum number of multipliers available.
   * @return cost of the solution or -1 if no solution found.
   */
  public static int experiment1P(Store store, Filter filter, int addNum, int mulNum) {

    log.info(
        "\n\nTest of pipeline scheduling for "
            + filter.name()
            + " example without cumulative constraint");
    log.info(WITH_PREFIX + addNum + ADDERS_AND + mulNum + MULTIPLIERS);
    log.info(ADD_DURATION + filter.addDel() + AND_MUL_DURATION + filter.mulDel());

    List<List<IntVar>> taskVars = makeConstraintsPipeline(store, filter, addNum, mulNum);

    int pipeLb = computePipelineLowerBound(filter, addNum, mulNum);
    log.info("Lower bound = " + pipeLb);

    List<IntVar> cc = new ArrayList<>();
    cc.add(new IntVar(store, 10000, 10000));
    cc.add(cost);
    taskVars.add(cc);

    final SelectChoicePoint<IntVar> select =
        new SimpleMatrixSelect<>(
            taskVarsToMatrix(taskVars),
            new SmallestMax<>(),
            new MostConstrainedStatic<>(),
            new IndomainMin<>(),
            0);

    CreditCalculator<IntVar> credit = new CreditCalculator<>(taskVars.size(), 20, 10);
    Search<IntVar> search = new DepthFirstSearch<>();
    attachCreditListeners(search, credit);

    checkConsistency(
        store, "6. Constraints consistent", () -> store.impose(new XgteqC(cost, pipeLb)));

    final long t1 = System.currentTimeMillis();
    boolean result = search.labeling(store, select, cost);
    log.info(EXECUTION_TIME_PREFIX + (System.currentTimeMillis() - t1) + " ms");

    return reportResult(result);
  }

  /**
   * It optimizes scheduling of filter operations. It performs algorithmic pipelining three times.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param addNum number of adders available.
   * @param mulNum number of multipliers available.
   * @return cost of the solution or -1 if no solution found.
   */
  public static int experiment2P(Store store, Filter filter, int addNum, int mulNum) {

    log.info(
        "\n\nTest of pipeline scheduling for "
            + filter.name()
            + " example without cumulative constraint");
    log.info(WITH_PREFIX + addNum + ADDERS_AND + mulNum + MULTIPLIERS);
    log.info(ADD_DURATION + filter.addDel() + AND_MUL_DURATION + filter.mulDel());

    List<List<IntVar>> taskVars = makeConstraintsPipeline(store, filter, addNum, mulNum);
    int pipeLb = computePipelineLowerBound(filter, addNum, mulNum);
    log.info("Lower bound = " + pipeLb);

    final SelectChoicePoint<IntVar> selectMc =
        new SimpleSelect<>(
            listToArray(taskStarts),
            new SmallestMin<>(),
            new MostConstrainedStatic<>(),
            new IndomainMin<>());
    final SelectChoicePoint<IntVar> selectIo =
        new SimpleSelect<>(listToArray(taskResources), null, null, new IndomainMin<>());

    CreditCalculator<IntVar> credit = new CreditCalculator<>(taskVars.size() / 2, 5, 10);
    Search<IntVar> search = new DepthFirstSearch<>();
    attachCreditListeners(search, credit);

    checkConsistency(
        store, "7. Constraints consistent", () -> store.impose(new XgteqC(cost, pipeLb)));

    return reportResult(runTwoPhaseLabelingWithTiming(store, selectMc, selectIo, search));
  }

  /**
   * It optimizes scheduling of filter operations.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param addNum number of adders available.
   * @param mulNum number of multipliers available.
   * @return cost of the solution or -1 if no solution found.
   */
  public static int experiment2(Store store, Filter filter, int addNum, int mulNum) {
    printExperimentHeader(filter, addNum, mulNum);
    final SelectChoicePoint<IntVar> selectMc =
        new SimpleSelect<>(
            listToArray(taskStarts),
            new MostConstrainedStatic<>(),
            new SmallestDomain<>(),
            new IndomainMin<>());
    final SelectChoicePoint<IntVar> selectIo =
        new SimpleSelect<>(listToArray(taskResources), null, null, new IndomainMin<>());
    return runTwoPhaseExperiment(
        store,
        null,
        () -> makeConstraints(store, filter, addNum, mulNum),
        selectMc,
        selectIo,
        "8. Constraints consistent",
        null,
        null);
  }

  /**
   * It optimizes scheduling of filter operation in fashion allowing chaining of operations within
   * one clock cycle.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param addNum number of adders available.
   * @param mulNum number of multipliers available.
   * @param clock number of time units within a clock.
   * @return cost of the solution or -1 if no solution found.
   */
  public static int experiment2C(Store store, Filter filter, int addNum, int mulNum, int clock) {
    printExperimentHeader(filter, addNum, mulNum, clock);
    final SelectChoicePoint<IntVar> selectMc =
        new SimpleSelect<>(
            listToArray(taskStarts),
            new SmallestMin<>(),
            new MostConstrainedStatic<>(),
            new IndomainMin<>());
    final SelectChoicePoint<IntVar> selectIo =
        new SimpleSelect<>(listToArray(taskResources), null, null, new IndomainMin<>());
    return runTwoPhaseExperiment(
        store,
        null,
        () -> makeConstraintsChain(store, filter, addNum, mulNum, clock),
        selectMc,
        selectIo,
        "10. Constraints consistent",
        () -> "Schedule length: " + div(cost.min(), clock),
        null);
  }

  /**
   * It creates constraint model for scheduling of filter operations.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param addNum number of adders available.
   * @param mulNum number of multipliers available.
   * @return start time and resource assignment variables describing the scheduling problem.
   */
  public static List<List<IntVar>> makeConstraints(
      Store store, Filter filter, int addNum, int mulNum) {

    ResourceRanges ranges = new ResourceRanges(addNum, mulNum);
    int[][] dependencies = filter.dependencies();
    int[] delays = filter.delays();
    int[] lastOp = filter.lastOp();
    IntVar addDelay = new IntVar(store, filter.addDel(), filter.addDel());
    IntVar mulDelay = new IntVar(store, filter.mulDel(), filter.mulDel());
    IntVar one = new IntVar(store, 1, 1);

    IntVar[] startTimes = new IntVar[delays.length];
    IntVar[] resources = new IntVar[delays.length];
    int[] durations = new int[delays.length];

    IntVar[] startTimesAdd = new IntVar[filter.noAdd()];
    IntVar[] resourcesAdd = new IntVar[filter.noAdd()];
    IntVar[] durationsAdd = new IntVar[filter.noAdd()];
    IntVar[] resourceUsageAdd = new IntVar[filter.noAdd()];

    IntVar[] startTimesMul = new IntVar[filter.noMul()];
    IntVar[] resourcesMul = new IntVar[filter.noMul()];
    IntVar[] durationsMul = new IntVar[filter.noMul()];
    IntVar[] resourceUsageMul = new IntVar[filter.noMul()];

    populateResourceArrays(
        store,
        filter,
        ranges,
        startTimes,
        resources,
        durations,
        startTimesAdd,
        resourcesAdd,
        durationsAdd,
        resourceUsageAdd,
        startTimesMul,
        resourcesMul,
        durationsMul,
        resourceUsageMul,
        addDelay,
        mulDelay,
        one,
        0,
        100);

    cost =
        createDependencyAndCostConstraints(
            store, dependencies, delays, lastOp, startTimes, durations, null, 100);

    store.impose(new Diffn(startTimesAdd, resourcesAdd, durationsAdd, resourceUsageAdd));
    store.impose(new Diffn(startTimesMul, resourcesMul, durationsMul, resourceUsageMul));

    IntVar limitAdd = new IntVar(store, 1, addNum);
    store.impose(
        new Cumulative(startTimesAdd, durationsAdd, resourceUsageAdd, limitAdd, true, false));
    IntVar limitMul = new IntVar(store, 1, mulNum);
    store.impose(
        new Cumulative(startTimesMul, durationsMul, resourceUsageMul, limitMul, true, false));

    finalizeStaticFields(startTimes, resources, durations, filter.names());

    return makeLabelingList(startTimes, resources);
  }

  /**
   * It creates constraint model for scheduling of filter operation in fashion allowing pipelining
   * of multiplication operations.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param addNum number of adders available.
   * @param mulNum number of multipliers available.
   * @return start time and resource assignment variables describing the scheduling problem.
   */
  public static List<List<IntVar>> makeConstraintsPipeMultiplier(
      Store store, Filter filter, int addNum, int mulNum) {

    ResourceRanges ranges = new ResourceRanges(addNum, mulNum);
    int[][] dependencies = filter.dependencies();
    int[] delays = filter.delays();
    int[] lastOp = filter.lastOp();
    IntVar addDelay = new IntVar(store, filter.addDel(), filter.addDel());
    IntVar mulDelay =
        new IntVar(store, 1, 1); // since pipelined multiplier the effective delay is 1
    IntVar one = new IntVar(store, 1, 1);

    IntVar[] startTimes = new IntVar[delays.length];
    IntVar[] resources = new IntVar[delays.length];
    int[] durations = new int[delays.length];

    IntVar[] startTimesAdd = new IntVar[filter.noAdd()];
    IntVar[] resourcesAdd = new IntVar[filter.noAdd()];
    IntVar[] durationsAdd = new IntVar[filter.noAdd()];
    IntVar[] resourceUsageAdd = new IntVar[filter.noAdd()];

    IntVar[] startTimesMul = new IntVar[filter.noMul()];
    IntVar[] resourcesMul = new IntVar[filter.noMul()];
    IntVar[] durationsMul = new IntVar[filter.noMul()];
    IntVar[] resourceUsageMul = new IntVar[filter.noMul()];

    populateResourceArrays(
        store,
        filter,
        ranges,
        startTimes,
        resources,
        durations,
        startTimesAdd,
        resourcesAdd,
        durationsAdd,
        resourceUsageAdd,
        startTimesMul,
        resourcesMul,
        durationsMul,
        resourceUsageMul,
        addDelay,
        mulDelay,
        one,
        0,
        100);

    cost =
        createDependencyAndCostConstraints(
            store, dependencies, delays, lastOp, startTimes, durations, null, 100);

    store.impose(new Diffn(startTimesAdd, resourcesAdd, durationsAdd, resourceUsageAdd));
    store.impose(new Diffn(startTimesMul, resourcesMul, durationsMul, resourceUsageMul));

    IntVar limitAdd = new IntVar(store, 0, addNum);
    store.impose(
        new Cumulative(startTimesAdd, durationsAdd, resourceUsageAdd, limitAdd, true, false));
    IntVar limitMul = new IntVar(store, 0, mulNum);
    store.impose(
        new Cumulative(startTimesMul, durationsMul, resourceUsageMul, limitMul, true, false));

    finalizeStaticFields(startTimes, resources, durations, filter.names());

    return makeLabelingList(startTimes, resources);
  }

  /**
   * It creates constraint model for scheduling of filter operation in fashion allowing chaining of
   * operations within one clock cycle.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param addNum number of adders available.
   * @param mulNum number of multipliers available.
   * @param clk number of time units within a clock.
   * @return start time and resource assignment variables describing the scheduling problem.
   */
  public static List<List<IntVar>> makeConstraintsChain(
      Store store, Filter filter, int addNum, int mulNum, int clk) {

    ResourceRanges ranges = new ResourceRanges(addNum, mulNum);
    int[][] dependencies = filter.dependencies();
    int[] delays = filter.delays();
    int[] lastOp = filter.lastOp();

    IntVar addDelay = new IntVar(store, filter.addDel(), filter.addDel());
    IntVar mulDelay = new IntVar(store, filter.mulDel(), filter.mulDel());
    IntVar one = new IntVar(store, 1, 1);

    IntVar[] startTimes = new IntVar[delays.length];
    IntVar[] clockTimes = new IntVar[delays.length];
    IntVar[] stepTimes = new IntVar[delays.length];
    IntVar[] resources = new IntVar[delays.length];
    int[] durations = new int[delays.length];

    IntVar[] startTimesAdd = new IntVar[filter.noAdd()];
    IntVar[] clockTimesAdd = new IntVar[filter.noAdd()];
    IntVar[] resourcesAdd = new IntVar[filter.noAdd()];
    IntVar[] durationsAdd = new IntVar[filter.noAdd()];
    IntVar[] resourceUsageAdd = new IntVar[filter.noAdd()];

    IntVar[] startTimesMul = new IntVar[filter.noMul()];
    IntVar[] clockTimesMul = new IntVar[filter.noMul()];
    IntVar[] resourcesMul = new IntVar[filter.noMul()];
    IntVar[] durationsMul = new IntVar[filter.noMul()];
    IntVar[] durationsMulClock = new IntVar[filter.noMul()];
    IntVar[] resourceUsageMul = new IntVar[filter.noMul()];

    String nameT = "T";
    String nameR = "R";
    int j = 0;
    int k = 0;
    for (int i = 0; i < delays.length; i++) {
      String t = nameT + i;
      String r = nameR + i;

      startTimes[i] = new IntVar(store, t, 0, 1000);
      clockTimes[i] = new IntVar(store, "Tclock" + i, 0, 100);

      if (filter.ids()[i] == filter.addId()) {

        stepTimes[i] = new IntVar(store, "Tstep" + i, 0, clk - filter.addDel());
        resources[i] = new IntVar(store, r, ranges.addMin, ranges.addMax);
        startTimesAdd[j] = startTimes[i];
        clockTimesAdd[j] = clockTimes[i];
        resourcesAdd[j] = resources[i];
        durationsAdd[j] = addDelay;
        durations[i] = filter.addDel();
        resourceUsageAdd[j] = one;

        j++;
      } else {
        stepTimes[i] = new IntVar(store, "Tstep" + i, 0, clk - filter.mulDel());
        resources[i] = new IntVar(store, r, ranges.mulMin, ranges.mulMax);
        startTimesMul[k] = startTimes[i];
        clockTimesMul[k] = clockTimes[i];
        resourcesMul[k] = resources[i];
        durations[i] = filter.mulDel();
        durationsMul[k] = mulDelay;
        durationsMulClock[k] = addDelay;
        resourceUsageMul[k] = one;

        k++;
      }

      IntVar temp = new IntVar(store, 0, 1000);
      store.impose(new XmulCeqZ(clockTimes[i], clk, temp));
      store.impose(new XplusYeqZ(temp, stepTimes[i], startTimes[i]));
    }

    cost =
        createDependencyAndCostConstraints(
            store, dependencies, delays, lastOp, startTimes, durations, null, 1000);

    store.impose(new Diffn(startTimesAdd, resourcesAdd, durationsAdd, resourceUsageAdd));
    store.impose(new Diffn(startTimesMul, resourcesMul, durationsMul, resourceUsageMul));

    store.impose(new Diffn(clockTimesMul, resourcesMul, durationsMulClock, resourceUsageMul));

    store.impose(new Diffn(clockTimesAdd, resourcesAdd, durationsAdd, resourceUsageAdd));

    IntVar limitAdd = new IntVar(store, 1, addNum);
    store.impose(
        new Cumulative(clockTimesAdd, durationsAdd, resourceUsageAdd, limitAdd, true, false));
    IntVar limitMul = new IntVar(store, 1, mulNum);
    store.impose(
        new Cumulative(startTimesMul, durationsMul, resourceUsageMul, limitMul, true, false));

    finalizeStaticFields(startTimes, resources, durations, filter.names());

    return makeLabelingList(startTimes, resources);
  }

  /**
   * It creates a model for optimization of scheduling of operations of a given filter. The
   * pipelined model assumes that the filter is unrolled three times.
   *
   * @param store constraint store in which the constraints are imposed.
   * @param filter filter for which pipelined execution is optimized.
   * @param addNum number of available adders
   * @param mulNum number of available multipliers.
   * @return variables corresponding to start time and resource assignment of the filter operations.
   */
  public static List<List<IntVar>> makeConstraintsPipeline(
      Store store, Filter filter, int addNum, int mulNum) {

    final int addMin = 1;
    final int addMax = addMin + addNum - 1;
    final int mulMin = addMax + 1;
    final int mulMax = mulMin + mulNum - 1;

    String nameT = "T";
    String nameR = "R";

    int[][] dependencies = filter.dependencies();
    int[] delays = filter.delays();
    int[] lastOp = filter.lastOp();
    IntVar addDelay = new IntVar(store, filter.addDel(), filter.addDel());
    IntVar mulDelay = new IntVar(store, filter.mulDel(), filter.mulDel());
    IntVar pipe = new IntVar(store, "InitRate", 1, 100);
    IntVar pipe2 = new IntVar(store, "InitRate*2", 1, 100);
    store.impose(new XmulCeqZ(pipe, 2, pipe2));
    IntVar pipe3 = new IntVar(store, "InitRate*3", 1, 100);
    store.impose(new XmulCeqZ(pipe, 3, pipe3));
    IntVar one = new IntVar(store, 1, 1);

    IntVar[] startTimes = new IntVar[delays.length];
    IntVar[] startTimesA = new IntVar[delays.length];
    IntVar[] startTimesB = new IntVar[delays.length];
    IntVar[] resources = new IntVar[delays.length];
    int[] durations = new int[delays.length];

    IntVar[] startTimesAdd = new IntVar[3 * filter.noAdd()];
    IntVar[] resourcesAdd = new IntVar[3 * filter.noAdd()];
    IntVar[] durationsAdd = new IntVar[3 * filter.noAdd()];
    IntVar[] resourceUsageAdd = new IntVar[3 * filter.noAdd()];

    IntVar[] startTimesMul = new IntVar[3 * filter.noMul()];
    IntVar[] resourcesMul = new IntVar[3 * filter.noMul()];
    IntVar[] durationsMul = new IntVar[3 * filter.noMul()];
    IntVar[] resourceUsageMul = new IntVar[3 * filter.noMul()];

    int j = 0;
    int k = 0;

    for (int i = 0; i < delays.length; i++) {
      final String t = nameT + i;
      final String ta = nameT + "a" + i;
      final String tb = nameT + "b" + i;
      final String r = nameR + i;

      startTimes[i] = new IntVar(store, t, 0, 100);
      startTimesA[i] = new IntVar(store, ta, 0, 100);
      startTimesB[i] = new IntVar(store, tb, 0, 100);
      store.impose(new XplusYeqZ(startTimes[i], pipe, startTimesA[i]));
      store.impose(new XplusYeqZ(startTimes[i], pipe2, startTimesB[i]));

      if (filter.ids()[i] == filter.addId()) {

        resources[i] = new IntVar(store, r, addMin, addMax);
        startTimesAdd[3 * j] = startTimes[i];
        startTimesAdd[3 * j + 1] = startTimesA[i];
        startTimesAdd[3 * j + 2] = startTimesB[i];
        resourcesAdd[3 * j] = resources[i];
        resourcesAdd[3 * j + 1] = resources[i];
        resourcesAdd[3 * j + 2] = resources[i];
        durationsAdd[3 * j] = addDelay;
        durationsAdd[3 * j + 1] = addDelay;
        durationsAdd[3 * j + 2] = addDelay;
        durations[i] = filter.addDel();
        resourceUsageAdd[3 * j] = one;
        resourceUsageAdd[3 * j + 1] = one;
        resourceUsageAdd[3 * j + 2] = one;

        j++;
      } else {
        resources[i] = new IntVar(store, r, mulMin, mulMax);
        startTimesMul[3 * k] = startTimes[i];
        startTimesMul[3 * k + 1] = startTimesA[i];
        startTimesMul[3 * k + 2] = startTimesB[i];
        resourcesMul[3 * k] = resources[i];
        resourcesMul[3 * k + 1] = resources[i];
        resourcesMul[3 * k + 2] = resources[i];
        durationsMul[3 * k] = mulDelay;
        durationsMul[3 * k + 1] = mulDelay;
        durationsMul[3 * k + 2] = mulDelay;
        durations[i] = filter.mulDel();
        resourceUsageMul[3 * k] = one;
        resourceUsageMul[3 * k + 1] = one;
        resourceUsageMul[3 * k + 2] = one;

        IntVar temp1 = new IntVar(store, 0, 100);
        store.impose(new XplusCeqZ(startTimes[i], 1, temp1));
        store.impose(new XneqY(temp1, pipe));
        IntVar temp2 = new IntVar(store, 0, 100);
        store.impose(new XplusCeqZ(startTimes[i], 1, temp2));
        store.impose(new XneqY(temp2, pipe2));

        k++;
      }
    }

    for (int[] dependency : dependencies) {
      store.impose(
          new XplusClteqZ(
              startTimes[dependency[0]], delays[dependency[0]], startTimes[dependency[1]]));
    }

    List<IntVar> endOp = new ArrayList<>();
    for (int value : lastOp) {
      IntVar end = new IntVar(store, 0, 100);
      store.impose(new XplusCeqZ(startTimes[value], durations[value], end));
      endOp.add(end);
    }
    IntVar cost = new IntVar(store, 0, 100);
    store.impose(new Max(endOp, cost));

    store.impose(new XlteqY(cost, pipe3));

    store.impose(new Diffn(startTimesAdd, resourcesAdd, durationsAdd, resourceUsageAdd));
    store.impose(new Diffn(startTimesMul, resourcesMul, durationsMul, resourceUsageMul));

    taskStarts = new ArrayList<>();
    taskStarts.addAll(Arrays.asList(startTimes));
    taskStarts.addAll(Arrays.asList(startTimesA));
    taskStarts.addAll(Arrays.asList(startTimesB));

    taskResources = new ArrayList<>();
    taskResources.addAll(Arrays.asList(resources));
    taskResources.addAll(Arrays.asList(resources));
    taskResources.addAll(Arrays.asList(resources));

    taskDurations = new ArrayList<>();
    for (Integer v : durations) {
      taskDurations.add(v);
    }
    for (int v : durations) {
      taskDurations.add(v);
    }
    for (int v : durations) {
      taskDurations.add(v);
    }

    taskNames = filter.namesPipeline();
    FilterBenchmark.cost = pipe;

    return makeLabelingList(startTimes, resources);
  }

  /**
   * It creates an array of arrays using two arrays.
   *
   * @param t an array of variables corresponding to start time of an operation.
   * @param r an array of variables corresponding to resource of an operation.
   * @return an array of arrays, each array containing one starttime and one resource assignment
   *     variable.
   */
  public static List<List<IntVar>> makeLabelingList(IntVar[] t, IntVar[] r) {

    List<List<IntVar>> list = new ArrayList<>();

    for (int i = 0; i < t.length; i++) {
      List<IntVar> tr = new ArrayList<>();
      tr.add(t[i]);
      tr.add(r[i]);
      list.add(tr);
    }
    return list;
  }
}
