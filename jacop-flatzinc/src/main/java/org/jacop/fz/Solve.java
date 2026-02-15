/*
 * Solve.java
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

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.text.NumberFormat;
import java.util.ArrayList;
import java.util.Locale;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XplusYeqC;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.LargestDomainFloat;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.satwrapper.SatTranslation;
import org.jacop.search.AfcMax;
import org.jacop.search.AfcMaxDeg;
import org.jacop.search.ComparatorVariable;
import org.jacop.search.CreditCalculator;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.FailConstraintsStatistics;
import org.jacop.search.IndomainMin;
import org.jacop.search.InitializeListener;
import org.jacop.search.Lds;
import org.jacop.search.PrioritySearch;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.restart.Calculator;
import org.jacop.search.restart.ConstantCalculator;
import org.jacop.search.restart.GeometricCalculator;
import org.jacop.search.restart.LinearCalculator;
import org.jacop.search.restart.LubyCalculator;
import org.jacop.search.restart.RestartSearch;
import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMin;

/**
 * The parser part responsible for parsing the solve part of the flatzinc file, building a related
 * search and executing it.
 *
 * <p>Current implementation runs also final search on all variables to ensure that they are ground.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class Solve<T extends Var> implements ParserTreeConstants {

  static final String P = System.getProperty("fz_system_timer");
  final Store store;
  final boolean debug = false;
  final boolean print_search_info = false;
  final SatTranslation sat;
  final NumberFormat nf = NumberFormat.getInstance(Locale.of("en"));
  public StringBuffer lastSolution;
  Tables dictionary;
  Options options;
  int initNumberConstraints;
  Timer timer;
  long startCpu;
  long initTime;
  long searchTime;
  SelectChoicePoint<T> variable_selection;
  ArrayList<Search<T>> list_seq_searches;
  boolean heuristicSeqSearch;
  Var costVariable;
  // restart search
  Calculator restartCalculator;
  RestartSearch<T> rs;
  // -------- for print-out of statistics
  boolean singleSearch;
  boolean result;
  boolean optimization;
  boolean minimize;
  SearchItem<T> si;
  // single search
  boolean defaultSearch;
  DepthFirstSearch<T> label;
  // --------
  DepthFirstSearch<T>[] final_search;
  // sequence search
  Search<T> final_search_seq;
  // Values for search created from flatzinc
  DepthFirstSearch<T> flatzincDfs;
  SelectChoicePoint<T> flatzincVariableSelection;
  Var flatzincCost;
  int solveKind = -1;
  FailConstraintsStatistics failStatistics;
  int numberSolutions;
  // relax and reconstruct
  IntVar[] relaxVars;
  int probability;
  int finalNumberSolutions;

  // Search type literals
  private static final String INT_SEARCH = "int_search";
  private static final String SET_SEARCH = "set_search";
  private static final String BOOL_SEARCH = "bool_search";
  private static final String FLOAT_SEARCH = "float_search";
  private static final String SEQ_SEARCH = "seq_search";
  private static final String PRIORITY_SEARCH = "priority_search";
  private static final String WARM_START = "warm_start";
  private static final String COMPLETE = "complete";
  // Solve kind literals
  private static final String SATISFY = "satisfy";
  private static final String MINIMIZE = "minimize";
  private static final String MAXIMIZE = "maximize";
  // Output message literals
  private static final String SEPARATOR_LINE = "==========";
  private static final String TIME_OUT_MSG = "%% =====TIME-OUT=====";
  private static final String MZN_STAT_OBJECTIVE = "%%%mzn-stat: objective=";

  /**
   * It creates a parser for the solve part of the flatzinc file.
   *
   * @param store the constraint store within which context the search will take place.
   * @param sat sat translation used
   */
  public Solve(Store store, SatTranslation sat) {
    this.store = store;
    this.sat = sat;
    this.nf.setGroupingUsed(false);
  }

  /**
   * Solves the flatzinc model represented by the AST tree.
   *
   * @param astTree the abstract syntax tree of the model
   * @param table the tables containing all variable definitions
   * @param opt the options for solving
   */
  public void solveModel(SimpleNode astTree, Tables table, Options opt) {

    dictionary = table;

    // use restart search if defined by options in command line;
    // default "none"
    switch (opt.getRestartType()) {
      case NONE:
        break;
      case CONSTANT:
        restartCalculator = new ConstantCalculator(opt.getRestartScale());
        break;
      case LINEAR:
        restartCalculator = new LinearCalculator(opt.getRestartScale());
        break;
      case LUBY:
        restartCalculator = new LubyCalculator(opt.getRestartScale());
        break;
      case GEOMETRIC:
        restartCalculator = new GeometricCalculator(opt.getRestartBase(), opt.getRestartScale());
        break;
      default:
        throw new RuntimeException("Internal error; wrong restart type");
    }

    int n = astTree.jjtGetNumChildren();

    for (int i = 0; i < n; i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);

      if (node.getId() == JJTMODELEND) {
        search((ASTSolveItem) node.jjtGetChild(0), table, opt);
      }
    }
  }

  /**
   * It parses the solve part.
   *
   * @param node the current parsing node.
   * @param table the table containing all the various variable definitions encoutered thus far.
   * @param opt option specifies to flatzinc parser in respect to search (e.g. all solutions).
   */
  public void search(ASTSolveItem node, Tables table, Options opt) {

    if (opt.debug()) {
      failStatistics = new FailConstraintsStatistics(store);
    }

    store.setDecay(opt.getDecay());

    initNumberConstraints = store.numberConstraints();

    // Get runtime system
    Runtime runtime = Runtime.getRuntime();
    long modelMem = (runtime.totalMemory() - runtime.freeMemory()) / (1024 * 1024);

    dictionary = table;

    if (opt.debug()) {
      IO.println(
          "%% Model constraints defined.\n%% Variables = "
              + store.size()
              + " and  Bool variables = "
              + dictionary.getNumberBoolVariables()
              + " of that constant variables = "
              + table.constantTable.size()
              + "\n%% Constraints = "
              + (initNumberConstraints - 1)
              + ", SAT clauses = "
              + sat.numberClauses()
              + "\n%% Memory used by the model = "
              + modelMem
              + "[MB]");
    }

    options = opt;
    solveKind = -1;

    ASTSolveKind kind;
    int count = node.jjtGetNumChildren();

    if (count == 1) { // only solve kind => default search
      kind = (ASTSolveKind) node.jjtGetChild(0);
      solveKind = getKind(kind.getKind());
      run_single_search(solveKind, kind, null);
    } else if (count == 2) { // single annotation
      SearchItem<T> si = new SearchItem<>(store, dictionary);
      si.searchParameters(node, 0);
      kind = (ASTSolveKind) node.jjtGetChild(1);
      solveKind = getKind(kind.getKind());
      runSearchForSingleAnnotation(opt, kind, solveKind, si, node);
    } else if (count > 2) { // several annotations

      SearchItem<T> si = new SearchItem<>(store, dictionary);
      si.searchParametersForSeveralAnnotations(node, 0);

      ArrayList<SearchItem<T>> nsi = parseSearchAnnotations(si.search_seq);

      if (nsi.size() == 1) { // single search (int, set, float, seq or priority) + other annotations
        // (restart_*)
        SearchItem<T> fs = nsi.getFirst();

        kind = (ASTSolveKind) node.jjtGetChild(si.search_seqSize());
        solveKind = getKind(kind.getKind());

        if (SEQ_SEARCH.equals(fs.type())) {
          run_sequence_search(solveKind, kind, fs);
        } else {
          run_single_search(solveKind, kind, fs);
        }
      } else {
        kind = (ASTSolveKind) node.jjtGetChild(si.search_seqSize());
        solveKind = getKind(kind.getKind());

        // create seq_search from a number of searches without
        // explicit sq_search annotation (no order defined)
        SearchItem<T> siq = new SearchItem<>(store, dictionary);
        siq.setSearchType(SEQ_SEARCH);
        for (SearchItem<T> se : nsi) {
          siq.addSearch(se);
        }

        run_sequence_search(solveKind, kind, siq);
      }
    } else {
      throw new IllegalArgumentException(
          "%% Error: Not recognized structure of solve statement; compilation aborted");
    }
  }

  private void runSearchForSingleAnnotation(
      Options opt, ASTSolveKind kind, int solveKind, SearchItem<T> si, SimpleNode node) {
    String search_type = si.type();
    if (opt.freeSearch()) {
      run_single_search(solveKind, kind, null);
      return;
    }
    if (INT_SEARCH.equals(search_type)
        || SET_SEARCH.equals(search_type)
        || BOOL_SEARCH.equals(search_type)
        || FLOAT_SEARCH.equals(search_type)
        || PRIORITY_SEARCH.equals(search_type)
        || WARM_START.equals(search_type)
        || (search_type != null && search_type.startsWith("restart_"))) {
      run_single_search(solveKind, kind, si);
      return;
    }
    if (SEQ_SEARCH.equals(search_type)) {
      run_sequence_search(solveKind, kind, si);
      return;
    }
    String warnType = search_type;
    if ("$expr".equals(search_type)) {
      warnType = ((ASTScalarFlatExpr) node.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0)).getIdent();
    }
    System.err.println(
        "%% Warning: Not supported search annotation: \"" + warnType + "\"; ignored");
    run_single_search(solveKind, kind, null);
  }

  /**
   * Parses search annotations and filters them into a list.
   *
   * @param searchSeq the list of search items to parse
   * @return the filtered list of search items
   */
  ArrayList<SearchItem<T>> parseSearchAnnotations(ArrayList<SearchItem<T>> searchSeq) {
    ArrayList<SearchItem<T>> ns = new ArrayList<>();

    for (SearchItem<T> s : searchSeq) {
      if ("restart_none".equals(s.search_type)) {
      } else if ("restart_constant".equals(s.search_type)
          || "restart_linear".equals(s.search_type)
          || "restart_geometric".equals(s.search_type)
          || "restart_luby".equals(s.search_type)) {
        if (!options.freeSearch()) {
          restartCalculator = s.restartCalculator;
        }
      } else if ("relax_and_reconstruct".equals(s.search_type)) {
        relaxVars = s.relax_and_reconstruct_variables;
        probability = s.probability;
      } else if (s.search_type.endsWith("_search")) {
        ns.add(s);
      } else if (s.search_type.endsWith(WARM_START)) {
        ns.addFirst(s);
      } else {
        System.err.println(
            "%% Warning: Not supported search annotation: " + s.search_type + "; ignored.");
      }
    }

    return ns;
  }

  @SuppressWarnings("unchecked")
  void run_single_search(int solveKind, SimpleNode kind, SearchItem<T> si) {

    singleSearch = true;

    defaultSearch = false;

    this.si = si;

    if (solveKind == 1) {
      minimize = true;
    }

    if (options.debug()) {
      printSolveKindDebug(solveKind, kind, si);
    }

    label = null;
    optimization = solveKind > 0;
    list_seq_searches = new ArrayList<>();

    label = null;
    si = applySearchItemToLabel(si);

    // Set up cost variable before sub-search setup so constraints are visible
    Var costVar = null;
    if (solveKind > 0) {
      costVar = setupCostVariable(kind, solveKind);
    }

    // adds child search for cost; to be sure that all variables get a value
    final_search = setSubSearchForAll(label, options);

    if (si == null) {
      defaultSearch = true;
      si = new SearchItem<>(store, dictionary);
      si.explore = COMPLETE;
      resolveLabelFromFinalSearch(final_search);
    } else {
      for (DepthFirstSearch<T> s : final_search) {
        if (s != null) {
          list_seq_searches.add(s);
        }
      }
    }
    list_seq_searches.getLast();

    applyHeuristicSearch(label, si);

    result = false;

    long currentTime = timer.getCpuTime();
    initTime = currentTime - startCpu;
    startCpu = currentTime;

    if (si.exploration() == null
        || COMPLETE.equals(si.exploration())
        || "lds".equals(si.exploration())
        || "credit".equals(si.exploration())) {
      FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

      if (options.getAll()) { // all solutions
        if (restartCalculator != null) {
          throw new IllegalArgumentException(
              "Flatzinc option for search for all solutions (-a) cannot be used in restart search.");
        }
        searchForAll(label);
      }

      this.si = si;

      String solveType;
      switch (solveKind) {
        case 0:
          solveType = SATISFY;
          break;
        case 1:
          solveType = MINIMIZE;
          break;
        case 2:
          solveType = MAXIMIZE;
          break;
        default:
          throw new IllegalArgumentException(
              "Not recognized or supported search strategy; compilation aborted");
      }

      result = executeSearch(label, costVar, solveType);
      if (!options.runSearch()) {
        return;
      }
    } else {
      throw new IllegalArgumentException(
          "Not recognized or supported "
              + si.exploration()
              + " search explorarion strategy ; compilation aborted");
    }

    if (!options.getAll() && lastSolution != null) {
      helperSolutionPrinter(lastSolution.toString());
    }

    printStatisticsForSingleSearch(false, result);
  }

  /**
   * Applies the search item to set the main search label. Returns the search item to use for the
   * rest of run_single_search, or null for default/restart handling.
   */
  private SearchItem<T> applySearchItemToLabel(SearchItem<T> si) {
    if (si == null) {
      return null;
    }
    if (INT_SEARCH.equals(si.type()) || BOOL_SEARCH.equals(si.type())) {
      label = int_search(si);
    } else if (SET_SEARCH.equals(si.type())) {
      label = set_search(si);
    } else if (FLOAT_SEARCH.equals(si.type())) {
      label = float_search(si);
    } else if (PRIORITY_SEARCH.equals(si.type())) {
      label = priority_search(si);
    } else if (WARM_START.equals(si.type())) {
      label = warm_start_search(si);
    } else if (si.type().startsWith("restart_")) {
      ArrayList<SearchItem<T>> sa = new ArrayList<>();
      sa.add(si);
      parseSearchAnnotations(sa);
      return null;
    } else {
      throw new IllegalArgumentException(
          "Not recognized or supported search type \"" + si.type() + "\"; compilation aborted");
    }
    list_seq_searches.add(label);
    label.setPrintInfo(false);
    setSearchTimeout(label);
    return si;
  }

  private void resolveLabelFromFinalSearch(DepthFirstSearch<T>[] finalSearch) {
    if (finalSearch[0] != null) {
      label = finalSearch[0];
      list_seq_searches.add(label);
      for (int i = 1; i < finalSearch.length; i++) {
        if (finalSearch[i] != null) {
          list_seq_searches.add(finalSearch[i]);
        }
      }
      return;
    }
    if (finalSearch[1] != null) {
      label = finalSearch[1];
      list_seq_searches.add(label);
      if (finalSearch[2] != null) {
        list_seq_searches.add(finalSearch[2]);
      }
      return;
    }
    if (finalSearch[2] != null) {
      label = finalSearch[2];
      list_seq_searches.add(label);
      if (finalSearch[3] != null) {
        list_seq_searches.add(finalSearch[3]);
      }
      return;
    }
    if (finalSearch[3] != null) {
      label = finalSearch[3];
      list_seq_searches.add(label);
    }
  }

  /**
   * Configures search to find all solutions.
   *
   * @param label the depth first search to configure
   */
  @SuppressWarnings("unchecked")
  void searchForAll(DepthFirstSearch<T> label) {

    DepthFirstSearch<T> s = label;
    DepthFirstSearch<T> parentSearch = null;
    do {
      s.getSolutionListener().recordSolutions(false);
      s.getSolutionListener().searchAll(true);

      if (parentSearch != null) {
        s.getSolutionListener().setParentSolutionListener(parentSearch.getSolutionListener());
      }

      parentSearch = s;
      // find next search
      if (s.childSearches == null) {
        s = null;
      } else {
        s = (DepthFirstSearch<T>) s.childSearches[0];
      }
    } while (s != null);
  }

  /**
   * Prints search statistics.
   *
   * @param result whether a solution was found
   */
  public void statistics(boolean result) {

    printStatistics(false, result);
  }

  /** Prints statistics when search is interrupted. */
  public void printStatisticsIterrupt() {
    printStatistics(true, result);
  }

  /**
   * Prints search statistics.
   *
   * @param interrupted whether the search was interrupted
   * @param result whether a solution was found
   */
  public void printStatistics(boolean interrupted, boolean result) {

    if (singleSearch) {
      printStatisticsForSingleSearch(interrupted, result);
    } else {
      printStatisticsForSeqSearch(interrupted, result);
    }
  }

  /**
   * Sets timeout on a search if timeout option is configured.
   *
   * @param search the search to set timeout on
   */
  void setSearchTimeout(Search<T> search) {
    int to = options.getTimeOut();
    if (to > 0) {
      search.setTimeOutMilliseconds(to);
    }
  }

  /**
   * Executes a search with optional restart and cost variable.
   *
   * @param label the depth first search to execute
   * @param costVar the cost variable (null for satisfy)
   * @param solveType the solve type string for debug output ("satisfy", "minimize", "maximize")
   * @return true if a solution was found, false otherwise
   */
  private boolean executeSearch(DepthFirstSearch<T> label, Var costVar, String solveType) {
    return executeSearch(label, variable_selection, costVar, solveType);
  }

  /**
   * Resolves the cost variable for a given solve expression, trying int first, then float.
   *
   * @param kind the solve kind AST node
   * @return the resolved cost variable
   */
  private Var resolveCostVar(SimpleNode kind) {
    Var cost = getCost((ASTSolveExpr) kind.jjtGetChild(0));
    return cost != null ? cost : getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
  }

  /**
   * Prints debug output showing the solve kind and search items.
   *
   * @param solveKind the solve kind (0=satisfy, 1=minimize, 2=maximize)
   * @param kind the AST node for the solve expression
   * @param si the search items
   */
  private void printSolveKindDebug(int solveKind, SimpleNode kind, SearchItem<T> si) {
    String solve =
        switch (solveKind) {
          case 0 -> "%% satisfy";
          case 1 -> "%% minimize(" + resolveCostVar(kind) + ") ";
          case 2 -> "%% maximize(" + resolveCostVar(kind) + ") ";
          default -> throw new RuntimeException("Internal error in " + getClass().getName());
        };
    IO.println(solve + " : " + si);
  }

  /**
   * Executes a search with optional restart and cost variable, using specified selection.
   *
   * @param label the depth first search to execute
   * @param select the choice point selector to use
   * @param costVar the cost variable (null for satisfy)
   * @param solveType the solve type string for debug output ("satisfy", "minimize", "maximize")
   * @return true if a solution was found, false otherwise
   */
  @SuppressWarnings("unchecked")
  private boolean executeSearch(
      DepthFirstSearch<T> label, SelectChoicePoint<T> select, Var costVar, String solveType) {
    if (!options.runSearch()) {
      flatzincDfs = label;
      flatzincVariableSelection = select;
      flatzincCost = costVar;
      return false;
    }
    try {
      if (restartCalculator != null) {
        return executeRestartSearch(label, select, costVar, solveType);
      }
      return executeNonRestartSearch(label, select, costVar, solveType);
    } catch (NumberSolutionsReached _) {
      return numberSolutions > 0;
    }
  }

  @SuppressWarnings("unchecked")
  private boolean executeRestartSearch(
      DepthFirstSearch<T> label, SelectChoicePoint<T> select, Var costVar, String solveType) {
    if (options.debug()) {
      IO.print("% RestartSearch(" + restartCalculator + "), ");
      label.setSelectChoicePoint(select);
      IO.print(" " + solveType + (costVar != null ? " (" + costVar + ") " : " "));
      printSearch(label);
    }
    rs =
        new RestartSearch<>(
            store, label, select, restartCalculator, costVar != null ? (T) costVar : null);
    rs.setRestartsLimit(options.getRestartLimit());
    setSearchTimeout(rs);
    if (relaxVars != null) {
      rs.setRelaxAndReconstruct(relaxVars, probability);
    }
    return rs.labeling();
  }

  private boolean executeNonRestartSearch(
      DepthFirstSearch<T> label, SelectChoicePoint<T> select, Var costVar, String solveType) {
    if (options.debug()) {
      label.setSelectChoicePoint(select);
      IO.print("% " + solveType + (costVar != null ? " (" + costVar + ") " : " "));
      printSearch(label);
    }
    if (costVar != null) {
      return label.labeling(store, select, costVar);
    }
    return label.labeling(store, select);
  }

  /**
   * Sets up cost variable for optimization (minimize or maximize).
   *
   * @param kind the solve kind AST node
   * @param solveKind the solve kind (1 for minimize, 2 for maximize)
   * @return the cost variable to use for optimization
   */
  private Var setupCostVariable(SimpleNode kind, int solveKind) {
    Var cost = getCost((ASTSolveExpr) kind.jjtGetChild(0));
    Var max_cost = null;

    if (cost != null) {
      if (solveKind == 1) { // minimize
        costVariable = cost;
        return cost;
      } else { // maximize
        max_cost =
            new IntVar(store, "-" + cost.id(), -((IntVar) cost).max(), -((IntVar) cost).min());
        pose(new XplusYeqC((IntVar) max_cost, (IntVar) cost, 0));
        costVariable = max_cost;
        return max_cost;
      }
    } else {
      cost = getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
      if (solveKind == 1) { // minimize
        costVariable = cost;
        return cost;
      } else { // maximize
        max_cost =
            new FloatVar(
                store, "-" + cost.id(), -((FloatVar) cost).max(), -((FloatVar) cost).min());
        pose(new PplusQeqR((FloatVar) max_cost, (FloatVar) cost, new FloatVar(store, 0.0, 0.0)));
        costVariable = max_cost;
        return max_cost;
      }
    }
  }

  void setSearchTimeout(RestartSearch<T> search) {
    int to = options.getTimeOut();
    if (to > 0) {
      search.setTimeOutMilliseconds(to);
    }
  }

  /**
   * Sets timeout on all searches in a list if timeout option is configured.
   *
   * @param searches the list of searches to set timeout on
   */
  void setSearchTimeout(ArrayList<Search<T>> searches) {
    int to = options.getTimeOut();
    if (to > 0) {
      for (Search<T> s : searches) {
        s.setTimeOutMilliseconds(to);
      }
    }
  }

  /**
   * Prints the result status based on search outcome.
   *
   * @param interrupted whether the search was interrupted
   * @param result whether a solution was found
   * @param timeoutOccurred whether a timeout occurred
   * @param isComplete whether the search exploration is complete
   */
  void printResultStatus(
      boolean interrupted, boolean result, boolean timeoutOccurred, boolean isComplete) {
    if (result || (rs != null && rs.atLeastOneSolution() && !interrupted)) {
      printResultStatusWhenSolutionFound(interrupted, timeoutOccurred, isComplete);
      return;
    }
    if (timeoutOccurred) {
      IO.println("=====UNKNOWN=====");
      IO.println(TIME_OUT_MSG);
      return;
    }
    if (interrupted) {
      IO.println("%% =====INTERRUPTED=====");
      return;
    }
    if (isComplete) {
      IO.println("=====UNSATISFIABLE=====");
      writeUnsatToOutputFile();
      return;
    }
    IO.println("=====UNKNOWN=====");
  }

  private void printResultStatusWhenSolutionFound(
      boolean interrupted, boolean timeoutOccurred, boolean isComplete) {
    if (!optimization && options.getAll()) {
      if (!interrupted) {
        if (isComplete
            && !timeoutOccurred
            && (options.getNumberSolutions() == -1
                || options.getNumberSolutions() > numberSolutions)
            && relaxVars == null) {
          IO.println(SEPARATOR_LINE);
        } else if (timeoutOccurred) {
          IO.println(TIME_OUT_MSG);
        }
      }
      return;
    }
    if (optimization) {
      if (!interrupted
          && isComplete
          && !timeoutOccurred
          && (options.getNumberSolutions() == -1 || options.getNumberSolutions() > numberSolutions)
          && relaxVars == null) {
        IO.println(SEPARATOR_LINE);
      } else if (!interrupted && timeoutOccurred) {
        IO.println(TIME_OUT_MSG);
      } else if (timeoutOccurred) {
        IO.println(TIME_OUT_MSG);
      }
    }
  }

  private void writeUnsatToOutputFile() {
    if (options.getOutputFilename().isEmpty()) {
      return;
    }
    try {
      Files.writeString(Path.of(options.getOutputFilename()), "=====UNSATISFIABLE=====");
    } catch (IOException e1) {
      log.error("Failed to write output to {}", options.getOutputFilename(), e1);
    }
  }

  /**
   * Prints statistics for single search execution.
   *
   * @param interrupted whether the search was interrupted
   * @param result whether a solution was found
   */
  void printStatisticsForSingleSearch(boolean interrupted, boolean result) {

    if (label == null) {
      IO.println("%% =====INTERRUPTED=====\n%% Model not yet posed..");
      return;
    }

    printResultStatus(interrupted, result, label.timeOutOccured, COMPLETE.equals(si.exploration()));

    if (options.getStatistics()) {
      int nodes = 0;
      int decisions = 0;
      int wrong = 0;
      int backtracks = 0;
      int depth = 0;
      int solutions = 0;

      if (!defaultSearch) {
        nodes = label.getNodes();
        decisions = label.getDecisions();
        wrong = label.getWrongDecisions();
        backtracks = label.getBacktracks();
        depth = label.getMaximumDepth();
        solutions = label.getSolutionListener().solutionsNo();
      }

      for (DepthFirstSearch<T> l : final_search) {
        if (l != null) {
          nodes += l.getNodes();
          decisions += l.getDecisions();
          wrong += l.getWrongDecisions();
          backtracks += l.getBacktracks();
          depth += l.getMaximumDepth();
          solutions =
              l instanceof PrioritySearch ? solutions : l.getSolutionListener().solutionsNo();
        }
      }

      printStatisticsOutput(nodes, wrong, depth, solutions);
    }
  }

  @SuppressWarnings("unchecked")
  DepthFirstSearch<T>[] setSubSearchForAll(DepthFirstSearch<T> label, Options opt) {

    DepthFirstSearch<T>[] intAndSetSearch = new DepthFirstSearch[4];

    DefaultSearchVars searchVars = new DefaultSearchVars(dictionary);

    if (!options.complementarySearch() && label != null) {
      // ==== Collect ALL OUTPUT variables ====
      searchVars.outputVars();
    }

    IntVar[] int_search_variables = searchVars.getIntVars();
    SetVar[] set_search_variables = searchVars.getSetVars();
    BooleanVar[] bool_search_variables = searchVars.getBoolVars();
    FloatVar[] float_search_variables = searchVars.getFloatVars();

    // if there are no output variables collect GUESSED SEARCH
    // VARIABLES override selection if option
    // "complementarySearch" or no search is defined is defined.
    if (int_search_variables.length == 0
            && bool_search_variables.length == 0
            && set_search_variables.length == 0
            && float_search_variables.length == 0
        || options.complementarySearch()
        || options.freeSearch()) {

      searchVars.defaultVars();

      int_search_variables = searchVars.getIntVars();
      set_search_variables = searchVars.getSetVars();
      bool_search_variables = searchVars.getBoolVars();
      float_search_variables = searchVars.getFloatVars();
    }

    if (opt.debug()) {
      IO.println(searchVars);
    }

    DepthFirstSearch<T> lastSearch = label;
    DepthFirstSearch<T> intSearch = new DepthFirstSearch<>();

    if (set_search_variables.length != 0) {
      // add set search containing all variables to be sure that they get a value
      DepthFirstSearch<T> setSearch = new DepthFirstSearch<>();

      if (opt.debug()) {
        setSearch.setConsistencyListener(failStatistics);
      }

      SelectChoicePoint<SetVar> setSelect =
          options.freeSearch() || options.complementarySearch()
              ? new SimpleSelect<>(
                  set_search_variables, new AfcMaxDeg<>(store), new IndomainSetMin<>())
              : new SimpleSelect<>(set_search_variables, null, new IndomainSetMin<>());

      if (variable_selection == null) {
        variable_selection = (SelectChoicePoint<T>) setSelect;
      }
      setSearch.setSelectChoicePoint((SelectChoicePoint<T>) setSelect);
      setSearch.setPrintInfo(false);
      if (lastSearch != null) {
        lastSearch.addChildSearch(setSearch);
      }
      lastSearch = setSearch;
      if (int_search_variables.length == 0
          && bool_search_variables.length == 0
          && float_search_variables.length == 0) {
        setSearch.setSolutionListener(new CostListener<>());
      }

      if (costVariable != null) {
        intSearch.setCostVar(costVariable);
        intSearch.setOptimize(true);
      }

      setSearchTimeout(setSearch);

      intAndSetSearch[0] = setSearch;
    }

    if (opt.debug()) {
      intSearch.setConsistencyListener(failStatistics);
    }

    if (int_search_variables.length != 0) {
      // add search containing int variables to be sure that they get a value
      SelectChoicePoint<IntVar> intSelect =
          options.freeSearch() || options.complementarySearch()
              ? new SimpleSelect<>(
                  int_search_variables, new AfcMaxDeg<>(store), new IndomainMin<>())
              : new SimpleSelect<>(int_search_variables, null, new IndomainMin<>());

      if (variable_selection == null) {
        variable_selection = (SelectChoicePoint<T>) intSelect;
      }
      intSearch.setSelectChoicePoint((SelectChoicePoint<T>) intSelect);
      intSearch.setPrintInfo(false);
      if (lastSearch != null) {
        lastSearch.addChildSearch(intSearch);
      }
      lastSearch = intSearch;
      if (bool_search_variables.length == 0 && float_search_variables.length == 0) {
        intSearch.setSolutionListener(new CostListener<>());

        if (costVariable != null) {
          intSearch.setCostVar(costVariable);
          intSearch.setOptimize(true);
        }
      }

      setSearchTimeout(intSearch);

      intAndSetSearch[1] = intSearch;
    }

    DepthFirstSearch<T> boolSearch = new DepthFirstSearch<>();

    if (opt.debug()) {
      boolSearch.setConsistencyListener(failStatistics);
    }

    if (bool_search_variables.length != 0) {
      // add search containing boolean variables to be sure that they get a value
      SelectChoicePoint<BooleanVar> boolSelect =
          options.freeSearch() || options.complementarySearch()
              ? new SimpleSelect<>(bool_search_variables, new AfcMax<>(store), new IndomainMin<>())
              : new SimpleSelect<>(bool_search_variables, null, new IndomainMin<>());

      if (variable_selection == null) {
        variable_selection = (SelectChoicePoint<T>) boolSelect;
      }
      boolSearch.setSelectChoicePoint((SelectChoicePoint<T>) boolSelect);
      boolSearch.setPrintInfo(false);
      if (lastSearch != null) {
        lastSearch.addChildSearch(boolSearch);
      }
      lastSearch = boolSearch;
      if (float_search_variables.length == 0) {
        boolSearch.setSolutionListener(new CostListener<>());

        if (costVariable != null) {
          intSearch.setCostVar(costVariable);
          intSearch.setOptimize(true);
        }
      }

      // time-out option
      int to = options.getTimeOut();
      if (to > 0) {
        boolSearch.setTimeOutMilliseconds(to);
      }

      intAndSetSearch[2] = boolSearch;
    }

    if (float_search_variables.length != 0) {
      // add float search containing all variables to be sure that they get a value
      DepthFirstSearch<T> floatSearch = new DepthFirstSearch<>();

      if (opt.debug()) {
        floatSearch.setConsistencyListener(failStatistics);
      }

      SelectChoicePoint<Var> floatSelect =
          options.freeSearch() || options.complementarySearch()
              ? new SplitSelectFloat<>(store, float_search_variables, new LargestDomainFloat<>())
              : new SplitSelectFloat<>(store, float_search_variables, null);

      if (variable_selection == null) {
        variable_selection = (SelectChoicePoint<T>) floatSelect;
      }
      floatSearch.setSelectChoicePoint((SelectChoicePoint<T>) floatSelect);
      floatSearch.setPrintInfo(false);
      if (lastSearch != null) {
        lastSearch.addChildSearch(floatSearch);
      }
      floatSearch.setSolutionListener(new CostListener<>());

      if (costVariable != null) {
        intSearch.setCostVar(costVariable);
        intSearch.setOptimize(true);
      }

      setSearchTimeout(floatSearch);

      intAndSetSearch[3] = floatSearch;
    }

    if (int_search_variables.length == 0
        && bool_search_variables.length == 0
        && set_search_variables.length == 0
        && float_search_variables.length == 0) {

      printSolution();

      if (lastSolution != null) {
        helperSolutionPrinter(lastSolution.toString());
      }

      if (options.getAll() || costVariable != null) {
        IO.println(SEPARATOR_LINE);
      }

      if (options.getStatistics()) {
        IO.println(
            "%%%mzn-stat: variables="
                + (store.size()
                    + dictionary.getNumberBoolVariables()
                    - dictionary.constantTable.size())
                // + "\n%%%mzn-stat: boolVariables="+
                // (dictionary.getNumberBoolVariables()-dictionary.aliasTable.size())
                // + "\n%%%mzn-stat: setVariables="+ dictionary.getNumberSetVariables()
                // + "\n%%%mzn-stat: floatVariables="+ dictionary.getNumberFloatVariables()
                + "\n%%%mzn-stat: propagators="
                + initNumberConstraints
                + "\n\n%%%mzn-stat: initTime="
                + getInitTime_ms() / 1000.0
                + "\n%%%mzn-stat: solveTime="
                + "0"
                + "\n%%%mzn-stat: nodes=0"
                + "\n%%man-stat: propagations="
                + store.numberConsistencyCalls
                + "\n%%%mzn-stat: restarts=0"
                + "\n%%%mzn-stat: failures=0"
                // + "\n%%%mzn-stat: backtracks=0"
                + "\n%%%mzn-stat: peakDepth=0"
                + "\n%%%mzn-stat: solutions=1"
                + "\n%%%mzn-stat-end");
      }
      throw new TrivialSolution();
    }

    // add restart search for free search (option -f)

    return intAndSetSearch;
  }

  @SuppressWarnings("unchecked")
  void run_sequence_search(int solveKind, SimpleNode kind, SearchItem<T> si) {

    singleSearch = false;

    this.si = si;

    if (solveKind == 1) {
      minimize = true;
    }

    if (options.debug()) {
      printSolveKindDebug(solveKind, kind, si);
    }

    DepthFirstSearch<T> masterLabel = null;
    DepthFirstSearch<T> last_search = null;
    SelectChoicePoint<T> masterSelect = null;
    list_seq_searches = new ArrayList<>();

    for (int i = 0; i < si.getSearchItems().size(); i++) {
      if (i == 0) { // master search
        masterLabel = sub_search(si.getSearchItems().get(i), null, true);
        last_search = getLastSearch(masterLabel);
        masterSelect = variable_selection;
        if (!print_search_info) {
          masterLabel.setPrintInfo(false);
        }
      } else {
        DepthFirstSearch<T> label = sub_search(si.getSearchItems().get(i), last_search, false);
        last_search.addChildSearch(label);
        last_search = getLastSearch(label);
        if (!print_search_info) {
          last_search.setPrintInfo(false);
        }
      }
    }

    // Set up cost variable before sub-search setup so constraints are visible
    Var costVar = null;
    if (solveKind > 0) {
      costVar = setupCostVariable(kind, solveKind);
    }

    DepthFirstSearch<T>[] complementary_search = setSubSearchForAll(last_search, options);
    for (DepthFirstSearch<T> aComplementary_search : complementary_search) {
      if (aComplementary_search != null) {
        list_seq_searches.add(aComplementary_search);
        if (!print_search_info) {
          aComplementary_search.setPrintInfo(false);
        }
      }
    }

    result = false;
    optimization = solveKind > 0;

    final_search_seq = list_seq_searches.getLast();

    long currentTime = timer.getCpuTime();
    initTime = currentTime - startCpu;
    startCpu = currentTime;

    setSearchTimeout(list_seq_searches);

    if (si.exploration() == null || COMPLETE.equals(si.exploration())) {
      FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

      if (options.getAll()) { // all solutions
        if (restartCalculator != null) {
          throw new IllegalArgumentException(
              "Flatzinc option for search for all solutions (-a) cannot be used in restart search.");
        }
        searchForAll(masterLabel);
      }

      String solveType;
      switch (solveKind) {
        case 0: // satisfy
          solveType = "satisfy";
          break;
        case 1: // minimize
          solveType = "minimize";
          for (Search<T> list_seq_searche : list_seq_searches) {
            list_seq_searche.setOptimize(true);
          }
          break;
        case 2: // maximize
          solveType = "maximize";
          for (Search<T> list_seq_searche : list_seq_searches) {
            list_seq_searche.setOptimize(true);
          }
          break;
        default:
          throw new IllegalArgumentException(
              "Not recognized or supported search strategy; compilation aborted");
      }

      label = masterLabel;
      result = executeSearch(masterLabel, masterSelect, costVar, solveType);
      if (!options.runSearch()) {
        return;
      }
    } else {
      throw new IllegalArgumentException(
          "Not recognized or supported "
              + si.exploration()
              + " search explorarion strategy ; compilation aborted");
    }

    if (!options.getAll() && lastSolution != null) {
      helperSolutionPrinter(lastSolution.toString());
    }

    printStatisticsForSeqSearch(false, result);
  }

  @SuppressWarnings("unchecked")
  DepthFirstSearch<T> getLastSearch(DepthFirstSearch<T> s) {
    DepthFirstSearch<T> ns = s;
    DepthFirstSearch<T> lastNotNullSearch;

    do {

      lastNotNullSearch = ns;

      // find next search
      if (ns.childSearches == null) {
        ns = null;
      } else {
        ns = (DepthFirstSearch<T>) ns.childSearches[0];
      }
    } while (ns != null);

    return lastNotNullSearch;
  }

  void printStatisticsForSeqSearch(boolean interrupted, boolean result) {

    if (list_seq_searches == null) {
      IO.println("%% =====INTERRUPTED=====\n%% Model not yet posed..");
      return;
    }

    boolean timeoutOccurred = anyTimeOutOccured(list_seq_searches);
    printResultStatus(interrupted, result, timeoutOccurred, !heuristicSeqSearch);

    if (options.getStatistics()) {
      int nodes = 0;
      int decisions = 0;
      int wrong = 0;
      int backtracks = 0;
      int depth = 0;
      int solutions = 0;
      for (Search<T> label : list_seq_searches) {
        nodes += label.getNodes();
        decisions += label.getDecisions();
        wrong += label.getWrongDecisions();
        backtracks += label.getBacktracks();
        depth += label.getMaximumDepth();
        solutions = label.getSolutionListener().solutionsNo();
      }

      printStatisticsOutput(nodes, wrong, depth, solutions);
    }
  }

  /**
   * Prints the common statistics output block shared by single and sequence search.
   *
   * @param nodes total nodes explored.
   * @param wrong total wrong decisions (failures).
   * @param depth peak search depth.
   * @param solutions total solutions found.
   */
  private void printStatisticsOutput(int nodes, int wrong, int depth, int solutions) {
    int restarts = rs != null ? rs.restarts() : 0;

    IO.println(
        "%%%mzn-stat: variables="
            + nf.format(
                (long) store.size()
                    + dictionary.getNumberBoolVariables()
                    - dictionary.constantTable.size())
            + "\n%%%mzn-stat: propagators="
            + nf.format((long) initNumberConstraints - 1)
            + "\n\n%%%mzn-stat: initTime="
            + nf.format(getInitTime_ms() / 1000.0)
            + "\n%%%mzn-stat: solveTime="
            + nf.format(getSearchTime_ms() / 1000.0)
            + "\n%%%mzn-stat: nodes="
            + nf.format(nodes)
            + "\n%%%mzn-stat: restarts="
            + nf.format(restarts)
            + "\n%%%mzn-stat: propagations="
            + nf.format(store.numberConsistencyCalls)
            + "\n%%%mzn-stat: failures="
            + nf.format(wrong)
            + "\n%%%mzn-stat: peakDepth="
            + nf.format(depth)
            + "\n%%%mzn-stat: solutions="
            + nf.format(solutions)
            + "\n%%%mzn-stat-end");

    if (options.debug()) {
      String s = "% " + failStatistics.toString();
      IO.println(s.replace("\n", "\n% "));
    }
  }

  /**
   * Returns the search time in milliseconds.
   *
   * @return the search time in milliseconds
   */
  double getSearchTime_ms() {
    searchTime = timer.getCpuTime() - startCpu;
    return (double) searchTime / (long) 1e+6;
  }

  /**
   * Returns the initialization time in milliseconds.
   *
   * @return the initialization time in milliseconds
   */
  double getInitTime_ms() {
    return (double) initTime / (long) 1e+6;
  }

  /**
   * Checks if any timeout occurred in the list of searches.
   *
   * @param listSeqSearches the list of searches to check
   * @return true if any timeout occurred, false otherwise
   */
  boolean anyTimeOutOccured(ArrayList<Search<T>> listSeqSearches) {

    for (Search<T> listSeqSearche : listSeqSearches) {
      if (((DepthFirstSearch<T>) listSeqSearche).timeOutOccured) {
        return true;
      }
    }
    return false;
  }

  DepthFirstSearch<T> sub_search(SearchItem<T> si, DepthFirstSearch<T> l, boolean master) {
    DepthFirstSearch<T> label =
        switch (si.type()) {
          case INT_SEARCH, BOOL_SEARCH -> subSearchIntOrBool(si, master);
          case SET_SEARCH -> subSearchSet(si, master);
          case PRIORITY_SEARCH -> subSearchPriority(si);
          case WARM_START -> subSearchWarmStart(si, master);
          case SEQ_SEARCH -> subSearchSeq(si, l);
          case FLOAT_SEARCH -> subSearchFloat(si, master);
          default -> subSearchDefault();
        };
    return label;
  }

  private DepthFirstSearch<T> subSearchIntOrBool(SearchItem<T> si, boolean master) {
    DepthFirstSearch<T> label = int_search(si);
    if (!master) {
      label.setSelectChoicePoint(variable_selection);
    }
    heuristicSeqSearch |= applyHeuristicSearch(label, si);
    list_seq_searches.add(label);
    label.setPrintInfo(false);
    return label;
  }

  private DepthFirstSearch<T> subSearchSet(SearchItem<T> si, boolean master) {
    DepthFirstSearch<T> label = set_search(si);
    if (!master) {
      label.setSelectChoicePoint(variable_selection);
    }
    heuristicSeqSearch |= applyHeuristicSearch(label, si);
    list_seq_searches.add(label);
    label.setPrintInfo(false);
    return label;
  }

  private DepthFirstSearch<T> subSearchPriority(SearchItem<T> si) {
    DepthFirstSearch<T> label = priority_search(si);
    list_seq_searches.add(label);
    return label;
  }

  private DepthFirstSearch<T> subSearchWarmStart(SearchItem<T> si, boolean master) {
    DepthFirstSearch<T> label = warm_start_search(si);
    if (!master) {
      label.setSelectChoicePoint(variable_selection);
    }
    return label;
  }

  private DepthFirstSearch<T> subSearchSeq(SearchItem<T> si, DepthFirstSearch<T> lastSearch) {
    DepthFirstSearch<T> label = null;
    for (int i = 0; i < si.getSearchItems().size(); i++) {
      DepthFirstSearch<T> label_seq = sub_search(si.getSearchItems().get(i), lastSearch, false);
      if (i == 0) {
        label = label_seq;
      } else {
        lastSearch.addChildSearch(label_seq);
      }
      lastSearch = getLastSearch(label_seq);
    }
    return label;
  }

  private DepthFirstSearch<T> subSearchFloat(SearchItem<T> si, boolean master) {
    DepthFirstSearch<T> label = float_search(si);
    if (!master) {
      label.setSelectChoicePoint(variable_selection);
    }
    heuristicSeqSearch |= applyHeuristicSearch(label, si);
    list_seq_searches.add(label);
    label.setPrintInfo(false);
    return label;
  }

  private DepthFirstSearch<T> subSearchDefault() {
    DepthFirstSearch<T>[] ls = setSubSearchForAll(null, options);
    if (ls[0] != null) {
      return ls[0];
    }
    if (ls[1] != null) {
      return ls[1];
    }
    if (ls[2] != null) {
      return ls[2];
    }
    if (ls[3] != null) {
      return ls[3];
    }
    return null;
  }

  @SuppressWarnings("unchecked")
  DepthFirstSearch<T> int_search(SearchItem<T> si) {

    variable_selection = (SelectChoicePoint<T>) si.getIntSelect();
    DepthFirstSearch<T> label = new DepthFirstSearch<>();
    label.setAssignSolution(false);

    if (options.debug()) {
      label.setConsistencyListener(failStatistics);
    }

    return label;
  }

  @SuppressWarnings("unchecked")
  DepthFirstSearch<T> warm_start_search(SearchItem<T> si) {

    variable_selection = (SelectChoicePoint<T>) si.getWarmStartSelect();
    DepthFirstSearch<T> label = new DepthFirstSearch<>();
    label.setAssignSolution(false);
    label.setPrintInfo(false);

    if (options.debug()) {
      label.setConsistencyListener(failStatistics);
    }

    return label;
  }

  @SuppressWarnings("unchecked")
  DepthFirstSearch<T> set_search(SearchItem<T> si) {

    variable_selection = (SelectChoicePoint<T>) si.getSetSelect();
    DepthFirstSearch<T> label = new DepthFirstSearch<>();
    label.setAssignSolution(false);

    if (options.debug()) {
      label.setConsistencyListener(failStatistics);
    }

    return label;
  }

  @SuppressWarnings("unchecked")
  DepthFirstSearch<T> float_search(SearchItem<T> si) {
    variable_selection = (SelectChoicePoint<T>) si.getFloatSelect();
    DepthFirstSearch<T> label = new DepthFirstSearch<>();
    label.setAssignSolution(false);

    if (options.debug()) {
      label.setConsistencyListener(failStatistics);
    }

    if (options.precision()) {
      label.setInitializeListener(new PrecisionSetting(options.getPrecision()));
    } else {
      label.setInitializeListener(new PrecisionSetting(si.precision));
    }

    return label;
  }

  @SuppressWarnings("unchecked")
  private DepthFirstSearch<T> createPrioritySubSearch(SearchItem<T> s) {
    return switch (s.search_type) {
      case INT_SEARCH, BOOL_SEARCH -> int_search(s);
      case SET_SEARCH -> set_search(s);
      case FLOAT_SEARCH -> float_search(s);
      case SEQ_SEARCH -> {
        DepthFirstSearch<T> sub = sub_search(s, null, false);
        DepthFirstSearch<T> ns = sub;
        do {
          ns.setPrintInfo(false);
          ns = ns.childSearches == null ? null : (DepthFirstSearch<T>) ns.childSearches[0];
        } while (ns != null);
        yield sub;
      }
      case PRIORITY_SEARCH -> priority_search(s);
      default ->
          throw new RuntimeException(
              "Error: Not supported search type "
                  + s.search_type
                  + "in priority_search; execution aborted");
    };
  }

  @SuppressWarnings("unchecked")
  DepthFirstSearch<T> priority_search(SearchItem<T> si) {

    ArrayList<SearchItem<T>> dfs_s = si.getSearchItems();
    DepthFirstSearch<T>[] searches = new DepthFirstSearch[dfs_s.size()];
    int i = 0;
    for (SearchItem<T> s : dfs_s) {
      DepthFirstSearch<T> subSearch = createPrioritySubSearch(s);
      subSearch.setSelectChoicePoint(variable_selection);
      subSearch.setPrintInfo(false);
      searches[i++] = subSearch;
    }

    SearchItem.ComparatorsVar<IntVar> vs = si.getVarSelect();
    ComparatorVariable<IntVar> comparator = vs.v1;
    ComparatorVariable<IntVar> tieBreak = vs.v2;

    PrioritySearch<T> label =
        new PrioritySearch<>(
            (T[]) si.vars(),
            (ComparatorVariable<T>) comparator,
            (ComparatorVariable<T>) tieBreak,
            searches);
    label.setPrintInfo(false);
    label.setAssignSolution(false);

    if (options.debug()) {
      label.setConsistencyListener(failStatistics);
    }

    setSearchTimeout(label);
    int to = options.getTimeOut();
    if (to > 0) {
      for (DepthFirstSearch<T> s : searches) {
        s.setTimeOutMilliseconds(to);
      }
    }

    if (options.getNumberSolutions() > 0) {
      label.setSolutionLimit(options.getNumberSolutions());
    }

    return label;
  }

  @SuppressWarnings("unchecked")
  private void appendVariableOutput(StringBuffer printBuffer, Var v) {
    if (v instanceof BooleanVar var1) {
      printBuffer.append(v.id()).append(" = ");
      if (v.singleton()) {
        switch (var1.value()) {
          case 0 -> printBuffer.append("false");
          case 1 -> printBuffer.append("true");
          default -> printBuffer.append(v.dom());
        }
      } else {
        printBuffer.append("false..true");
      }
      printBuffer.append(";\n");
    } else if (v instanceof SetVar setVar) {
      printBuffer.append(v.id()).append(" = ");
      if (v.singleton()) {
        IntDomain glb = setVar.dom().glb();
        if (glb.getSize() > 0 && glb.getSize() == glb.max() - glb.min() + 1) {
          printBuffer.append(glb.min()).append("..").append(glb.max());
        } else {
          printBuffer.append("{");
          for (ValueEnumeration e = glb.valueEnumeration(); e.hasMoreElements(); ) {
            printBuffer.append(e.nextElement());
            if (e.hasMoreElements()) {
              printBuffer.append(", ");
            }
          }
          printBuffer.append("}");
        }
      } else {
        printBuffer.append(v.dom().toString());
      }
      printBuffer.append(";\n");
    } else {
      printBuffer.append(v).append(";\n");
    }
  }

  @SuppressWarnings("unchecked")
  void printSolution() {

    StringBuffer printBuffer = new StringBuffer();
    numberSolutions++;

    if (!dictionary.outputVariables.isEmpty()) {
      for (int i = 0; i < dictionary.outputVariables.size(); i++) {
        appendVariableOutput(printBuffer, dictionary.outputVariables.get(i));
      }
    }

    for (int i = 0; i < dictionary.outputArray.size(); i++) {
      OutputArrayAnnotation a = dictionary.outputArray.get(i);

      printBuffer.append(a).append("\n");
    }

    if (options.getVerbose()) {
      // print number of search nodes and CPU time for this solution
      int nodes = 0;
      DepthFirstSearch<T> dfs = label;
      while (dfs != null) {
        nodes += dfs.getNodes();
        dfs = dfs.childSearches == null ? null : (DepthFirstSearch) dfs.childSearches[0];
      }

      if (costVariable != null) {
        if (minimize) {
          if (costVariable instanceof IntVar var1) {
            printBuffer.append(MZN_STAT_OBJECTIVE).append(var1.value()).append("\n");
          } else if (costVariable instanceof FloatVar fv) {
            printBuffer.append(MZN_STAT_OBJECTIVE).append(fv.value()).append("\n");
          }
        } else {
          if (costVariable instanceof IntVar var1) {
            printBuffer.append(MZN_STAT_OBJECTIVE).append(-var1.value()).append("\n");
          } else if (costVariable instanceof FloatVar fv) {
            printBuffer.append(MZN_STAT_OBJECTIVE).append(-fv.value()).append("\n");
          }
        }
      }
      double cpuTime = getSearchTime_ms();
      printBuffer.append("%%%mzn-stat: nodes=").append(nf.format(nodes)).append("\n");
      printBuffer
          .append("%%%mzn-stat: nodesPerSecond=")
          .append(nf.format(cpuTime == 0 ? 0.0 : (double) nodes / (cpuTime / 1000)))
          .append("\n");
      if (restartCalculator != null) {
        printBuffer.append("%%%%mzn-stat: restarts=").append(nf.format(rs.restarts()));
      }
      printBuffer
          .append("\n%%%mzn-stat: solveTime=")
          .append(nf.format(cpuTime / 1000))
          .append("\n");
      printBuffer.append("%%%mzn-stat-end\n");
    }

    printBuffer.append("----------\n");

    if (options.getAll()) {
      IO.print(printBuffer.toString());
    } else { // store the print-out

      lastSolution = printBuffer;
    }

    if (options.getNumberSolutions() == numberSolutions) {
      throw new NumberSolutionsReached();
    }
  }

  int getKind(String k) {
    return switch (k) {
      case SATISFY ->
          // 0 = satisfy
          0;
      case MINIMIZE ->
          // 1 = minimize
          1;
      case MAXIMIZE ->
          // 2 = maximize
          2;
      default ->
          throw new IllegalArgumentException("Not supported search kind; compilation aborted");
    };
  }

  private IntVar getCostFromIdent(String ident) {
    IntVar cost = dictionary.getVariable(ident);
    if (cost != null) {
      return cost;
    }
    Integer costInt = dictionary.checkInt(ident);
    return costInt != null ? new IntVar(store, costInt, costInt) : null;
  }

  private IntVar getCostFromArrayAccess(String ident, int index) {
    IntVar[] a = dictionary.getVariableArray(ident);
    if (a != null) {
      return a[index];
    }
    int[] costInt = dictionary.getIntArray(ident);
    if (costInt != null) {
      return new IntVar(store, costInt[index], costInt[index]);
    }
    return null;
  }

  IntVar getCost(ASTSolveExpr node) {

    if (node.getType() == 0) { // ident
      return getCostFromIdent(node.getIdent());
    }
    if (node.getType() == 1) { // array access
      return getCostFromArrayAccess(node.getIdent(), node.getIndex());
    }
    throw new IllegalArgumentException("Wrong cost function specification " + node);
  }

  FloatVar getCostFloat(ASTSolveExpr node) {
    if (node.getType() == 0) { // ident
      FloatVar cost = dictionary.getFloatVariable(node.getIdent());
      if (cost != null) {
        return cost;
      } else { // cost is constant ?
        Double costFloat = dictionary.checkFloat(node.getIdent());
        if (costFloat != null) {
          return new FloatVar(store, costFloat, costFloat);
        } else {
          return null;
        }
      }
    } else if (node.getType() == 1) { // array access
      FloatVar[] a = dictionary.getVariableFloatArray(node.getIdent());
      return a[node.getIndex()];
    } else {
      throw new IllegalArgumentException("Wrong cost function specification " + node);
    }
  }

  void pose(Constraint c) {
    store.impose(c);
    if (debug) {
      IO.println(c);
    }
  }

  /**
   * Applies LDS or Credit heuristic search exploration if configured on the search item.
   *
   * @param label the search to apply heuristic to
   * @param si the search item with exploration configuration
   * @return true if a heuristic was applied, false otherwise
   */
  boolean applyHeuristicSearch(DepthFirstSearch<T> label, SearchItem<T> si) {
    if ("lds".equals(si.exploration())) {
      lds_search(label, si.ldsValue);
      return true;
    }
    if ("credit".equals(si.exploration())) {
      credit_search(label, si.creditValue, si.bbsValue);
      return true;
    }
    return false;
  }

  void lds_search(DepthFirstSearch<T> label, int ldsValue) {

    Lds<T> lds = new Lds<>(ldsValue);
    if (label.getExitChildListener() == null) {
      label.setExitChildListener(lds);
    } else {
      label.getExitChildListener().setChildrenListeners(lds);
    }
  }

  void credit_search(DepthFirstSearch<T> label, int creditValue, int bbsValue) {

    int maxDepth = 1000; // IntDomain.MAX_INT;
    CreditCalculator<T> credit = new CreditCalculator<>(creditValue, bbsValue, maxDepth);

    if (label.getConsistencyListener() == null) {
      label.setConsistencyListener(credit);
    } else {
      label.getConsistencyListener().setChildrenListeners(credit);
    }

    label.setExitChildListener(credit);
    label.setTimeOutListener(credit);
  }

  @SuppressWarnings("unchecked")
  void printSearch(DepthFirstSearch<T> s) {

    do {

      IO.print(s);

      // find next search
      if (s.childSearches == null) {
        s = null;
      } else {
        s = (DepthFirstSearch<T>) s.childSearches[0];
        IO.print(", ");
      }
    } while (s != null);
    IO.println();
  }

  public SearchItem<T> getSearch() {
    return si;
  }

  public int getSolveKind() {
    return solveKind;
  }

  void helperSolutionPrinter(String lastSolution) {

    IO.print(lastSolution);

    if (!options.getOutputFilename().isEmpty() && !lastSolution.isEmpty()) {
      try {
        IO.println("%%Output filename " + options.getOutputFilename());
        Files.writeString(
            Path.of(options.getOutputFilename()),
            lastSolution,
            StandardOpenOption.CREATE,
            StandardOpenOption.TRUNCATE_EXISTING);
      } catch (IOException e) {
        log.error("Failed to write solution to {}", options.getOutputFilename(), e);
      }
    }
  }

  /** Starts the CPU timer for measuring search time. */
  void startTimer() {

    if ("true".equals(P)) {
      timer = new SystemTimer();
    } else {
      timer = new ThreadTimer();
    }

    startCpu = timer.getCpuTime();
  }

  /** Sets floating point precision for the store. */
  public static class PrecisionSetting implements InitializeListener {

    final double precision;
    InitializeListener[] initializeChildListeners;

    /**
     * Constructs precision setting with the specified precision value.
     *
     * @param p the precision value
     */
    PrecisionSetting(double p) {
      precision = p;
    }

    /** {@inheritDoc} */
    public void executedAtInitialize(Store store) {
      FloatDomain.setPrecision(precision);
    }

    /** {@inheritDoc} */
    public void setChildrenListeners(InitializeListener[] children) {
      initializeChildListeners = new InitializeListener[children.length];
      System.arraycopy(children, 0, initializeChildListeners, 0, children.length);
    }

    /** {@inheritDoc} */
    public void setChildrenListeners(InitializeListener child) {
      initializeChildListeners = new InitializeListener[1];
      initializeChildListeners[0] = child;
    }
  }

  /** Listener that tracks cost during solve. */
  public class CostListener<T extends Var> extends SimpleSolutionListener<T> {

    /** {@inheritDoc} */
    public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

      boolean returnCode = super.executeAfterSolution(search, select);

      finalNumberSolutions++;

      printSolution();

      return returnCode;
    }
  }
}
