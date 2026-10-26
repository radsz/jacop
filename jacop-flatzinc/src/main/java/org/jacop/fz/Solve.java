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
import java.time.Duration;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.function.IntFunction;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.BoolClause;
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
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.jasat.lcg.LcgSolver;
import org.jacop.satwrapper.SatTranslation;
import org.jacop.search.AfcMax;
import org.jacop.search.AfcMaxDeg;
import org.jacop.search.ComparatorVariable;
import org.jacop.search.CreditCalculator;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.FailConstraintsStatistics;
import org.jacop.search.Indomain;
import org.jacop.search.IndomainMiddle;
import org.jacop.search.IndomainMin;
import org.jacop.search.InitializeListener;
import org.jacop.search.Lds;
import org.jacop.search.PrioritySearch;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SequenceSelect;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.SmallestDomain;
import org.jacop.search.SplitSelect;
import org.jacop.search.free.DomWdeg;
import org.jacop.search.free.FreeSearch;
import org.jacop.search.free.IndomainBoundImpact;
import org.jacop.search.free.IndomainLastSolution;
import org.jacop.search.free.LastConflict;
import org.jacop.search.free.SearchMonitor;
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
  final boolean printSearchInfo = false;
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
  SelectChoicePoint<T> variableSelection;
  ArrayList<Search<T>> listSeqSearches;
  boolean heuristicSeqSearch;
  Var costVariable;
  // the variable of the solve item; for maximisation costVariable is its negation
  Var objectiveVariable;
  // restart search
  Calculator restartCalculator;
  RestartSearch<T> rs;
  // free search with the FreeSearch engine
  FreeSearch freeSearch;
  FreeSearch.Status freeSearchStatus;
  LcgSolver lcg;
  int lcgStatus;
  // the search annotation of the model, interleaved with free search
  SearchItem<T> annotatedSearch;
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
  DepthFirstSearch<T>[] finalSearch;
  // labels the variables a search on output variables leaves out
  DepthFirstSearch<T> completionSearch;
  // sequence search
  Search<T> finalSearchSeq;
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
  private static final String MINIMIZE_LITERAL = "minimize";
  private static final String MAXIMIZE_LITERAL = "maximize";
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
      printSearchModelDebugInfo(table, modelMem);
    }

    options = opt;
    solveKind = -1;

    int count = node.jjtGetNumChildren();
    if (count == 1) {
      searchCountOne(node);
    } else if (count == 2) {
      searchCountTwo(opt, node);
    } else if (count > 2) {
      searchCountMany(node);
    } else {
      throw new IllegalArgumentException(
          "%% Error: Not recognized structure of solve statement; compilation aborted");
    }
  }

  private void printSearchModelDebugInfo(Tables table, long modelMem) {
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

  private void searchCountOne(ASTSolveItem node) {
    ASTSolveKind kind = (ASTSolveKind) node.jjtGetChild(0);
    solveKind = getKind(kind.getKind());
    run_single_search(solveKind, kind, null);
  }

  private void searchCountTwo(Options opt, ASTSolveItem node) {
    SearchItem<T> si = new SearchItem<>(store, dictionary);
    si.searchParameters(node, 0);
    ASTSolveKind kind = (ASTSolveKind) node.jjtGetChild(1);
    solveKind = getKind(kind.getKind());
    annotatedSearch = si;
    runSearchForSingleAnnotation(opt, kind, solveKind, si, node);
  }

  private void searchCountMany(ASTSolveItem node) {
    SearchItem<T> si = new SearchItem<>(store, dictionary);
    si.searchParametersForSeveralAnnotations(node, 0);

    ArrayList<SearchItem<T>> nsi = parseSearchAnnotations(si.searchSeq);

    if (options.freeSearch()) {
      if (!nsi.isEmpty()) {
        annotatedSearch = new SearchItem<>(store, dictionary);
        annotatedSearch.setSearchType(SEQ_SEARCH);
        for (SearchItem<T> se : nsi) {
          annotatedSearch.addSearch(se);
        }
      }
      ASTSolveKind kind = (ASTSolveKind) node.jjtGetChild(si.searchSeqSize());
      solveKind = getKind(kind.getKind());
      run_single_search(solveKind, kind, null);
      return;
    }

    if (nsi.size() == 1) {
      runSingleOrSequenceSearch(node, si, nsi.getFirst());
    } else {
      runSequenceSearchFromMultiple(node, si, nsi);
    }
  }

  private void runSingleOrSequenceSearch(ASTSolveItem node, SearchItem<T> si, SearchItem<T> fs) {
    ASTSolveKind kind = (ASTSolveKind) node.jjtGetChild(si.searchSeqSize());
    solveKind = getKind(kind.getKind());
    if (SEQ_SEARCH.equals(fs.type())) {
      run_sequence_search(solveKind, kind, fs);
    } else {
      run_single_search(solveKind, kind, fs);
    }
  }

  private void runSequenceSearchFromMultiple(
      ASTSolveItem node, SearchItem<T> si, ArrayList<SearchItem<T>> nsi) {
    ASTSolveKind kind = (ASTSolveKind) node.jjtGetChild(si.searchSeqSize());
    solveKind = getKind(kind.getKind());

    SearchItem<T> siq = new SearchItem<>(store, dictionary);
    siq.setSearchType(SEQ_SEARCH);
    for (SearchItem<T> se : nsi) {
      siq.addSearch(se);
    }
    run_sequence_search(solveKind, kind, siq);
  }

  private void runSearchForSingleAnnotation(
      Options opt, ASTSolveKind kind, int solveKind, SearchItem<T> si, SimpleNode node) {
    String searchType = si.type();
    if (opt.freeSearch()) {
      run_single_search(solveKind, kind, null);
      return;
    }
    if (INT_SEARCH.equals(searchType)
        || SET_SEARCH.equals(searchType)
        || BOOL_SEARCH.equals(searchType)
        || FLOAT_SEARCH.equals(searchType)
        || PRIORITY_SEARCH.equals(searchType)
        || WARM_START.equals(searchType)
        || (searchType != null && searchType.startsWith("restart_"))) {
      run_single_search(solveKind, kind, si);
      return;
    }
    if (SEQ_SEARCH.equals(searchType)) {
      run_sequence_search(solveKind, kind, si);
      return;
    }
    String warnType = searchType;
    if ("$expr".equals(searchType)) {
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
      if (!handleSearchAnnotation(s, ns)) {
        System.err.println(
            "%% Warning: Not supported search annotation: " + s.searchType + "; ignored.");
      }
    }

    return ns;
  }

  private boolean handleSearchAnnotation(SearchItem<T> s, ArrayList<SearchItem<T>> ns) {
    if ("restart_none".equals(s.searchType)) {
      return true;
    }
    if ("restart_constant".equals(s.searchType)
        || "restart_linear".equals(s.searchType)
        || "restart_geometric".equals(s.searchType)
        || "restart_luby".equals(s.searchType)) {
      if (!options.freeSearch()) {
        restartCalculator = s.restartCalculator;
      }
      return true;
    }
    if ("relax_and_reconstruct".equals(s.searchType)) {
      relaxVars = s.relaxAndReconstructVariables;
      probability = s.probability;
      return true;
    }
    if (s.searchType.endsWith("_search")) {
      ns.add(s);
      return true;
    }
    if (s.searchType.endsWith(WARM_START)) {
      ns.addFirst(s);
      return true;
    }
    return false;
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
    listSeqSearches = new ArrayList<>();

    label = null;
    si = applySearchItemToLabel(si);

    // Set up cost variable before sub-search setup so constraints are visible
    Var costVar = null;
    if (solveKind > 0) {
      costVar = setupCostVariable(kind, solveKind);
    }

    // adds child search for cost; to be sure that all variables get a value
    finalSearch = setSubSearchForAll(label, options);

    if (si == null) {
      defaultSearch = true;
      si = new SearchItem<>(store, dictionary);
      si.explore = COMPLETE;
      resolveLabelFromFinalSearch(finalSearch);
    } else {
      for (DepthFirstSearch<T> s : finalSearch) {
        if (s != null) {
          listSeqSearches.add(s);
        }
      }
    }

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

      ensureAllSolutionsIfRequested(label, solveKind);

      this.si = si;

      String solveType;
      switch (solveKind) {
        case 0:
          solveType = SATISFY;
          break;
        case 1:
          solveType = MINIMIZE_LITERAL;
          break;
        case 2:
          solveType = MAXIMIZE_LITERAL;
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
    listSeqSearches.add(label);
    label.setPrintInfo(false);
    setSearchTimeout(label);
    return si;
  }

  private void resolveLabelFromFinalSearch(DepthFirstSearch<T>[] finalSearch) {
    for (int primary = 0; primary < finalSearch.length; primary++) {
      if (finalSearch[primary] != null) {
        assignLabelFromFinalSearch(finalSearch, primary);
        return;
      }
    }
  }

  private void assignLabelFromFinalSearch(DepthFirstSearch<T>[] finalSearch, int primary) {
    label = finalSearch[primary];
    listSeqSearches.add(label);
    for (int i = primary + 1; i < finalSearch.length; i++) {
      if (finalSearch[i] != null) {
        listSeqSearches.add(finalSearch[i]);
      }
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
      s.getSolutionListener().searchAll(s != completionSearch);

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
   * Executes a search with optional restart and cost variable.
   *
   * @param label the depth first search to execute
   * @param costVar the cost variable (null for satisfy)
   * @param solveType the solve type string for debug output ("satisfy", "minimize", "maximize")
   * @return true if a solution was found, false otherwise
   */
  private boolean executeSearch(DepthFirstSearch<T> label, Var costVar, String solveType) {
    return executeSearch(label, variableSelection, costVar, solveType);
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
      if (useLcg(costVar)) {
        return executeLcgSearch(costVar);
      }
      if (useFreeSearchEngine(costVar)) {
        return executeFreeSearch(costVar);
      }
      if (restartCalculator != null) {
        return executeRestartSearch(label, select, costVar, solveType);
      }
      return executeNonRestartSearch(label, select, costVar, solveType);
    } catch (NumberSolutionsReached _) {
      return numberSolutions > 0;
    }
  }

  private boolean useLcg(Var costVar) {
    if (!options.lcg()) {
      return false;
    }
    String unsupported = lcgUnsupported(costVar);
    if (unsupported != null) {
      IO.println("%% --lcg ignored: " + unsupported);
      postCollectedClauses();
      return false;
    }
    return true;
  }

  /**
   * Imposes the clauses kept for the LCG solver as constraints, when the model is solved without
   * it.
   */
  private void postCollectedClauses() {
    for (IntVar[][] clause : sat.collectedClauses()) {
      store.impose(new BoolClause(clause[0], clause[1]));
    }
    sat.collectedClauses().clear();
  }

  private String lcgUnsupported(Var costVar) {
    if (options.getAll() && costVar == null) {
      return "all solutions are not supported";
    }
    if (costVar != null && !(costVar instanceof IntVar)) {
      return "the objective is not an integer variable";
    }
    for (int i = 0; i < store.size(); i++) {
      if (!(store.vars[i] instanceof IntVar)) {
        return "the model has float or set variables";
      }
    }
    return null;
  }

  /**
   * Solves with lazy clause generation: JaSAT searches, the store's constraints propagate and
   * explain their prunings. Solutions are printed when found, with the domains fixed to them.
   */
  private boolean executeLcgSearch(Var costVar) {
    lcg = new LcgSolver(store);
    for (IntVar[][] clause : sat.collectedClauses()) {
      lcg.addClause(clause[0], clause[1]);
    }
    lcg.onSolution(this::printSolution);
    if (options.getTimeOut() > 0) {
      lcg.sat().setDeadline(System.nanoTime() + options.getTimeOut() * 1_000_000L);
    }
    lcgStatus = costVar == null ? lcg.solve() : lcg.minimize((IntVar) costVar);
    return numberSolutions > 0;
  }

  private void printLcgStatistics(boolean interrupted) {
    boolean complete = lcgStatus != CdclSolver.UNKNOWN;
    printResultStatus(interrupted, numberSolutions > 0, !complete, complete && !interrupted);
    if (options.getStatistics()) {
      printStatisticsOutput(
          (int) lcg.sat().decisions, (int) lcg.sat().conflicts, 0, numberSolutions);
      printLcgExplanationStatistics();
    }
  }

  /**
   * Prints the LCG counts: atoms given to the SAT solver, reasons it asked for, and per constraint
   * class the reasons and failures explained, the share given by the generic reason and the average
   * number of atoms.
   */
  private void printLcgExplanationStatistics() {
    long reasons = 0;
    long generic = 0;
    long atoms = 0;
    StringBuilder perClass = new StringBuilder();
    for (Map.Entry<String, long[]> e : lcg.explanationStatistics().entrySet()) {
      long[] n = e.getValue();
      reasons += n[0] + n[3];
      generic += n[1] + n[4];
      atoms += n[2] + n[5];
      perClass
          .append("%% lcg ")
          .append(e.getKey())
          .append(": reasons=")
          .append(n[0])
          .append(" generic=")
          .append(n[1])
          .append(" avgAtoms=")
          .append(nf.format(n[0] == 0 ? 0 : (double) n[2] / n[0]))
          .append(" failures=")
          .append(n[3])
          .append(" generic=")
          .append(n[4])
          .append(" avgAtoms=")
          .append(nf.format(n[3] == 0 ? 0 : (double) n[5] / n[3]))
          .append('\n');
    }
    IO.print(
        "%%%mzn-stat: lcgAtoms="
            + lcg.atomsPropagated
            + "\n%%%mzn-stat: lcgAtomLiterals="
            + lcg.atomLiterals
            + "\n%%%mzn-stat: lcgAtomLiteralsLearnt="
            + lcg.atomLiteralsLearnt
            + "\n%%%mzn-stat: lcgExplanations="
            + reasons
            + "\n%%%mzn-stat: lcgGenericShare="
            + nf.format(reasons == 0 ? 0 : (double) generic / reasons)
            + "\n%%%mzn-stat: lcgAvgExplanation="
            + nf.format(reasons == 0 ? 0 : (double) atoms / reasons)
            + "\n%%%mzn-stat: lcgLearntAvg="
            + nf.format((double) lcg.sat().learntLiterals / Math.max(1, lcg.sat().conflicts))
            + "\n%%%mzn-stat-end\n"
            + perClass);
  }

  private boolean useFreeSearchEngine(Var costVar) {
    return options.freeSearch()
        && options.newFreeSearchEngine()
        && singleSearch
        && defaultSearch
        && relaxVars == null
        && (costVar == null || costVar instanceof IntVar);
  }

  /**
   * Runs free search with the FreeSearch engine. It branches on the set variables first, then on
   * the integer and Boolean variables, then on the objective and on the float variables. The
   * settings of --free-config select the heuristics; by default dom/wdeg with last conflict and
   * solution-based phase saving, and geometric restarts (100 failures, growing by 1.5) with nogoods
   * learned at each restart.
   */
  private boolean executeFreeSearch(Var costVar) {
    DefaultSearchVars searchVars = new DefaultSearchVars(dictionary);
    searchVars.defaultVars();
    boolean objectiveLast = "1".equals(options.freeConfig("objective-last", "1"));
    boolean restartOnSolution = "1".equals(options.freeConfig("restart-on-solution", "1"));
    boolean nogoods = "1".equals(options.freeConfig("nogoods", "1"));
    Calculator restarts = restartCalculator;
    if (!options.restartGiven()) {
      int scale = Integer.parseInt(options.freeConfig("scale", "100"));
      restarts =
          switch (options.freeConfig("restarts", "geometric")) {
            case "luby" -> new LubyCalculator(scale);
            case "geometric" ->
                new GeometricCalculator(
                    Double.parseDouble(options.freeConfig("base", "1.5")), scale);
            default -> null;
          };
    }

    List<SearchMonitor> monitors = new ArrayList<>();
    List<SelectChoicePoint<? extends Var>> selects = new ArrayList<>();
    IntVar objective = costVar instanceof IntVar c && objectiveLast ? c : null;
    boolean allSolutions = options.getAll() && costVar == null;
    Var[] shown = null;
    if (allSolutions) {
      // solutions are told apart by the output variables, so they are fixed first and the
      // other variables are completed once per solution
      DefaultSearchVars output = new DefaultSearchVars(dictionary);
      output.outputVars();
      Set<Var> outputSet = Collections.newSetFromMap(new IdentityHashMap<>());
      outputSet.addAll(Arrays.asList(output.getSetVars()));
      outputSet.addAll(Arrays.asList(output.getIntVars()));
      outputSet.addAll(Arrays.asList(output.getBoolVars()));
      outputSet.addAll(Arrays.asList(output.getFloatVars()));
      shown = outputSet.toArray(new Var[0]);
      addFreeSelects(
          selects,
          monitors,
          output.getSetVars(),
          output.getIntVars(),
          output.getBoolVars(),
          output.getFloatVars(),
          null);
      addFreeSelects(
          selects,
          monitors,
          withoutVars(searchVars.getSetVars(), outputSet, SetVar[]::new),
          withoutVars(searchVars.getIntVars(), outputSet, IntVar[]::new),
          withoutVars(searchVars.getBoolVars(), outputSet, BooleanVar[]::new),
          withoutVars(searchVars.getFloatVars(), outputSet, FloatVar[]::new),
          null);
    } else {
      addFreeSelects(
          selects,
          monitors,
          searchVars.getSetVars(),
          searchVars.getIntVars(),
          searchVars.getBoolVars(),
          searchVars.getFloatVars(),
          objective);
    }
    if (selects.isEmpty()) {
      selects.add(new SimpleSelect<>(new IntVar[0], null, new IndomainMin<>()));
    }

    SequenceSelect free = new SequenceSelect(selects);
    FreeSearch.Builder builder =
        FreeSearch.builder(store, free)
            .restarts(restarts)
            .restartOnSolution(restartOnSolution)
            .nogoodsFromRestarts(nogoods)
            .allSolutions(options.getAll())
            .onSolution(s -> printSolution());
    if (shown != null) {
      builder.distinctOn(shown);
    }
    for (SearchMonitor m : monitors) {
      builder.monitor(m);
    }
    String interleave = options.freeConfig("interleave", "restart");
    // all solutions are found in one run without restarts, which interleaving would give to the
    // annotation
    SelectChoicePoint<? extends Var> annotated =
        "none".equals(interleave) || allSolutions ? null : annotationSelect(annotatedSearch);
    if (annotated != null) {
      // free search completes what the annotation leaves unfixed
      builder.alternateWith(
          new SequenceSelect(List.of(annotated, free)),
          "solution".equals(interleave)
              ? FreeSearch.Alternation.UNTIL_FIRST_SOLUTION
              : FreeSearch.Alternation.EVERY_RESTART);
    }
    if (options.getTimeOut() > 0) {
      builder.timeLimit(Duration.ofMillis(options.getTimeOut()));
    }
    if (costVar != null) {
      builder.minimize((IntVar) costVar);
    }
    freeSearch = builder.build();
    if (options.debug()) {
      IO.println("% FreeSearch(" + restarts + ") " + selects);
    }
    freeSearchStatus = freeSearch.solve();
    return freeSearch.getSolutions() > 0;
  }

  /**
   * Adds the free search branching on the given variables: the set variables first, then the
   * integer and Boolean variables, then the objective and the float variables. The settings of
   * --free-config select the heuristics.
   */
  private void addFreeSelects(
      List<SelectChoicePoint<? extends Var>> selects,
      List<SearchMonitor> monitors,
      SetVar[] sets,
      IntVar[] ints,
      BooleanVar[] bools,
      FloatVar[] floats,
      IntVar objective) {
    String heuristic = options.freeConfig("heuristic", "domwdeg");
    int lastConflict = Integer.parseInt(options.freeConfig("lc", "1"));
    boolean phase = "1".equals(options.freeConfig("phase", "1"));
    if (sets.length > 0) {
      selects.add(new SimpleSelect<>(sets, new AfcMaxDeg<>(store), new IndomainSetMin<>()));
    }
    LinkedHashSet<IntVar> intAndBool = new LinkedHashSet<>(Arrays.asList(ints));
    intAndBool.addAll(Arrays.asList(bools));
    if (objective != null) {
      intAndBool.remove(objective);
      // for maximisation the cost variable is the negation of the objective of the model
      if (objectiveVariable instanceof IntVar o) {
        intAndBool.remove(o);
      }
    }
    IntVar[] vars = intAndBool.toArray(new IntVar[0]);
    Indomain<IntVar> values = new IndomainMin<>();
    int impact = Integer.parseInt(options.freeConfig("impact", "0"));
    if (impact > 0 && costVariable instanceof IntVar cost) {
      // costVariable is minimised; for maximisation it is the negated objective
      IndomainBoundImpact boundImpact = new IndomainBoundImpact(store, cost, false, impact, values);
      if ("first".equals(options.freeConfig("impact-until", "first"))) {
        boundImpact.untilFirstSolution();
      }
      monitors.add(boundImpact);
      values = boundImpact;
    }
    if (phase) {
      IndomainLastSolution saving = new IndomainLastSolution(vars, values);
      monitors.add(saving);
      values = saving;
    }
    if ("afc".equals(heuristic)) {
      if (ints.length > 0) {
        selects.add(new SimpleSelect<>(ints, new AfcMaxDeg<>(store), values));
      }
      if (bools.length > 0) {
        selects.add(new SimpleSelect<>(bools, new AfcMax<>(store), values));
      }
    } else if (vars.length > 0) {
      DomWdeg.Weighting weighting =
          switch (heuristic) {
            case "cacd" -> DomWdeg.Weighting.CACD;
            case "chs" -> DomWdeg.Weighting.CHS;
            default -> DomWdeg.Weighting.WDEG;
          };
      DomWdeg domWdeg = new DomWdeg(vars, values, weighting);
      monitors.add(domWdeg);
      SelectChoicePoint<IntVar> select = domWdeg;
      if (lastConflict > 0) {
        LastConflict lc = new LastConflict(domWdeg, values, lastConflict);
        monitors.add(lc);
        select = lc;
      }
      selects.add(select);
    }
    if (objective != null) {
      selects.add(new SimpleSelect<>(new IntVar[] {objective}, null, new IndomainMin<>()));
    }
    if (floats.length > 0) {
      selects.add(new SplitSelectFloat<>(store, floats, new LargestDomainFloat<>()));
    }
  }

  private static <V extends Var> V[] withoutVars(
      V[] vars, Set<Var> excluded, IntFunction<V[]> array) {
    return Arrays.stream(vars).filter(v -> !excluded.contains(v)).toArray(array);
  }

  /**
   * The branching of a search annotation, or null when there is none or it cannot be expressed as a
   * selection (priority search).
   */
  private SelectChoicePoint<? extends Var> annotationSelect(SearchItem<T> item) {
    if (item == null || item.type() == null) {
      return null;
    }
    return switch (item.type()) {
      case INT_SEARCH, BOOL_SEARCH -> item.getIntSelect();
      case SET_SEARCH -> item.getSetSelect();
      case FLOAT_SEARCH -> item.getFloatSelect();
      case WARM_START -> item.getWarmStartSelect();
      case SEQ_SEARCH -> {
        List<SelectChoicePoint<? extends Var>> selects = new ArrayList<>();
        for (SearchItem<T> sub : item.getSearchItems()) {
          SelectChoicePoint<? extends Var> s = annotationSelect(sub);
          if (s == null) {
            yield null;
          }
          selects.add(s);
        }
        yield selects.isEmpty() ? null : new SequenceSelect(selects);
      }
      default -> null;
    };
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
    objectiveVariable = cost;

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
      printAllSolutionsResult(interrupted, timeoutOccurred, isComplete);
      return;
    }
    if (optimization) {
      printOptimizationResult(interrupted, timeoutOccurred, isComplete);
    }
  }

  private void printAllSolutionsResult(
      boolean interrupted, boolean timeoutOccurred, boolean isComplete) {
    if (interrupted) {
      return;
    }
    if (isComplete && !timeoutOccurred && isSearchComplete() && relaxedSearchComplete()) {
      IO.println(SEPARATOR_LINE);
    } else if (timeoutOccurred) {
      IO.println(TIME_OUT_MSG);
    }
  }

  private void printOptimizationResult(
      boolean interrupted, boolean timeoutOccurred, boolean isComplete) {
    if (!interrupted
        && isComplete
        && !timeoutOccurred
        && isSearchComplete()
        && relaxedSearchComplete()) {
      IO.println(SEPARATOR_LINE);
    } else if (timeoutOccurred) {
      IO.println(TIME_OUT_MSG);
    }
  }

  /** Relax and reconstruct is complete only when its restart search explored everything. */
  private boolean relaxedSearchComplete() {
    return relaxVars == null || rs == null || rs.complete();
  }

  private boolean isSearchComplete() {
    return options.getNumberSolutions() == -1 || options.getNumberSolutions() > numberSolutions;
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

    if (lcg != null) {
      printLcgStatistics(interrupted);
      return;
    }

    if (freeSearch != null) {
      boolean complete =
          freeSearchStatus == FreeSearch.Status.OPTIMAL
              || freeSearchStatus == FreeSearch.Status.UNSATISFIABLE;
      printResultStatus(
          interrupted,
          freeSearch.getSolutions() > 0,
          freeSearch.limitReached(),
          complete && !interrupted);
      if (options.getStatistics()) {
        printStatisticsOutput(
            (int) freeSearch.getNodes(),
            (int) freeSearch.getFailures(),
            freeSearch.getMaxDepth(),
            (int) freeSearch.getSolutions());
      }
      return;
    }

    printResultStatus(
        interrupted,
        result,
        label.timeOutOccured,
        COMPLETE.equals(si.exploration()) && (rs == null || !rs.restartsLimitReached()));

    if (options.getStatistics()) {
      int[] stats = gatherSingleSearchStats();
      printStatisticsOutput(stats[0], stats[1], stats[2], stats[3]);
    }
  }

  private int[] gatherSingleSearchStats() {
    int nodes = 0;
    int wrong = 0;
    int depth = 0;
    int solutions = 0;

    if (!defaultSearch) {
      nodes = label.getNodes();
      wrong = label.getWrongDecisions();
      depth = label.getMaximumDepth();
      solutions = label.getSolutionListener().solutionsNo();
    }

    for (DepthFirstSearch<T> l : finalSearch) {
      if (l != null) {
        nodes += l.getNodes();
        wrong += l.getWrongDecisions();
        depth += l.getMaximumDepth();
        solutions = l instanceof PrioritySearch ? solutions : l.getSolutionListener().solutionsNo();
      }
    }

    return new int[] {nodes, wrong, depth, solutions};
  }

  @SuppressWarnings("unchecked")
  DepthFirstSearch<T>[] setSubSearchForAll(DepthFirstSearch<T> label, Options opt) {

    DepthFirstSearch<T>[] intAndSetSearch = new DepthFirstSearch[5];

    DefaultSearchVars searchVars = new DefaultSearchVars(dictionary);

    // With all solutions requested the default search also labels the output variables first:
    // labelling every variable would report a solution again for each assignment of variables
    // that are not output, such as the Boolean of a half-reification.
    boolean outputVarsOnly = !options.complementarySearch() && (label != null || options.getAll());
    if (outputVarsOnly) {
      searchVars.outputVars();
    }

    IntVar[] intSearchVariables = searchVars.getIntVars();
    SetVar[] setSearchVariables = searchVars.getSetVars();
    BooleanVar[] boolSearchVariables = searchVars.getBoolVars();
    FloatVar[] floatSearchVariables = searchVars.getFloatVars();

    if (shouldUseDefaultSearchVars(
        intSearchVariables, boolSearchVariables, setSearchVariables, floatSearchVariables)) {
      outputVarsOnly = false;
      searchVars.defaultVars();
      intSearchVariables = searchVars.getIntVars();
      setSearchVariables = searchVars.getSetVars();
      boolSearchVariables = searchVars.getBoolVars();
      floatSearchVariables = searchVars.getFloatVars();
    }

    if (opt.debug()) {
      IO.println(searchVars);
    }

    DepthFirstSearch<T> lastSearch = label;
    DepthFirstSearch<T> intSearch = new DepthFirstSearch<>();

    if (opt.debug()) {
      intSearch.setConsistencyListener(failStatistics);
    }

    if (setSearchVariables.length != 0) {
      // add set search containing all variables to be sure that they get a value
      DepthFirstSearch<T> setSearch = new DepthFirstSearch<>();

      if (opt.debug()) {
        setSearch.setConsistencyListener(failStatistics);
      }

      SelectChoicePoint<SetVar> setSelect =
          options.freeSearch() || options.complementarySearch()
              ? new SimpleSelect<>(
                  setSearchVariables, new AfcMaxDeg<>(store), new IndomainSetMin<>())
              : new SimpleSelect<>(setSearchVariables, null, new IndomainSetMin<>());

      if (variableSelection == null) {
        variableSelection = (SelectChoicePoint<T>) setSelect;
      }
      setSearch.setSelectChoicePoint((SelectChoicePoint<T>) setSelect);
      setSearch.setPrintInfo(false);
      if (lastSearch != null) {
        lastSearch.addChildSearch(setSearch);
      }
      lastSearch = setSearch;
      if (intSearchVariables.length == 0
          && boolSearchVariables.length == 0
          && floatSearchVariables.length == 0) {
        setSearch.setSolutionListener(new CostListener<>());
      }

      if (costVariable != null) {
        intSearch.setCostVar(costVariable);
        intSearch.setOptimize(true);
      }

      setSearchTimeout(setSearch);

      intAndSetSearch[0] = setSearch;
    }

    if (intSearchVariables.length != 0) {
      // add search containing int variables to be sure that they get a value
      SelectChoicePoint<IntVar> intSelect =
          options.freeSearch() || options.complementarySearch()
              ? new SimpleSelect<>(intSearchVariables, new AfcMaxDeg<>(store), new IndomainMin<>())
              // x <= middle keeps the order of the solutions of x = min, but needs only a
              // logarithmic number of nested choices to reach a value of a large domain
              : new SplitSelect<>(intSearchVariables, null, new IndomainMiddle<>());

      if (variableSelection == null) {
        variableSelection = (SelectChoicePoint<T>) intSelect;
      }
      intSearch.setSelectChoicePoint((SelectChoicePoint<T>) intSelect);
      intSearch.setPrintInfo(false);
      if (lastSearch != null) {
        lastSearch.addChildSearch(intSearch);
      }
      lastSearch = intSearch;
      if (boolSearchVariables.length == 0 && floatSearchVariables.length == 0) {
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

    if (boolSearchVariables.length != 0) {
      // add search containing boolean variables to be sure that they get a value
      SelectChoicePoint<BooleanVar> boolSelect =
          options.freeSearch() || options.complementarySearch()
              ? new SimpleSelect<>(boolSearchVariables, new AfcMax<>(store), new IndomainMin<>())
              : new SimpleSelect<>(boolSearchVariables, null, new IndomainMin<>());

      if (variableSelection == null) {
        variableSelection = (SelectChoicePoint<T>) boolSelect;
      }
      boolSearch.setSelectChoicePoint((SelectChoicePoint<T>) boolSelect);
      boolSearch.setPrintInfo(false);
      if (lastSearch != null) {
        lastSearch.addChildSearch(boolSearch);
      }
      lastSearch = boolSearch;
      if (floatSearchVariables.length == 0) {
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

    if (floatSearchVariables.length != 0) {
      // add float search containing all variables to be sure that they get a value
      DepthFirstSearch<T> floatSearch = new DepthFirstSearch<>();

      if (opt.debug()) {
        floatSearch.setConsistencyListener(failStatistics);
      }

      SelectChoicePoint<Var> floatSelect =
          options.freeSearch() || options.complementarySearch()
              ? new SplitSelectFloat<>(store, floatSearchVariables, new LargestDomainFloat<>())
              : new SplitSelectFloat<>(store, floatSearchVariables, null);

      if (variableSelection == null) {
        variableSelection = (SelectChoicePoint<T>) floatSelect;
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

      lastSearch = floatSearch;
      intAndSetSearch[3] = floatSearch;
    }

    if (outputVarsOnly && lastSearch != label) {
      intAndSetSearch[4] = addCompletionSearch(lastSearch);
    }

    if (noSearchVariables(
        intSearchVariables, boolSearchVariables, setSearchVariables, floatSearchVariables)) {
      handleTrivialSolution();
    }

    return intAndSetSearch;
  }

  /**
   * Adds a search on the integer and Boolean variables that the search on output variables leaves
   * out. Propagation alone does not guarantee that they can take values consistent with the output
   * variables, so a solution is reported only once they do. One assignment is enough: the search
   * stops at the first one, also when all solutions are requested.
   */
  @SuppressWarnings("unchecked")
  private DepthFirstSearch<T> addCompletionSearch(DepthFirstSearch<T> lastSearch) {
    DefaultSearchVars allVars = new DefaultSearchVars(dictionary);
    allVars.defaultVars();
    LinkedHashSet<IntVar> rest = new LinkedHashSet<>(Arrays.asList(allVars.getIntVars()));
    rest.addAll(Arrays.asList(allVars.getBoolVars()));
    if (rest.isEmpty()) {
      return null;
    }

    DepthFirstSearch<T> completion = new DepthFirstSearch<>();
    if (options.debug()) {
      completion.setConsistencyListener(failStatistics);
    }
    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            rest.toArray(new IntVar[0]), new SmallestDomain<>(), new IndomainMin<>());
    completion.setSelectChoicePoint((SelectChoicePoint<T>) select);
    completion.setPrintInfo(false);
    // the completion search finds solutions now, so it prints them
    lastSearch.setSolutionListener(new SimpleSolutionListener<>());
    completion.setSolutionListener(new CostListener<>());
    lastSearch.addChildSearch(completion);
    setSearchTimeout(completion);
    completionSearch = completion;
    return completion;
  }

  private boolean shouldUseDefaultSearchVars(
      IntVar[] intVars, BooleanVar[] boolVars, SetVar[] setVars, FloatVar[] floatVars) {
    return (intVars.length == 0
            && boolVars.length == 0
            && setVars.length == 0
            && floatVars.length == 0)
        || options.complementarySearch()
        || options.freeSearch();
  }

  private boolean noSearchVariables(
      IntVar[] intVars, BooleanVar[] boolVars, SetVar[] setVars, FloatVar[] floatVars) {
    return intVars.length == 0
        && boolVars.length == 0
        && setVars.length == 0
        && floatVars.length == 0;
  }

  private void handleTrivialSolution() {
    if (!sat.collectedClauses().isEmpty()) {
      postCollectedClauses();
      if (!store.consistency()) {
        IO.println("=====UNSATISFIABLE=====");
        throw new TrivialSolution();
      }
    }
    printSolution();

    if (lastSolution != null) {
      helperSolutionPrinter(lastSolution.toString());
    }

    if (options.getAll() || costVariable != null) {
      IO.println(SEPARATOR_LINE);
    }

    if (options.getStatistics()) {
      IO.println(buildTrivialSolutionStatsLine());
    }
    throw new TrivialSolution();
  }

  private String buildTrivialSolutionStatsLine() {
    return "%%%mzn-stat: variables="
        + (store.size() + dictionary.getNumberBoolVariables() - dictionary.constantTable.size())
        + "\n%%%mzn-stat: propagators="
        + initNumberConstraints
        + "\n\n%%%mzn-stat: initTime="
        + getInitTime_ms() / 1000.0
        + "\n%%%mzn-stat: solveTime=0"
        + "\n%%%mzn-stat: nodes=0"
        + "\n%%%mzn-stat: propagations="
        + store.numberConsistencyCalls
        + "\n%%%mzn-stat: restarts=0"
        + "\n%%%mzn-stat: failures=0"
        + "\n%%%mzn-stat: peakDepth=0"
        + "\n%%%mzn-stat: solutions=1"
        + "\n%%%mzn-stat-end";
  }

  @SuppressWarnings("unchecked")
  void run_sequence_search(int solveKind, SimpleNode kind, SearchItem<T> si) {

    if (si.getSearchItems().isEmpty()) {
      // every annotation in the sequence was ignored
      run_single_search(solveKind, kind, null);
      return;
    }

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
    listSeqSearches = new ArrayList<>();

    for (int i = 0; i < si.getSearchItems().size(); i++) {
      if (i == 0) {
        masterLabel = sub_search(si.getSearchItems().get(i), null, true);
        last_search = getLastSearch(masterLabel);
        masterSelect = variableSelection;
        if (!printSearchInfo) {
          masterLabel.setPrintInfo(false);
        }
      } else {
        last_search = addChildSequenceSearch(si.getSearchItems().get(i), last_search);
      }
    }

    Var costVar = null;
    if (solveKind > 0) {
      costVar = setupCostVariable(kind, solveKind);
    }

    DepthFirstSearch<T>[] complementarySearch = setSubSearchForAll(last_search, options);
    for (DepthFirstSearch<T> aComplementarySearch : complementarySearch) {
      if (aComplementarySearch != null) {
        listSeqSearches.add(aComplementarySearch);
        if (!printSearchInfo) {
          aComplementarySearch.setPrintInfo(false);
        }
      }
    }

    result = false;
    optimization = solveKind > 0;

    finalSearchSeq = listSeqSearches.getLast();

    long currentTime = timer.getCpuTime();
    initTime = currentTime - startCpu;
    startCpu = currentTime;

    setSearchTimeout(listSeqSearches);

    if (si.exploration() == null || COMPLETE.equals(si.exploration())) {
      FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

      ensureAllSolutionsIfRequested(masterLabel, solveKind);

      String solveType = resolveSolveTypeForSequenceSearch(solveKind);

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

  /**
   * Handles option -a. For satisfaction problems it asks for all solutions, which restart search
   * cannot enumerate. For optimization it only prints every improving solution, which restart
   * search does as it finds them, so the search itself is left as it is.
   */
  private void ensureAllSolutionsIfRequested(DepthFirstSearch<T> masterLabel, int solveKind) {
    if (!options.getAll()) {
      return;
    }
    if (restartCalculator != null) {
      // the FreeSearch engine finds all solutions without restarts
      if (solveKind == 0 && !useFreeSearchEngine(null)) {
        throw new IllegalArgumentException(
            "Flatzinc option for search for all solutions (-a) cannot be used in restart search"
                + " of a satisfaction problem.");
      }
      return;
    }
    searchForAll(masterLabel);
  }

  private String resolveSolveTypeForSequenceSearch(int solveKind) {
    return switch (solveKind) {
      case 0 -> SATISFY;
      case 1 -> {
        for (Search<T> seqSearch : listSeqSearches) {
          seqSearch.setOptimize(true);
        }
        yield MINIMIZE_LITERAL;
      }
      case 2 -> {
        for (Search<T> seqSearch : listSeqSearches) {
          seqSearch.setOptimize(true);
        }
        yield MAXIMIZE_LITERAL;
      }
      default ->
          throw new IllegalArgumentException(
              "Not recognized or supported search strategy; compilation aborted");
    };
  }

  private DepthFirstSearch<T> addChildSequenceSearch(
      SearchItem<T> item, DepthFirstSearch<T> lastSearch) {
    DepthFirstSearch<T> label = sub_search(item, lastSearch, false);
    lastSearch.addChildSearch(label);
    DepthFirstSearch<T> newLast = getLastSearch(label);
    if (!printSearchInfo) {
      newLast.setPrintInfo(false);
    }
    return newLast;
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

    if (lcg != null) {
      printLcgStatistics(interrupted);
      return;
    }

    if (listSeqSearches == null) {
      IO.println("%% =====INTERRUPTED=====\n%% Model not yet posed..");
      return;
    }

    boolean timeoutOccurred = anyTimeOutOccured(listSeqSearches);
    printResultStatus(
        interrupted,
        result,
        timeoutOccurred,
        !heuristicSeqSearch && (rs == null || !rs.restartsLimitReached()));

    if (options.getStatistics()) {
      int[] stats = gatherSequenceSearchStats();
      // each search of the sequence counts the solutions of its own phase, so count the
      // solutions that were reported instead
      printStatisticsOutput(stats[0], stats[1], stats[2], numberSolutions);
    }
  }

  private int[] gatherSequenceSearchStats() {
    int nodes = 0;
    int wrong = 0;
    int depth = 0;
    int solutions = 0;
    for (Search<T> searchLabel : listSeqSearches) {
      nodes += searchLabel.getNodes();
      wrong += searchLabel.getWrongDecisions();
      depth += searchLabel.getMaximumDepth();
      solutions += searchLabel.getSolutionListener().solutionsNo();
    }
    return new int[] {nodes, wrong, depth, solutions};
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
    long restarts = rs != null ? rs.restarts() : 0;
    if (freeSearch != null) {
      restarts = freeSearch.getRestarts();
    }

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
            + (freeSearch != null && freeSearch.getNogoods() > 0
                ? "\n%%%mzn-stat: nogoods=" + nf.format(freeSearch.getNogoods())
                : "")
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
    return searchTime / 1_000_000.0;
  }

  /**
   * Returns the initialization time in milliseconds.
   *
   * @return the initialization time in milliseconds
   */
  double getInitTime_ms() {
    return initTime / 1_000_000.0;
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
      label.setSelectChoicePoint(variableSelection);
    }
    heuristicSeqSearch |= applyHeuristicSearch(label, si);
    listSeqSearches.add(label);
    label.setPrintInfo(false);
    return label;
  }

  private DepthFirstSearch<T> subSearchSet(SearchItem<T> si, boolean master) {
    DepthFirstSearch<T> label = set_search(si);
    if (!master) {
      label.setSelectChoicePoint(variableSelection);
    }
    heuristicSeqSearch |= applyHeuristicSearch(label, si);
    listSeqSearches.add(label);
    label.setPrintInfo(false);
    return label;
  }

  private DepthFirstSearch<T> subSearchPriority(SearchItem<T> si) {
    DepthFirstSearch<T> label = priority_search(si);
    listSeqSearches.add(label);
    return label;
  }

  private DepthFirstSearch<T> subSearchWarmStart(SearchItem<T> si, boolean master) {
    DepthFirstSearch<T> label = warm_start_search(si);
    if (!master) {
      label.setSelectChoicePoint(variableSelection);
    }
    listSeqSearches.add(label);
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
      label.setSelectChoicePoint(variableSelection);
    }
    heuristicSeqSearch |= applyHeuristicSearch(label, si);
    listSeqSearches.add(label);
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

    variableSelection = (SelectChoicePoint<T>) si.getIntSelect();
    DepthFirstSearch<T> label = new DepthFirstSearch<>();
    label.setAssignSolution(false);

    if (options.debug()) {
      label.setConsistencyListener(failStatistics);
    }

    return label;
  }

  @SuppressWarnings("unchecked")
  DepthFirstSearch<T> warm_start_search(SearchItem<T> si) {

    variableSelection = (SelectChoicePoint<T>) si.getWarmStartSelect();
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

    variableSelection = (SelectChoicePoint<T>) si.getSetSelect();
    DepthFirstSearch<T> label = new DepthFirstSearch<>();
    label.setAssignSolution(false);

    if (options.debug()) {
      label.setConsistencyListener(failStatistics);
    }

    return label;
  }

  @SuppressWarnings("unchecked")
  DepthFirstSearch<T> float_search(SearchItem<T> si) {
    variableSelection = (SelectChoicePoint<T>) si.getFloatSelect();
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
    return switch (s.searchType) {
      case INT_SEARCH, BOOL_SEARCH -> withSelect(int_search(s));
      case SET_SEARCH -> withSelect(set_search(s));
      case FLOAT_SEARCH -> withSelect(float_search(s));
      // a seq_search or a priority_search already has the heuristics of its own sub-searches
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
                  + s.searchType
                  + "in priority_search; execution aborted");
    };
  }

  private DepthFirstSearch<T> withSelect(DepthFirstSearch<T> label) {
    label.setSelectChoicePoint(variableSelection);
    return label;
  }

  @SuppressWarnings("unchecked")
  DepthFirstSearch<T> priority_search(SearchItem<T> si) {

    DepthFirstSearch<T>[] searches = buildPrioritySearchesArray(si.getSearchItems());

    SearchItem.ComparatorsVar<IntVar> vs = si.getVarSelect();
    PrioritySearch<T> label =
        new PrioritySearch<>(
            (T[]) si.vars(),
            (ComparatorVariable<T>) vs.v1,
            (ComparatorVariable<T>) vs.v2,
            searches);
    label.setPrintInfo(false);
    label.setAssignSolution(false);

    configurePriorityLabel(label, searches);
    return label;
  }

  private DepthFirstSearch<T>[] buildPrioritySearchesArray(ArrayList<SearchItem<T>> items) {
    DepthFirstSearch<T>[] searches = new DepthFirstSearch[items.size()];
    int i = 0;
    for (SearchItem<T> s : items) {
      DepthFirstSearch<T> subSearch = createPrioritySubSearch(s);
      subSearch.setPrintInfo(false);
      searches[i++] = subSearch;
    }
    return searches;
  }

  private void configurePriorityLabel(PrioritySearch<T> label, DepthFirstSearch<T>[] searches) {
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
      // printSolution stops the search at the requested number of solutions; the priority search
      // cannot count them itself, since its child searches' listeners count each other's solutions
      label.setSolutionLimit(Integer.MAX_VALUE);
    }
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
      appendOutputVariablesToBuffer(printBuffer);
    }

    for (int i = 0; i < dictionary.outputArray.size(); i++) {
      printBuffer.append(dictionary.outputArray.get(i)).append("\n");
    }

    if (options.getVerbose()) {
      appendVerboseStatsToBuffer(printBuffer);
    }

    printBuffer.append("----------\n");

    if (options.getAll()) {
      IO.print(printBuffer.toString());
      appendSolutionToOutputFile(printBuffer.toString());
    } else {
      lastSolution = printBuffer;
    }

    if (options.getNumberSolutions() == numberSolutions) {
      throw new NumberSolutionsReached();
    }
  }

  private void appendOutputVariablesToBuffer(StringBuffer printBuffer) {
    for (int i = 0; i < dictionary.outputVariables.size(); i++) {
      appendVariableOutput(printBuffer, dictionary.outputVariables.get(i));
    }
  }

  private int countNodesFromLabel() {
    int nodes = 0;
    @SuppressWarnings("unchecked")
    DepthFirstSearch<T> dfs = label;
    while (dfs != null) {
      nodes += dfs.getNodes();
      dfs = dfs.childSearches == null ? null : (DepthFirstSearch<T>) dfs.childSearches[0];
    }
    return nodes;
  }

  private void appendCostLineToBuffer(StringBuffer printBuffer) {
    if (costVariable == null) {
      return;
    }
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

  private void appendVerboseStatsToBuffer(StringBuffer printBuffer) {
    int nodes = countNodesFromLabel();
    appendCostLineToBuffer(printBuffer);
    double cpuTime = getSearchTime_ms();
    printBuffer.append("%%%mzn-stat: nodes=").append(nf.format(nodes)).append("\n");
    printBuffer
        .append("%%%mzn-stat: nodesPerSecond=")
        .append(nf.format(cpuTime == 0 ? 0.0 : (double) nodes / (cpuTime / 1000)))
        .append("\n");
    if (restartCalculator != null) {
      printBuffer.append("%%%%mzn-stat: restarts=").append(nf.format(rs.restarts()));
    }
    printBuffer.append("\n%%%mzn-stat: solveTime=").append(nf.format(cpuTime / 1000)).append("\n");
    printBuffer.append("%%%mzn-stat-end\n");
  }

  int getKind(String k) {
    return switch (k) {
      case SATISFY ->
          // 0 = satisfy
          0;
      case MINIMIZE_LITERAL ->
          // 1 = minimize
          1;
      case MAXIMIZE_LITERAL ->
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

  /** With option -a every solution goes to the output file; the first one truncates it. */
  private void appendSolutionToOutputFile(String solution) {
    if (options.getOutputFilename().isEmpty()) {
      return;
    }
    try {
      Files.writeString(
          Path.of(options.getOutputFilename()),
          solution,
          StandardOpenOption.CREATE,
          numberSolutions == 1 ? StandardOpenOption.TRUNCATE_EXISTING : StandardOpenOption.APPEND);
    } catch (IOException e) {
      log.error("Failed to write solution to {}", options.getOutputFilename(), e);
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
