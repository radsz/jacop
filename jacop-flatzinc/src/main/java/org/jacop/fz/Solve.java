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
      case none:
        break;
      case constant:
        restartCalculator = new ConstantCalculator(opt.getRestartScale());
        break;
      case linear:
        restartCalculator = new LinearCalculator(opt.getRestartScale());
        break;
      case luby:
        restartCalculator = new LubyCalculator(opt.getRestartScale());
        break;
      case geometric:
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
      String search_type = si.type();

      kind = (ASTSolveKind) node.jjtGetChild(1);
      solveKind = getKind(kind.getKind());

      if (opt.freeSearch()) { // free search -> ignoring search annotations
        run_single_search(solveKind, kind, null);
      } else if ("int_search".equals(search_type)
          || "set_search".equals(search_type)
          || "bool_search".equals(search_type)) {
        run_single_search(solveKind, kind, si);
      } else if ("float_search".equals(search_type)) {
        run_single_search(solveKind, kind, si);
      } else if ("seq_search".equals(search_type)) {
        run_sequence_search(solveKind, kind, si);
      } else if ("priority_search".equals(search_type)) {
        run_single_search(solveKind, kind, si);
      } else if ("warm_start".equals(search_type)) {
        run_single_search(solveKind, kind, si);
      } else if (search_type.startsWith("restart_")) {
        run_single_search(solveKind, kind, si);
      } else {
        if ("$expr".equals(search_type)) {
          search_type =
              ((ASTScalarFlatExpr) node.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0)).getIdent();
        }
        System.err.println(
            "%% Warning: Not supported search annotation: \"" + search_type + "\"; ignored");

        run_single_search(solveKind, kind, null);
      }
    } else if (count > 2) { // several annotations

      SearchItem<T> si = new SearchItem<>(store, dictionary);
      si.searchParametersForSeveralAnnotations(node, 0);

      ArrayList<SearchItem<T>> nsi = parseSearchAnnotations(si.search_seq);

      if (nsi.size() == 1) { // single search (int, set, float, seq or priority) + other annotations
        // (restart_*)
        SearchItem<T> fs = nsi.getFirst();

        kind = (ASTSolveKind) node.jjtGetChild(si.search_seqSize());
        solveKind = getKind(kind.getKind());

        if ("seq_search".equals(fs.type())) {
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
        siq.setSearchType("seq_search");
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
      } else if (s.search_type.endsWith("warm_start")) {
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
      String solve =
          switch (solveKind) {
            case 0 -> "%% satisfy"; // satisfy
            case 1 -> {
              Var costMin =
                  getCost((ASTSolveExpr) kind.jjtGetChild(0)) != null
                      ? getCost((ASTSolveExpr) kind.jjtGetChild(0))
                      : getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
              yield "%% minimize(" + costMin + ") ";
            }
            case 2 -> {
              Var costMax =
                  getCost((ASTSolveExpr) kind.jjtGetChild(0)) != null
                      ? getCost((ASTSolveExpr) kind.jjtGetChild(0))
                      : getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
              yield "%% maximize(" + costMax + ") ";
            }
            default -> throw new RuntimeException("Internal error in " + getClass().getName());
          };
      IO.println(solve + " : " + si);
    }

    label = null;
    optimization = false;
    list_seq_searches = new ArrayList<>();

    Var cost = null;
    Var max_cost = null;
    label = null;
    if (si != null) {
      if ("int_search".equals(si.type())) {
        label = int_search(si);
        list_seq_searches.add(label);
        label.setPrintInfo(false);
        setSearchTimeout(label);
      } else if ("bool_search".equals(si.type())) {
        label = int_search(si);
        list_seq_searches.add(label);
        label.setPrintInfo(false);
        setSearchTimeout(label);
      } else if ("set_search".equals(si.type())) {
        label = set_search(si);
        list_seq_searches.add(label);
        label.setPrintInfo(false);
        setSearchTimeout(label);
      } else if ("float_search".equals(si.type())) {
        label = float_search(si);
        list_seq_searches.add(label);
        label.setPrintInfo(false);
        setSearchTimeout(label);
      } else if ("priority_search".equals(si.type())) {
        label = priority_search(si);
        list_seq_searches.add(label);
        label.setPrintInfo(false);
        setSearchTimeout(label);
      } else if ("warm_start".equals(si.type())) {
        label = warm_start_search(si);
        list_seq_searches.add(label);
        label.setPrintInfo(false);
        setSearchTimeout(label);
      } else if (si.type().startsWith("restart_")) {
        ArrayList<SearchItem<T>> sa = new ArrayList<>();
        sa.add(si);
        ArrayList<SearchItem<T>> ns = parseSearchAnnotations(sa);
        si = null;
      } else {
        throw new IllegalArgumentException(
            "Not recognized or supported search type \"" + si.type() + "\"; compilation aborted");
      }
    }

    if (solveKind > 0) {
      optimization = true;

      cost = getCost((ASTSolveExpr) kind.jjtGetChild(0));
      if (cost != null) {
        if (solveKind == 1) { // minimize
          costVariable = cost;
        } else { // maximize
          max_cost =
              new IntVar(
                  store,
                  "-" + cost.id(),
                  -((IntVar) cost).max(),
                  -((IntVar) cost).min()); // IntDomain.MIN_INT, IntDomain.MAX_INT);
          pose(new XplusYeqC((IntVar) max_cost, (IntVar) cost, 0));
          costVariable = max_cost;
        }
      } else {
        cost = getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
        if (solveKind == 1) { // minimize
          costVariable = cost;
        } else { // maximize
          max_cost =
              new FloatVar(
                  store,
                  "-" + cost.id(),
                  -((FloatVar) cost).max(),
                  -((FloatVar) cost)
                      .min()); // VariablesParameters.MIN_FLOAT, VariablesParameters.MAX_FLOAT);
          pose(new PplusQeqR((FloatVar) max_cost, (FloatVar) cost, new FloatVar(store, 0.0, 0.0)));
          costVariable = max_cost;
        }
      }
    }

    // adds child search for cost; to be sure that all variables get a value
    final_search = setSubSearchForAll(label, options);
    Search<T> last_search;

    if (si == null) {
      defaultSearch = true;
      si = new SearchItem<>(store, dictionary);
      si.explore = "complete";
      if (final_search[0] != null) {
        label = final_search[0];
        list_seq_searches.add(label);
        for (int i = 1; i < final_search.length; i++) {
          if (final_search[i] != null) {
            list_seq_searches.add(final_search[i]);
          }
        }
      } else if (final_search[1] != null) {
        label = final_search[1];
        list_seq_searches.add(label);
        if (final_search[2] != null) {
          list_seq_searches.add(final_search[2]);
        }

      } else if (final_search[2] != null) {
        label = final_search[2];
        list_seq_searches.add(label);
        if (final_search[3] != null) {
          list_seq_searches.add(final_search[3]);
        }
      } else if (final_search[3] != null) {
        label = final_search[3];
        list_seq_searches.add(label);
      }
    } else {
      for (DepthFirstSearch<T> s : final_search) {
        if (s != null) {
          list_seq_searches.add(s);
        }
      }
    }
    list_seq_searches.getLast();

    // Lds & Credit heuristic search
    if ("lds".equals(si.exploration())) {
      lds_search(label, si.ldsValue);
      // Credit heuristic search
    } else if ("credit".equals(si.exploration())) {
      credit_search(label, si.creditValue, si.bbsValue);
    }

    result = false;

    long currentTime = timer.getCpuTime();
    initTime = currentTime - startCpu;
    startCpu = currentTime;

    if (si.exploration() == null
        || "complete".equals(si.exploration())
        || "lds".equals(si.exploration())
        || "credit".equals(si.exploration())) {
      switch (solveKind) {
        case 0: // satisfy
          FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

          if (options.getAll()) { // all solutions
            if (restartCalculator != null) {
              throw new IllegalArgumentException(
                  "Flatzinc option for search for all solutions (-a) cannot be used in restart search.");
            }

            searchForAll(label);
          }

          this.si = si;

          if (options.runSearch()) {
            try {
              if (restartCalculator != null) {
                if (options.debug()) {
                  IO.print("% RestartSearch(" + restartCalculator + "), ");
                  label.setSelectChoicePoint(variable_selection);
                  IO.print(" satisfy ");
                  printSearch(label);
                }

                rs = new RestartSearch<>(store, label, variable_selection, restartCalculator);
                rs.setRestartsLimit(options.getRestartLimit());
                setSearchTimeout(rs);

                if (relaxVars != null) {
                  rs.setRelaxAndReconstruct(relaxVars, probability);
                }

                result = rs.labeling();
              } else {
                if (options.debug()) {
                  label.setSelectChoicePoint(variable_selection);
                  IO.print("% satisfy ");
                  printSearch(label);
                }

                result = label.labeling(store, variable_selection);
              }
            } catch (NumberSolutionsReached _) {
              result = numberSolutions > 0;
            }
          } else {
            // storing flatiznc defined search
            flatzincDfs = label;
            flatzincVariableSelection = variable_selection;
            flatzincCost = null;
            return;
          }

          break;
        case 1: // minimize
          FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

          this.si = si;

          if (options.runSearch()) {
            try {
              if (restartCalculator != null) {
                if (options.debug()) {
                  IO.print("% RestartSearch(" + restartCalculator + "), ");
                  label.setSelectChoicePoint(variable_selection);
                  IO.print(" minimize (" + cost + ") ");
                  printSearch(label);
                }

                rs =
                    new RestartSearch<>(
                        store, label, variable_selection, restartCalculator, (T) cost);
                rs.setRestartsLimit(options.getRestartLimit());
                setSearchTimeout(rs);

                if (relaxVars != null) {
                  rs.setRelaxAndReconstruct(relaxVars, probability);
                }

                result = rs.labeling();
              } else {
                if (options.debug()) {
                  label.setSelectChoicePoint(variable_selection);
                  IO.print("% minimize (" + cost + ") ");
                  printSearch(label);
                }
                result = label.labeling(store, variable_selection, cost);
              }
            } catch (NumberSolutionsReached _) {
              result = numberSolutions > 0;
            }
          } else {
            // storing flatiznc defined search
            flatzincDfs = label;
            flatzincVariableSelection = variable_selection;
            flatzincCost = cost;
            return;
          }

          break;
        case 2: // maximize
          FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

          this.si = si;

          if (options.runSearch()) {
            try {
              if (restartCalculator != null) {
                if (options.debug()) {
                  IO.print("% RestartSearch(" + restartCalculator + "), ");
                  label.setSelectChoicePoint(variable_selection);
                  IO.print("% maximize (" + cost + ") ");
                  printSearch(label);
                }

                rs =
                    new RestartSearch<>(
                        store, label, variable_selection, restartCalculator, (T) max_cost);
                rs.setRestartsLimit(options.getRestartLimit());
                setSearchTimeout(rs);

                if (relaxVars != null) {
                  rs.setRelaxAndReconstruct(relaxVars, probability);
                }

                result = rs.labeling();
              } else {
                if (options.debug()) {
                  label.setSelectChoicePoint(variable_selection);
                  IO.print("% maximize (" + cost + ") ");
                  printSearch(label);
                }

                result = label.labeling(store, variable_selection, max_cost);
              }
            } catch (NumberSolutionsReached _) {
              result = numberSolutions > 0;
            }
          } else {
            // storing flatiznc defined search
            flatzincDfs = label;
            flatzincVariableSelection = variable_selection;
            flatzincCost = max_cost;
            return;
          }

          break;
        default:
          throw new IllegalArgumentException(
              "Not recognized or supported search strategy; compilation aborted");
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
      if (!optimization && options.getAll()) {
        if (!interrupted) {
          if (isComplete) {
            if (!timeoutOccurred) {
              if ((options.getNumberSolutions() == -1
                      || options.getNumberSolutions() > numberSolutions)
                  && relaxVars == null) {
                IO.println("==========");
              }
            } else {
              IO.println("%% =====TIME-OUT=====");
            }
          } else if (timeoutOccurred) {
            IO.println("%% =====TIME-OUT=====");
          }
        }
      } else if (optimization) {
        if (!interrupted && isComplete) {
          if (!timeoutOccurred) {
            if ((options.getNumberSolutions() == -1
                    || options.getNumberSolutions() > numberSolutions)
                && relaxVars == null) {
              IO.println("==========");
            }
          } else {
            IO.println("%% =====TIME-OUT=====");
          }
        } else if (timeoutOccurred) {
          IO.println("%% =====TIME-OUT=====");
        }
      }
    } else if (timeoutOccurred) {
      IO.println("=====UNKNOWN=====");
      IO.println("%% =====TIME-OUT=====");
    } else if (interrupted) {
      IO.println("%% =====INTERRUPTED=====");
    } else if (isComplete) {
      IO.println("=====UNSATISFIABLE=====");
      if (!options.getOutputFilename().isEmpty()) {
        String st = "=====UNSATISFIABLE=====";
        try {
          Files.writeString(Path.of(options.getOutputFilename()), st);
        } catch (IOException e1) {
          log.error("Failed to write output to {}", options.getOutputFilename(), e1);
        }
      }
    } else {
      IO.println("=====UNKNOWN=====");
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

    printResultStatus(
        interrupted, result, label.timeOutOccured, "complete".equals(si.exploration()));

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
        IO.println("==========");
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
      String solve =
          switch (solveKind) {
            case 0 -> "%% satisfy"; // satisfy
            case 1 -> {
              Var costMin =
                  getCost((ASTSolveExpr) kind.jjtGetChild(0)) != null
                      ? getCost((ASTSolveExpr) kind.jjtGetChild(0))
                      : getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
              yield "%% minimize(" + costMin + ") ";
            }
            case 2 -> {
              Var costMax =
                  getCost((ASTSolveExpr) kind.jjtGetChild(0)) != null
                      ? getCost((ASTSolveExpr) kind.jjtGetChild(0))
                      : getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
              yield "%% maximize(" + costMax + ") ";
            }
            default -> throw new RuntimeException("Internal error in " + getClass().getName());
          };
      IO.println(solve + " : " + si);
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
    optimization = false;

    final_search_seq = list_seq_searches.getLast();
    Var cost;
    Var max_cost;

    long currentTime = timer.getCpuTime();
    initTime = currentTime - startCpu;
    startCpu = currentTime;

    setSearchTimeout(list_seq_searches);

    if (si.exploration() == null || "complete".equals(si.exploration())) {
      switch (solveKind) {
        case 0: // satisfy
          FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

          if (options.getAll()) { // all solutions
            if (restartCalculator != null) {
              throw new IllegalArgumentException(
                  "Flatzinc option for search for all solutions (-a) cannot be used in restart search.");
            }

            searchForAll(masterLabel);
          }

          if (options.runSearch()) {
            try {
              if (restartCalculator != null) {

                label = masterLabel;

                if (options.debug()) {
                  IO.print("% RestartSearch(" + restartCalculator + "), ");
                  label.setSelectChoicePoint(masterSelect);
                  IO.print(" satisfy ");
                  printSearch(label);
                }

                rs = new RestartSearch<>(store, masterLabel, masterSelect, restartCalculator);
                rs.setRestartsLimit(options.getRestartLimit());
                setSearchTimeout(rs);

                if (relaxVars != null) {
                  rs.setRelaxAndReconstruct(relaxVars, probability);
                }

                result = rs.labeling();
              } else {
                if (options.debug()) {
                  masterLabel.setSelectChoicePoint(masterSelect);
                  IO.print("% satisfy ");
                  printSearch(masterLabel);
                }

                label = masterLabel;
                result = masterLabel.labeling(store, masterSelect);
              }
            } catch (NumberSolutionsReached _) {
              result = numberSolutions > 0;
            }
          } else {
            // storing flatiznc defined search
            flatzincDfs = masterLabel;
            flatzincVariableSelection = masterSelect;
            flatzincCost = null;
            return;
          }

          break;

        case 1: // minimize
          optimization = true;

          FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

          cost = getCost((ASTSolveExpr) kind.jjtGetChild(0));
          if (cost == null) {
            cost = getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
          }
          costVariable = cost;

          // result = restart_search(masterLabel, masterSelect, cost, true);

          for (Search<T> list_seq_searche : list_seq_searches) {
            list_seq_searche.setOptimize(true);
          }

          if (options.runSearch()) {

            try {
              if (restartCalculator != null) {

                label = masterLabel;

                if (options.debug()) {
                  IO.print("% RestartSearch(" + restartCalculator + "), ");
                  label.setSelectChoicePoint(masterSelect);
                  IO.print(" minimize (" + cost + ") ");
                  printSearch(label);
                }

                rs =
                    new RestartSearch<>(
                        store, masterLabel, masterSelect, restartCalculator, (T) cost);
                rs.setRestartsLimit(options.getRestartLimit());
                setSearchTimeout(rs);

                if (relaxVars != null) {
                  rs.setRelaxAndReconstruct(relaxVars, probability);
                }

                result = rs.labeling();
              } else {

                label = masterLabel;

                if (options.debug()) {
                  masterLabel.setSelectChoicePoint(masterSelect);
                  IO.print("% minimize (" + cost + ") ");
                  printSearch(masterLabel);
                }

                result = masterLabel.labeling(store, masterSelect, cost);
              }
            } catch (NumberSolutionsReached _) {
              result = numberSolutions > 0;
            }
          } else {
            // storing flatiznc defined search
            flatzincDfs = masterLabel;
            flatzincVariableSelection = masterSelect;
            flatzincCost = cost;
            return;
          }

          break;
        case 2: // maximize
          optimization = true;
          // cost = getCost((ASTSolveExpr)kind.jjtGetChild(0));

          FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

          cost = getCost((ASTSolveExpr) kind.jjtGetChild(0));
          if (cost != null) { // maximize
            max_cost = new IntVar(store, "-" + cost.id(), IntDomain.MIN_INT, IntDomain.MAX_INT);
            pose(new XplusYeqC((IntVar) max_cost, (IntVar) cost, 0));
          } else {
            cost = getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
            max_cost =
                new FloatVar(
                    store,
                    "-" + cost.id(),
                    VariablesParameters.MIN_FLOAT,
                    VariablesParameters.MAX_FLOAT);
            pose(
                new PplusQeqR((FloatVar) max_cost, (FloatVar) cost, new FloatVar(store, 0.0, 0.0)));
          }
          costVariable = max_cost;

          // result = restart_search(masterLabel, masterSelect, cost, false);

          for (Search<T> list_seq_searche : list_seq_searches) {
            list_seq_searche.setOptimize(true);
          }

          if (options.runSearch()) {
            try {
              if (restartCalculator != null) {

                label = masterLabel;

                if (options.debug()) {
                  IO.print("% RestartSearch(" + restartCalculator + "), ");
                  label.setSelectChoicePoint(masterSelect);
                  IO.print(" maximize (" + cost + ") ");
                  printSearch(label);
                }

                rs =
                    new RestartSearch<>(
                        store, masterLabel, masterSelect, restartCalculator, (T) max_cost);
                rs.setRestartsLimit(options.getRestartLimit());
                setSearchTimeout(rs);

                if (relaxVars != null) {
                  rs.setRelaxAndReconstruct(relaxVars, probability);
                }

                result = rs.labeling();
              } else {
                if (options.debug()) {
                  masterLabel.setSelectChoicePoint(masterSelect);
                  IO.print("% maximize (" + cost + ") ");
                  printSearch(masterLabel);
                }

                label = masterLabel;
                result = masterLabel.labeling(store, masterSelect, max_cost);
              }
            } catch (NumberSolutionsReached _) {
              result = numberSolutions > 0;
            }
          } else {
            // storing flatiznc defined search
            flatzincDfs = masterLabel;
            flatzincVariableSelection = masterSelect;
            flatzincCost = max_cost;
            return;
          }

          break;
        default:
          throw new IllegalArgumentException(
              "Not recognized or supported search strategy; compilation aborted");
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
      IO.println(s.replaceAll("\n", "\n% "));
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
    DepthFirstSearch<T> last_search = l;
    DepthFirstSearch<T> label = null;

    switch (si.type()) {
      case "int_search", "bool_search" -> {
        label = int_search(si);
        if (!master) {
          label.setSelectChoicePoint(variable_selection);
        }

        // Lds heuristic search
        if ("lds".equals(si.exploration())) {
          lds_search(label, si.ldsValue);
          heuristicSeqSearch = true;
        }
        // Credit heuristic search
        if ("credit".equals(si.exploration())) {
          credit_search(label, si.creditValue, si.bbsValue);
          heuristicSeqSearch = true;
        }
        list_seq_searches.add(label);
        label.setPrintInfo(false);
      }
      case "set_search" -> {
        label = set_search(si);
        if (!master) {
          label.setSelectChoicePoint(variable_selection);
        }

        // Lds heuristic search
        if ("lds".equals(si.exploration())) {
          lds_search(label, si.ldsValue);
          heuristicSeqSearch = true;
        }
        // Credit heuristic search
        if ("credit".equals(si.exploration())) {
          credit_search(label, si.creditValue, si.bbsValue);
          heuristicSeqSearch = true;
        }

        list_seq_searches.add(label);
        label.setPrintInfo(false);
      }
      case "priority_search" -> {
        label = priority_search(si);

        list_seq_searches.add(label);
      }
      case "warm_start" -> {
        label = warm_start_search(si);
        if (!master) {
          label.setSelectChoicePoint(variable_selection);
        }
      }
      case "seq_search" -> {
        for (int i = 0; i < si.getSearchItems().size(); i++) {
          if (i == 0) { // master search
            DepthFirstSearch<T> label_seq =
                sub_search(si.getSearchItems().get(i), last_search, false);
            last_search = getLastSearch(label_seq);
            label = label_seq;
          } else {
            DepthFirstSearch<T> label_seq =
                sub_search(si.getSearchItems().get(i), last_search, false);
            last_search.addChildSearch(label_seq);
            last_search = getLastSearch(label_seq);
          }
        }
      }
      case "float_search" -> {
        label = float_search(si);
        if (!master) {
          label.setSelectChoicePoint(variable_selection);
        }

        // Lds heuristic search
        if ("lds".equals(si.exploration())) {
          lds_search(label, si.ldsValue);
          heuristicSeqSearch = true;
        }
        // Credit heuristic search
        if ("credit".equals(si.exploration())) {
          credit_search(label, si.creditValue, si.bbsValue);
          heuristicSeqSearch = true;
        }
        list_seq_searches.add(label);
        label.setPrintInfo(false);
      }
      default -> {
        DepthFirstSearch<T>[] ls = setSubSearchForAll(null, options);

        if (ls[0] != null) {
          label = ls[0];
        } else if (ls[1] != null) {
          label = ls[1];
        } else if (ls[2] != null) {
          label = ls[2];
        } else if (ls[3] != null) {
          label = ls[3];
        }
      }
    }

    return label;
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
  DepthFirstSearch<T> priority_search(SearchItem<T> si) {

    ArrayList<SearchItem<T>> dfs_s = si.getSearchItems();
    DepthFirstSearch<T>[] searches = new DepthFirstSearch[dfs_s.size()];
    int i = 0;
    for (SearchItem<T> s : dfs_s) {

      DepthFirstSearch<T> subSearch;
      switch (s.search_type) {
        case "int_search", "bool_search" -> {
          subSearch = int_search(s);
          subSearch.setSelectChoicePoint(variable_selection);
          subSearch.setPrintInfo(false);
          searches[i++] = subSearch;
        }
        case "set_search" -> {
          subSearch = set_search(s);
          subSearch.setSelectChoicePoint(variable_selection);
          subSearch.setPrintInfo(false);
          searches[i++] = subSearch;
        }
        case "float_search" -> {
          subSearch = float_search(s);
          subSearch.setSelectChoicePoint(variable_selection);
          subSearch.setPrintInfo(false);
          searches[i++] = subSearch;
        }
        case "seq_search" -> {
          subSearch = sub_search(s, null, false);

          DepthFirstSearch<T> ns = subSearch;
          do {
            ns.setPrintInfo(false);
            // find next search
            if (ns.childSearches == null) {
              ns = null;
            } else {
              ns = (DepthFirstSearch) ns.childSearches[0];
            }
          } while (ns != null);

          searches[i++] = subSearch;
        }
        case "priority_search" -> {
          subSearch = priority_search(s);
          subSearch.setPrintInfo(false);
          searches[i++] = subSearch;
        }
        default ->
            throw new RuntimeException(
                "Error: Not supported search type "
                    + s.search_type
                    + "in priority_search; execution aborted");
      }
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
  void printSolution() {

    StringBuffer printBuffer = new StringBuffer();
    numberSolutions++;

    if (!dictionary.outputVariables.isEmpty()) {
      for (int i = 0; i < dictionary.outputVariables.size(); i++) {
        Var v = dictionary.outputVariables.get(i);

        if (v instanceof BooleanVar var1) {
          // print boolean variables
          printBuffer.append(v.id()).append(" = ");
          if (v.singleton()) {
            switch (var1.value()) {
              case 0:
                printBuffer.append("false");
                break;
              case 1:
                printBuffer.append("true");
                break;
              default:
                printBuffer.append(v.dom());
            }
          } else {
            printBuffer.append("false..true");
          }

          printBuffer.append(";\n");
        } else if (v instanceof SetVar setVar) {
          // print set variables
          printBuffer.append(v.id()).append(" = ");
          if (v.singleton()) {
            IntDomain glb = setVar.dom().glb();
            if (glb.getSize() > 0 && glb.getSize() == glb.max() - glb.min() + 1) {
              printBuffer.append(glb.min()).append("..").append(glb.max());
            } else {
              printBuffer.append("{");
              for (ValueEnumeration e = glb.valueEnumeration(); e.hasMoreElements(); ) {
                int element = e.nextElement();
                printBuffer.append(element);
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
            printBuffer.append("%%%mzn-stat: objective=").append(var1.value()).append("\n");
          } else if (costVariable instanceof FloatVar fv) {
            printBuffer.append("%%%mzn-stat: objective=").append(fv.value()).append("\n");
          }
        } else {
          if (costVariable instanceof IntVar var1) {
            printBuffer.append("%%%mzn-stat: objective=").append(-var1.value()).append("\n");
          } else if (costVariable instanceof FloatVar fv) {
            printBuffer.append("%%%mzn-stat: objective=").append(-fv.value()).append("\n");
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
      case "satisfy" ->
          // 0 = satisfy
          0;
      case "minimize" ->
          // 1 = minimize
          1;
      case "maximize" ->
          // 2 = maximize
          2;
      default ->
          throw new IllegalArgumentException("Not supported search kind; compilation aborted");
    };
  }

  IntVar getCost(ASTSolveExpr node) {

    if (node.getType() == 0) { // ident
      IntVar cost = dictionary.getVariable(node.getIdent());
      if (cost != null) {
        return cost;
      } else { // cost is constant ?
        Integer costInt = dictionary.checkInt(node.getIdent());
        if (costInt != null) {
          return new IntVar(store, costInt, costInt);
        } else {
          return null;
        }
      }
    } else if (node.getType() == 1) { // array access
      IntVar[] a = dictionary.getVariableArray(node.getIdent());
      if (a != null) {
        return a[node.getIndex()];
      } else { // cost is constant ?
        int[] costInt = dictionary.getIntArray(node.getIdent());
        if (costInt != null) {
          return new IntVar(store, costInt[node.getIndex()], costInt[node.getIndex()]);
        } else {
          return null;
        }
      }
    } else {
      throw new IllegalArgumentException("Wrong cost function specification " + node);
    }
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
