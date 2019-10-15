/*
 * Solve.java
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
package org.jacop.fz;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.XplusYeqC;
import org.jacop.core.*;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.satwrapper.SatTranslation;
import org.jacop.search.*;
import org.jacop.search.restart.*;
import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMin;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.nio.charset.Charset;

/**
 * The parser part responsible for parsing the solve part of the flatzinc file,
 * building a related search and executing it.
 * <p>
 * Current implementation runs also final search on all variables to ensure
 * that they are ground.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.6
 */
public class Solve implements ParserTreeConstants {

    Tables dictionary;
    Options options;
    Store store;
    int initNumberConstraints;

    Timer timer;
    long startCPU;
    long initTime=0;
    long searchTime=0;
    
    //ComparatorVariable tieBreaking=null;
    SelectChoicePoint<Var> variable_selection;
    ArrayList<Search<Var>> list_seq_searches = null;

    boolean debug = false;
    boolean print_search_info = false;
    boolean heuristicSeqSearch = false;

    Var costVariable;

    // restart search
    Calculator restartCalculator;
    RestartSearch<Var> rs;
    
    // -------- for print-out of statistics
    boolean singleSearch;
    boolean Result;
    boolean optimization;
    boolean minimize = false;
    SearchItem si;

    // single search
    boolean defaultSearch;
    DepthFirstSearch<Var> label;
    DepthFirstSearch<Var>[] final_search;

    // sequence search 
    Search<Var> final_search_seq;
    // --------

    // Values for search created from flatzinc
    DepthFirstSearch<Var> flatzincDFS;
    SelectChoicePoint<Var> flatzincVariableSelection;
    Var flatzincCost;

    int solveKind = -1;

    SatTranslation sat;

    public StringBuffer lastSolution = null;

    FailConstraintsStatistics failStatistics;

    /**
     * It creates a parser for the solve part of the flatzinc file.
     *
     * @param store the constraint store within which context the search will take place.
     * @param sat   sat translation used
     */
    public Solve(Store store, SatTranslation sat) {
        this.store = store;
        this.sat = sat;

    }

    public void solveModel(SimpleNode astTree, Tables table, Options opt) {

        dictionary = table;

        int n = astTree.jjtGetNumChildren();

        for (int i = 0; i < n; i++) {
            SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);

            if (node.getId() == JJTMODELEND) {
                // int k = node.jjtGetNumChildren();
                search((ASTSolveItem) node.jjtGetChild(0), table, opt);
            }
        }
    }

    /**
     * It parses the solve part.
     *
     * @param node  the current parsing node.
     * @param table the table containing all the various variable definitions encoutered thus far.
     * @param opt   option specifies to flatzinc parser in respect to search (e.g. all solutions).
     */
    public void search(ASTSolveItem node, Tables table, Options opt) {

        if (opt.debug())
            failStatistics = new FailConstraintsStatistics(store);

	store.setDecay(opt.getDecay());

        // 	System.out.println(table);

        initNumberConstraints = store.numberConstraints();

        //Get runtime system
        Runtime runtime = Runtime.getRuntime();
        long modelMem = (runtime.totalMemory() - runtime.freeMemory()) / (1024 * 1024);

        dictionary = table;

        if (opt.getVerbose())
            System.out.println("%% Model constraints defined.\n%% Variables = " + store.size()
			       + " and  Bool variables = " + dictionary.getNumberBoolVariables()
			       + " of that constant variables = " + table.constantTable.size()
			       + "\n%% Constraints = " + (initNumberConstraints-1)
			       + ", SAT clauses = " + sat.numberClauses() + "\n%% Memory used by the model = " + modelMem + "[MB]");

        options = opt;
        solveKind = -1;

        // node.dump("");

        ASTSolveKind kind;
        int count = node.jjtGetNumChildren();

        // 	System.out.println("Number constraints = "+store.numberConstraints());
        // 	System.out.println("Number  of variables = "+store.size());

        if (count == 1) {// only solve kind => default search

            kind = (ASTSolveKind) node.jjtGetChild(0);
            solveKind = getKind(kind.getKind());
            run_single_search(solveKind, kind, null);
        } else if (count == 2) {// single annotation

            SearchItem si = new SearchItem(store, dictionary);
            si.searchParameters(node, 0);
            // System.out.println("1. *** "+si);
            String search_type = si.type();

            if (search_type.equals("int_search") || search_type.equals("set_search") || search_type.equals("bool_search")) {

                kind = (ASTSolveKind) node.jjtGetChild(1);
                solveKind = getKind(kind.getKind());

                run_single_search(solveKind, kind, si);
            } else if (search_type.equals("float_search")) {

                kind = (ASTSolveKind) node.jjtGetChild(1);
                solveKind = getKind(kind.getKind());

                run_single_search(solveKind, kind, si);
            } else if (search_type.equals("seq_search")) {

                kind = (ASTSolveKind) node.jjtGetChild(1);
                solveKind = getKind(kind.getKind());

                run_sequence_search(solveKind, kind, si);
            } else if (search_type.equals("priority_search")) {
		
                kind = (ASTSolveKind) node.jjtGetChild(1);
                solveKind = getKind(kind.getKind());

                run_single_search(solveKind, kind, si);
            } else {
                throw new IllegalArgumentException(
                    "Not recognized structure of solve statement \"" + search_type + "\"; compilation aborted");
            }
        } else if (count > 2) {// several annotations

            SearchItem si = new SearchItem(store, dictionary);
            si.searchParametersForSeveralAnnotations(node, 0);

	    ArrayList<SearchItem> nsi = parseSearchAnnotations(si.search_seq);

	    if (nsi.size() == 1) { // single search (int, set, float, seq or priority) + other annotations (restart_*)
		SearchItem fs = nsi.get(0);

		kind = (ASTSolveKind) node.jjtGetChild(si.search_seqSize());
		solveKind = getKind(kind.getKind());

		if (fs.type().equals("seq_search"))
		    run_sequence_search(solveKind, kind, fs);
		else
		    run_single_search(solveKind, kind, fs);
	    }
	    else {
		kind = (ASTSolveKind) node.jjtGetChild(si.search_seqSize());
		solveKind = getKind(kind.getKind());

		run_sequence_search(solveKind, kind, si);
	    }
        } else {
            throw new IllegalArgumentException("Not recognized structure of solve statement; compilation aborted");
        }
    }

    ArrayList<SearchItem> parseSearchAnnotations(ArrayList<SearchItem> search_seq) {
	ArrayList<SearchItem> ns = new ArrayList<SearchItem>();

	for (SearchItem s : search_seq) 
	    if (s.search_type.equals("restart_none"))
		continue;
	    else if (s.search_type.equals("restart_constant") || s.search_type.equals("restart_linear") || s.search_type.equals("restart_geometric") ||
		     s.search_type.equals("restart_luby"))
		restartCalculator = s.restartCalculator;
	    else if (s.search_type.endsWith("_search"))// && !s.search_type.equals("priority_search"))
		ns.add(s);
	    else
		System.out.println("%% Warning: Not supported search annotation: "+s.search_type+"; ignored.");

	return ns;
    }
    
    void run_single_search(int solveKind, SimpleNode kind, SearchItem si) {

        singleSearch = true;

        defaultSearch = false;

        this.si = si;

        if (options.getVerbose()) {
            String solve = "notKnown";
            switch (solveKind) {
                case 0:
                    solve = "%% satisfy";
                    break; // satisfy
                case 1:
                    Var costMin = (getCost((ASTSolveExpr) kind.jjtGetChild(0)) != null) ?
                        getCost((ASTSolveExpr) kind.jjtGetChild(0)) :
                        getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
                    solve = "%% minimize(" + costMin + ") ";
		    minimize = true;
                    break; // minimize
                case 2:
                    Var costMax = (getCost((ASTSolveExpr) kind.jjtGetChild(0)) != null) ?
                        getCost((ASTSolveExpr) kind.jjtGetChild(0)) :
                        getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
                    solve = "%% maximize(" + costMax + ") ";
                    break; // maximize
                default:
                    throw new RuntimeException("Internal error in " + getClass().getName());
            }
            System.out.println(solve + " : " + si);
        }

        Var cost = null;
        Var max_cost = null;

        label = null;
        optimization = false;
        list_seq_searches = new ArrayList<Search<Var>>();

        label = null;
        if (si != null) {
            if (si.type().equals("int_search")) {
                label = int_search(si);
                list_seq_searches.add(label);
                //label.setSolutionListener(new EmptyListener<Var>());
                label.setPrintInfo(false);

                // time-out option
                int to = options.getTimeOut();
                if (to > 0)
                    label.setTimeOutMilliseconds(to);
            } else if (si.type().equals("bool_search")) {
                label = int_search(si);
                list_seq_searches.add(label);
                //label.setSolutionListener(new EmptyListener<Var>());
                label.setPrintInfo(false);

                // time-out option
                int to = options.getTimeOut();
                if (to > 0)
                    label.setTimeOutMilliseconds(to);
            } else if (si.type().equals("set_search")) {
                label = set_search(si);
                list_seq_searches.add(label);
                //label.setSolutionListener(new EmptyListener<Var>());
                label.setPrintInfo(false);

                // time-out option
                int to = options.getTimeOut();
                if (to > 0)
                    label.setTimeOutMilliseconds(to);
            } else if (si.type().equals("float_search")) {
                label = float_search(si);
                list_seq_searches.add(label);
                //label.setSolutionListener(new EmptyListener<Var>());
                label.setPrintInfo(false);

                // time-out option
                int to = options.getTimeOut();
                if (to > 0)
                    label.setTimeOutMilliseconds(to);
	    } else if (si.type().equals("priority_search")) {
                label = priority_search(si);
                list_seq_searches.add(label);
                label.setPrintInfo(false);

                // time-out option
                int to = options.getTimeOut();
                if (to > 0)
                    label.setTimeOutMilliseconds(to);
            } else {
                throw new IllegalArgumentException("Not recognized or supported search type \"" + si.type() + "\"; compilation aborted");
            }
        }

        if (solveKind > 0) {
            optimization = true;

            cost = getCost((ASTSolveExpr) kind.jjtGetChild(0));
            if (cost != null)
                if (solveKind == 1)  // minimize
                    costVariable = cost;
                else { // maximize
                    max_cost = new IntVar(store, "-" + cost.id(), -((IntVar) cost).max(),
                        -((IntVar) cost).min());//IntDomain.MinInt, IntDomain.MaxInt);
                    pose(new XplusYeqC((IntVar) max_cost, (IntVar) cost, 0));
                    costVariable = max_cost;
                }
            else {
                cost = getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
                if (solveKind == 1)  // minimize
                    costVariable = cost;
                else { // maximize
                    max_cost = new FloatVar(store, "-" + cost.id(), -((FloatVar) cost).max(),
                        -((FloatVar) cost).min());//VariablesParameters.MIN_FLOAT, VariablesParameters.MAX_FLOAT);
                    pose(new PplusQeqR((FloatVar) max_cost, (FloatVar) cost, new FloatVar(store, 0.0, 0.0)));
                    costVariable = max_cost;
                }

            }
        }

        // adds child search for cost; to be sure that all variables get a value
        final_search = setSubSearchForAll(label, options);
        Search last_search;

        if (si == null) {
            defaultSearch = true;
            si = new SearchItem(store, dictionary);
            si.explore = "complete";
            if (final_search[0] != null) {
                label = final_search[0];
                list_seq_searches.add(label);
                for (int i = 1; i < final_search.length; i++)
                    if (final_search[i] != null)
                        list_seq_searches.add(final_search[i]);
            } else if (final_search[1] != null) {
                label = final_search[1];
                list_seq_searches.add(label);
                if (final_search[2] != null)
                    list_seq_searches.add(final_search[2]);

            } else if (final_search[2] != null) {
                label = final_search[2];
                list_seq_searches.add(label);
                if (final_search[3] != null)
                    list_seq_searches.add(final_search[3]);
            } else if (final_search[3] != null) {
                label = final_search[3];
                list_seq_searches.add(label);
            }
        } else {
            for (DepthFirstSearch<Var> s : final_search)
                if (s != null)
                    list_seq_searches.add(s);
        }
        last_search = list_seq_searches.get(list_seq_searches.size() - 1);

        // LDS & Credit heuristic search
        if (si.exploration().equals("lds"))
            lds_search(label, si.ldsValue);
            // Credit heuristic search
        else if (si.exploration().equals("credit"))
            credit_search(label, si.creditValue, si.bbsValue);

        Result = false;

	long currentTime = timer.getCPUTime();
	initTime = currentTime - startCPU;
        startCPU = currentTime;

        if (si == null || si.exploration() == null || si.exploration().equals("complete") || si.exploration().equals("lds") || si
            .exploration().equals("credit"))
            switch (solveKind) {
                case 0: // satisfy

                    FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

                    if (options.getAll()) { // all solutions
			if (restartCalculator != null)
			    throw new IllegalArgumentException("Flatzinc option for search for all solutions (-a) cannot be used in restart search.");

                        label.getSolutionListener().searchAll(true);
                        label.getSolutionListener().recordSolutions(false);

                        // =====> add "search for all" flag to all sub-searches, 2012-03-19
                        java.util.LinkedHashSet<Search<? extends Var>> l = new java.util.LinkedHashSet<Search<? extends Var>>();
                        l.add(label);
                        while (l.size() != 0) {
                            java.util.LinkedHashSet<Search<? extends Var>> ns = new java.util.LinkedHashSet<Search<? extends Var>>();
                            for (Search s1 : l) {
                                Search<? extends Var>[] child = (Search<? extends Var>[]) ((DepthFirstSearch) s1).childSearches;
                                if (child != null)
                                    for (Search<? extends Var> s : child) {
                                        ns.add(s);

                                        s.getSolutionListener().searchAll(true);
                                        s.getSolutionListener().recordSolutions(false);

                                    }
                            }
                            l = ns;
                        }
                        // <=====
                        if (options.getNumberSolutions() > 0)
                            last_search.getSolutionListener().setSolutionLimit(options.getNumberSolutions());

                    }

                    // printSearch(label);

                    this.si = si;

                    if (options.runSearch())
			if (restartCalculator != null) {
			    if (options.debug()) {
				System.out.print("% RestartSearch(" + restartCalculator + "), ");
				label.setSelectChoicePoint(variable_selection);
				System.out.print(" satisfy ");
				printSearch(label);
			    }

			    rs = new RestartSearch<>(store, label, variable_selection, restartCalculator);
			    int to = options.getTimeOut();
			    if (to > 0)
				rs.setTimeOutMilliseconds(to);
			    Result = rs.labeling();
			}
			else {
			    if (options.debug()) {
				label.setSelectChoicePoint(variable_selection);
				System.out.print("% satisfy ");
				printSearch(label);
			    }

			    Result = label.labeling(store, variable_selection);
			}
                    else {
                        // storing flatiznc defined search
                        flatzincDFS = label;
                        flatzincVariableSelection = variable_selection;
                        flatzincCost = null;
                        return;
                    }

                    break;
                case 1: // minimize

                    FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

                    if (options.getNumberSolutions() > 0) {
                        for (Search<Var> list_seq_searche : list_seq_searches)
                            ((DepthFirstSearch) list_seq_searche).respectSolutionListenerAdvice = true;
                        last_search.getSolutionListener().setSolutionLimit(options.getNumberSolutions());
                    }

                    this.si = si;

                    if (options.runSearch())
			if (restartCalculator != null) {
			    if (options.debug()) {
				System.out.print("% RestartSearch(" + restartCalculator + "), ");
				label.setSelectChoicePoint(variable_selection);
				System.out.print(" minimize (" + cost +") ");
				printSearch(label);
			    }

			    rs = new RestartSearch<>(store, label, variable_selection, restartCalculator, cost);
			    int to = options.getTimeOut();
			    if (to > 0)
				rs.setTimeOutMilliseconds(to);
			    Result = rs.labeling();
			}
			else {
			    if (options.debug()) {
				label.setSelectChoicePoint(variable_selection);
				System.out.print("% minimize (" + cost +") ");
				printSearch(label);
			    }
			    Result = label.labeling(store, variable_selection, cost);
			}
                    else {
                        // storing flatiznc defined search
                        flatzincDFS = label;
                        flatzincVariableSelection = variable_selection;
                        flatzincCost = cost;
                        return;
                    }

                    // last_search.setSolutionListener(new ResultListener(si.vars()));
                    // org.jacop.floats.search.Optimize opt = new org.jacop.floats.search.Optimize(store, label, variable_selection, (FloatVar)cost);
                    // Result = opt.minimize();

                    break;
                case 2: //maximize

                    FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

                    if (options.getNumberSolutions() > 0) {
                        for (Search<Var> list_seq_searche : list_seq_searches)
                            ((DepthFirstSearch) list_seq_searche).respectSolutionListenerAdvice = true;
                        last_search.getSolutionListener().setSolutionLimit(options.getNumberSolutions());
                    }

                    this.si = si;

                    if (options.runSearch())
			if (restartCalculator != null) {
			    if (options.debug()) {
				System.out.print("% RestartSearch(" + restartCalculator + "), ");
				label.setSelectChoicePoint(variable_selection);
				System.out.print("% maximize (" + cost +") ");
				printSearch(label);
			    }

			    rs = new RestartSearch<>(store, label, variable_selection, restartCalculator, max_cost);
			    int to = options.getTimeOut();
			    if (to > 0)
				rs.setTimeOutMilliseconds(to);
			    Result = rs.labeling();
			}
			else {
			    if (options.debug()) {
				label.setSelectChoicePoint(variable_selection);
				System.out.print("% maximize (" + cost +") ");
				printSearch(label);
			    }

			    Result = label.labeling(store, variable_selection, max_cost);
			}
                    else {
                        // storing flatiznc defined search
                        flatzincDFS = label;
                        flatzincVariableSelection = variable_selection;
                        flatzincCost = max_cost;
                        return;
                    }

                    break;
            }
        else {
            throw new IllegalArgumentException(
                "Not recognized or supported " + si.exploration() + " search explorarion strategy ; compilation aborted");
        }

        if (!options.getAll() && lastSolution != null)
            helperSolutionPrinter(lastSolution.toString());

        printStatisticsForSingleSearch(false, Result);

    }

    public void statistics(boolean result) {

        printStatistics(false, result);
    }

    public void printStatisticsIterrupt() {
        printStatistics(true, Result);
    }

    public void printStatistics(boolean interrupted, boolean result) {

        if (singleSearch)
            printStatisticsForSingleSearch(interrupted, result);
        else
            printStatisticsForSeqSearch(interrupted, result);
    }

    void printStatisticsForSingleSearch(boolean interrupted, boolean result) {

        if (label == null) {
            System.out.println("%% =====INTERRUPTED=====\n%% Model not yet posed..");
            return;
        }

        if (result) {
            if (!optimization && options.getAll()) {
                if (!interrupted)
                    if (si.exploration().equals("complete"))
                        if (!label.timeOutOccured) {
			    if (si.type() != null && si.type().equals("priority_search")) {
				if (options.getNumberSolutions() == -1 || options.getNumberSolutions() > ((PrioritySearch)label).noSolutions())
				    System.out.println("==========");
			    } else {// no priority_search
				if (options.getNumberSolutions() == -1 || options.getNumberSolutions() > label.getSolutionListener()
				    .solutionsNo())
				    System.out.println("==========");
			    }
                        } else
                            System.out.println("%% =====TIME-OUT=====");
                    else if (label.timeOutOccured)
                        System.out.println("%% =====TIME-OUT=====");
            } else if (optimization) {
                if (!interrupted && si.exploration().equals("complete"))
                    if (!label.timeOutOccured) {
			if (si.type() != null && si.type().equals("priority_search")) {
			    if (options.getNumberSolutions() == -1 || options.getNumberSolutions() > ((PrioritySearch)label).noSolutions())
				System.out.println("==========");
			} else {// no priority_search
			    if (options.getNumberSolutions() == -1 || options.getNumberSolutions() > label.getSolutionListener().solutionsNo())
				System.out.println("==========");
			}
                    } else
                        System.out.println("%% =====TIME-OUT=====");
                else if (label.timeOutOccured)
                    System.out.println("%% =====TIME-OUT=====");
            }
        } else if (label.timeOutOccured) {
            System.out.println("=====UNKNOWN=====");
            System.out.println("%% =====TIME-OUT=====");
        } else if (interrupted)
            System.out.println("%% =====INTERRUPTED=====");
        else if (si.exploration().equals("complete")) {
            System.out.println("=====UNSATISFIABLE=====");
            if (!options.getOutputFilename().equals("")) {
                String st = "=====UNSATISFIABLE=====";
                try {
                    Files.write(Paths.get(options.getOutputFilename()), st.getBytes(Charset.forName("UTF-8")));
                } catch (IOException e1) {
                    e1.printStackTrace();
                }
            }
        } else
            System.out.println("=====UNKNOWN=====");

        if (options.getStatistics()) {

	    // if (si.type() != null && si.type().equals("priority_search"))
	    // 	((PrioritySearch)label).getStatistics();

            int nodes = 0, //label.getNodes(),
                decisions = 0, //label.getDecisions(),
                wrong = 0, //label.getWrongDecisions(),
                backtracks = 0, //label.getBacktracks(),
                depth = 0, //label.getMaximumDepth(),
                solutions = 0; //label.getSolutionListener().solutionsNo();

            if (!defaultSearch) {
                nodes = label.getNodes();
                decisions = label.getDecisions();
                wrong = label.getWrongDecisions();
                backtracks = label.getBacktracks();
                depth = label.getMaximumDepth();
                solutions = label.getSolutionListener().solutionsNo();
            }

            for (DepthFirstSearch<Var> l : final_search) {
                if (l != null) {
                    nodes += l.getNodes();
                    decisions += l.getDecisions();
                    wrong += l.getWrongDecisions();
                    backtracks += l.getBacktracks();
                    depth += l.getMaximumDepth();
                    solutions = (l != null && l instanceof PrioritySearch) ? solutions : l.getSolutionListener().solutionsNo();
                }
            }

	    int restarts = (rs != null) ? rs.restarts() : 0;
	    
            System.out.println("%%%mzn-stat: variables=" + (store.size() + dictionary.getNumberBoolVariables() - dictionary.constantTable.size())
			       // + "\n%%%mzn-stat: boolVariables="+ (dictionary.getNumberBoolVariables()-dictionary.aliasTable.size())
			       // + "\n%%%mzn-stat: setVariables="+ dictionary.getNumberSetVariables()
			       // + "\n%%%mzn-stat: floatVariables="+ dictionary.getNumberFloatVariables()
			       + "\n%%%mzn-stat: propagators=" + (initNumberConstraints - 1)
			       + "\n\n%%%mzn-stat: initTime=" + getInitTime_ms()/1000.0
			       + "\n%%%mzn-stat: solveTime=" + getSearchTime_ms()/1000.0
			       + "\n%%%mzn-stat: nodes=" + String.format("%,d", nodes)
			       + "\n%%%mzn-stat: restarts=" + String.format("%,d", restarts)
			       + "\n%%%mzn-stat: propagations=" + String.format("%,d", store.numberConsistencyCalls)
			       // + "\n%% Search decisions : "+ String.format("%,d", decisions)
			       + "\n%%%mzn-stat: failers=" + String.format("%,d", wrong) //Wrong search decisions : 
			       // + "\n%%%mzn-stat: backtracks=" + String.format("%,d", backtracks)
			       + "\n%%%mzn-stat; peakDepth=" + depth
			       + "\n%%%mzn-stat: solutions=" + solutions
			       + "\n%%%mzn-stat-end"
			       );

            if (options.debug())
                System.out.print(failStatistics);
        }
    }

    @SuppressWarnings("unchecked") DepthFirstSearch<Var>[] setSubSearchForAll(DepthFirstSearch<Var> label, Options opt) {

        DepthFirstSearch<Var>[] intAndSetSearch = new DepthFirstSearch[4];

        DefaultSearchVars searchVars = new DefaultSearchVars(dictionary);

        if (!options.complementarySearch() && label != null) {
            // ==== Collect ALL OUTPUT variables ====
            searchVars.outputVars();
        }

        Var[] int_search_variables = searchVars.getIntVars();
        Var[] set_search_variables = searchVars.getSetVars();
        Var[] bool_search_variables = searchVars.getBoolVars();
        FloatVar[] float_search_variables = searchVars.getFloatVars();

        // if there are no output variables collect GUESSED SEARCH
        // VARIABLES override selection if option
        // "complementarySearch" or no search is defined is defined.
        if (int_search_variables.length == 0 && bool_search_variables.length == 0 && set_search_variables.length == 0
            && float_search_variables.length == 0 || options.complementarySearch()) {

            searchVars.defaultVars();

            int_search_variables = searchVars.getIntVars();
            set_search_variables = searchVars.getSetVars();
            bool_search_variables = searchVars.getBoolVars();
            float_search_variables = searchVars.getFloatVars();
        }

        if (opt.getVerbose()) {
            System.out.println(searchVars);
            // System.out.println ("cost = " + costVariable);
        }

        DepthFirstSearch<Var> lastSearch = label;
        DepthFirstSearch<Var> intSearch = new DepthFirstSearch<Var>();

        if (set_search_variables.length != 0) {
            // add set search containing all variables to be sure that they get a value
            DepthFirstSearch<Var> setSearch = new DepthFirstSearch<Var>();

            if (opt.debug())
                setSearch.setConsistencyListener(failStatistics);

            SelectChoicePoint<Var> setSelect = new SimpleSelect<Var>(set_search_variables, null,
                // 								     new org.jacop.search.MostConstrainedStatic<Var>(),
                new IndomainSetMin());
            if (variable_selection == null)
                variable_selection = setSelect;
            setSearch.setSelectChoicePoint(setSelect);
            setSearch.setPrintInfo(false);
            if (lastSearch != null)
                lastSearch.addChildSearch(setSearch);
            lastSearch = setSearch;
            if (int_search_variables.length == 0 && bool_search_variables.length == 0 && float_search_variables.length == 0)
                setSearch.setSolutionListener(new CostListener<Var>());

            if (costVariable != null) {
                intSearch.setCostVar(costVariable);
                intSearch.setOptimize(true);
            }

            // time-out option
            int to = options.getTimeOut();
            if (to > 0)
                setSearch.setTimeOutMilliseconds(to);

            intAndSetSearch[0] = setSearch;
        }

        if (opt.debug())
            intSearch.setConsistencyListener(failStatistics);

        if (int_search_variables.length != 0) {
            // add search containing int variables to be sure that they get a value
            SelectChoicePoint<Var> intSelect = new SimpleSelect<Var>(int_search_variables, null,
								     // new org.jacop.search.MostConstrainedDynamic<Var>(),
								     // new org.jacop.search.SmallestDomain<Var>(),
                new IndomainMin());
            if (variable_selection == null)
                variable_selection = intSelect;
            intSearch.setSelectChoicePoint(intSelect);
            intSearch.setPrintInfo(false);
            if (lastSearch != null)
                lastSearch.addChildSearch(intSearch);
            lastSearch = intSearch;
            if (bool_search_variables.length == 0 && float_search_variables.length == 0) {
                intSearch.setSolutionListener(new CostListener<Var>());

                if (costVariable != null) {
                    intSearch.setCostVar(costVariable);
                    intSearch.setOptimize(true);
                }
            }

            // time-out option
            int to = options.getTimeOut();
            if (to > 0)
                intSearch.setTimeOutMilliseconds(to);

            intAndSetSearch[1] = intSearch;

        }

        DepthFirstSearch<Var> boolSearch = new DepthFirstSearch<Var>();

        if (opt.debug())
            boolSearch.setConsistencyListener(failStatistics);

        if (bool_search_variables.length != 0) {
            // add search containing boolean variables to be sure that they get a value
            SelectChoicePoint<Var> boolSelect = new SimpleSelect<Var>(bool_search_variables, null,
                 								      // new org.jacop.search.MostConstrainedDynamic<Var>(),
                new IndomainMin());
            if (variable_selection == null)
                variable_selection = boolSelect;
            boolSearch.setSelectChoicePoint(boolSelect);
            boolSearch.setPrintInfo(false);
            if (lastSearch != null)
                lastSearch.addChildSearch(boolSearch);
            lastSearch = boolSearch;
            if (float_search_variables.length == 0) {
                boolSearch.setSolutionListener(new CostListener<Var>());

                if (costVariable != null) {
                    intSearch.setCostVar(costVariable);
                    intSearch.setOptimize(true);
                }
            }

            // time-out option
            int to = options.getTimeOut();
            if (to > 0)
                boolSearch.setTimeOutMilliseconds(to);

            intAndSetSearch[2] = boolSearch;
        }


        if (float_search_variables.length != 0) {
            // add float search containing all variables to be sure that they get a value
            DepthFirstSearch<Var> floatSearch = new DepthFirstSearch<Var>();

            if (opt.debug())
                floatSearch.setConsistencyListener(failStatistics);

            SelectChoicePoint<Var> floatSelect = new SplitSelectFloat<Var>(store, float_search_variables, null);

            if (variable_selection == null)
                variable_selection = floatSelect;
            floatSearch.setSelectChoicePoint(floatSelect);
            floatSearch.setPrintInfo(false);
            if (lastSearch != null)
                lastSearch.addChildSearch(floatSearch);
            floatSearch.setSolutionListener(new CostListener<Var>());

            if (costVariable != null) {
                intSearch.setCostVar(costVariable);
                intSearch.setOptimize(true);
            }

            // time-out option
            int to = options.getTimeOut();
            if (to > 0)
                floatSearch.setTimeOutMilliseconds(to);

            intAndSetSearch[3] = floatSearch;
        }

        if (int_search_variables.length == 0 && bool_search_variables.length == 0 && set_search_variables.length == 0
            && float_search_variables.length == 0) {

            printSolution();

            if (lastSolution != null)
                helperSolutionPrinter(lastSolution.toString());

	    if (options.getAll())
		System.out.println("==========");

            if (options.getStatistics()) {
                System.out.println(
				   "%%%mzn-stat: variables=" + (store.size() + dictionary.getNumberBoolVariables() - dictionary.constantTable.size())
				   // + "\n%%%mzn-stat: boolVariables="+ (dictionary.getNumberBoolVariables()-dictionary.aliasTable.size())
				   // + "\n%%%mzn-stat: setVariables="+ dictionary.getNumberSetVariables()
				   // + "\n%%%mzn-stat: floatVariables="+ dictionary.getNumberFloatVariables()
				   + "\n%%%mzn-stat: propagators=" + initNumberConstraints
				   + "\n\n%%%mzn-stat: initTime=" + getInitTime_ms()/1000.0
				   + "\n%%%mzn-stat: solveTime=" + "0"
				   + "\n%%%mzn-stat: nodes=0"
				   + "\n%%man-stat: propagations="+ store.numberConsistencyCalls
				   + "\n%%%mzn-stat: nodes=0"
				   + "\n%%%mzn-stat: restarts=0"
				   + "\n%%%mzn-stat: failers=0"
				   // + "\n%%%mzn-stat: backtracks=0"
				   + "\n%%%mzn-stat: peakDepth=0"
				   + "\n%%%mzn-stat: solutions=1"
				   + "\n%%%mzn-stat-end");

	    }
	    throw new TrivialSolution();
	}

        return intAndSetSearch;
    }	


    void run_sequence_search(int solveKind, SimpleNode kind, SearchItem si) {

        singleSearch = false;
	//kind.dump("");
	
        this.si = si;

        if (options.getVerbose()) {
            String solve = "notKnown";
            switch (solveKind) {
                case 0:
                    solve = "%% satisfy";
                    break; // satisfy
                case 1:
                    Var costMin = (getCost((ASTSolveExpr) kind.jjtGetChild(0)) != null) ?
                        getCost((ASTSolveExpr) kind.jjtGetChild(0)) :
                        getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
                    solve = "%% minimize(" + costMin + ") ";
		    minimize = true;
                    break; // minimize

                case 2:
                    Var costMax = (getCost((ASTSolveExpr) kind.jjtGetChild(0)) != null) ?
                        getCost((ASTSolveExpr) kind.jjtGetChild(0)) :
                        getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
                    solve = "%% maximize(" + costMax + ") ";
                    break; // maximize
                default:
                    throw new RuntimeException("Internal error in " + getClass().getName());
            }
            System.out.println(solve + " : " + si);
        }

        DepthFirstSearch<Var> masterLabel = null;
        DepthFirstSearch<Var> last_search = null;
        SelectChoicePoint<Var> masterSelect = null;
        list_seq_searches = new ArrayList<Search<Var>>();

        for (int i = 0; i < si.getSearchItems().size(); i++) {
            if (i == 0) { // master search
                masterLabel = sub_search(si.getSearchItems().get(i), masterLabel, true);
                last_search = getLastSearch(masterLabel);
                masterSelect = variable_selection;
                if (!print_search_info)
                    masterLabel.setPrintInfo(false);
            } else {
                DepthFirstSearch<Var> label = sub_search(si.getSearchItems().get(i), last_search, false);
                last_search.addChildSearch(label);
                last_search = getLastSearch(label);
                if (!print_search_info)
                    last_search.setPrintInfo(false);
            }
        }

        DepthFirstSearch<Var>[] complementary_search = setSubSearchForAll(last_search, options);
        for (DepthFirstSearch<Var> aComplementary_search : complementary_search) {
            if (aComplementary_search != null) {
                list_seq_searches.add(aComplementary_search);
                if (!print_search_info)
                    aComplementary_search.setPrintInfo(false);
            }
        }

        Result = false;
        Var cost = null;
        Var max_cost = null;
        optimization = false;

        final_search_seq = list_seq_searches.get(list_seq_searches.size() - 1);

	long currentTime = timer.getCPUTime();
	initTime = currentTime - startCPU;
        startCPU = currentTime;

        int to = options.getTimeOut();
        if (to > 0)
            for (Search s : list_seq_searches)
                s.setTimeOutMilliseconds(to);

        int ns = options.getNumberSolutions();
        if (si.exploration() == null || si.exploration().equals("complete"))
            switch (solveKind) {
                case 0: // satisfy

                    FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

                    if (options.getAll()) { // all solutions
			if (restartCalculator != null)
			    throw new IllegalArgumentException("Flatzinc option for search for all solutions (-a) cannot be used in restart search.");

                        for (int i = 0; i < si.getSearchItems().size(); i++) {  //list_seq_searches.size(); i++) {
                            list_seq_searches.get(i).getSolutionListener().searchAll(true);
                            list_seq_searches.get(i).getSolutionListener().recordSolutions(false);
                            if (ns > 0)
                                list_seq_searches.get(i).getSolutionListener().setSolutionLimit(ns);
                        }
                    }

                    if (options.runSearch())
			if (restartCalculator != null) {
			    if (options.debug()) {
				System.out.print("% RestartSearch(" + restartCalculator + "), ");
				label.setSelectChoicePoint(masterSelect);
				System.out.print(" satisfy ");
				printSearch(label);
			    }

			    label = masterLabel;
			    rs = new RestartSearch<>(store, masterLabel, masterSelect, restartCalculator);
			    Result = rs.labeling();
			}
			else {
			    if (options.debug()) {
				masterLabel.setSelectChoicePoint(masterSelect);
				System.out.print("% satisfy ");
				printSearch(masterLabel);
			    }

			    label = masterLabel;
			    Result = masterLabel.labeling(store, masterSelect);
			}
                    else {
                        // storing flatiznc defined search
                        flatzincDFS = masterLabel;
                        flatzincVariableSelection = masterSelect;
                        flatzincCost = null;
                        return;
                    }

                    break;

                case 1: // minimize
                    optimization = true;

                    FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

                    cost = getCost((ASTSolveExpr) kind.jjtGetChild(0));
                    if (cost != null)
                        costVariable = cost;
                    else {
                        cost = getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
                        costVariable = cost;
                   }

                    // Result = restart_search(masterLabel, masterSelect, cost, true);

                    for (Search<Var> list_seq_searche : list_seq_searches)
                        list_seq_searche.setOptimize(true);

                    if (ns > 0) {
                        for (int i = 0; i < list_seq_searches.size() - 1; i++) {
                            ((DepthFirstSearch) list_seq_searches.get(i)).respectSolutionListenerAdvice = true;
			    ((DepthFirstSearch) list_seq_searches.get(i)).getSolutionListener().setSolutionLimit(ns);
			}
			final_search_seq.getSolutionListener().setSolutionLimit(ns);
                        ((DepthFirstSearch) final_search_seq).respectSolutionListenerAdvice = true;
                    }

                    if (options.runSearch())
			if (restartCalculator != null) {
			    if (options.debug()) {
				System.out.print("% RestartSearch(" + restartCalculator + "), ");
				label.setSelectChoicePoint(masterSelect);
				System.out.print(" minimize (" + cost +") ");
				printSearch(label);
			    }

			    label = masterLabel;
			    rs = new RestartSearch<>(store, masterLabel, masterSelect, restartCalculator, cost);
			    Result = rs.labeling();
			}
			else {
			    if (options.debug()) {
				masterLabel.setSelectChoicePoint(masterSelect);
				System.out.print("% minimize (" + cost + ") ");
				printSearch(masterLabel);
			    }

			    label = masterLabel;
			    Result = masterLabel.labeling(store, masterSelect, cost);
			}
                    else {
                        // storing flatiznc defined search
                        flatzincDFS = masterLabel;
                        flatzincVariableSelection = masterSelect;
                        flatzincCost = cost;
                        return;
                    }

                    break;
                case 2: //maximize
                    optimization = true;
                    // cost = getCost((ASTSolveExpr)kind.jjtGetChild(0));

                    FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

                    cost = getCost((ASTSolveExpr) kind.jjtGetChild(0));
                    if (cost != null) { // maximize
                        max_cost = new IntVar(store, "-" + cost.id(), IntDomain.MinInt, IntDomain.MaxInt);
                        pose(new XplusYeqC((IntVar) max_cost, (IntVar) cost, 0));
                        costVariable = max_cost;
                    } else {
                        cost = getCostFloat((ASTSolveExpr) kind.jjtGetChild(0));
                        max_cost = new FloatVar(store, "-" + cost.id(), VariablesParameters.MIN_FLOAT, VariablesParameters.MAX_FLOAT);
                        pose(new PplusQeqR((FloatVar) max_cost, (FloatVar) cost, new FloatVar(store, 0.0, 0.0)));
                        costVariable = max_cost;
                    }

                    // Result = restart_search(masterLabel, masterSelect, cost, false);

                    for (Search<Var> list_seq_searche : list_seq_searches)
                        list_seq_searche.setOptimize(true);

                    if (ns > 0) {
                        for (int i = 0; i < list_seq_searches.size() - 1; i++)
                            ((DepthFirstSearch) list_seq_searches.get(i)).respectSolutionListenerAdvice = true;
                        final_search_seq.getSolutionListener().setSolutionLimit(ns);
                        ((DepthFirstSearch) final_search_seq).respectSolutionListenerAdvice = true;
                    }

                    if (options.runSearch())
			if (restartCalculator != null) {
			    if (options.debug()) {
				System.out.print("% RestartSearch(" + restartCalculator + "), ");
				label.setSelectChoicePoint(masterSelect);
				System.out.print(" maximize (" + cost +") ");
				printSearch(label);
			    }

			    label = masterLabel;
			    rs = new RestartSearch<>(store, masterLabel, masterSelect, restartCalculator, max_cost);
			    Result = rs.labeling();
			}
			else {
			    if (options.debug()) {
				masterLabel.setSelectChoicePoint(masterSelect);
				System.out.print("% maximize (" + cost + ") ");
				printSearch(masterLabel);
			    }

			    label = masterLabel;
			    Result = masterLabel.labeling(store, masterSelect, max_cost);
			}
                    else {
                        // storing flatiznc defined search
                        flatzincDFS = masterLabel;
                        flatzincVariableSelection = masterSelect;
                        flatzincCost = max_cost;
                        return;
                    }

                    break;
            }
        else {
            throw new IllegalArgumentException(
                "Not recognized or supported " + si.exploration() + " search explorarion strategy ; compilation aborted");
        }

        if (!options.getAll() && lastSolution != null)
            helperSolutionPrinter(lastSolution.toString());

        printStatisticsForSeqSearch(false, Result);

    }


    @SuppressWarnings("unchecked") 
    DepthFirstSearch<Var> getLastSearch(DepthFirstSearch<Var> s) {
	DepthFirstSearch<Var> ns = s;
	DepthFirstSearch<Var> lastNotNullSearch = ns;

	do {

	    lastNotNullSearch = ns;

	    // find next search
	    if (ns.childSearches == null)
		ns = null;
	    else
		ns = (DepthFirstSearch<Var>)ns.childSearches[0];
	} while (ns != null);

	return lastNotNullSearch;
    }


    void printStatisticsForSeqSearch(boolean interrupted, boolean result) {

        if (list_seq_searches == null) {
            System.out.println("%% =====INTERRUPTED=====\n%% Model not yet posed..");
            return;
        }

        if (result) {
            if (!optimization && options.getAll()) {
                if (!heuristicSeqSearch)
                    if (!anyTimeOutOccured(list_seq_searches)) {
                        if (options.getNumberSolutions() == -1 || options.getNumberSolutions() > final_search_seq.getSolutionListener()
                            .solutionsNo())
                            System.out.println("==========");
                    } else
                        System.out.println("%% =====TIME-OUT=====");
                else if (anyTimeOutOccured(list_seq_searches))
                    System.out.println("%% =====TIME-OUT=====");
            } else if (optimization) {
                if (!heuristicSeqSearch)
                    if (!anyTimeOutOccured(list_seq_searches)) {
                        if (options.getNumberSolutions() == -1 || options.getNumberSolutions() > final_search_seq.getSolutionListener()
                            .solutionsNo())
                            System.out.println("==========");
                    } else
                        System.out.println("%% =====TIME-OUT=====");
                else if (anyTimeOutOccured(list_seq_searches))
                    System.out.println("%% =====TIME-OUT=====");
            }
        } else if (anyTimeOutOccured(list_seq_searches)) {
            System.out.println("=====UNKNOWN=====");
            System.out.println("%% =====TIME-OUT=====");
        } else if (interrupted)
            System.out.println("%% =====INTERRUPTED=====");
        else
            System.out.println("=====UNSATISFIABLE=====");

        if (options.getStatistics()) {
            int nodes = 0, decisions = 0, wrong = 0, backtracks = 0, depth = 0, solutions = 0;
            for (Search<Var> label : list_seq_searches) {
                nodes += label.getNodes();
                decisions += label.getDecisions();
                wrong += label.getWrongDecisions();
                backtracks += label.getBacktracks();
                depth += label.getMaximumDepth();
                solutions = label.getSolutionListener().solutionsNo();
            }

	    int restarts = (rs != null) ? rs.restarts() : 0;
	    
            System.out.println("%%%mzn-stat: variables=" + (store.size() + dictionary.getNumberBoolVariables() - dictionary.constantTable.size())
			       // + "\n%%%mzn-stat: boolVariables="+ (dictionary.getNumberBoolVariables()-dictionary.aliasTable.size())
			       // + "\n%%%mzn-stat: setVariables="+ dictionary.getNumberSetVariables()
			       // + "\n%%%mzn-stat: floatVariables="+ dictionary.getNumberFloatVariables()
			       + "\n%%%mzn-stat: propagators=" + (initNumberConstraints - 1)
			       + "\n\n%%%mzn-stat: initTime=" + getInitTime_ms()/1000.0
			       + "\n%%%mzn-stat: solveTime=" + getSearchTime_ms()/1000.0
			       + "\n%%%mzn-stat: nodes=" + String.format("%,d", nodes)
			       + "\n%%%mzn-stat: restarts=" + String.format("%,d", restarts)
			       + "\n%%%mzn-stat: propagations=" + String.format("%,d", store.numberConsistencyCalls)
			       // + "\n%% Search decisions : " + String.format("%,d", decisions)
			       + "\n%%%mzn-stat: failers=" + String.format("%,d", wrong) //Wrong search decisions : 
			       // + "\n%%%mzn-stat: backtracks=" + String.format("%,d", backtracks)
			       + "\n%%%mzn-stat: peakDepth=" + depth
			       + "\n%%%mzn-stat: solutions=" + solutions
			       + "\n%%%mzn-stat-end");
        }

        if (options.debug())
            System.out.print(failStatistics);
    }

    double getSearchTime_ms() {
	searchTime = timer.getCPUTime()  - startCPU;
        return searchTime / (long) 1e+6;
    }

    double getInitTime_ms() {
	return initTime / (long) 1e+6;
    }

    boolean anyTimeOutOccured(ArrayList<Search<Var>> list_seq_searches) {

        for (Search<Var> list_seq_searche : list_seq_searches)
            if (((DepthFirstSearch) list_seq_searche).timeOutOccured)
                return true;
        return false;
    }


    DepthFirstSearch<Var> sub_search(SearchItem si, DepthFirstSearch<Var> l, boolean master) {
        DepthFirstSearch<Var> last_search = l;
        DepthFirstSearch<Var> label = null;

        if (si.type().equals("int_search") || si.type().equals("bool_search")) {
            label = int_search(si);
            if (!master)
                label.setSelectChoicePoint(variable_selection);

            // LDS heuristic search
            if (si.exploration().equals("lds")) {
                lds_search(label, si.ldsValue);
                heuristicSeqSearch = true;
            }
            // Credit heuristic search
            if (si.exploration().equals("credit")) {
                credit_search(label, si.creditValue, si.bbsValue);
                heuristicSeqSearch = true;
            }
            list_seq_searches.add(label);
	    label.setPrintInfo(false);
        } else if (si.type().equals("set_search")) {
            label = set_search(si);
            if (!master)
                label.setSelectChoicePoint(variable_selection);

            // LDS heuristic search
            if (si.exploration().equals("lds")) {
                lds_search(label, si.ldsValue);
                heuristicSeqSearch = true;
            }
            // Credit heuristic search
            if (si.exploration().equals("credit")) {
                credit_search(label, si.creditValue, si.bbsValue);
                heuristicSeqSearch = true;
            }

            list_seq_searches.add(label);
	    label.setPrintInfo(false);
        } else if (si.type().equals("priority_search")) {
            label = priority_search(si);

            list_seq_searches.add(label);
        } else if (si.type().equals("seq_search")) {
            for (int i = 0; i < si.getSearchItems().size(); i++) {
                if (i == 0) { // master search
                    DepthFirstSearch<Var> label_seq = sub_search(si.getSearchItems().get(i), last_search, false);
		    last_search = getLastSearch(label_seq);
                    label = label_seq;
                } else {
                    DepthFirstSearch<Var> label_seq = sub_search(si.getSearchItems().get(i), last_search, false);
                    last_search.addChildSearch(label_seq);
                    last_search = getLastSearch(label_seq);
                }
	    }
        } else if (si.type().equals("float_search")) {
            label = float_search(si);
            if (!master)
                label.setSelectChoicePoint(variable_selection);

            // LDS heuristic search
            if (si.exploration().equals("lds")) {
                lds_search(label, si.ldsValue);
                heuristicSeqSearch = true;
            }
            // Credit heuristic search
            if (si.exploration().equals("credit")) {
                credit_search(label, si.creditValue, si.bbsValue);
                heuristicSeqSearch = true;
            }
            list_seq_searches.add(label);
	    label.setPrintInfo(false);
        } else {
            throw new IllegalArgumentException("Not recognized or supported search type \"" + si.type() + "\"; compilation aborted");
        }

        return label;
    }

    @SuppressWarnings("unchecked") DepthFirstSearch<Var> int_search(SearchItem si) {

        variable_selection = si.getIntSelect();
        DepthFirstSearch label = new DepthFirstSearch<Var>();
	label.setAssignSolution(false);

        if (options.debug())
            label.setConsistencyListener(failStatistics);

        return label;
    }

    @SuppressWarnings("unchecked") DepthFirstSearch<Var> set_search(SearchItem si) {

        variable_selection = si.getSetSelect();
        DepthFirstSearch label = new DepthFirstSearch<Var>();
	label.setAssignSolution(false);

        if (options.debug())
            label.setConsistencyListener(failStatistics);

        return label;
    }

    @SuppressWarnings("unchecked") DepthFirstSearch<Var> float_search(SearchItem si) {

        variable_selection = si.getFloatSelect();

        DepthFirstSearch<Var> label = new DepthFirstSearch<Var>();
	label.setAssignSolution(false);

        if (options.debug())
            label.setConsistencyListener(failStatistics);

        if (options.precision())
            label.setInitializeListener(new PrecisionSetting(options.getPrecision()));
        else
            label.setInitializeListener(new PrecisionSetting(si.precision));

        return label;
    }

    @SuppressWarnings("unchecked") DepthFirstSearch<Var> priority_search(SearchItem si) {

	// System.out.println("============\n"+si);
	
	ArrayList<SearchItem> dfs_s = si.getSearchItems();
	DepthFirstSearch<Var>[] searches = new DepthFirstSearch[dfs_s.size()];
	int i = 0;
	for (SearchItem s : dfs_s) {

	    DepthFirstSearch<Var> subSearch = null;
	    if (s.search_type.equals("int_search") || s.search_type.equals("bool_search")) {
		subSearch = int_search(s);
		subSearch.setSelectChoicePoint(variable_selection);
		subSearch.setPrintInfo(false);
		searches[i++] = subSearch;
	    } else if (s.search_type.equals("set_search")) {
		subSearch = set_search(s);
		subSearch.setSelectChoicePoint(variable_selection);
		subSearch.setPrintInfo(false);
		searches[i++] = subSearch;
	    } else if (s.search_type.equals("float_search")) {
		subSearch = float_search(s);
		subSearch.setSelectChoicePoint(variable_selection);
		subSearch.setPrintInfo(false);
		searches[i++] = subSearch;
	    } else if (s.search_type.equals("seq_search")) {
		subSearch = sub_search(s, null, false);

		DepthFirstSearch ns = subSearch;
		do {
		    ns.setPrintInfo(false);
		    // find next search
		    if (ns.childSearches == null)
			ns = null;
		    else 
			ns = (DepthFirstSearch)ns.childSearches[0];
		} while (ns != null);
		
		searches[i++] = subSearch;
	    } else if (s.search_type.equals("priority_search")) {
		subSearch = priority_search(s);
		subSearch.setPrintInfo(false);
		searches[i++] = subSearch;
	    } else
		throw new RuntimeException("Error: Not supported search type " + s.search_type + "in priority_search; execution aborted");
	}

	ComparatorVariable<IntVar> comparator = si.getVarSelect();

        PrioritySearch<Var> label = new PrioritySearch(si.vars(), comparator, searches);
	label.setPrintInfo(false);
	label.setAssignSolution(false);

        if (options.debug())
            label.setConsistencyListener(failStatistics);

	int to = options.getTimeOut();
	if (to > 0) {
	    label.setTimeOutMilliseconds(to);
	    for (DepthFirstSearch s : searches)
		s.setTimeOutMilliseconds(to);
	}

	if (options.getNumberSolutions() > 0)
	    ((PrioritySearch)label).setSolutionLimit(options.getNumberSolutions());
	
        return label;
    }



    void printSolution() {

        StringBuffer printBuffer = new StringBuffer();

        if (dictionary.outputVariables.size() > 0)
            for (int i = 0; i < dictionary.outputVariables.size(); i++) {
                Var v = dictionary.outputVariables.get(i);

                if (v instanceof BooleanVar) {
                    // print boolean variables
                    printBuffer.append(v.id() + " = ");
                    if (v.singleton())
                        switch (((BooleanVar) v).value()) {
                            case 0:
                                printBuffer.append("false");
                                break;
                            case 1:
                                printBuffer.append("true");
                                break;
                            default:
                                printBuffer.append(v.dom());
                        }
                    else
                        printBuffer.append("false..true");

                    printBuffer.append(";\n");
                } else if (v instanceof SetVar) {
                    // print set variables
                    printBuffer.append(v.id() + " = ");
                    if (v.singleton()) {
                        IntDomain glb = ((SetVar) v).dom().glb();
                        if (glb.getSize() > 0 && glb.getSize() == glb.max() - glb.min() + 1) {
                            printBuffer.append(glb.min() + ".." + glb.max());
                        } else {
                            printBuffer.append("{");
                            for (ValueEnumeration e = glb.valueEnumeration(); e.hasMoreElements(); ) {
                                int element = e.nextElement();
                                printBuffer.append(element);
                                if (e.hasMoreElements())
                                    printBuffer.append(", ");
                            }
                            printBuffer.append("}");
                        }
                    } else
                        printBuffer.append(v.dom().toString());

                    printBuffer.append(";\n");
                } else

                    printBuffer.append(v).append(";\n");
            }

        for (int i = 0; i < dictionary.outputArray.size(); i++) {
            OutputArrayAnnotation a = dictionary.outputArray.get(i);

            printBuffer.append(a).append("\n");
        }

	if (options.getVerbose()) {
	    // print number of search nodes and CPU time for this solution
	    int nodes=0;
	    DepthFirstSearch dfs = label;
	    while (dfs != null) {
		nodes += dfs.getNodes();
		dfs = (dfs.childSearches == null) ? null : (DepthFirstSearch)dfs.childSearches[0];
	    }

	    if (costVariable != null)
		if (minimize) {
		    if (costVariable instanceof org.jacop.core.IntVar)
			printBuffer.append("%%%mzn-stat objective=" + ((IntVar)costVariable).value() + "\n");
		    else if (costVariable instanceof org.jacop.floats.core.FloatVar)
			printBuffer.append("%%%mzn-stat objective=" + ((FloatVar)costVariable).value() + "\n");
		} else {
		    if (costVariable instanceof org.jacop.core.IntVar)
			printBuffer.append("%%%mzn-stat objective=" + (-((IntVar)costVariable).value()) + "\n");
		    else if (costVariable instanceof org.jacop.floats.core.FloatVar)
			printBuffer.append("%%%mzn-stat objective=" + (-((FloatVar)costVariable).value()) + "\n");
		}
	    double cpuTime = getSearchTime_ms();
	    printBuffer.append(String.format("%%%%%%mzn-stat nodes=%,d", nodes));
	    printBuffer.append(String.format(" (%,.1f nodes/s)\n", (cpuTime == 0) ? 0.0 : (double)nodes/(cpuTime/1000)));
	    if (restartCalculator != null)
		printBuffer.append(String.format("%%%%%%mzn-stat restarts=%,d", rs.restarts()));
	    printBuffer.append("\n%%%mzn-stat solveTime=" + cpuTime/1000 + "s\n");
	    printBuffer.append("%%%mzn-stat-end\n");
	}
	
        printBuffer.append("----------\n");

	if (options.getAll())
            System.out.print(printBuffer.toString());
        else { // store the print-out

            lastSolution = printBuffer;
        }
    }

    int getKind(String k) {
        if (k.equals("satisfy")) // 0 = satisfy
            return 0;
        else if (k.equals("minimize")) // 1 = minimize
            return 1;
        else if (k.equals("maximize")) // 2 = maximize
            return 2;
        else {
            throw new IllegalArgumentException("Not supported search kind; compilation aborted");
        }
    }

    IntVar getCost(ASTSolveExpr node) {

        if (node.getType() == 0) {// ident
            IntVar cost = dictionary.getVariable(node.getIdent());
            if (cost != null)
                return cost;
            else { // cost is constant ?
                Integer costInt = dictionary.checkInt(node.getIdent());
                if (costInt != null)
                    return new IntVar(store, costInt, costInt);
                else
                    return null;
            }
        } else if (node.getType() == 1) { // array access
            IntVar[] a = dictionary.getVariableArray(node.getIdent());
            if (a != null)
                return a[node.getIndex()];
            else { // cost is constant ?
                int[] costInt = dictionary.getIntArray(node.getIdent());
                if (costInt != null)
                    return new IntVar(store, costInt[node.getIndex()], costInt[node.getIndex()]);
                else
                    return null;
            }
        } else {
            throw new IllegalArgumentException("Wrong cost function specification " + node);
        }
    }

    FloatVar getCostFloat(ASTSolveExpr node) {
        if (node.getType() == 0) { // ident
            FloatVar cost = dictionary.getFloatVariable(node.getIdent());
            if (cost != null)
                return cost;
            else { // cost is constant ?
                Double costFloat = dictionary.checkFloat(node.getIdent());
                if (costFloat != null)
                    return new FloatVar(store, costFloat, costFloat);
                else
                    return null;
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
        if (debug)
            System.out.println(c);
    }

    /*
    boolean restart_search(Search<Var> masterLabel, SelectChoicePoint<Var> masterSelect, 
			   IntVar cost, boolean minimize) {
	costVariable = cost;
	Search<Var> final_search = list_seq_searches.get(list_seq_searches.size()-1);

	for (Search s : list_seq_searches) 
	    s.setAssignSolution(false);
	store.setLevel(store.level+1);
	boolean Result = true, optimalResult = false; 
	while (Result) {
	    Result = masterLabel.labeling(store, masterSelect);
	    if (minimize) //minimize
		pose(new XltC(cost, costValue));
	    else // maximize
		pose(new XgtC(cost, costValue));

	    optimalResult = optimalResult || Result;

	    if (options.getNumberSolutions() == final_search.getSolutionListener().solutionsNo())
		break;
	}
	store.removeLevel(store.level);
	store.setLevel(store.level-1);

	Result = optimalResult;
	if (Result)
	    for (Search s : list_seq_searches) 
		s.assignSolution();

	return Result;
    }
    */

    void lds_search(DepthFirstSearch<Var> label, int lds_value) {
        //  	System.out.println("LDS("+lds_value+")");

        LDS<Var> lds = new LDS<Var>(lds_value);
        if (label.getExitChildListener() == null)
            label.setExitChildListener(lds);
        else
            label.getExitChildListener().setChildrenListeners(lds);
    }


    void credit_search(DepthFirstSearch<Var> label, int creditValue, int bbsValue) {
        //  	System.out.println("Credit("+creditValue+", "+bbsValue+")");

        int maxDepth = 1000; //IntDomain.MaxInt;
        CreditCalculator<Var> credit = new CreditCalculator<Var>(creditValue, bbsValue, maxDepth);

        if (label.getConsistencyListener() == null)
            label.setConsistencyListener(credit);
        else
            label.getConsistencyListener().setChildrenListeners(credit);

        label.setExitChildListener(credit);
        label.setTimeOutListener(credit);
    }

    @SuppressWarnings("unchecked") void printSearch(DepthFirstSearch<Var> s) {

	do {

	    System.out.print(s);

	    // find next search
	    if (s.childSearches == null)
		s = null;
	    else {
		s = (DepthFirstSearch<Var>)s.childSearches[0];
		System.out.print(", ");

	    }
	} while (s != null);
	System.out.println();
    }

    int FinalNumberSolutions = 0;


    /**
     * @author Krzysztof Kuchcinski
     */
    public class CostListener<T extends Var> extends SimpleSolutionListener<T> {

        public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

            boolean returnCode = super.executeAfterSolution(search, select);

	    /* // === used to print number of search nodes for each solution
            int nodes=0;
	    for (Search<Var> label : list_seq_searches) 
		nodes += label.getNodes();
	    System.out.println("%% Search nodes : "+ nodes );
	    */

	    /* // ==> used for restart search
            if (costVariable != null)
                if (costVariable instanceof IntVar)
                    costValue = ((IntVar) costVariable).value();
                else
                    floatCostValue = ((FloatVar) costVariable).value();
	    */

            FinalNumberSolutions++;

            printSolution();

            return returnCode;
        }
    }


    public static class PrecisionSetting implements InitializeListener {

        InitializeListener[] initializeChildListeners;

        double precision;

        PrecisionSetting(double p) {
            precision = p;
        }

        public void executedAtInitialize(Store store) {
            FloatDomain.setPrecision(precision);
        }

        public void setChildrenListeners(InitializeListener[] children) {
            initializeChildListeners = new InitializeListener[children.length];
            System.arraycopy(children, 0, initializeChildListeners, 0, children.length);
        }

        public void setChildrenListeners(InitializeListener child) {
            initializeChildListeners = new InitializeListener[1];
            initializeChildListeners[0] = child;
        }
    }

    public SearchItem getSearch() {
        return si;
    }

    public int getSolveKind() {
        return solveKind;
    }

    // public class ResultListener<T extends Var> extends SimpleSolutionListener<T> {

    // 	Var[] var;

    // 	public ResultListener(Var[] v) {
    // 	    var = v;
    // 	}

    // 	public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

    // 	    boolean returnCode = super.executeAfterSolution(search, select);

    // 	    FinalNumberSolutions++;

    // 	    printSolution();
    // 	    System.out.println("----------");

    // 	    return returnCode;
    // 	}
    // }

    void helperSolutionPrinter(String lastSolution) {

        System.out.print(lastSolution);

        if (!options.getOutputFilename().equals("") && !lastSolution.isEmpty()) {
            try {
                System.out.println("%%Output filename " + options.getOutputFilename());
                Files.write(Paths.get(options.getOutputFilename()), lastSolution.getBytes(Charset.forName("UTF-8")), StandardOpenOption.CREATE,
                    StandardOpenOption.TRUNCATE_EXISTING);
            } catch (IOException e) {
                e.printStackTrace();

            }
        }

    }

    final static String p = System.getProperty("fz_system_timer");

    void startTimer() {
	
	if (p != null && p.equals("true")) 
	    timer = new SystemTimer();
	else
	    timer = new ThreadTimer();

	startCPU = timer.getCPUTime();
    }
}
