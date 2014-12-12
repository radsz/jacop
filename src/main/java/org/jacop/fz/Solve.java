/**
 *  Solve.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
package org.jacop.fz;

import java.util.ArrayList;
import java.util.Comparator;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XltC;
import org.jacop.constraints.XplusYeqC;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.ValueEnumeration;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.search.CreditCalculator;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.LDS;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.InitializeListener;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.floats.core.FloatDomain;

import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMin;

/**
 * 
 * The parser part responsible for parsing the solve part of the flatzinc file,
 * building a related search and executing it.
 *
 * Current implementation runs also final search on all variables to ensure
 * that they are ground.
 * 
 * @author Krzysztof Kuchcinski
 *
 */
public class Solve implements ParserTreeConstants {

    Tables dictionary;
    Options options;
    Store store;
    int initNumberConstraints;
    int NumberBoolVariables;

    Thread tread;
    java.lang.management.ThreadMXBean searchTimeMeter;
    long startCPU;

    //ComparatorVariable tieBreaking=null;
    SelectChoicePoint<Var> variable_selection;
    ArrayList<Search<Var>> list_seq_searches = null;

    boolean debug = false;
    boolean print_search_info = false;
    boolean setSearch = false;
    boolean heuristicSeqSearch = false;
	
    Var costVariable;
	
    int costValue;
    double floatCostValue;

    Parser parser;

    // -------- for print-out of statistics
    boolean singleSearch;
    boolean Result;
    boolean optimization;
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

    int solveKind=-1;

    /**
     * It creates a parser for the solve part of the flatzinc file. 
     * 
     * @param store the constraint store within which context the search will take place.
     */
    public Solve(Store store) {
	this.store = store;
    }

    /**
     * It parses the solve part. 
     * 
     * @param node the current parsing node.
     * @param table the table containing all the various variable definitions encoutered thus far.
     * @param opt option specifies to flatzinc parser in respect to search (e.g. all solutions). 
     */
    public void search(ASTSolveItem node, Tables table, Options opt) {

// 	System.out.println(table);

	initNumberConstraints = store.numberConstraints();

	if (opt.getVerbose())
	    System.out.println("%% Model constraints defined.\n%% Variables = "+store.size() + ", Bool variables = "+NumberBoolVariables +
			       ", Constraints = "+initNumberConstraints);

	dictionary = table;
	options = opt;
	solveKind=-1;

	// node.dump("");

	ASTSolveKind kind;
	int count = node.jjtGetNumChildren();

	// 	System.out.println("Number constraints = "+store.numberConstraints());
	// 	System.out.println("Number  of variables = "+store.size());

	if (count == 1) {// only solve kind => default search

 	    SearchItem si_int = new SearchItem(store, dictionary);
	    kind = (ASTSolveKind)node.jjtGetChild(0);
	    solveKind = getKind(kind.getKind());
	    run_single_search(solveKind, kind, null);
	}
	else if (count == 2) {// single annotation

	    SearchItem si = new SearchItem(store, dictionary);
	    si.searchParameters(node, 0);
	    // System.out.println("1. *** "+si);
	    String search_type = si.type();

	    if (search_type.equals("int_search") || search_type.equals("set_search") ||
		search_type.equals("bool_search")) {

		kind = (ASTSolveKind)node.jjtGetChild(1);
		solveKind = getKind(kind.getKind());

		run_single_search(solveKind, kind, si);
	    }
	    else if (search_type.equals("float_search")) {

		kind = (ASTSolveKind)node.jjtGetChild(1);
		solveKind = getKind(kind.getKind());

		run_single_search(solveKind, kind, si);
	    }
	    else if (search_type.equals("seq_search")) {
		kind = (ASTSolveKind)node.jjtGetChild(1);
		solveKind = getKind(kind.getKind());

		run_sequence_search(solveKind, kind, si);
	    }
	    else {
		System.err.println("Not recognized structure of solve statement \""+search_type+"\"; compilation aborted");
		System.exit(0);
	    } 
	}
	else if (count > 2) {// several annotations
	    SearchItem si = new SearchItem(store, dictionary);
	    si.searchParametersForSeveralAnnotations(node, 0);
// 	    System.out.println("*** "+si +"\nsize="+si.search_seqSize());

 	    kind = (ASTSolveKind)node.jjtGetChild(si.search_seqSize());
 	    solveKind = getKind(kind.getKind());
// 	    System.out.println ("kind="+kind+" solveKind="+solveKind);

  	    run_sequence_search(solveKind, kind, si);
	}
	else
	    {
	    System.err.println("Not recognized structure of solve statement; compilation aborted");
	    System.exit(0);
	}
    }

    void run_single_search(int solveKind, SimpleNode kind, SearchItem si) {

	singleSearch = true;

	defaultSearch = false;

	this.si = si;

	if (options.getVerbose()) {
	    String solve="notKnown";
	    switch (solveKind) {
	    case 0: 
		solve = "%% satisfy"; break; // satisfy
	    case 1: 
		Var costMin  = (getCost((ASTSolveExpr)kind.jjtGetChild(0)) != null) ? getCost((ASTSolveExpr)kind.jjtGetChild(0)) :
		getCostFloat((ASTSolveExpr)kind.jjtGetChild(0));
		solve = "%% minimize("+ costMin+") "; 
                break; // minimize
	    case 2: 
		Var costMax = (getCost((ASTSolveExpr)kind.jjtGetChild(0)) != null) ? getCost((ASTSolveExpr)kind.jjtGetChild(0)) :
		getCostFloat((ASTSolveExpr)kind.jjtGetChild(0));
		solve = "%% maximize("+ costMax +") "; 
                break; // maximize
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
		    label.setTimeOut(to);
	    }
	    else if (si.type().equals("bool_search")) {
		label = int_search(si);
		list_seq_searches.add(label);
		//label.setSolutionListener(new EmptyListener<Var>());
		label.setPrintInfo(false);

		// time-out option
		int to = options.getTimeOut();
		if (to > 0) 
		    label.setTimeOut(to);
	    }
	    else if (si.type().equals("set_search")) {
		label = set_search(si);
		list_seq_searches.add(label);
		setSearch=true;
		//label.setSolutionListener(new EmptyListener<Var>());
		label.setPrintInfo(false);

		// time-out option
		int to = options.getTimeOut();
		if (to > 0) 
		    label.setTimeOut(to);
	    }
	    else if (si.type().equals("float_search")) {
		label = float_search(si);
		list_seq_searches.add(label);
		//label.setSolutionListener(new EmptyListener<Var>());
		label.setPrintInfo(false);

		// time-out option
		int to = options.getTimeOut();
		if (to > 0) 
		    label.setTimeOut(to);
	    }
	    else {
		System.err.println("Not recognized or supported search type \""+si.type()+"\"; compilation aborted");
		System.exit(0);
	    }
	}

	if (solveKind > 0) {
	    optimization = true;

	    cost = getCost((ASTSolveExpr)kind.jjtGetChild(0));
	    if (cost != null)
		if ( solveKind == 1)  // minimize
		    costVariable = cost; 
		else { // maximize
		    max_cost = new IntVar(store, "-"+cost.id(), IntDomain.MinInt, 
					  IntDomain.MaxInt);
		    pose(new XplusYeqC((IntVar)max_cost, (IntVar)cost, 0));
		    costVariable = max_cost;
		}
	    else {
		cost = getCostFloat((ASTSolveExpr)kind.jjtGetChild(0));
		if ( solveKind == 1)  // minimize
		    costVariable = cost; 
		else { // maximize
		    max_cost = new FloatVar(store, "-"+cost.id(), VariablesParameters.MIN_FLOAT, 
					  VariablesParameters.MAX_FLOAT);
		    pose(new PplusQeqR((FloatVar)max_cost, (FloatVar)cost, new FloatVar(store, 0.0, 0.0)));
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
		for (int i=1; i<final_search.length; i++)
		    if (final_search[i] != null)
			list_seq_searches.add(final_search[i]);
	    }
	    else if (final_search[1] != null) {
		label = final_search[1];
		list_seq_searches.add(label);
		if (final_search[2] != null)
		    list_seq_searches.add(final_search[2]);

	    }
	    else if (final_search[2] != null) {
		label = final_search[2];
		list_seq_searches.add(label);
		if (final_search[3] != null)
		    list_seq_searches.add(final_search[3]);
	    }
	    else if (final_search[3] != null) {
		label = final_search[3];
		list_seq_searches.add(label);
	    }
	}
	else {
	    for (DepthFirstSearch<Var> s : final_search)
		if (s != null)
		    list_seq_searches.add(s);
	}
	last_search = list_seq_searches.get(list_seq_searches.size()-1);


	// LDS & Credit heuristic search
	if (si.exploration().equals("lds")) 
	    lds_search(label, si.ldsValue);
	// Credit heuristic search
	else if (si.exploration().equals("credit")) 
	    credit_search(label, si.creditValue, si.bbsValue);

	Result = false;	

	tread = java.lang.Thread.currentThread();
	java.lang.management.ThreadMXBean b = java.lang.management.ManagementFactory.getThreadMXBean();
	searchTimeMeter = b;

	startCPU = b.getThreadCpuTime(tread.getId());
	// 	long startUser = b.getThreadUserTime(tread.getId());

	if (si == null || si.exploration() == null || si.exploration().equals("complete") 
		|| si.exploration().equals("lds")
		|| si.exploration().equals("credit")
		)
	    switch (solveKind) {
	    case 0: // satisfy

		FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

		if (options.getAll()) { // all solutions
 		    label.getSolutionListener().searchAll(true); 
 		    label.getSolutionListener().recordSolutions(false);

		    // =====> add "search for all" flag to all sub-searches, 2012-03-19
		    java.util.LinkedHashSet<Search<? extends Var>> l = 
			new java.util.LinkedHashSet<Search<? extends Var>>();
		    l.add(label);
		    while (l.size() != 0) {
		    java.util.LinkedHashSet<Search<? extends Var>> ns = 
			new java.util.LinkedHashSet<Search<? extends Var>>();
			for (Search s1 : l) {
			    Search<? extends Var>[] child = ((DepthFirstSearch)s1).childSearches;
			    if (child != null)
				for (Search s : child) {
				    ns.add(s);	

				    s.getSolutionListener().searchAll(true); 
				    s.getSolutionListener().recordSolutions(false);

				}	    
			}
			l = ns;
		    }
		    // <=====
		    if (options.getNumberSolutions()>0) 
			last_search.getSolutionListener().setSolutionLimit(options.getNumberSolutions());

		}

		// printSearch(label);

		this.si = si;

		if (options.runSearch())
		    Result = label.labeling(store, variable_selection);
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

		if (options.getNumberSolutions()>0) {
		    for (Search<Var> list_seq_searche : list_seq_searches)
			((DepthFirstSearch) list_seq_searche).respectSolutionListenerAdvice = true;
		    last_search.getSolutionListener().setSolutionLimit(options.getNumberSolutions());
		}

		this.si = si;

		if (options.runSearch())
		    Result = label.labeling(store, variable_selection, cost);
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

		if (options.getNumberSolutions()>0) {
		    for (Search<Var> list_seq_searche : list_seq_searches)
			((DepthFirstSearch) list_seq_searche).respectSolutionListenerAdvice = true;
		    last_search.getSolutionListener().setSolutionLimit(options.getNumberSolutions());
		}

		this.si = si;

		if (options.runSearch())
		    Result = label.labeling(store, variable_selection, max_cost);
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
	    System.err.println("Not recognized or supported "+si.exploration()+" search explorarion strategy ; compilation aborted");
	    System.exit(0);
	}

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
	    System.out.println ("%% =====INTERRUPTED=====\n%% Model not yet posed..");
	    return;
	}

	if (result) {
	    if (!optimization && options.getAll()) {
		if (!interrupted)
		    if (si.exploration().equals("complete")) 
			if (! label.timeOutOccured) {
			    if (options.getNumberSolutions() == -1 || options.getNumberSolutions() > label.getSolutionListener().solutionsNo())
				System.out.println("==========");
			}
			else
			    System.out.println("%% =====TIME-OUT=====");
		    else
			if (label.timeOutOccured) 
			    System.out.println("%% =====TIME-OUT=====");
	    }
	    else if (optimization) {
		if (!interrupted)
		    if (si.exploration().equals("complete"))
			if (! label.timeOutOccured) {
			    if (options.getNumberSolutions() == -1 || options.getNumberSolutions() > label.getSolutionListener().solutionsNo())
				System.out.println("==========");
			}    
			else
			    System.out.println("%% =====TIME-OUT=====");
		    else
			if (label.timeOutOccured) 
			    System.out.println("%% =====TIME-OUT=====");
	    }
	}
	else
	    if (label.timeOutOccured) {
		System.out.println("=====UNKNOWN=====");
		System.out.println("%% =====TIME-OUT=====");
	    }
	    else 
		if (interrupted)
		    System.out.println ("%% =====INTERRUPTED=====");
		else
		    if (si.exploration().equals("complete"))
			System.out.println("=====UNSATISFIABLE=====");
		    else
			System.out.println("=====UNKNOWN=====");

	if (options.getStatistics()) {
	    int nodes = 0, //label.getNodes(), 
		decisions = 0, //label.getDecisions(), 
		wrong = 0, //label.getWrongDecisions(), 
		backtracks = 0, //label.getBacktracks(), 
		depth = 0, //label.getMaximumDepth(),
		solutions = 0; //label.getSolutionListener().solutionsNo();

	    if ( ! defaultSearch) {
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
                solutions = l.getSolutionListener().solutionsNo();
            }
        }

	System.out.println("\n%% Model variables : "+ (store.size()+NumberBoolVariables)+
			   "\n%% Model constraints : "+initNumberConstraints+
			   "\n\n%% Search CPU time : " + (searchTimeMeter.getThreadCpuTime(tread.getId()) - startCPU)/(long)1e+6 + "ms"+
			   "\n%% Search nodes : "+nodes+
			   "\n%% Search decisions : "+decisions+
			   "\n%% Wrong search decisions : "+wrong+
			   "\n%% Search backtracks : "+backtracks+
			   "\n%% Max search depth : "+depth+
			   "\n%% Number solutions : "+ solutions 
			   );
	}

    }

    DepthFirstSearch<Var>[] setSubSearchForAll(DepthFirstSearch<Var> label, Options opt) {

	DepthFirstSearch<Var>[] intAndSetSearch = new DepthFirstSearch[4];

	Var[] int_search_variables = null,
	    set_search_variables = null,
	    bool_search_variables = null;
	FloatVar[] float_search_variables = null;

	// collect integer & bool variables for search
	int int_varSize = 0, bool_varSize=0;
	for (int i=0; i<dictionary.defaultSearchVariables.size(); i++)
	    if (dictionary.defaultSearchVariables.get(i) instanceof org.jacop.core.BooleanVar)
		bool_varSize++;
	    else
		int_varSize++;

	for (int i=0; i<dictionary.defaultSearchArrays.size(); i++)
	    if (dictionary.defaultSearchArrays.get(i).length != 0)
		if (dictionary.defaultSearchArrays.get(i)[0]  instanceof org.jacop.core.BooleanVar)
		    bool_varSize += dictionary.defaultSearchArrays.get(i).length;
		else
		    int_varSize += dictionary.defaultSearchArrays.get(i).length;


	int_search_variables = new IntVar[int_varSize];
	bool_search_variables = new IntVar[bool_varSize];

	int bool_n=0, int_n=0;
	for (int i=0; i<dictionary.defaultSearchArrays.size(); i++)
	    for (int j=0; j<dictionary.defaultSearchArrays.get(i).length; j++) {
		Var v = dictionary.defaultSearchArrays.get(i)[j];
 		if (v  instanceof org.jacop.core.BooleanVar) 
 		    bool_search_variables[bool_n++] = v;
		else
 		    int_search_variables[int_n++] = v;
	    }
	for (int i=0; i<dictionary.defaultSearchVariables.size(); i++) {
	    Var v = dictionary.defaultSearchVariables.get(i);
	    if (v  instanceof org.jacop.core.BooleanVar) 
		bool_search_variables[bool_n++] = v;
	    else
		int_search_variables[int_n++] = v;
	}
 	java.util.Arrays.sort(int_search_variables, new DomainSizeComparator<Var>());

	// collect set variables for search
	int n=0;
	int varSize = dictionary.defaultSearchSetVariables.size();
	for (int i=0; i<dictionary.defaultSearchSetArrays.size(); i++)
	    varSize += dictionary.defaultSearchSetArrays.get(i).length;

	set_search_variables = new SetVar[varSize];
	for (int i=0; i<dictionary.defaultSearchSetArrays.size(); i++)
	    for (int j=0; j<dictionary.defaultSearchSetArrays.get(i).length; j++)
		set_search_variables[n++] = dictionary.defaultSearchSetArrays.get(i)[j];
	for (int i=0; i<dictionary.defaultSearchSetVariables.size(); i++)
	    set_search_variables[n++] = dictionary.defaultSearchSetVariables.get(i);
	// =====


	// collect float variables for search
	n=0;
	varSize = dictionary.defaultSearchFloatVariables.size();
	for (int i=0; i<dictionary.defaultSearchFloatArrays.size(); i++)
	    varSize += dictionary.defaultSearchFloatArrays.get(i).length;

	float_search_variables = new FloatVar[varSize];
	for (int i=0; i<dictionary.defaultSearchFloatArrays.size(); i++)
	    for (int j=0; j<dictionary.defaultSearchFloatArrays.get(i).length; j++)
		float_search_variables[n++] = (FloatVar)dictionary.defaultSearchFloatArrays.get(i)[j];
	for (int i=0; i<dictionary.defaultSearchFloatVariables.size(); i++)
	    float_search_variables[n++] = (FloatVar)dictionary.defaultSearchFloatVariables.get(i);
	// =====

	if (opt.getVerbose()) {
	    System.out.println ("%% default int search variables = " + java.util.Arrays.asList(int_search_variables));
	    System.out.println ("%% default boolean search variables = " + java.util.Arrays.asList(bool_search_variables));
	    System.out.println ("%% default set search variables = " + java.util.Arrays.asList(set_search_variables));
	    System.out.println ("%% default float search variables = " + java.util.Arrays.asList(float_search_variables));
// 	System.out.println ("cost = " + costVariable);
	}

	DepthFirstSearch<Var> lastSearch = label;
	DepthFirstSearch<Var> intSearch = new DepthFirstSearch<Var>();
 	if (int_search_variables.length != 0) {
	    // add search containing int variables to be sure that they get a value
 	    SelectChoicePoint<Var> intSelect = new SimpleSelect<Var>(int_search_variables, 
   								     null,
//    								     new JaCoP.search.MostConstrainedStatic<Var>(), 
								     new IndomainMin());
	    if (variable_selection == null)
		variable_selection = intSelect;
	    intSearch.setSelectChoicePoint(intSelect);
	    intSearch.setPrintInfo(false);
	    if (lastSearch != null) 
		lastSearch.addChildSearch(intSearch);
	    lastSearch = intSearch;
	    if (bool_search_variables.length == 0 && set_search_variables.length == 0 
		&& float_search_variables.length == 0) {
		intSearch.setSolutionListener(new CostListener<Var>());

		if (costVariable != null) {
		    intSearch.setCostVar(costVariable);
		    intSearch.setOptimize( true);
		}
	    }
	    // else
	    // 	intSearch.setSolutionListener(new EmptyListener<Var>());

	    // if (searchAll) {
  	    // 	intSearch.getSolutionListener().searchAll(true); 
	    // 	intSearch.getSolutionListener().recordSolutions(false);
	    // }	    
	    // if (options.getNumberSolutions() > 0)
	    // 	intSearch.getSolutionListener().setSolutionLimit(options.getNumberSolutions());

	    // time-out option
	    int to = options.getTimeOut();
	    if (to > 0) 
		intSearch.setTimeOut(to);

	    intAndSetSearch[0] = intSearch;
	}

	DepthFirstSearch<Var> boolSearch = new DepthFirstSearch<Var>();
 	if (bool_search_variables.length != 0) {
	    // add search containing boolean variables to be sure that they get a value
	    SelectChoicePoint<Var> boolSelect = new SimpleSelect<Var>(bool_search_variables, 
								      null,
// 								      new JaCoP.search.MostConstrainedStatic<Var>(), 
								      new IndomainMin());
	    if (variable_selection == null)
		variable_selection = boolSelect;
	    boolSearch.setSelectChoicePoint(boolSelect);
	    boolSearch.setPrintInfo(false);
	    if (lastSearch != null) 
		lastSearch.addChildSearch(boolSearch);
	    lastSearch = boolSearch;
	    if (set_search_variables.length == 0 && float_search_variables.length == 0) {
		boolSearch.setSolutionListener(new CostListener<Var>()); 

		if (costVariable != null) {
		    intSearch.setCostVar( costVariable);
		    intSearch.setOptimize( true);
		}
	    }

	    // time-out option
	    int to = options.getTimeOut();
	    if (to > 0) 
		boolSearch.setTimeOut(to);

	    intAndSetSearch[1] = boolSearch;
	}


	if (set_search_variables.length != 0) {
	    // add set search containing all variables to be sure that they get a value
	    DepthFirstSearch<Var> setSearch = new DepthFirstSearch<Var>();
	    SelectChoicePoint<Var> setSelect = new SimpleSelect<Var>(set_search_variables, 
								     null,
// 								     new JaCoP.search.MostConstrainedStatic<Var>(), 
								     new IndomainSetMin());
	    if (variable_selection == null)
		variable_selection = setSelect;
	    setSearch.setSelectChoicePoint(setSelect);
	    setSearch.setPrintInfo(false);
	    if (lastSearch != null) 
		lastSearch.addChildSearch(setSearch);
	    if (float_search_variables.length == 0)
		setSearch.setSolutionListener(new CostListener<Var>());

	    if (costVariable != null) {
		intSearch.setCostVar( costVariable);
		intSearch.setOptimize( true);
	    }

	    // time-out option
	    int to = options.getTimeOut();
	    if (to > 0) 
		setSearch.setTimeOut(to);

	    intAndSetSearch[2] = setSearch;
	}

	if (float_search_variables.length != 0) {
	    // add float search containing all variables to be sure that they get a value
	    DepthFirstSearch<Var> floatSearch = new DepthFirstSearch<Var>();
	    SelectChoicePoint<Var> floatSelect = new SplitSelectFloat<Var>(store, float_search_variables, null);

	    if (variable_selection == null)
		variable_selection = floatSelect;
	    floatSearch.setSelectChoicePoint(floatSelect);
	    floatSearch.setPrintInfo(false);
	    if (lastSearch != null) 
		lastSearch.addChildSearch(floatSearch);
   	    floatSearch.setSolutionListener(new CostListener<Var>());

	    if (costVariable != null) {
		intSearch.setCostVar( costVariable);
		intSearch.setOptimize( true);
	    }

	    // time-out option
	    int to = options.getTimeOut();
	    if (to > 0) 
		floatSearch.setTimeOut(to);

	    intAndSetSearch[3] = floatSearch;
	}

	if (int_search_variables.length == 0 && 
	    bool_search_variables.length == 0 && 
	    set_search_variables.length == 0 &&
	    float_search_variables.length == 0) {

	    printSolution();

	    System.out.println("----------");

	    if (options.getStatistics())
		System.out.println("\n%% Model variables : "+ (store.size()+ NumberBoolVariables) +
				   "\n%% Model constraints : "+initNumberConstraints+
				   "\n\n%% Search CPU time : " + "0ms"+
				   "\n%% Search nodes : 0"+
				   "\n%% Search decisions : 0"+
				   "\n%% Wrong search decisions : 0"+
				   "\n%% Search backtracks : 0"+
				   "\n%% Max search depth : 0"+
				   "\n%% Number solutions : 1"
				   );
	    System.exit(0);
	}

	return intAndSetSearch;
    }


    void run_sequence_search(int solveKind, SimpleNode kind, SearchItem si) {

	singleSearch = false;

	this.si = si;

	if (options.getVerbose()) {
	    String solve="notKnown";
	    switch (solveKind) {
	    case 0: solve = "%% satisfy"; break; // satisfy
	    case 1: 
		Var costMin  = (getCost((ASTSolveExpr)kind.jjtGetChild(0)) != null) ? getCost((ASTSolveExpr)kind.jjtGetChild(0)) :
		getCostFloat((ASTSolveExpr)kind.jjtGetChild(0));
		solve = "%% minimize("+ costMin +") "; break; // minimize

	    case 2: 
		Var costMax = (getCost((ASTSolveExpr)kind.jjtGetChild(0)) != null) ? getCost((ASTSolveExpr)kind.jjtGetChild(0)) :
		getCostFloat((ASTSolveExpr)kind.jjtGetChild(0));
		solve = "%% maximize("+ costMax +") "; break; // maximize
	    }
	    System.out.println(solve + " : seq_search([" + si + "])");
	}

	DepthFirstSearch<Var> masterLabel = null;
	DepthFirstSearch<Var> last_search = null;
	SelectChoicePoint<Var> masterSelect = null;
	list_seq_searches = new ArrayList<Search<Var>>();

	for (int i=0; i<si.getSearchItems().size(); i++) {
	    if (i == 0) { // master search
		masterLabel = sub_search(si.getSearchItems().get(i), masterLabel, true);
		last_search = masterLabel;
		masterSelect = variable_selection;
		if (!print_search_info) masterLabel.setPrintInfo(false);
	    }
	    else {
		DepthFirstSearch<Var> label = sub_search(si.getSearchItems().get(i), last_search, false);
		last_search.addChildSearch(label);
		last_search = label;
		if (!print_search_info) last_search.setPrintInfo(false);
	    }
	}

 	DepthFirstSearch<Var>[] complementary_search = setSubSearchForAll(last_search, options);	
        for (DepthFirstSearch<Var> aComplementary_search : complementary_search) {
            if (aComplementary_search != null) {
                list_seq_searches.add(aComplementary_search);
                if (!print_search_info) aComplementary_search.setPrintInfo(false);
            }
        }

       	// System.out.println("*** " + list_seq_searches);

	Result = false;	
	Var cost = null;
	Var max_cost = null;
	optimization = false;

	final_search_seq = list_seq_searches.get(list_seq_searches.size()-1);

	tread = java.lang.Thread.currentThread();
	java.lang.management.ThreadMXBean b = java.lang.management.ManagementFactory.getThreadMXBean();
	searchTimeMeter = b;

	startCPU = b.getThreadCpuTime(tread.getId());
	// 	long startUser = b.getThreadUserTime(tread.getId());

	int to = options.getTimeOut();
	if (to > 0)
	    for (Search s : list_seq_searches)
		s.setTimeOut(to);

	int ns = options.getNumberSolutions();
	if (si.exploration() == null || si.exploration().equals("complete"))
	    switch (solveKind) {
	    case 0: // satisfy

		FloatDomain.intervalPrint(options.getInterval()); // print intervals for float variables

 		if (options.getAll() ) { // all solutions
  		    for (int i=0; i<si.getSearchItems().size(); i++) {  //list_seq_searches.size(); i++) {
  			list_seq_searches.get(i).getSolutionListener().searchAll(true);
  			list_seq_searches.get(i).getSolutionListener().recordSolutions(false);
       			if ( ns>0 )
     			    list_seq_searches.get(i).getSolutionListener().setSolutionLimit(ns);
 		    }
 		}

		if (options.runSearch())
		    Result = masterLabel.labeling(store, masterSelect);
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

		cost = getCost((ASTSolveExpr)kind.jjtGetChild(0));
		if (cost != null)
		    costVariable = cost; 
		else {
		    cost = getCostFloat((ASTSolveExpr)kind.jjtGetChild(0));
		    costVariable = cost; 
		}
		
 		// Result = restart_search(masterLabel, masterSelect, cost, true);

		for (Search<Var> list_seq_searche : list_seq_searches)
		    list_seq_searche.setOptimize(true);

		if (ns > 0) {
		    for (int i=0; i<list_seq_searches.size()-1; i++)
		     	((DepthFirstSearch)list_seq_searches.get(i)).respectSolutionListenerAdvice = true;
		    final_search_seq.getSolutionListener().setSolutionLimit(ns);
		    ((DepthFirstSearch)final_search_seq).respectSolutionListenerAdvice = true;
		}

		if (options.runSearch())
		    Result = masterLabel.labeling(store, masterSelect, cost);
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

		cost = getCost((ASTSolveExpr)kind.jjtGetChild(0));
		if (cost != null) { // maximize
		    max_cost = new IntVar(store, "-"+cost.id(), IntDomain.MinInt, 
					  IntDomain.MaxInt);
		    pose(new XplusYeqC((IntVar)max_cost, (IntVar)cost, 0));
		    costVariable = max_cost;
		}
		else {
		    cost = getCostFloat((ASTSolveExpr)kind.jjtGetChild(0));
		    max_cost = new FloatVar(store, "-"+cost.id(), VariablesParameters.MIN_FLOAT, 
					    VariablesParameters.MAX_FLOAT);
		    pose(new PplusQeqR((FloatVar)max_cost, (FloatVar)cost, new FloatVar(store, 0.0, 0.0)));
		    costVariable = max_cost;
		}

		// Result = restart_search(masterLabel, masterSelect, cost, false);

            for (Search<Var> list_seq_searche : list_seq_searches)
                list_seq_searche.setOptimize(true);

		if (ns > 0) {
		    for (int i=0; i<list_seq_searches.size()-1; i++)
			((DepthFirstSearch)list_seq_searches.get(i)).respectSolutionListenerAdvice=true;
		    final_search_seq.getSolutionListener().setSolutionLimit(ns);
		    ((DepthFirstSearch)final_search_seq).respectSolutionListenerAdvice=true;
		}

		if (options.runSearch())
		    Result = masterLabel.labeling(store, masterSelect, max_cost);
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
	    System.err.println("Not recognized or supported "+si.exploration()+
			       " search explorarion strategy ; compilation aborted");
	    System.exit(0);
	}

	printStatisticsForSeqSearch(false, Result);
    
    }


    void printStatisticsForSeqSearch(boolean interrupted, boolean result) {

	if (list_seq_searches == null) {
	    System.out.println ("%% =====INTERRUPTED=====\n%% Model not yet posed..");
	    return;
	}

	if (result) {
	    if (!optimization && options.getAll()) {
		if (!heuristicSeqSearch)
		    if (! anyTimeOutOccured(list_seq_searches)) {
			if (options.getNumberSolutions() == -1 || options.getNumberSolutions() > final_search_seq.getSolutionListener().solutionsNo())
			    System.out.println("==========");
		    }
		    else
			System.out.println("%% =====TIME-OUT=====");
		else
		    if (anyTimeOutOccured(list_seq_searches)) 
			System.out.println("%% =====TIME-OUT=====");
	    }
	    else if (optimization) {
		if (!heuristicSeqSearch)
		    if (! anyTimeOutOccured(list_seq_searches)) {
			if (options.getNumberSolutions() == -1 || options.getNumberSolutions() > final_search_seq.getSolutionListener().solutionsNo())
			    System.out.println("==========");
		    }
		    else
			System.out.println("%% =====TIME-OUT=====");
		else
		    if (anyTimeOutOccured(list_seq_searches)) 
			System.out.println("%% =====TIME-OUT=====");
	    }
	}
	else
	    if (anyTimeOutOccured(list_seq_searches)) {
		System.out.println("=====UNKNOWN=====");
		System.out.println("%% =====TIME-OUT=====");
	    }
	    else
		if (interrupted)
		    System.out.println ("%% =====INTERRUPTED=====");
		else
		    System.out.println("=====UNSATISFIABLE=====");

	if (options.getStatistics()) {
	    int nodes=0, decisions=0, wrong=0, backtracks=0, depth=0,solutions=0;
        for (Search<Var> label : list_seq_searches) {
            nodes += label.getNodes();
            decisions += label.getDecisions();
            wrong += label.getWrongDecisions();
            backtracks += label.getBacktracks();
            depth += label.getMaximumDepth();
            solutions = label.getSolutionListener().solutionsNo();
        }

	System.out.println("\n%% Model variables : "+ (store.size()+ NumberBoolVariables) +
			   "\n%% Model constraints : "+initNumberConstraints+
			   "\n\n%% Search CPU time : " + (searchTimeMeter.getThreadCpuTime(tread.getId()) - startCPU)/(long)1e+6 + "ms"+
			   "\n%% Search nodes : "+nodes+
			   "\n%% Search decisions : "+decisions+
			   "\n%% Wrong search decisions : "+wrong+
			   "\n%% Search backtracks : "+backtracks+
			   "\n%% Max search depth : "+depth+
			   "\n%% Number solutions : "+ solutions 
			   );
	}

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
	    if (!master) label.setSelectChoicePoint(variable_selection);

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
	}
	else if (si.type().equals("set_search")) {
	    setSearch=true;
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
	}
	else if (si.type().equals("seq_search")) {
	    for (int i=0; i<si.getSearchItems().size(); i++)
		if (i == 0) { // master search
		    DepthFirstSearch<Var> label_seq = sub_search(si.getSearchItems().get(i), last_search, false);
		    last_search = label_seq;
		    label = label_seq;
		}
		else {
		    DepthFirstSearch<Var> label_seq = sub_search(si.getSearchItems().get(i), last_search, false);
		    last_search.addChildSearch(label_seq);
		    last_search = label_seq;
		}
	}
	else if (si.type().equals("float_search")) {
	    label = float_search(si);
	    if (!master) label.setSelectChoicePoint(variable_selection);

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
	}
	else {
	    System.err.println("Not recognized or supported search type \""+si.type()+"\"; compilation aborted");
	    System.exit(0);
	}

	return label;
    }

    DepthFirstSearch<Var> int_search(SearchItem si) {

        variable_selection = si.getIntSelect();
        return new DepthFirstSearch<Var>();
    }

    DepthFirstSearch<Var> set_search(SearchItem si) {

        variable_selection = si.getSetSelect();
        return new DepthFirstSearch<Var>();
    }

    DepthFirstSearch<Var> float_search(SearchItem si) {

        variable_selection = si.getFloatSelect();

	DepthFirstSearch<Var> label = new DepthFirstSearch<Var>();

	if (options.precision())
	    label.setInitializeListener(new PrecisionSetting(options.getPrecision()));
	else
	    label.setInitializeListener(new PrecisionSetting(si.precision));

        return label;
    }



    void printSolution() {

	// T = System.currentTimeMillis();
	// System.out.println("% Search time since last solution : " + (T - TOld)/1000 + " s");
	// TOld = T;

	if (dictionary.outputVariables.size() > 0)
	    for (int i=0; i<dictionary.outputVariables.size(); i++) {
		Var v = dictionary.outputVariables.get(i);

 		if (v instanceof BooleanVar) {
		    // print boolean variables
		    String boolVar = v.id()+" = ";
		    if (v.singleton())
			switch ( ((BooleanVar)v).value()) {
			case 0: boolVar += "false";
			    break;
			case 1: boolVar += "true";
			    break;
			default: boolVar += v.dom();
			}
		    else
			boolVar += "false..true";
		    System.out.println(boolVar+";");
		}
		else if (v instanceof SetVar) {
		    // print set variables
		    String setVar = v.id() + " = ";
		    if (v.singleton()) {
			IntDomain glb = ((SetVar)v).dom().glb();
			setVar += "{";
			for (ValueEnumeration e = glb.valueEnumeration(); e.hasMoreElements();) {
			    int element = e.nextElement();
			    setVar += element;
			    if (e.hasMoreElements())
				setVar += ", ";
			}
			setVar += "}";
		    }
		    else
			setVar += v.dom().toString();
		    System.out.println(setVar+";");
		}
		else
		    System.out.println(v+";");
	    }

	for (int i=0; i<dictionary.outputArray.size(); i++) {
	    OutputArrayAnnotation a = dictionary.outputArray.get(i);
	    System.out.println(a);
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
	    System.err.println("Not supported search kind; compilation aborted");
	    System.exit(0);
	    return -1;
	}
    }

    IntVar getCost(ASTSolveExpr node) {
	if (node.getType() == 0) // ident
	    return dictionary.getVariable(node.getIdent());
	else if (node.getType() == 1) { // array access
	    IntVar[] a = dictionary.getVariableArray(node.getIdent());
	    if ( a != null)
		return a[node.getIndex()];
	    else
		return null;
	}
	else {
	    System.err.println("Wrong cost function specification " + node);
	    System.exit(0);
	    return new IntVar(store);
	}
    }

    FloatVar getCostFloat(ASTSolveExpr node) {
	if (node.getType() == 0) // ident
	    return dictionary.getFloatVariable(node.getIdent());
	else if (node.getType() == 1) // array access
	    return dictionary.getVariableFloatArray(node.getIdent())[node.getIndex()];
	else {
	    System.err.println("Wrong cost function specification " + node);
	    System.exit(0);
	    return new FloatVar(store);
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

    void setNumberBoolVariables(int n) {
	NumberBoolVariables = n;
    }

    void printSearch(Search label) {

	int N = 1;
	System.out.println (N++ + ". " + label);

	java.util.LinkedHashSet<Search<? extends Var>> l = 
	    new java.util.LinkedHashSet<Search<? extends Var>>();
	l.add(label);

	while (l.size() != 0) {
	    java.util.LinkedHashSet<Search<? extends Var>> ns = 
		new java.util.LinkedHashSet<Search<? extends Var>>();
	    for (Search s1 : l) {
		Search<? extends Var>[] child = ((DepthFirstSearch)s1).childSearches;
		if (child != null)
		    for (Search s : child) {
			System.out.println (N + ". " + s);
			ns.add(s);	
		    }
	    }
	    N++;

	    l = ns;
	}
    }

    int FinalNumberSolutions = 0;

    /**
     * 
     * 
     * @author Krzysztof Kuchcinski
     *
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

	    if (costVariable != null)
		if (costVariable instanceof IntVar)
		    costValue = ((IntVar)costVariable).value();
		else
		    floatCostValue = ((FloatVar)costVariable).value();

	    FinalNumberSolutions++;

	    printSolution();
	    System.out.println("----------");

	    return returnCode;
	}
    }

    public class PrecisionSetting implements InitializeListener {

	InitializeListener[] initializeChildListeners;	

	double precision;

	PrecisionSetting(double p) {
	    precision = p;
	}

	public void executedAtInitialize(Store store) {
	    FloatDomain.setPrecision(precision);
	}

	public void setChildrenListeners(InitializeListener[] children) {
		initializeChildListeners = children;
	}

	public void setChildrenListeners(InitializeListener child) {
		initializeChildListeners = new InitializeListener[1];
		initializeChildListeners[0] = child;
	}
    }

    class DomainSizeComparator<T extends Var> implements Comparator<T> {

	DomainSizeComparator() { }

	public int compare(T o1, T o2) {
	    int v1 = o1.getSize();
	    int v2 = o2.getSize();
	    return v1 - v2;
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

}
