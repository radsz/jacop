/**
 *  SGMPCSearch.java 
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

package org.jacop.search.sgmpcs;

import java.util.HashMap;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Random;

import java.lang.Math;

import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.IntVar;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;

import org.jacop.constraints.XltC;

import org.jacop.search.Search;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.IndomainRandom;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainDefaultValue;
import org.jacop.search.SmallestMax;
import org.jacop.search.SmallestMin;
import org.jacop.search.SimpleSolutionListener;

/**
 * SGMPCSearch - implements Solution-Guided Multi-Point Constructive
 * Search. This search starts with several elite solutions and tries
 * to impove (minimizing cost variable) them by doing either search
 * assuming an elite solution or staring with an empty solution.
 *
 * This implementation is based on paper "Solution-guided Multi-point
 * Constructive Search for Job Shop Scheduling" by J. Christopher
 * Beck, Journal of Artificial Intelligence Research 29 (2007) 49–77.
 *
 * @author Krzysztof Kuchcinski
 * 
 * @version 4.2
 */

public class SGMPCSearch {

    public Store store;

    boolean trace = false;
    boolean printInfo = true;

    // Start time of the search to compute termination criteria
    long searchStartTime;

    /**
     * Variables for search
     */
    public IntVar[] vars;

    /**
     * Cost variable
     */
    public IntVar cost;

    /*
     * The cost produced by last search
     */
    int searchCost;

    /**
     * Parameters
     */

    // p- probablity of selecting search starting from reference
    // solution or from empty solution
    double p = 0.25;

    // e- number of elite solutions
    public int e = 4;

    // eInit- number of solution for selecting the best e elite solutions
    public int eInit = 20;

    // l- current fail limit
    int l;

    // strategy to get limit l on fails
    public final int luby = 1;
    public final int poly = 2;
    int strategy = poly;

    // elite solutions 
    // at position 0 is cost and values of variables start at positions 1
    public int[][] elite;

    // number of consequtive fails when searching for a solution
    int numberConsecutiveFails = 0;

    // index fro computing Luby number
    int lubyIndex = 1;

    // last found solution
    int[] solution;


    // time-out value in miliseconds (default 10 second)
    long timeOut=10000; 

    ImproveSolution<IntVar> search;

    public int costPosition;

    public SGMPCSearch(Store store, IntVar[] vars, IntVar cost) {

	this.store = store;
	this.vars = vars;
	this.cost = cost;       

	search = new SimpleImprovementSearch<IntVar>(store, vars, cost);
    }

    public SGMPCSearch(Store store, IntVar[] vars, IntVar cost, ImproveSolution search) {

    	this.store = store;
    	this.vars = vars;
    	this.cost = cost;

	this.search = search;

    }


    public boolean search() {

	l = (strategy == luby) ? getLuby(1) : 32;

	findEliteSolutions();

	int bestCostSolution = bestCostSolution();
	if (trace)
	    System.out.println("%% Best Cost elite solution is " + bestCostSolution + " with cost " + 
			       elite[bestCostSolution][costPosition]);

	improveSolution();

	return true;
    }

    /*
     * 	Finds elite solutions if they do not exist yet
     */
    public void findEliteSolutions() {

	if (elite == null) {
	    elite = new int[e][];
	    for (int i = 0; i < e; i++) 
		elite[i] = new int[vars.length+1];
	}
	else
	    return;

	costPosition = vars.length;
	for (int i = 0; i < vars.length; i++) 
	    if (vars[i] == cost)
		costPosition = i;

	IntVar[] v;
	if (costPosition == vars.length) {
	    v = new IntVar[vars.length+1];
	    for (int i = 0; i < vars.length; i++) 
		v[i] = vars[i];
	    v[vars.length] = cost;
	}
	else
	    v = vars;

	DepthFirstSearch<IntVar> label = new DepthFirstSearch<IntVar>();
	SelectChoicePoint<IntVar> select = new SimpleSelect<IntVar>(v, null,
								    new IndomainMin<IntVar>());
	label.getSolutionListener().searchAll(true); 
	label.getSolutionListener().recordSolutions(true);
	label.getSolutionListener().setSolutionLimit(eInit);
	label.setAssignSolution(false);
	label.setPrintInfo(false);

	label.labeling(store, select);

	int[][] solutionPool = new int[label.getSolutionListener().solutionsNo()][];
	for (int i=0; i<label.getSolutionListener().solutionsNo(); i++){ 
	    solutionPool[i] = new int[v.length];
	    for (int j=0; j<label.getSolution(i+1).length; j++) 
		solutionPool[i][j] = ((IntDomain)label.getSolution(i+1)[j]).value();
	}

	if (trace) {
	    System.out.println("%% Initial pool of solutions");

	    for (int i=0; i<solutionPool.length; i++){ 
		System.out.print("%% Solution " + (int)(i+1) + ": "); 
		for (int j=0; j<v.length; j++) 
		    System.out.print(solutionPool[i][j] + " ");
		System.out.println(); 
	    }
	}

	Arrays.sort(solutionPool, new SolutionComparator(costPosition));

	elite = new int[e][];
	for (int i=0; i<e; i++){ 
	    elite[i] = new int[solutionPool[i].length];
	    for (int j=0; j<elite[i].length; j++) 
		elite[i][j] = solutionPool[i][j];
	}
	

	if (trace) {
	    System.out.println("%% Selected best " + e + " solutions");
	    
	    for (int i=0; i<e; i++){
		System.out.print("%% Solution " + (int)(i+1) + ": "); 
		for (int j=0; j<v.length; j++) 
		    System.out.print(elite[i][j] + " ");
		System.out.println(); 
	    }
	}
    }


    /*
     * method tries to improve elite solutions by using
     * solution-guided multi-point constructive search
     */
    boolean improveSolution() {
    
	Random rand = new Random();
	Random randomSolution = new Random();

	searchStartTime = System.currentTimeMillis();

	search.setPrintInfo(printInfo);

	while (! terminationCriteria() ) {

	    long currentTime = System.currentTimeMillis();
	    long restTimeOut = (timeOut - (currentTime - searchStartTime))/1000;
	    if (restTimeOut <= 0)
		break; 

	    search.setTimeOut( restTimeOut );

	    int bestCost = elite[bestCostSolution()][costPosition];
	    store.impose(new XltC(cost, bestCost));

	    if (rand.nextFloat() < p) {

		boolean result = search.searchFromEmptySolution(l);

		if (!result) {
		    numberConsecutiveFails++;
		    updateFailLimit(true);
		}
		else {
		    if (printInfo)
		    	System.out.println("%% Fails "+ search.getNumberFails() + "(" + search.getFailLimit() + ")");

		    solution = search.getSolution();

		    if (printInfo) {
			System.out.println("%% Solution starting from empty " );
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
		}
		else {

		    if (printInfo)
		    	System.out.println("%% Fails "+ search.getNumberFails() + "(" + search.getFailLimit() + ")");

		    solution = search.getSolution();

		    if (printInfo) {
			System.out.println("%% Solution starting from reference with cost " + elite[n][costPosition]);
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

	boolean termination = false;

	long currentTime = System.currentTimeMillis();

	// terminate after time-out or when optimal
	termination = (currentTime - searchStartTime > timeOut) || 
	    (numberConsecutiveFails > 0 && search.getNumberFails() < search.getFailLimit());

	if (printInfo && termination) {
	    System.out.println("%% Termination search fails "+ search.getNumberFails() + 
			       "(" + search.getFailLimit() + ")");

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
	    if (fail)
		l += 32;
	    else
		l = 32;

	} 
	// Luby
	else {
	    l = getLuby(lubyIndex);

	    lubyIndex++;
	}
    }

    public int getLuby(int i) {

	if ( i == 1) {
	    return 1;
	}

	double k = Math.log(i+1)/Math.log(2d);

	if (k == Math.floor(k+0.5)) {
	    return (int)Math.pow(2, k-1);
	} else {
	    k = Math.floor(k);
	    return getLuby(i - (int)Math.pow(2, k) + 1);
	}
    }

    /* 
     * Finds a solution with minimal cost
     */
    int bestCostSolution() {
	 int currentCost = IntDomain.MaxInt;
	 int solution = -1;

	 for (int i = 0; i < elite.length; i++) 
	     if (currentCost > elite[i][costPosition]) {
		 currentCost = elite[i][costPosition];
		 solution = i;
	     }

	 return solution;
     }

    /* 
     * Finds a solution with maximal cost
     */
    int worstCostSolution() {
	 int currentCost = IntDomain.MinInt;
	 int solution = -1;

	 for (int i = 0; i < elite.length; i++) 
	     if (currentCost < elite[i][costPosition]) {
		 currentCost = elite[i][costPosition];
		 solution = i;
	     }

	 return solution;
     }

    public void setEliteSolutions(int[][] solutions) {
	if (solutions.length != e) {
	    System.out.println("Number of initial siolutions not correct; it is " + solutions.length + "and should be " + e);
	    return;
	}

	elite = new int[e][];
	for (int i=0; i<e; i++){ 
	    elite[i] = new int[solutions[i].length];
	    for (int j=0; j<elite[i].length; j++) 
		elite[i][j] = solutions[i][j];
	}
    }

    void replaceEliteSolution(int n, int[] solution, int searchCost) {

	for (int i = 0; i < elite[n].length-1; i++) 
	    elite[n][i] = solution[i];
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
	if (strategy == poly || strategy == luby)
	    this.strategy = strategy;
	else {
	    System.out.println("Wrong fail strategy limit; assumed poly");

	    this.strategy = poly;
	}
    }

    public void setPrintInfo(boolean print) {
	printInfo = print;
    }

    public void printSolution(int[] solution) {

	    for (int i = 0; i < solution.length; i++) {
		System.out.print(solution[i] + " ");

	    }
	    System.out.println();
    }


    public int[] lastSolution() {
	return solution;
    }

    public int lastCost() {
	return searchCost;
    }

    public class SolutionComparator implements Comparator<int[]> {

	int p;

	public SolutionComparator(int costPosition) {
	    p = costPosition;
	}

	@Override
	public int compare(int[] o1, int[] o2) {
	    return (o1[p] - o2[p]);
	}
    }


}
