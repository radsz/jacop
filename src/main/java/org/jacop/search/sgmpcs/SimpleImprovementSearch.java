/**
 *  SimpleImprovementSearch.java 
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

import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.IntVar;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;

import org.jacop.search.Search;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.RandomSelect;
import org.jacop.search.SmallestMax;
import org.jacop.search.SmallestMin;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.IndomainDefaultValue;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.sgmpcs.SGMPCSCalculator;

/**
 * Defines an interface for defining different methods for selecting next search
 * decision to be taken. The search decision called choice point will be first
 * enforced and later upon backtrack a negation of that search decision will be
 * enforced.
 * 
 * @author krzysztof Kuchcinski
 * @version 4.2
 * @param <T> type of the variable for which choice point is being created.
 */

public class SimpleImprovementSearch<T extends IntVar> implements ImproveSolution<T> {


    boolean printInfo = true;

    /*
     * current store
     */
    public Store store;

    /*
     * search variable
     */
    public IntVar[] vars;

    /*
     * cost variable
     */
    IntVar cost;

    /*
     * The solution produced by last search
     */
    public int[] solution;

    /*
     * The cost produced by last search
     */
    int searchCost;

    long timeOut;

    public SGMPCSCalculator failCalculator;

    public SimpleImprovementSearch(Store store, IntVar[] vars, IntVar cost) {
	this.store = store;
	this.vars = vars;
	this.cost = cost;
    }

    public boolean searchFromEmptySolution(int failLimit) {

		DepthFirstSearch<IntVar> label = new DepthFirstSearch<IntVar>();
		SelectChoicePoint<IntVar> select = new SimpleSelect<IntVar>(vars, new SmallestMin<IntVar>(), new IndomainMin<IntVar>());
		// SelectChoicePoint<IntVar> select = new RandomSelect<IntVar>(vars, new IndomainRandom<IntVar>());
		label.setAssignSolution(false);
		label.setSolutionListener(new CostListener<IntVar>());
		label.getSolutionListener().recordSolutions(true);
		failCalculator = new SGMPCSCalculator(failLimit);
		label.setConsistencyListener(failCalculator);
		label.setPrintInfo(false);
		label.setTimeOut(timeOut);

		boolean result = label.labeling(store, select);

		if (result) {
		    Domain[] domSolution = label.getSolution();
		    solution = new int[domSolution.length];
		    for (int i = 0; i < domSolution.length; i++) 
		    	solution[i] = ((IntDomain)domSolution[i]).value();
		}

		return result;
    }

    public boolean searchFromEliteSolution(int[] eliteSolution, int failLimit) {

		HashMap<IntVar, Integer> mapping = new HashMap<IntVar, Integer>();
		for (int i = 0; i < eliteSolution.length-1; i++) 
		    mapping.put(vars[i], eliteSolution[i]);

		DepthFirstSearch<IntVar> label = new DepthFirstSearch<IntVar>();
		// SelectChoicePoint<IntVar> select = new SimpleSelect<IntVar>(vars, new SmallestMax<IntVar>(), 
		// 					       new IndomainDefaultValue<IntVar>(mapping, new IndomainRandom<IntVar>()));
		SelectChoicePoint<IntVar> select = new RandomSelect<IntVar>(vars, new IndomainDefaultValue<IntVar>(mapping, new IndomainMin<IntVar>()));
		label.setAssignSolution(false);
		label.setSolutionListener(new CostListener<IntVar>());
		label.getSolutionListener().recordSolutions(true);
		failCalculator = new SGMPCSCalculator(failLimit);
		label.setConsistencyListener(failCalculator);
		label.setPrintInfo(false);
		label.setTimeOut(timeOut);

		boolean result = label.labeling(store, select);

		if (result) {
		    Domain[] domSolution = label.getSolution();
		    solution = new int[domSolution.length];
		    for (int i = 0; i < domSolution.length; i++)
		    	solution[i] = ((IntDomain)domSolution[i]).value();
		}

		return result;
    }

    public int getCurrentCost() {
	return searchCost;
    }

    public int[] getSolution() {
	return solution;
    }

    public int getNumberFails() {
	return failCalculator.getNumberFails();
    }

    public int getFailLimit() {
	return failCalculator.getFailLimit();
    }

    public void setPrintInfo(boolean print) {
	printInfo = print;
    }

    public void setTimeOut(long timeOut) {
	this.timeOut = timeOut;
    }

    /**
     * Saves the cost produced by a given search
     * 
     * @author Krzysztof Kuchcinski
     *
     */
    public class CostListener<T extends IntVar> extends SimpleSolutionListener<T> {

	public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

	    boolean returnCode = super.executeAfterSolution(search, select);

	    searchCost = cost.value();

	    if (printInfo)
		System.out.println("----------\nCost = " + searchCost);

	    return returnCode;
	}
    }
}
